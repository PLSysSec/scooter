use policy_lang::ir::{
    expr::{ExprType, Func},
    policy::Policy,
    schema::{Collection, Field, Schema},
    Ident,
};
use std::{
    collections::HashMap,
    fmt::Display,
    io::{BufRead, BufReader, Write},
    process::{Command, Stdio},
};

use translate::*;
mod translate;

pub struct Equiv(pub Ident<Field>, pub Func);

pub fn is_as_strict(
    schema: &Schema,
    eqs: &[Equiv],
    coll: &Ident<Collection>,
    before: &Policy,
    after: &Policy,
) -> Result<(), Model> {
    let verif_problem = gen_assert(schema, &eqs, coll, before, after);
    let assertion = verif_problem
        .stmts
        .iter()
        .map(Statement::to_string)
        .collect::<Vec<_>>()
        .join("");
    eprintln!("{}", assertion);
    let mut child = Command::new("z3")
        .arg("-smt2")
        .arg("-in")
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .spawn()
        .expect("Unable to spawn z3");

    {
        let input = child
            .stdin
            .as_mut()
            .expect("Failed to open stdin of z3 process");
        input
            .write_all(assertion.as_bytes())
            .expect("Error writing to z3 input");
        input
            .write_all("(check-sat)\n".as_bytes())
            .expect("Error writing to z3 input");

        let output = child.stdout.as_mut().expect("Error capturing z3 output");
        let mut reader = BufReader::new(output);
        let mut sat_result = String::new();
        reader
            .read_line(&mut sat_result)
            .expect("Unable to read SAT result");

        match sat_result.as_str() {
            "unsat\n" => {
                child.wait().expect("Error closing z3 process");
                return Ok(());
            }
            "sat\n" => {}
            s => panic!("Unable to read SMT output: {}", s),
        }

        let mut line = String::new();
        input
            .write_all("(get-model)\n(eval \"ENDMODEL\")\n".as_bytes())
            .unwrap();
        while line != "\"ENDMODEL\"\n" {
            line = String::new();
            reader.read_line(&mut line).unwrap();
        }
        input
            .write_all(format!("(eval {})\n", ident(&verif_problem.princ)).as_bytes())
            .unwrap();
        line = String::new();
        reader.read_line(&mut line).unwrap();
        let princ = line.trim().to_owned();

        let mut model = Model {
            princ,
            objects: vec![],
        };
        let mut tables_to_vars: HashMap<Ident<Collection>, Vec<Ident<SMTVar>>> = HashMap::new();
        for (coll_id, var_id) in join_objects(&verif_problem) {
            let vars = tables_to_vars.entry(coll_id).or_insert(Vec::new());
            (*vars).push(var_id);
        }
        for (coll_id, var_id) in db_objects(&verif_problem) {
            let mut fields = vec![];
            let maybe_coll = schema.collections.iter().find(|c| c.name == coll_id);
            let coll = match maybe_coll {
                Some(ref coll) => coll,
                None => continue,
            };
            for field in coll.fields() {
                match &field.typ {
                    ExprType::Set(_inner_ty) => {
                        let mut lines = Vec::new();
                        let (join_coll_id, _from_id, to_id, _typ) =
                            &verif_problem.join_tables[&field.name];
                        if let Some(vars) = tables_to_vars.get(&join_coll_id) {
                            for var in vars {
                                input
                                    .write_all(
                                        format!("(eval ({} {}))\n", ident(&to_id), ident(&var))
                                            .as_bytes(),
                                    )
                                    .unwrap();
                                line = String::new();
                                reader.read_line(&mut line).unwrap();
                                lines.push(line.trim().to_owned());
                            }
                        }

                        fields.push((field.name.clone(), format!("[{}]", lines.join(", "))));
                    }
                    ExprType::I64 => {
                        input
                            .write_all(
                                format!("(eval ({} {}))\n", ident(&field.name), ident(&var_id))
                                    .as_bytes(),
                            )
                            .unwrap();
                        line = String::new();
                        reader.read_line(&mut line).unwrap();
                        let raw = line.trim().trim_start_matches("#x");
                        fields.push((
                            field.name.clone(),
                            format!(
                                "{}",
                                i64::from_str_radix(raw, 16)
                                    .expect(&format!("Couldn't parse hex {}", raw))
                            ),
                        ))
                    }
                    _ => {
                        input
                            .write_all(
                                format!("(eval ({} {}))\n", ident(&field.name), ident(&var_id))
                                    .as_bytes(),
                            )
                            .unwrap();
                        line = String::new();
                        reader.read_line(&mut line).unwrap();
                        fields.push((field.name.clone(), line.trim().to_owned()));
                    }
                };
            }
            let obj = ModelObject {
                coll: coll.name.clone(),
                fields,
                is_record: var_id == verif_problem.rec,
            };
            model.add_obj(obj);
        }

        Err(model)
    }
}

fn db_objects<'a>(
    vp: &'a VerifProblem,
) -> impl Iterator<Item = (Ident<Collection>, Ident<SMTVar>)> + 'a {
    vp.stmts.iter().filter_map(move |stmt| match stmt {
        Statement::DeclFun {
            id,
            params,
            typ: ExprType::Object(ref coll),
        } if params.is_empty() => Some((coll.clone(), id.clone())),
        _ => None,
    })
}
fn join_objects<'a>(
    vp: &'a VerifProblem,
) -> impl Iterator<Item = (Ident<Collection>, Ident<SMTVar>)> + 'a {
    let join_vals = vp.join_tables.values().collect::<Vec<_>>();
    vp.stmts.iter().filter_map(move |stmt| match stmt {
        Statement::DeclFun {
            id,
            params,
            typ: ExprType::Object(ref coll),
        } if params.is_empty() && join_vals.iter().find(|t| t.0 == *coll).is_some() => {
            Some((coll.clone(), id.clone()))
        }
        _ => None,
    })
}

#[derive(Debug)]
pub struct Model {
    princ: String,
    objects: Vec<ModelObject>,
}

impl Model {
    fn add_obj(&mut self, m: ModelObject) {
        let mut duplicate: Option<&mut ModelObject> = None;
        let mut is_referenced = false;
        for obj in self.objects.iter_mut() {
            for (_, field_str_value) in obj.fields.iter() {
                let m_id = m
                    .fields
                    .iter()
                    .find(|(ident, _)| ident.orig_name == "id")
                    .unwrap()
                    .1
                    .clone();
                if field_str_value.contains(&m_id) {
                    is_referenced = true;
                }
            }
            if *obj == m {
                duplicate = Some(obj);
            }
        }
        if !is_referenced {
            match duplicate {
                Some(obj) => {
                    obj.is_record = obj.is_record || m.is_record;
                    return;
                }
                None => (),
            };
        }
        self.objects.push(m);
    }

    fn rec(&self) -> &ModelObject {
        self.objects.iter().find(|obj| obj.is_record).unwrap()
    }
}

impl Display for Model {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let rec = self.rec();
        write!(f, "Model:\nprinc: {}\nrec: {}\n", self.princ, rec)?;

        for obj in self.objects.iter() {
            if obj != rec {
                write!(f, "{}\n", obj)?;
            }
        }
        Ok(())
    }
}

#[derive(Debug, Eq)]
pub struct ModelObject {
    coll: Ident<Collection>,
    fields: Vec<(Ident<Field>, String)>,
    is_record: bool,
}

impl PartialEq for ModelObject {
    fn eq(&self, other: &Self) -> bool {
        if self.coll != other.coll {
            return false;
        }

        for (l, r) in self.fields.iter().zip(other.fields.iter()) {
            if l.0.orig_name == "id" {
                continue;
            }
            if l != r {
                return false;
            }
        }

        return true;
    }
}

impl Display for ModelObject {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let mut dbug_struct = f.debug_struct(&self.coll.orig_name);
        for (f_id, val) in self.fields.iter() {
            dbug_struct.field(&f_id.orig_name, val);
        }
        dbug_struct.finish()
    }
}
