use policy_lang::ir::{
    expr::{ExprType, Func},
    policy::Policy,
    schema::{Collection, Field, Schema},
    Ident,
};
use std::{collections::HashMap, fmt::{Debug, Display}, io::{BufRead, BufReader, Write}, process::{Command, Stdio}};
use lazy_static::lazy_static;
use regex::Regex;
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
        let princ = parse(&ExprType::Principal, line.trim());

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
                    if let ExprType::Set(_inner_ty) = &field.typ {
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
                    } else {
                        input
                            .write_all(
                                format!("(eval ({} {}))\n", ident(&field.name), ident(&var_id))
                                    .as_bytes(),
                            )
                            .unwrap();
                        line = String::new();
                        reader.read_line(&mut line).unwrap();

                        let clean_value = parse(&field.typ, &line.trim());
                        fields.push((field.name.clone(), clean_value));

                    }
                    // ExprType::I64 => {
                    //     input
                    //         .write_all(
                    //             format!("(eval ({} {}))\n", ident(&field.name), ident(&var_id))
                    //                 .as_bytes(),
                    //         )
                    //         .unwrap();
                    //     line = String::new();
                    //     reader.read_line(&mut line).unwrap();
                    //     let raw = line.trim().trim_start_matches("#x");
                    //     fields.push((
                    //         field.name.clone(),
                    //         format!(
                    //             "{}",
                    //             i64::from_str_radix(raw, 16)
                    //                 .expect(&format!("Couldn't parse hex {}", raw))
                    //         ),
                    //     ))
                    // }
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

fn parse(typ: &ExprType, text: &str) -> String {
    match typ {
        ExprType::I64 => {
            i64::from_str_radix(text.trim_start_matches("#x"), 16).expect(&format!("Couldn't parse hex from SMT {}", text)).to_string()
        }
        ExprType::Id(_) => {
            lazy_static! {
                static ref ID_RE: Regex = Regex::new(r#"_i\d+!val!(?P<id>\d+)"#).unwrap();
            }
            ID_RE.replace_all(text, "($id)").into()
        },
        ExprType::Principal => {
            lazy_static! {
                static ref ID_PRINC: Regex = Regex::new(r#"\(\S+ (?P<id>[^)]*)\)"#).unwrap();
            }
            if ID_PRINC.is_match(text) {
                parse(&ExprType::Id(Ident::new("dummy")), &ID_PRINC.replace_all(text, "$id"))
            } else {
                text.to_owned()
            }
        }
        _ => {
            text.to_owned()
        }
    }
}

fn db_objects<'a>(
    vp: &'a VerifProblem
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

        if m.is_record || self.princ.contains(&m.id()) {
            self.objects.push(m);
            return;
        }
        for obj in self.objects.iter_mut() {
            for (_, field_str_value) in obj.fields.iter() {
                if field_str_value.contains(&m.id()) {
                    is_referenced = true;
                }
            }
            if *obj == m && !(obj.is_record || obj.id() == self.princ) {
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
        write!(f, "Principal: {}\n\nCAN NOW ACCESS:\n\n{:#}\n\nOTHER RECORDS:\n\n", self.princ, rec)?;

        for obj in self.objects.iter() {
            if obj.id() != rec.id() {
                write!(f, "{:#}\n", obj)?;
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

impl ModelObject {
    fn id(&self) -> String {
        self.fields
            .iter()
            .find(|(ident, _)| ident.orig_name == "id")
            .unwrap()
            .1
            .clone()
    }
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
            dbug_struct.field(&f_id.orig_name, &Literal(val));
        }
        dbug_struct.finish()
    }
}

struct Literal<'a>(&'a str);
impl<'a> Debug for Literal<'a> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.0)
    }
}
