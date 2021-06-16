use lazy_static::lazy_static;
use policy_lang::ir::{
    expr::{ExprType, Func},
    policy::Policy,
    schema::{Collection, Field, Schema},
    Ident,
};
use regex::Regex;
use std::{
    collections::{HashMap, HashSet},
    env,
    fmt::{Debug, Display},
    io::{BufRead, BufReader, Write},
    process::{ChildStdin, ChildStdout, Command, Stdio},
};
//use translate::*;
//mod translate;
mod translate2;
use translate2::*;

#[derive(Clone)]
pub struct Equiv(pub Ident<Field>, pub Func);

pub fn is_as_strict(
    schema: &Schema,
    eqs: &[Equiv],
    coll: &Ident<Collection>,
    before: &Policy,
    after: &Policy,
) -> Result<(), Model> {
    let verif_problem = gen_assert(schema, eqs, coll, before, after);
    let assertion = verif_problem
        .stmts
        .iter()
        .map(Statement::to_string)
        .collect::<Vec<_>>()
        .join("");
    let asserts = verif_problem
        .stmts
        .iter()
        .filter_map(|s| match s {
            Statement::Assert(_) => Some(s.to_string()),
            _ => None,
        })
        .collect::<Vec<_>>()
        .join("\n");
    let mut child = Command::new(&env::var("Z3_OVERRIDE").unwrap_or("z3".to_string()))
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
        let output = child.stdout.as_mut().expect("Error capturing z3 output");
        let mut reader = BufReader::new(output);

        input
            .write_all(assertion.as_bytes())
            .expect("Error writing to z3 input");

        let sat_result = exec_with_result_line(input, &mut reader, "(check-sat)\n");

        match sat_result.as_str() {
            "unsat" => {
                child.wait().expect("Error closing z3 process");
                return Ok(());
            }
            "sat" => {}
            s => panic!("Unable to read SMT output: {}", s),
        }

        let model_str = read_model(input, &mut reader);
        // The model we get back is a little bad
        let model_str = clean_model(&model_str);

        // Clear the verif problem
        input
            .write_all("(pop 1)\n".as_bytes())
            .expect("Error writing to z3 input");

        // Write the model
        input
            .write_all(model_str.as_bytes())
            .expect("Error writing to z3 input");

        let _sat =
            exec_with_result_line(input, &mut reader, &format!("\n{}\n(check-sat)\n", asserts));

        let princ = parse(
            &ExprType::Principal,
            &exec_with_result_line(
                input,
                &mut reader,
                &format!("(eval {})\n", ident(&verif_problem.princ)),
            ),
        );
        let rec = exec_with_result_line(
            input,
            &mut reader,
            &format!("(eval {})\n", ident(&verif_problem.rec)),
        );

        let mut model = Model {
            princ,
            rec_id: parse(&ExprType::Id(coll.clone()), &rec),
            objects: Vec::new(),
        };

        let tables_to_vars = extract_vars(&model_str);

        let mut join_vals = HashMap::<Ident<Field>, Vec<(String, String)>>::new();
        for (field, (coll, from, to, ty)) in verif_problem.join_tables {
            let mut vals = vec![];
            for id in tables_to_vars[&coll].iter() {
                let from = exec_with_result_line(
                    input,
                    &mut reader,
                    &format!("(eval ({} {}))\n", ident(&from), id),
                );

                let raw_to = exec_with_result_line(
                    input,
                    &mut reader,
                    &format!("(eval ({} {}))\n", ident(&to), id),
                );
                let to = parse(&ty, &raw_to.trim());

                vals.push((from, to));
            }
            join_vals.insert(field, vals);
        }

        for (coll_id, ids) in tables_to_vars.iter() {
            let maybe_coll = schema.collections.iter().find(|c| c.name == *coll_id);
            let coll = match maybe_coll {
                Some(ref coll) => coll,
                None => continue,
            };
            for id in ids {
                let mut fields = vec![];
                for field in coll.fields() {
                    if matches!(field.typ, ExprType::Set(_)) {
                        let x = join_vals[&field.name]
                            .iter()
                            .filter(|(from, _)| from == id)
                            .map(|(_, to)| to.clone())
                            .collect::<Vec<_>>()
                            .join(", ");

                        fields.push((field.name.clone(), format!("[{}]", x)));
                        continue;
                    }

                    let val = exec_with_result_line(
                        input,
                        &mut reader,
                        &format!("(eval ({} {}))\n", ident(&field.name), id),
                    );
                    let clean_value = parse(&field.typ, &val);

                    fields.push((field.name.clone(), clean_value));
                }

                let obj = ModelObject {
                    coll: coll.name.clone(),
                    fields,
                };

                model.objects.push(obj);
            }
        }

        Err(model)
    }
}

fn parse(typ: &ExprType, text: &str) -> String {
    match typ {
        ExprType::I64 => i64::from_str_radix(text.trim_start_matches("#x"), 16)
            .expect(&format!("Couldn't parse hex from SMT {}", text))
            .to_string(),
        ExprType::Id(_) => {
            lazy_static! {
                static ref ID_RE: Regex = Regex::new(r#"_i\d+!val!(?P<id>\d+)"#).unwrap();
            }
            ID_RE.replace_all(text, "($id)").into()
        }
        ExprType::Principal => {
            lazy_static! {
                static ref ID_PRINC: Regex = Regex::new(r#"\(\S+ (?P<id>[^)]*)\)"#).unwrap();
            }
            if ID_PRINC.is_match(text) {
                parse(
                    &ExprType::Id(Ident::new("dummy")),
                    &ID_PRINC.replace_all(text, "$id"),
                )
            } else {
                text.to_owned()
            }
        }
        _ => text.to_owned(),
    }
}

#[derive(Debug)]
pub struct Model {
    princ: String,
    rec_id: String,
    objects: Vec<ModelObject>,
}

impl Model {
    fn rec(&self) -> &ModelObject {
        self.objects.iter().find(|o| o.id() == self.rec_id).unwrap()
    }
}

impl Display for Model {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let rec = self.rec();
        write!(
            f,
            "Principal: {}\n\nCAN NOW ACCESS:\n\n{:#}\n\nOTHER RECORDS:\n\n",
            self.princ, rec
        )?;

        for obj in self.objects.iter() {
            if &obj.id() != &self.rec_id {
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

fn clean_model(model: &str) -> String {
    lazy_static! {
        static ref CARDINAL: Regex = Regex::new(r#";; cardinality constraint:([^;]*)"#).unwrap();
    }
    let clean = CARDINAL.replace_all(model, "(assert $1)");
    clean[1..clean.len() - 3].into()
}

fn extract_vars(model: &str) -> HashMap<Ident<Collection>, HashSet<String>> {
    lazy_static! {
        static ref UNIVERSE: Regex =
            Regex::new(r#";; universe for ([^:]*)_i([^:]*):\s*;;([^;]*)"#).unwrap();
        static ref ID: Regex = Regex::new(r#"\S+"#).unwrap();
    }

    UNIVERSE
        .captures_iter(model)
        .map(|cap| {
            let typ = cap.get(1).map(|u| u.as_str()).unwrap();
            let idx: u32 = cap
                .get(2)
                .map(|u| u.as_str().parse::<u32>().unwrap())
                .unwrap();
            let coll = Ident::unsafe_construct(idx, typ.into());
            let elems = cap.get(3).map(|u| u.as_str()).unwrap();
            let ids = ID
                .find_iter(elems)
                .map(|m| m.as_str().to_string())
                .collect();
            (coll, ids)
        })
        .collect()
}

fn read_model(input: &mut ChildStdin, reader: &mut BufReader<&mut ChildStdout>) -> String {
    let mut line = String::new();
    input
        .write_all("(get-model)\n(eval \"ENDMODEL\")\n".as_bytes())
        .unwrap();
    let mut model_str = String::new();
    while line != "\"ENDMODEL\"\n" {
        model_str += &line;
        line = String::new();
        reader.read_line(&mut line).unwrap();
    }

    model_str
}

fn exec_with_result_line(
    input: &mut ChildStdin,
    reader: &mut BufReader<&mut ChildStdout>,
    cmd: &str,
) -> String {
    let mut line = String::new();
    input.write_all(cmd.as_bytes()).unwrap();
    reader.read_line(&mut line).unwrap();

    line.trim().to_string()
}
