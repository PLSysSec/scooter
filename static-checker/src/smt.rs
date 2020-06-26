use policy_lang::ir::{
    policy::Policy,
    schema::{Collection, Schema},
    Ident, expr::ExprType,
};
use std::{
    io::{BufReader, BufRead, Write},
    process::{Command, Stdio},
};

use translate::*;
mod translate;

pub fn is_as_strict(schema: &Schema, coll: &Ident<Collection>, before: &Policy, after: &Policy) -> Result<(), String> {
    let verif_problem = gen_assert(schema, coll, before, after);
    let assertion = verif_problem.stmts.iter().map(Statement::to_string).collect::<Vec<_>>().join("");
    let mut child = Command::new("z3")
        .arg("-smt2")
        .arg("-in")
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .spawn()
        .expect("Unable to spawn z3");

    let mut model = String::new();
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
        reader.read_line(&mut sat_result).expect("Unable to read SAT result");

        match sat_result.as_str() {
            "unsat\n" => {
                child.wait().expect("Error closing z3 process");
                return Ok(());
            }
            "sat\n" => {}
            s => panic!("Unable to read SMT output: {}", s),
        }

        let mut line = String::new();
        input.write_all("(get-model)\n(eval \"ENDMODEL\")\n".as_bytes()).unwrap();
        while line != "\"ENDMODEL\"\n" {
            line = String::new();
            reader.read_line(&mut line).unwrap();
        }
        let mut model = String::new();
        for (coll_id, var_id) in objects(schema, &verif_problem) {
            let coll = &schema[&coll_id];
            if var_id == verif_problem.princ {
                model += "@principle\n"
            }
            if var_id == verif_problem.rec {
                model += "@record\n"
            }
            model += &coll.name.orig_name;
            model += "{\n";
            for field in coll.fields() {
                input.write_all(format!("(eval ({} {}))\n", ident(&field.name), ident(&var_id)).as_bytes()).unwrap();
                line = String::new();
                reader.read_line(&mut line).unwrap();
                model += "\t";
                model += &field.name.orig_name;
                model += ": ";
                model += &line;
            }
            model += "}\n\n"
        }

        Err(model)
    }
}

fn objects<'a>(schema: &'a Schema, vp: &'a VerifProblem) -> impl Iterator<Item=(Ident<Collection>, Ident<SMTVar>)> + 'a {
    vp.stmts.iter().filter_map(move |stmt| {
        match stmt {
            Statement::DeclFun { id, params, typ: ExprType::Object(ref coll)} if params.is_empty() => {
                Some((coll.clone(), id.clone()))
            }
            Statement::DeclFun { id, params, typ: ExprType::Id(ref coll)} if *id == vp.princ => {
                Some((coll.clone(), id.clone()))
            },
            _ => None
        }   
    })
}