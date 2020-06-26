use policy_lang::ir::{
    expr::{ExprType, Func, IRExpr},
    policy::Policy,
    schema::{Collection, Schema},
    Ident,
};
use std::{
    io::Write,
    process::{Command, Stdio},
    str::from_utf8, fmt::Display,
};

pub fn is_as_strict(schema: &Schema, coll: &Ident<Collection>, before: &Policy, after: &Policy) -> bool {
    let assertion = gen_assert(schema, coll, before, after);
    eprintln!("{}", &assertion);
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
    };

    let output = child.wait_with_output().expect("Error capturing z3 output");

    let output_txt: &str = from_utf8(&output.stdout).expect("Error parsing z3 output");

    return output_txt == "unsat\n";
}

pub fn gen_assert(schema: &Schema, coll: &Ident<Collection>, before: &Policy, after: &Policy) -> String {
    let schema_str = lower_schema(schema);
    let princ_type =  ExprType::Id(schema.principle.clone().expect("Schemas are guaranteed to have a policy at this point"));

    let princ_id = Ident::new("principle");
    let rec_id = Ident::new("rec");

    // Declare the principle and record
    let princ = declare(princ_id.clone(), princ_type);
    let rec = declare(rec_id.clone(),ExprType::Object(coll.clone()));

    // Lower the functions
    let before= lower_policy(&princ_id, &rec_id, coll, before);
    let after = lower_policy(&princ_id, &rec_id, coll, after);


    let safety_assertion = Statement::Assert(format!(
        "(and {} (not {}))",
        &after.expr,
        &before.expr,
    ));

    schema_str + &princ.to_string() + &rec.to_string() + &before.stmts.iter().chain(after.stmts.iter()).map(Statement::to_string).collect::<String>() + &safety_assertion.to_string() + "(check-sat)"
}

#[derive(Debug, Copy, Clone)]
struct SMTVar;



struct SMTResult {
    stmts: Vec<Statement>,
    expr: String,
}

impl SMTResult {
    fn expr(e: impl ToString) -> Self {
        Self {
            stmts: vec![], expr: e.to_string()
        }
    }

    fn new(stmts: Vec<Statement>, expr: impl ToString) -> Self {
        Self {
            stmts, expr: expr.to_string()
        }
    }
}

fn lower_policy(princ: &Ident<SMTVar>, rec: &Ident<SMTVar>, coll: &Ident<Collection>, pol: &Policy) -> SMTResult {
    let typ = ExprType::list(ExprType::Object(coll.clone()));
    let id= Ident::new("policy");
    let stmts = match pol {
        Policy::None => vec![define(id.clone(),  ExprType::Bool, false)],
        Policy::Anyone => vec![define(id.clone(), ExprType::Bool, true)],
        Policy::Func(f) => {
            // Declare the function param as a synonym for the record.
            // This will allow easy lowering of var's while still ensuring
            // that every policy references the same record
            let param = define(f.param.coerce(), f.param_type.clone(), ident(rec));
            let f = lower_expr(princ, &f.body);
            let func = define(id.clone(), ExprType::Bool, &f.expr);

            let mut out = f.stmts;
            out.insert(0, param);
            out.push(func);
            out
        }
    };

    SMTResult::new(stmts, ident(&id))
}


fn lower_expr(target: &Ident<SMTVar>, body: &IRExpr) -> SMTResult {
    debug_assert!(!contains_unknown(&body.type_of()));

    match body {
        IRExpr::AppendS(l, r) => simple_nary_op("str.++", target, body.type_of(), &[l, r]),
        IRExpr::AddI(l, r) | IRExpr::AddF(l, r) => simple_nary_op("+", target, body.type_of(), &[l, r]),
        IRExpr::SubI(l, r) | IRExpr::SubF(l, r) => simple_nary_op("-", target, body.type_of(), &[l, r]),
        // In policylang, equality is not defined for lists so no special handling is needed
        IRExpr::IsEq(_, l, r) => simple_nary_op("=", target, body.type_of(), &[l, r]),
        IRExpr::Not(b) => simple_nary_op("not", target, body.type_of(), &[b]),
        IRExpr::IsLessI(l, r) | IRExpr::IsLessF(l, r) => simple_nary_op("<", target, body.type_of(), &[l, r]),
        IRExpr::IntToFloat(b) => simple_nary_op("to-real", target, body.type_of(), &[b]),
        IRExpr::Path(_, obj, f) => simple_nary_op(&ident(f), target, body.type_of(), &[obj]),
        IRExpr::Var(_, i) => SMTResult::expr(ident(i)),
        // Because id's and object types are the same, find is a no-op
        IRExpr::LookupById(_, b) => lower_expr(target, b),
        IRExpr::IntConst(i) => SMTResult::expr(i),
        IRExpr::FloatConst(f) => SMTResult::expr(f),
        IRExpr::StringConst(s) => SMTResult::expr(format!("\"{}\"", s)),
        IRExpr::BoolConst(b) => SMTResult::expr(b),
        IRExpr::Find(_, fields) => {
            let mut stmts = vec![];
            let mut equalities = vec![];
            for (f, expr) in fields.iter() {
                let field_expr = lower_expr(target, expr);

                equalities.push(format!(
                    "(= ({} {}) {})\n",
                    ident(f),
                    ident(target),
                    &field_expr.expr
                ));

                stmts.extend(field_expr.stmts)
            }

            let anded_eqs = format!("(and {} true)", spaced(equalities.into_iter()));

            SMTResult::new(stmts, anded_eqs)
        }
        IRExpr::Object(coll, fields, template) => {
            let obj_id = Ident::new("obj_lit");
            let obj = declare(obj_id.clone(), ExprType::Object(coll.clone()));
            let template_expr = template.as_ref().map(|t| lower_expr(target, t));

            let mut stmts = vec![obj];
            let mut exprs = vec![];
            for (f_id, f_expr) in fields.iter() {
                if let Some(e) = f_expr {
                    let low_e = lower_expr(target, e);
                    exprs.push(format!("(= {} {})", ident(&obj_id), &low_e.expr));
                    stmts.extend(low_e.stmts);
                } else {
                    exprs.push(format!("(= {} {})", ident(&obj_id), template_expr.as_ref().unwrap().expr))
                }
            }

            stmts.push(Statement::Assert(format!("(and {})", spaced(exprs.into_iter()))));

            SMTResult::new(stmts, ident(&obj_id))
        }
        IRExpr::Map(_list_expr, _func) => {
            panic!("Unimplemented");
        }
        IRExpr::AppendL(_, l, r) => {
            let left= lower_expr(target, l);
            let right = lower_expr(target, r);
            let expr = format!("(or {} {})", &left.expr, &right.expr);

            let mut stmts = left.stmts;
            stmts.extend(right.stmts);
            SMTResult::new(stmts, expr)
        }
        IRExpr::List(_, exprs) => {
            let mut stmts = vec![];
            let mut equalities = vec![];
            for expr in exprs.iter() {
                let elem_expr = lower_expr(target, expr);

                equalities.push(format!(
                    "(= {} {})\n",
                    ident(target),
                    &elem_expr.expr
                ));

                stmts.extend(elem_expr.stmts)
            }

            let expr = format!("(or {} false)", spaced(equalities.into_iter()));
            SMTResult::new(stmts, expr)
        }
        IRExpr::If(_, c, t, e) => simple_nary_op("ite", target, body.type_of(), &[c, t, e]),
    }
}


/// Lowers the schema to a String containing an SMT2LIB script
fn lower_schema(schema: &Schema) -> String {
    schema.collections.iter().map(lower_collection).collect()
}

/// Lowers each collection one by one.
/// Each collection gets its own sort named after its Ident,
/// and each field is a function mapping that sort to either a native
/// SMT sort or to another sort.
fn lower_collection(coll: &Collection) -> String {
    let sort = format!("(declare-sort {})\n", ident(&coll.name));
    let fields: String = coll
        .fields()
        .map(|f| {
            if f.is_id() {
                format!(
                    "(define-fun {} ((x {})) {} x)\n",
                    ident(&f.name),
                    ident(&coll.name),
                    type_name(&f.typ)
                )
            } else {
                format!(
                    "(declare-fun {} ({}) {})\n",
                    ident(&f.name),
                    ident(&coll.name),
                    type_name(&f.typ)
                )
            }
        })
        .collect();
    sort + &fields
}

pub fn ident<T>(ident: &Ident<T>) -> String {
    format!("{}_i{}", ident.orig_name, ident.index)
}

pub fn type_name(typ: &ExprType) -> String {
    match typ {
        ExprType::String => "String".to_owned(),
        ExprType::I64 => "Int".to_owned(),
        ExprType::F64 => "Real".to_owned(),
        ExprType::Bool => "Bool".to_owned(),
        ExprType::List(t) => format!("(Array {} Bool)", type_name(t)),
        ExprType::Unknown(_) => panic!("ListUnknowns should never be serialized"),

        // Ids and objects are the same in SMT land
        ExprType::Id(t) | ExprType::Object(t) => ident(t),
    }
}

#[cfg(debug_assertions)]
/// A helper function used for debug asserts to guarantee we don't unknown types (i.e. empty lists)
fn contains_unknown(typ: &ExprType) -> bool {
    match typ {
        // Ids and objects are the same in SMT land
        ExprType::Id(_)
        | ExprType::Object(_)
        | ExprType::String
        | ExprType::I64
        | ExprType::F64
        | ExprType::Bool => false,
        ExprType::Unknown(_) => true,
        ExprType::List(t) => contains_unknown(t),
    }
}





fn simple_nary_op(op: &str, target: &Ident<SMTVar>, typ: ExprType, exprs: &[&IRExpr]) -> SMTResult {
    let (stmts, exprs): (Vec<Vec<Statement>>, Vec<String>) = exprs.into_iter().map(|e| lower_expr(target, e)).map(|r| (r.stmts, r.expr)).unzip();
    let body = format!("({} {})", op, spaced(exprs.iter()));
    SMTResult::new(stmts.concat(), body)
}

    // fn define_array(&self, ty: ExprType, mut gen_body: impl FnMut(&Ident<SMTVar>) -> String) -> (Ident<SMTVar>, String) {
    //     let elem = Ident::new("elem");
    //     let body = gen_body(&elem);

    //     let elem_ty = match ty {
    //         ExprType::List(ref it) => *it.clone(),
    //         _ => unreachable!("All list exprs should have type List")
    //     };

    //     let (bool_i, bool_b) = self.define("find-fn", &[(elem.clone(), elem_ty.clone())], ExprType::Bool,
    //         body);

    //     let (arr_i, arr_b) = self.declare("find-arr", &[], ty.clone());
    //     let assert_params = self.0.iter().map(|(i, t)| format!("({} {})", ident(i), type_name(t)));
    //     let assert = format!("(assert (forall ({} ({} {})) (= (select {} {1}) {})))\n", spaced(assert_params), ident(&elem), type_name(&elem_ty), self.invoke(&arr_i, &[]), self.invoke(&bool_i, &[elem.clone()]));
    //     (arr_i, bool_b + &arr_b + &assert)

    // }

#[derive(Debug, Clone)]
enum Statement {
    Decl {
        id: Ident<SMTVar>,
        typ: ExprType,
    },
    Def {
        id: Ident<SMTVar>,
        typ: ExprType,
        body: String
    },
    Assert(String),
}

impl Display for Statement {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Statement::Decl { id, typ } => {
                write!(f, "(declare-fun {} () {})\n", ident(id), type_name(typ))
            }
            Statement::Def { id, typ, body } => {
                write!(f, "(define-fun {} () {}\n\t{})\n", ident(id), type_name(typ), &body)
            }
            Statement::Assert(s) => {
                write!(f, "(assert {})\n", s)
            }
        }
    }
}

fn declare(id: Ident<SMTVar>, typ: ExprType) -> Statement {
    Statement::Decl {
        id,
        typ
    }
}

fn define(id: Ident<SMTVar>, typ: ExprType, body: impl ToString) -> Statement {
    Statement::Def {
        id, 
        typ, 
        body: body.to_string(),
    }
}

fn spaced(iter: impl Iterator<Item=impl ToString>) -> String {
    iter.map(|elem| elem.to_string()).collect::<Vec<_>>().join(" ")
}
