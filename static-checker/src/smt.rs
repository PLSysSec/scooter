use policy_lang::ir::{
    expr::{ExprType, Func, IRExpr},
    schema::{Collection, Schema},
    Ident, policy::{CollectionPolicy, FieldPolicy},
};
use std::{
    process::{Command, Stdio},
    io::Write, str::from_utf8,
};

pub(crate) fn check_collection_refine(
    schema: &Schema,
    old_collection_policy: CollectionPolicy,
    new_collection_poilcy: CollectionPolicy,
) -> bool {
    unimplemented!("Define in terms of is_as_strict")
}

pub(crate) fn check_field_refine(
    schema: &Schema,
    old_field_policy: FieldPolicy,
    new_field_policy: FieldPolicy,
) -> bool {
    unimplemented!("Define in terms of is_as_strict")
}

pub fn is_as_strict(schema: &Schema, before: &Func, after: &Func) -> bool {
    let assertion = gen_assert(schema, before, after);

    let mut child = Command::new("z3")
        .arg("-smt2")
        .arg("-in")
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .spawn()
        .expect("Unable to spawn z3");
    
    {
        let input = child.stdin.as_mut().expect("Failed to open stdin of z3 process");
        input.write_all(assertion.as_bytes()).expect("Error writing to z3 input");
    };

    let output = child.wait_with_output().expect("Error capturing z3 output");

    let output_txt: &str  = from_utf8(&output.stdout).expect("Error parsing z3 output");
    eprintln!("{}", output_txt);
    return output_txt == "unsat\n"
}

pub fn gen_assert(schema: &Schema, before: &Func, after: &Func) -> String {
    let mut preamble = lower_schema(schema);
    let princ_type = match before.body.type_of() {
        ExprType::List(princ) => princ.clone(),
        _ => unreachable!("All policy functions must return lists of principles."),
    };

    // Declare the principle and record
    let princ = Ident::<SMTVar>::new("principle");
    let rec = Ident::<SMTVar>::new("record");
    preamble += &format!(
        "(declare-fun {} () {})\n",
        ident(&princ),
        type_name(&princ_type)
    );
    preamble += &format!(
        "(declare-fun {} () {})\n",
        ident(&rec),
        type_name(&before.param_type)
    );

    // Declare the params
    let mut params = String::new();
    params += &format!(
        "(declare-fun {} () {})\n",
        ident(&before.param),
        type_name(&before.param_type)
    );
    params += &format!(
        "(declare-fun {} () {})\n",
        ident(&after.param),
        type_name(&after.param_type)
    );

    // "Apply the functions"
    params += &format!(
        "(assert (and (= {} {}) (= {} {0})))\n",
        ident(&rec),
        ident(&after.param),
        ident(&before.param)
    );

    let (b_i, b_b) = lower_expr(&before.body);
    let (a_i, a_b) = lower_expr(&after.body);

    let safety_assertion = format!(
        "(assert (not (=> (select {} {}) (select {} {1}))))\n(check-sat)",
        ident(&a_i),
        ident(&princ),
        ident(&b_i)
    );
    preamble + &params + &b_b + &a_b + &safety_assertion
}

struct SMTVar;

fn lower_expr(body: &IRExpr) -> (Ident<SMTVar>, String) {
    debug_assert!(!contains_unknown(&body.type_of()));

    match body {
        IRExpr::AppendS(l, r) => simple_binop("str.++", body.type_of(), l, r),
        IRExpr::AddI(l, r) | IRExpr::AddF(l, r) => simple_binop("+", body.type_of(), l, r),
        IRExpr::SubI(l, r) | IRExpr::SubF(l, r) => simple_binop("-", body.type_of(), l, r),
        // In policylang, equality is not defined for lists so no special handling is needed
        IRExpr::IsEq(_, l, r) => simple_binop("=", body.type_of(), l, r),
        IRExpr::Not(b) => simple_unop("not", body.type_of(), b),
        IRExpr::IsLessI(l, r) | IRExpr::IsLessF(l, r) => simple_binop("<", body.type_of(), l, r),
        IRExpr::IntToFloat(b) => simple_unop("to-real", body.type_of(), b),
        IRExpr::Path(_, body, f) => simple_unop(&ident(f), body.type_of(), body),
        // Avoid introducing a new expr for vars. Just reference the old var
        IRExpr::Var(_, i) => (i.coerce(), String::new()),
        // Because id's and object types are the same, find is a no-op
        IRExpr::LookupById(_, b) => lower_expr(b),
        IRExpr::IntConst(i) => const_val(&i.to_string(), body.type_of()),
        IRExpr::FloatConst(f) => const_val(&f.to_string(), body.type_of()),
        IRExpr::StringConst(s) => const_val(&format!("{}", s), body.type_of()),
        IRExpr::BoolConst(b) => const_val(&b.to_string(), body.type_of()),
        IRExpr::Find(coll, fields) => {
            let expr_ident = Ident::new("expr");
            let decl = format!(
                "(declare-fun {} () {})\n",
                ident(&expr_ident),
                type_name(&body.type_of())
            );

            let mut preamble = String::new();
            let mut equalities = vec![];
            let quantifier = Ident::<SMTVar>::new("quant");
            for (f, expr) in fields.iter() {
                let (e_i, e_b) = lower_expr(expr);
                preamble += &e_b;
                equalities.push(format!(
                    "(= ({} {}) {})\n",
                    ident(f),
                    ident(&quantifier),
                    ident(&e_i)
                ));
            }

            let anded_eqs = equalities.into_iter().fold("true".to_owned(), |anded, eq| {
                format!("(and {} {})", &eq, &anded)
            });

            let assert = format!(
                "(assert (forall (({} {})) (=> {} (select {} {0}))",
                ident(&quantifier),
                type_name(&ExprType::Object(coll.clone())),
                anded_eqs,
                ident(&expr_ident)
            );

            (expr_ident, preamble + &decl + &assert)
        }
        IRExpr::Object(_, fields, template) => {
            let expr_ident = Ident::new("expr");
            let decl = format!(
                "(declare-fun {} () {})\n",
                ident(&expr_ident),
                type_name(&body.type_of())
            );

            let smt_template = template.as_ref().map(|e| lower_expr(e));
            let mut preamble = String::new();
            let mut asserts = String::new();
            if let Some((_, ref t_b))  = smt_template {
                preamble += t_b;
            }
            for (f, expr) in fields {
                if let Some(expr) = expr {
                    let (e_i, e_b) = lower_expr(expr);
                    preamble += &e_b;
                    asserts += &format!(
                        "(assert (= ({} {}) {})\n",
                        ident(f),
                        ident(&expr_ident),
                        ident(&e_i)
                    );
                } else {
                    let (t_i, _) = smt_template.as_ref().unwrap();
                    asserts += &format!(
                        "(assert (= ({} {}) ({0} {})))\n",
                        ident(f),
                        ident(&expr_ident),
                        ident(t_i)
                    )
                }
            }

            (expr_ident, preamble + &decl + &asserts)
        }
        IRExpr::AppendL(_, l, r) => {
            let expr_ident = Ident::new("expr");
            let (l_i, l_b) = lower_expr(l);
            let (r_i, r_b) = lower_expr(r);
            let decl = format!(
                "(declare-fun {} () {})\n",
                ident(&expr_ident),
                type_name(&body.type_of())
            );
            let assert = format!(
                "(assert (= {} ((_ map or {} {}))))\n",
                ident(&expr_ident),
                ident(&l_i),
                ident(&r_i)
            );

            (expr_ident, l_b + &r_b + &decl + &assert)
        }
        IRExpr::List(_, exprs) => {
            let expr_ident = Ident::new("expr");
            let typ_name = type_name(&body.type_of());
            let (idents, bodies): (Vec<_>, Vec<_>) = exprs.iter().map(|e| lower_expr(e)).unzip();
            let preamble: String = bodies.join("");
            let decl = format!("(declare-fun {} () {})\n", ident(&expr_ident), typ_name);

            let empty = format!("((as const {}) false)", typ_name);
            let list = idents.into_iter().fold(empty, |list, id| {
                format!("(store {} {} true)", &list, ident(&id))
            });

            let assert = format!("(assert (= {} {}))\n", ident(&expr_ident), &list);

            (expr_ident, preamble + &decl + &assert)
        }
        IRExpr::If(_, c, t, e) => simple_nary_op("ite", body.type_of(), &[c, t, e]),
    }
}

fn simple_nary_op(op: &str, typ: ExprType, exprs: &[&IRExpr]) -> (Ident<SMTVar>, String) {
    let expr_ident = Ident::new("expr");
    let typ_name = type_name(&typ);

    let (idents, bodies): (Vec<_>, Vec<_>) = exprs.iter().map(|e| lower_expr(e)).unzip();
    let spaced_idents: String = idents.iter().map(ident).collect::<Vec<_>>().join(" ");
    let preamble: String = bodies.join("");
    let decl = format!("(declare-fun {} () {})\n", ident(&expr_ident), typ_name);
    let assert = format!(
        "(assert (= {} ({} {})))\n",
        ident(&expr_ident),
        op,
        spaced_idents
    );

    (expr_ident, preamble + &decl + &assert)
}

fn simple_binop(op: &str, typ: ExprType, l: &IRExpr, r: &IRExpr) -> (Ident<SMTVar>, String) {
    simple_nary_op(op, typ, &[l, r])
}

fn simple_unop(op: &str, typ: ExprType, body: &IRExpr) -> (Ident<SMTVar>, String) {
    simple_nary_op(op, typ, &[body])
}

fn const_val(val: &str, typ: ExprType) -> (Ident<SMTVar>, String) {
    let expr_ident = Ident::new("expr");
    let typ_name = type_name(&typ);
    let body = format!(
        "(define-fun {} () {} {})\n",
        ident(&expr_ident),
        typ_name,
        val
    );
    (expr_ident, body)
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
            format!(
                "(declare-fun {} ({}) {})\n",
                ident(&f.name),
                ident(&coll.name),
                type_name(&f.typ)
            )
        })
        .collect();
    let elements = format!(
        "(declare-fun {} () {})\n",
        all(&coll.name),
        type_name(&ExprType::list(ExprType::Object(coll.name.clone())))
    );
    sort + &fields + &elements
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
        ExprType::List(t) => format!("(Array {} bool)", type_name(t)),
        ExprType::Unknown(_) => panic!("ListUnknowns should never be serialized"),

        // Ids and objects are the same in SMT land
        ExprType::Id(t) | ExprType::Object(t) => ident(t),
    }
}

/// Produces the identifier for the complete set of records for a collection
pub fn all(coll: &Ident<Collection>) -> String {
    format!("{}_all", ident(coll))
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
