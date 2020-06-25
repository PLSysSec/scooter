use policy_lang::ir::{
    expr::{ExprType, Func, IRExpr},
    policy::{CollectionPolicy, FieldPolicy, Policy},
    schema::{Collection, Schema},
    Ident,
};
use std::{
    io::Write,
    process::{Command, Stdio},
    str::from_utf8,
};

pub fn check_collection_refine(
    schema: &Schema,
    old_collection_policy: CollectionPolicy,
    new_collection_poilcy: CollectionPolicy,
) -> bool {
    unimplemented!("Define in terms of is_as_strict")
}

pub fn check_field_refine(
    schema: &Schema,
    old_field_policy: FieldPolicy,
    new_field_policy: FieldPolicy,
) -> bool {
    unimplemented!("Define in terms of is_as_strict")
}

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
    let scope = Scope::empty();

    // Lower the functions
    let (before_i, before_b) = lower_policy(&scope, coll, before);
    let (after_i, after_b) = lower_policy(&scope, coll, after);

    // Declare the principle and record
    let (princ_i, princ_b) = scope.declare("principle", &[], princ_type);
    let (rec_i, rec_b) = scope.declare("record", &[], ExprType::Object(coll.clone()));

    let safety_assertion = format!(
        "(assert (not (=> (select {} {}) (select {} {1}))))\n(check-sat)",
        scope.invoke(&after_i, &[rec_i.clone()]),
        ident(&princ_i),
        scope.invoke(&before_i, &[rec_i.clone()])
    );
    schema_str + &before_b + &after_b + &princ_b + &rec_b + &safety_assertion
}

#[derive(Debug, Copy, Clone)]
struct SMTVar;

fn lower_policy(scope: &Scope, coll: &Ident<Collection>, pol: &Policy) -> (Ident<SMTVar>, String) {
    let typ = ExprType::list(ExprType::Object(coll.clone()));

    match pol {
        Policy::None => scope.define("none", &[(Ident::new("_"), ExprType::Object(coll.clone()))], typ.clone(), format!("((as const {}) false)", type_name(&typ))),
        Policy::Anyone => scope.define("anyone", &[(Ident::new("_"), ExprType::Object(coll.clone()))], typ.clone(), format!("((as const {}) true)", type_name(&typ))),
        Policy::Func(f) => lower_func(scope, f)
    }
}

fn lower_func(scope: &Scope, func: &Func) -> (Ident<SMTVar>, String) {
    lower_expr(&scope.extend(func.param.coerce(), func.param_type.clone()), &func.body)
}

fn lower_expr(scope: &Scope, body: &IRExpr) -> (Ident<SMTVar>, String) {
    debug_assert!(!contains_unknown(&body.type_of()));

    match body {
        IRExpr::AppendS(l, r) => scope.simple_nary_op("str.++", body.type_of(), &[l, r]),
        IRExpr::AddI(l, r) | IRExpr::AddF(l, r) => scope.simple_nary_op("+", body.type_of(), &[l, r]),
        IRExpr::SubI(l, r) | IRExpr::SubF(l, r) => scope.simple_nary_op("-", body.type_of(), &[l, r]),
        // In policylang, equality is not defined for lists so no special handling is needed
        IRExpr::IsEq(_, l, r) => scope.simple_nary_op("=", body.type_of(), &[l, r]),
        IRExpr::Not(b) => scope.simple_nary_op("not", body.type_of(), &[b]),
        IRExpr::IsLessI(l, r) | IRExpr::IsLessF(l, r) => scope.simple_nary_op("<", body.type_of(), &[l, r]),
        IRExpr::IntToFloat(b) => scope.simple_nary_op("to-real", body.type_of(), &[b]),
        IRExpr::Path(_, obj, f) => scope.simple_nary_op(&ident(f), body.type_of(), &[obj]),
        // Avoid introducing a new expr for vars. Just reference the old var
        IRExpr::Var(_, i) => Scope::empty().define(i.orig_name.clone(), &[(i.coerce(), body.type_of())], body.type_of(), ident(i)),
        // Because id's and object types are the same, find is a no-op
        IRExpr::LookupById(_, b) => lower_expr(scope, b),
        IRExpr::IntConst(i) => scope.define("const-int", &[], body.type_of(), i.to_string()),
        IRExpr::FloatConst(f) => scope.define("const-float", &[], body.type_of(), &f.to_string()),
        IRExpr::StringConst(s) => scope.define("const-string", &[], body.type_of(), &format!("\"{}\"", s)),
        IRExpr::BoolConst(b) => scope.define("const-bool", &[], body.type_of(), &b.to_string()),
        IRExpr::Find(_, fields) => {
            let mut preamble = String::new();

            let (arr_i, arr_b) = scope.define_array(body.type_of(), |id| {
                let mut equalities = vec![];
                for (f, expr) in fields.iter() {
                    let (e_i, e_b) = lower_expr(scope, expr);
                    preamble += &e_b;
                    equalities.push(format!(
                        "(= ({} {}) {})\n",
                        ident(f),
                        ident(&id),
                        scope.invoke(&e_i, &[])
                    ));
                }

                format!("(and {} true)", equalities.join(" "))
            });

            (arr_i, preamble + &arr_b)
        }
        IRExpr::Object(_, fields, template) => {
            let expr_ident = Ident::new("expr");
            let decl = format!(
                "(declare-fun {} () {})\n",
                ident(&expr_ident),
                type_name(&body.type_of())
            );

            let smt_template = template.as_ref().map(|e| lower_expr(scope, e));
            let mut preamble = String::new();
            let mut asserts = String::new();
            if let Some((_, ref t_b)) = smt_template {
                preamble += t_b;
            }
            for (f, expr) in fields {
                if let Some(expr) = expr {
                    let (e_i, e_b) = lower_expr(scope, expr);
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
            let (l_i, l_b) = lower_expr(scope, l);
            let (r_i, r_b) = lower_expr(scope, r);

            let (app_i, app_b) = scope.define("append", &[], body.type_of(), 
            format!(
                "((_ map or) {} {}))\n",
                scope.invoke(&l_i, &[]),
                scope.invoke(&r_i, &[]),
            ));

            (app_i, l_b + &r_b + &app_b)
        }
        IRExpr::List(_, exprs) => {
            let (idents, bodies): (Vec<_>, Vec<_>) = exprs.iter().map(|e| lower_expr(scope, e)).unzip();
            let preamble = bodies.join("");
            let (arr_i, arr_b) = scope.define_array(body.type_of(), |some_record| {
                let eqs = idents.iter().map(|id| format!("(= {} {})", ident(&some_record), scope.invoke(id, &[])));
                format!("(or {} false)", spaced(eqs))
            });

            
            (arr_i, preamble + &arr_b)
        }
        IRExpr::If(_, c, t, e) => scope.simple_nary_op("ite", body.type_of(), &[c, t, e]),
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
        ExprType::List(t) => format!("(Array {} Bool)", type_name(t)),
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

/// Tracks which variables are in scope. Each expr is parameterized by these
#[derive(Debug, Clone)]
struct Scope(Vec<(Ident<SMTVar>, ExprType)>);

impl Scope {
    fn empty() -> Self {
        Scope(vec![])
    }

    fn define(&self, name: impl AsRef<str>, args: &[(Ident<SMTVar>, ExprType)], typ: ExprType, body: impl AsRef<str>) -> (Ident<SMTVar>, String){
        let expr_id = Ident::new("expr_".to_string() + name.as_ref());
        let params = self.0.iter().chain(args.iter()).map(|(i, t)| format!("({} {})", ident(i), type_name(t)));
        let smt_decl = format!("(define-fun {} ({}) {}\n\t{})\n", ident(&expr_id), spaced(params), type_name(&typ), body.as_ref());
        (expr_id, smt_decl)
    }

    fn define_array(&self, ty: ExprType, mut gen_body: impl FnMut(&Ident<SMTVar>) -> String) -> (Ident<SMTVar>, String) {
        let elem = Ident::new("elem");
        let body = gen_body(&elem);

        let elem_ty = match ty {
            ExprType::List(ref it) => *it.clone(),
            _ => unreachable!("All list exprs should have type List")
        };

        let (bool_i, bool_b) = self.define("find-fn", &[(elem.clone(), elem_ty.clone())], ExprType::Bool,
            body);

        let (arr_i, arr_b) = self.declare("find-arr", &[], ty.clone());
        let assert_params = self.0.iter().map(|(i, t)| format!("({} {})", ident(i), type_name(t)));
        let assert = format!("(assert (forall ({} ({} {})) (= (select {} {1}) {})))\n", spaced(assert_params), ident(&elem), type_name(&elem_ty), self.invoke(&arr_i, &[]), self.invoke(&bool_i, &[elem.clone()]));
        (arr_i, bool_b + &arr_b + &assert)

    }

    fn declare(&self, name: impl AsRef<str>, args: &[ExprType], typ: ExprType) -> (Ident<SMTVar>, String){
        let expr_id = Ident::new("expr_".to_string() + name.as_ref());
        let params = self.0.iter().map(|(_, t)| t).chain(args.iter()).map(type_name);
        let smt_decl = format!("(declare-fun {} ({}) {})\n", ident(&expr_id), spaced(params), type_name(&typ));
        (expr_id, smt_decl)
    }


    fn invoke(&self, expr: &Ident<SMTVar>, args: &[Ident<SMTVar>]) -> String {
        let idents = spaced(self.0.iter().map(|(i, _)| i).chain(args.iter()).map(ident));
        format!("({} {})", ident(expr), idents)
    }

    fn simple_nary_op(&self, op: &str, typ: ExprType, exprs: &[&IRExpr]) -> (Ident<SMTVar>, String) {
        let (idents, decls): (Vec<_>, Vec<_>) = exprs.iter().map(|e| lower_expr(self, e)).unzip();
        let body = format!("({} {})", op, spaced(idents.iter().map(|id| self.invoke(id, &[]))));
        let (def_i, def_b) = self.define("op".to_string() + op, &[], typ, body);
        (def_i, decls.join("") + &def_b)
    }

    fn extend(&self, var: Ident<SMTVar>, typ: ExprType) -> Self {
        let mut new = self.clone();
        new.0.push((var, typ));
        new
    }


}

fn spaced(iter: impl Iterator<Item=impl ToString>) -> String {
    iter.map(|elem| elem.to_string()).collect::<Vec<_>>().join(" ")
}