use policy_lang::ir::{
    expr::{ExprType, IRExpr},
    policy::Policy,
    schema::{Collection, Schema},
    Ident,
};

use std::{fmt::Display, iter, collections::HashMap};

use lazy_static::lazy_static;

pub(crate) struct VerifProblem {
    pub princ: Ident<SMTVar>,
    pub rec: Ident<SMTVar>,
    pub stmts: Vec<Statement>,
}

lazy_static! {
    static ref NOW_IDENT: Ident<SMTVar> = Ident::new("datetime_now");
}

pub(crate) fn gen_assert(
    schema: &Schema,
    coll: &Ident<Collection>,
    before: &Policy,
    after: &Policy,
) -> VerifProblem {

    let mut ctx = SMTContext::default();
    let low_schema = ctx.lower_schema(schema);

    let princ_id = Ident::new("principle");
    let rec_id = Ident::new("rec");

    // Declare the principle and record
    let princ = declare(princ_id.clone(), &[], ExprType::Principle);
    let rec = declare(rec_id.clone(), &[], ExprType::Object(coll.clone()));
    let now = declare(NOW_IDENT.clone(), &[], ExprType::DateTime);

    // Lower the functions
    let mut before = ctx.lower_policy(&princ_id, &rec_id, coll, before);
    let mut after = ctx.lower_policy(&princ_id, &rec_id, coll, after);

    let safety_assertion =
        Statement::Assert(format!("(and {} (not {}))", &after.expr, &before.expr,));
    let mut out = low_schema;
    out.push(princ);
    out.push(rec);
    out.push(now);
    out.append(&mut before.stmts);
    out.append(&mut after.stmts);
    out.push(safety_assertion);

    VerifProblem {
        princ: princ_id,
        rec: rec_id,
        stmts: out,
    }
}

#[derive(Debug, Copy, Clone)]
pub(crate) struct SMTVar;

struct SMTResult {
    stmts: Vec<Statement>,
    expr: String,
}

impl SMTResult {
    fn expr(e: impl ToString) -> Self {
        Self {
            stmts: vec![],
            expr: e.to_string(),
        }
    }

    fn new(stmts: Vec<Statement>, expr: impl ToString) -> Self {
        Self {
            stmts,
            expr: expr.to_string(),
        }
    }
}



#[derive(Default)]
struct SMTContext {
    princ_casts: HashMap<Ident<Collection>, (Ident<SMTVar>, Ident<SMTVar>)>
}

impl SMTContext {

fn lower_policy(
    &self,
    princ: &Ident<SMTVar>,
    rec: &Ident<SMTVar>,
    _coll: &Ident<Collection>,
    pol: &Policy,
) -> SMTResult {
    let id = Ident::new("policy");
    eprintln!("----POLICY-----");
    let stmts = match pol {
        Policy::None => vec![define(id.clone(), &[], ExprType::Bool, false)],
        Policy::Anyone => vec![define(id.clone(), &[], ExprType::Bool, true)],
        Policy::Func(f) => {
            // Declare the function param as a synonym for the record.
            // This will allow easy lowering of var's while still ensuring
            // that every policy references the same record
            let param = define(f.param.coerce(), &[], f.param_type.clone(), ident(rec));
            let f = self.lower_expr((princ, &ExprType::Principle), &f.body);
            let func = define(id.clone(), &[], ExprType::Bool, &f.expr);

            let mut out = f.stmts;
            out.insert(0, param);
            out.push(func);
            out
        }
    };

    SMTResult::new(stmts, ident(&id))
}

fn lower_expr(&self, target: (&Ident<SMTVar>, &ExprType), body: &IRExpr) -> SMTResult {
    debug_assert!(!contains_unknown(&body.type_of()));
    eprintln!("{:?}", body.type_of()) ;
    match body.type_of() {
        ExprType::List(id) if *target.1 == ExprType::Principle => {
            eprintln!("SHIFT!");
            if let ExprType::Id(ref id) = *id {
                let new_target = (&self.princ_casts[id].1, &ExprType::Object(id.clone()));
                let low = self.lower_expr(new_target, body);
                let expr = format!("(and (= {} ({} {})) {})", ident(&target.0), ident(&self.princ_casts[id].0), ident(new_target.0), &low.expr);
                return SMTResult::new(low.stmts, expr);
            }
        }
        _ => eprintln!("{:?}", body.type_of())
    };

    match body {
        IRExpr::AppendS(l, r) => self.simple_nary_op("str.++", target, &[l, r]),
        IRExpr::AddI(l, r) | IRExpr::AddF(l, r) | IRExpr::AddD(l, r) => {
            self.simple_nary_op("+", target, &[l, r])
        }
        IRExpr::SubI(l, r) | IRExpr::SubF(l, r) | IRExpr::SubD(l, r) => {
            self.simple_nary_op("-", target, &[l, r])
        }
        // In policylang, equality is not defined for lists so no special handling is needed
        IRExpr::IsEq(_, l, r) => self.simple_nary_op("=", target, &[l, r]),
        IRExpr::Not(b) => self.simple_nary_op("not", target, &[b]),
        IRExpr::IsLessI(l, r) | IRExpr::IsLessF(l, r) | IRExpr::IsLessD(l, r) => {
            self.simple_nary_op("<", target, &[l, r])
        }
        IRExpr::IntToFloat(b) => self.simple_nary_op("to-real", target, &[b]),
        IRExpr::Path(_, obj, f) => self.simple_nary_op(&ident(f), target, &[obj]),
        IRExpr::Var(_, i) => SMTResult::expr(ident(i)),
        // Because id's and object types are the same, find is a no-op
        IRExpr::LookupById(_, b) => self.lower_expr(target, b),
        IRExpr::Now => SMTResult::expr(ident(&NOW_IDENT)),
        IRExpr::DateTimeConst(datetime) => {
            SMTResult::expr(datetime.timestamp())
        }
        IRExpr::IntConst(i) => SMTResult::expr(i),
        IRExpr::FloatConst(f) => SMTResult::expr(f),
        IRExpr::StringConst(s) => SMTResult::expr(format!("\"{}\"", s)),
        IRExpr::BoolConst(b) => SMTResult::expr(b),
        IRExpr::Find(_, fields) => {
            let mut stmts = vec![];
            let mut equalities = vec![];
            for (f, expr) in fields.iter() {
                let field_expr = self.lower_expr(target, expr);

                equalities.push(format!(
                    "(= ({} {}) {})\n",
                    ident(f),
                    ident(&target.0),
                    &field_expr.expr
                ));

                stmts.extend(field_expr.stmts)
            }

            let anded_eqs = format!("(and {} true)", spaced(equalities.into_iter()));

            SMTResult::new(stmts, anded_eqs)
        }
        IRExpr::Object(coll, fields, template) => {
            let obj_id = Ident::new("obj_lit");
            let obj = declare(obj_id.clone(), &[], ExprType::Object(coll.clone()));
            let template_expr = template.as_ref().map(|t| self.lower_expr(target, t));

            let mut stmts = vec![obj];
            let mut exprs = vec![];
            for (_f_id, f_expr) in fields.iter() {
                if let Some(e) = f_expr {
                    let low_e = self.lower_expr(target, e);
                    exprs.push(format!("(= {} {})", ident(&obj_id), &low_e.expr));
                    stmts.extend(low_e.stmts);
                } else {
                    exprs.push(format!(
                        "(= {} {})",
                        ident(&obj_id),
                        template_expr.as_ref().unwrap().expr
                    ))
                }
            }

            stmts.push(Statement::Assert(format!(
                "(and {})",
                spaced(exprs.into_iter())
            )));

            SMTResult::new(stmts, ident(&obj_id))
        }
        IRExpr::Map(list_expr, func) => {
            let obj = declare(func.param.coerce(), &[], func.param_type.clone());
            let mut list_expr = self.lower_expr((&func.param.coerce(), &func.param_type), &list_expr);
            let mut func_expr = self.lower_expr((&func.param.coerce(), &func.param_type), &func.body);
            let assert = Statement::Assert(format!("(= {} {})", &func_expr.expr, ident(target.0)));

            let mut out = vec![obj];
            out.append(&mut list_expr.stmts);
            out.append(&mut func_expr.stmts);
            out.push(assert);
            SMTResult::new(out, list_expr.expr)
        }
        IRExpr::AppendL(_, l, r) => {
            let left = self.lower_expr(target, l);
            let right = self.lower_expr(target, r);
            let expr = format!("(or {} {})", &left.expr, &right.expr);

            let mut stmts = left.stmts;
            stmts.extend(right.stmts);
            SMTResult::new(stmts, expr)
        }
        IRExpr::List(_, exprs) => {
            let mut stmts = vec![];
            let mut equalities = vec![];
            for expr in exprs.iter() {
                let elem_expr = self.lower_expr(target, expr);

                equalities.push(format!("(= {} {})\n", ident(target.0), &elem_expr.expr));

                stmts.extend(elem_expr.stmts)
            }

            let expr = format!("(or {} false)", spaced(equalities.into_iter()));
            SMTResult::new(stmts, expr)
        }
        IRExpr::If(_, c, t, e) => self.simple_nary_op("ite", target, &[c, t, e]),
        IRExpr::Public => SMTResult::expr(true),
    }
}

/// Lowers the schema to a String containing an SMT2LIB script
fn lower_schema(&mut self, schema: &Schema) -> Vec<Statement> {
    let princ = schema.principle.as_ref().unwrap();
    let princ_cons = Ident::new(format!("princ_{}", &princ.orig_name));
    let princ_obj= Ident::new(format!("princ_{}", &princ.orig_name));
    let princ_decl = Statement::Hack(format!(
        "(declare-datatypes () ((Principle unauth ({} ({0} {})))))", ident(&princ_cons), ident(princ)
    ));
    let princ_obj_decl = declare(princ_obj.clone(), &[], ExprType::Object(princ.clone()));

    self.princ_casts.insert(princ.clone(), (princ_cons, princ_obj));

    let mut out: Vec<_> = schema
        .collections
        .iter()
        .flat_map(|c| self.lower_collection(c))
        .collect();
    out.push(princ_decl);
    out.push(princ_obj_decl);
    out
}






/// Lowers each collection one by one.
/// Each collection gets its own sort named after its Ident,
/// and each field is a function mapping that sort to either a native
/// SMT sort or to another sort.
fn lower_collection<'a>(&self, coll: &'a Collection) -> impl Iterator<Item = Statement> + 'a {
    let sort = Statement::DeclSort {
        id: coll.name.coerce(),
    };
    let fields = coll.fields().map(move |f| {
        if f.is_id() {
            let id = Ident::new("id");
            define(
                f.name.coerce(),
                &[(id.clone(), ExprType::Object(coll.name.clone()))],
                f.typ.clone(),
                ident(&id),
            )
        } else {
            declare(
                f.name.coerce(),
                &[ExprType::Object(coll.name.clone())],
                f.typ.clone(),
            )
        }
    });

    iter::once(sort).chain(fields)
}

fn simple_nary_op(&self, op: &str, target: (&Ident<SMTVar>, &ExprType), exprs: &[&IRExpr]) -> SMTResult {
    let (stmts, exprs): (Vec<Vec<Statement>>, Vec<String>) = exprs
        .into_iter()
        .map(|e| self.lower_expr(target, e))
        .map(|r| (r.stmts, r.expr))
        .unzip();
    let body = format!("({} {})", op, spaced(exprs.iter()));
    SMTResult::new(stmts.concat(), body)
}
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
        ExprType::DateTime => "Int".to_owned(),
        ExprType::List(t) => format!("(Array {} Bool)", type_name(t)),
        ExprType::Unknown(_) => panic!("ListUnknowns should never be serialized"),

        // Ids and objects are the same in SMT land
        ExprType::Id(t) | ExprType::Object(t) => ident(t),
        ExprType::Principle => "Principle".to_owned(),
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
        | ExprType::DateTime
        | ExprType::Principle
        | ExprType::Bool => false,
        ExprType::Unknown(_) => true,
        ExprType::List(t) => contains_unknown(t),
    }
}



#[derive(Debug, Clone)]
pub(crate) enum Statement {
    Hack(String),
    DeclSort {
        id: Ident<SMTVar>,
    },
    DeclFun {
        id: Ident<SMTVar>,
        params: Vec<ExprType>,
        typ: ExprType,
    },
    DefFun {
        id: Ident<SMTVar>,
        params: Vec<(Ident<SMTVar>, ExprType)>,
        typ: ExprType,
        body: String,
    },
    Assert(String),
}

impl Display for Statement {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Statement::DeclFun { id, params, typ } => {
                let params = params.iter().map(type_name);
                write!(
                    f,
                    "(declare-fun {} ({}) {})\n",
                    ident(id),
                    spaced(params),
                    type_name(typ)
                )
            }
            Statement::DefFun {
                id,
                typ,
                params,
                body,
            } => {
                let params = params
                    .iter()
                    .map(|p| format!("({} {})", ident(&p.0), type_name(&p.1)));
                write!(
                    f,
                    "(define-fun {} ({}) {}\n\t{})\n",
                    ident(id),
                    spaced(params),
                    type_name(typ),
                    &body
                )
            }
            Statement::Assert(s) => write!(f, "(assert {})\n", s),
            Statement::DeclSort { id } => write!(f, "(declare-sort {})\n", ident(id)),
            Statement::Hack(s) => write!(f, "{}\n", s),
        }
    }
}

fn declare(id: Ident<SMTVar>, params: &[ExprType], typ: ExprType) -> Statement {
    Statement::DeclFun {
        id,
        params: params.to_vec(),
        typ,
    }
}

fn define(
    id: Ident<SMTVar>,
    params: &[(Ident<SMTVar>, ExprType)],
    typ: ExprType,
    body: impl ToString,
) -> Statement {
    Statement::DefFun {
        id,
        typ,
        params: params.to_vec(),
        body: body.to_string(),
    }
}

fn spaced(iter: impl Iterator<Item = impl ToString>) -> String {
    iter.map(|elem| elem.to_string())
        .collect::<Vec<_>>()
        .join(" ")
}
