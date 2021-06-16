use policy_lang::ir::{
    expr::{ExprType, FieldComparison, IRExpr},
    policy::Policy,
    schema::{Collection, Field, Schema},
    Ident,
};

use std::{collections::HashMap, fmt::Display, iter};

use super::Equiv;
use lazy_static::lazy_static;

pub(crate) struct VerifProblem {
    pub princ: Ident<SMTVar>,
    pub rec: Ident<SMTVar>,
    pub stmts: Vec<Statement>,
    pub join_tables:
        HashMap<Ident<Field>, (Ident<Collection>, Ident<Field>, Ident<Field>, ExprType)>,
}

lazy_static! {
    static ref NOW_IDENT: Ident<SMTVar> = Ident::new("datetime_now");
}

pub(crate) fn gen_assert(
    schema: &Schema,
    equivs: &[Equiv],
    coll: &Ident<Collection>,
    before: &Policy,
    after: &Policy,
) -> VerifProblem {
    let mut ctx = SMTContext::default();
    let low_schema_sorts = ctx.lower_schema_sorts(schema);

    let princ_id = Ident::new("principal");
    let rec_id = Ident::new("rec");

    // Declare the principal and record
    let princ = declare(princ_id.clone(), &[], ExprType::Principal);
    let rec = declare(rec_id.clone(), &[], ExprType::Object(coll.clone()));

    // Declare the now constant for datetimes
    let now = declare(NOW_IDENT.clone(), &[], ExprType::DateTime);

    // Declare the option datatype
    let option_datatype =
        Statement::Hack("(declare-datatypes (T) ((Option none (some (v T)))))".to_string());

    // Lower the fields
    let mut low_schema_fields = ctx.lower_schema_fields(schema);
    let mut eq_asserts = ctx.lower_equivs(equivs, schema);

    // Lower the functions
    let mut before = ctx.lower_policy(&princ_id, &rec_id, before);
    let mut after = ctx.lower_policy(&princ_id, &rec_id, after);

    let safety_assertion =
        Statement::Assert(format!("(and {} (not {}))", &after.expr, &before.expr,));
    let mut out = low_schema_sorts;
    out.insert(0, option_datatype);
    out.push(princ);
    out.push(rec);
    out.push(now);
    out.append(&mut low_schema_fields);
    out.append(&mut eq_asserts);
    out.append(&mut before.stmts);
    out.append(&mut after.stmts);
    out.push(safety_assertion);

    VerifProblem {
        princ: princ_id,
        rec: rec_id,
        stmts: out,
        join_tables: ctx.join_tables,
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
    princ_casts: HashMap<Ident<Collection>, (Ident<SMTVar>, Ident<SMTVar>)>,
    join_tables: HashMap<Ident<Field>, (Ident<Collection>, Ident<Field>, Ident<Field>, ExprType)>,
}

impl SMTContext {
    fn lower_policy(&self, princ: &Ident<SMTVar>, rec: &Ident<SMTVar>, pol: &Policy) -> SMTResult {
        let id = Ident::new("policy");
        let stmts = match pol {
            Policy::None => vec![define(id.clone(), &[], ExprType::Bool, false)],
            Policy::Anyone => vec![define(id.clone(), &[], ExprType::Bool, true)],
            Policy::Func(f) => {
                let low = self.lower_expr((princ, &ExprType::Principal), &f.body);
                let func = define(
                    id.clone(),
                    &[],
                    ExprType::Bool,
                    exists(
                        &f.param.coerce(),
                        &f.param_type,
                        &format!("(and (= {} {}) {})", ident(&f.param), ident(&rec), low.expr),
                    ),
                );

                let mut out = low.stmts;
                out.push(func);
                out
            }
        };

        SMTResult::new(stmts, ident(&id))
    }

    fn lower_expr(&self, target: (&Ident<SMTVar>, &ExprType), body: &IRExpr) -> SMTResult {
        // We need to downcast if target is a Principal and body is a list of concrete type
        match body.type_of() {
            ExprType::Set(id) if *target.1 == ExprType::Principal => {
                if let ExprType::Id(ref id) = *id {
                    let new_target = (&self.princ_casts[id].1, &ExprType::Object(id.clone()));
                    let low = self.lower_expr(new_target, body);
                    let expr = format!(
                        "(and (= {} ({} {})) {})",
                        ident(&target.0),
                        ident(&self.princ_casts[id].0),
                        ident(new_target.0),
                        &low.expr
                    );
                    return SMTResult::new(low.stmts, expr);
                }
            }
            _ => (), //eprintln!("{:?}", body.type_of()),
        };

        match body {
            IRExpr::AppendS(l, r) => self.simple_nary_op("str.++", target, &[l, r]),
            IRExpr::AddI(l, r) => self.simple_nary_op("bvadd", target, &[l, r]),
            IRExpr::AddD(l, r) => self.simple_nary_op("+", target, &[l, r]),
            IRExpr::AddF(l, r) => self.simple_nary_op("fp.add", target, &[l, r]),
            IRExpr::SubI(l, r) => self.simple_nary_op("bvsub", target, &[l, r]),
            IRExpr::SubD(l, r) => self.simple_nary_op("-", target, &[l, r]),
            IRExpr::SubF(l, r) => self.simple_nary_op("fp.sub", target, &[l, r]),
            IRExpr::IsEq(ExprType::F64, l, r) => self.simple_nary_op("fp.eq", target, &[l, r]),
            // In policylang, equality is not defined for lists so no special handling is needed
            IRExpr::IsEq(_, l, r) => self.simple_nary_op("=", target, &[l, r]),
            IRExpr::Not(b) => self.simple_nary_op("not", target, &[b]),
            IRExpr::IsLessI(l, r) => self.simple_nary_op("bvslt", target, &[l, r]),
            IRExpr::IsLessD(l, r) => self.simple_nary_op("<", target, &[l, r]),
            IRExpr::IsLessF(l, r) => self.simple_nary_op("fp.lt", target, &[l, r]),
            IRExpr::IntToFloat(b) => {
                self.simple_nary_op("(_ to_fp 11 53) roundNearestTiesToEven", target, &[b])
            }
            IRExpr::Path(ty, obj, f) => match ty {
                ExprType::Set(ref _inner_ty) => {
                    let lower = self.lower_expr(target, obj);

                    let (coll, from, to, _typ) = self.join_tables[f].clone();
                    let exi = Ident::new("join_exi");
                    let expr = exists(
                        &exi,
                        &ExprType::Id(coll),
                        &format!(
                            "(and (= ({} {}) {}) (= ({} {}) {}))",
                            ident(&from),
                            ident(&exi),
                            &lower.expr,
                            ident(&to),
                            ident(&exi),
                            ident(&target.0)
                        ),
                    );

                    SMTResult::new(lower.stmts, expr)
                }
                _ => {
                    let lowered = self.lower_expr(target, obj);

                    SMTResult::new(lowered.stmts, format!("({} {})", &ident(f), lowered.expr))
                }
            },
            IRExpr::Var(_, i) => SMTResult::expr(ident(i)),
            // Because id's and object types are the same, find is a no-op
            IRExpr::LookupById(_coll, b) => self.lower_expr(target, b),
            IRExpr::Now => SMTResult::expr(ident(&NOW_IDENT)),
            IRExpr::DateTimeConst(datetime) => SMTResult::expr(datetime.timestamp()),
            IRExpr::IntConst(i) => SMTResult::expr(format!("(_ bv{} 64)", i)),
            IRExpr::FloatConst(f) => {
                SMTResult::expr(format!("((_ to_fp 11 53) roundNearestTiesToEven {})", f))
            }
            IRExpr::StringConst(s) => SMTResult::expr(format!("\"{}\"", s)),
            IRExpr::BoolConst(b) => SMTResult::expr(b),
            IRExpr::Find(_coll, fields) => {
                let mut stmts = vec![];
                let mut field_checks = vec![];
                for (comp, f, fty, expr) in fields.iter() {
                    let field_expr = self.lower_expr(target, expr);
                    stmts.extend(field_expr.stmts);
                    match comp {
                        FieldComparison::Equals => {
                            field_checks.push(format!(
                                "(= ({} {}) {})\n",
                                ident(f),
                                ident(&target.0),
                                &field_expr.expr
                            ));
                        }
                        FieldComparison::Greater => match (fty, expr.type_of()) {
                            (ExprType::I64, ExprType::I64) => field_checks.push(format!(
                                "(bvsgt ({} {}) {})\n",
                                ident(f),
                                ident(&target.0),
                                &field_expr.expr
                            )),
                            (ExprType::I64, ExprType::F64) => field_checks.push(format!(
                                "(fp.gt ((_ to_fp 11 53) roundNearestTiesToEven ({} {})) {})\n",
                                ident(f),
                                ident(&target.0),
                                &field_expr.expr
                            )),
                            (ExprType::F64, ExprType::I64) => field_checks.push(format!(
                                "(fp.gt ({} {}) ((_ to_fp 11 53) roundNearestTiesToEven {}))\n",
                                ident(f),
                                ident(&target.0),
                                &field_expr.expr
                            )),
                            (ExprType::F64, ExprType::F64) => field_checks.push(format!(
                                "(fp.gt ({} {}) {})",
                                ident(f),
                                ident(&target.0),
                                &field_expr.expr
                            )),
                            _ => panic!("Type error: this should not happen"),
                        },
                        FieldComparison::GreaterOrEquals => match (fty, expr.type_of()) {
                            (ExprType::I64, ExprType::I64) => field_checks.push(format!(
                                "(bvsge ({} {}) {})\n",
                                ident(f),
                                ident(&target.0),
                                &field_expr.expr
                            )),
                            (ExprType::I64, ExprType::F64) => field_checks.push(format!(
                                "(fp.geq ((_ to_fp 11 53) roundNearestTiesToEven ({} {})) {})\n",
                                ident(f),
                                ident(&target.0),
                                &field_expr.expr
                            )),
                            (ExprType::F64, ExprType::I64) => field_checks.push(format!(
                                "(fp.geq ({} {}) ((_ to_fp 11 53) roundNearestTiesToEven {}))\n",
                                ident(f),
                                ident(&target.0),
                                &field_expr.expr
                            )),
                            (ExprType::F64, ExprType::F64) => field_checks.push(format!(
                                "(fp.geq ({} {}) {})",
                                ident(f),
                                ident(&target.0),
                                &field_expr.expr
                            )),
                            _ => panic!("Type error: this should not happen"),
                        },
                        FieldComparison::Less => match (fty, expr.type_of()) {
                            (ExprType::I64, ExprType::I64) => field_checks.push(format!(
                                "(bvslt ({} {}) {})\n",
                                ident(f),
                                ident(&target.0),
                                &field_expr.expr
                            )),
                            (ExprType::I64, ExprType::F64) => field_checks.push(format!(
                                "(fp.lt ((_ to_fp 11 53) roundNearestTiesToEven ({} {})) {})\n",
                                ident(f),
                                ident(&target.0),
                                &field_expr.expr
                            )),
                            (ExprType::F64, ExprType::I64) => field_checks.push(format!(
                                "(fp.lt ({} {}) ((_ to_fp 11 53) roundNearestTiesToEven {}))\n",
                                ident(f),
                                ident(&target.0),
                                &field_expr.expr
                            )),
                            (ExprType::F64, ExprType::F64) => field_checks.push(format!(
                                "(fp.lt ({} {}) {})",
                                ident(f),
                                ident(&target.0),
                                &field_expr.expr
                            )),
                            _ => panic!("Type error: this should not happen"),
                        },
                        FieldComparison::LessOrEquals => match (fty, expr.type_of()) {
                            (ExprType::I64, ExprType::I64) => field_checks.push(format!(
                                "(bvsle ({} {}) {})\n",
                                ident(f),
                                ident(&target.0),
                                &field_expr.expr
                            )),
                            (ExprType::I64, ExprType::F64) => field_checks.push(format!(
                                "(fp.leq ((_ to_fp 11 53) roundNearestTiesToEven ({} {})) {})\n",
                                ident(f),
                                ident(&target.0),
                                &field_expr.expr
                            )),
                            (ExprType::F64, ExprType::I64) => field_checks.push(format!(
                                "(fp.leq ({} {}) ((_ to_fp 11 53) roundNearestTiesToEven {}))\n",
                                ident(f),
                                ident(&target.0),
                                &field_expr.expr
                            )),
                            (ExprType::F64, ExprType::F64) => field_checks.push(format!(
                                "(fp.leq ({} {}) {})",
                                ident(f),
                                ident(&target.0),
                                &field_expr.expr
                            )),
                            _ => panic!("Type error: this should not happen"),
                        },
                        FieldComparison::Contains => {
                            let (coll, from, to, _typ) = self.join_tables[f].clone();
                            let exi = Ident::new("find_exi");
                            let expr = exists(
                                &exi,
                                &ExprType::Id(coll),
                                &format!(
                                    "(and (= ({} {}) {}) (= ({} {}) {}))",
                                    ident(&from),
                                    ident(&exi),
                                    ident(target.0),
                                    ident(&to),
                                    ident(&exi),
                                    &field_expr.expr
                                ),
                            );
                            field_checks.push(expr);
                        }
                    }
                }

                let anded_eqs = format!("(and {} true)", spaced(field_checks.into_iter()));

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
                let exi = func.param.clone();
                let low_list_expr = self.lower_expr((&exi.coerce(), &func.param_type), &list_expr);
                let mut func_expr = self.lower_expr(target, &func.body);
                let expr = exists(
                    &exi.coerce(),
                    &func.param_type,
                    &format!(
                        "(and (= {} {}) {})",
                        ident(target.0),
                        &func_expr.expr,
                        &low_list_expr.expr
                    ),
                );

                let mut stmts = low_list_expr.stmts;
                stmts.append(&mut func_expr.stmts);
                SMTResult::new(stmts, expr)
            }
            IRExpr::FlatMap(set_expr, func) => {
                let exi = func.param.coerce();
                let low_list_expr = self.lower_expr((&exi, &func.param_type), &set_expr);
                let mut func_expr = self.lower_expr(target, &func.body);
                let expr = exists(
                    &exi,
                    &func.param_type,
                    &format!("(and {} {})", &func_expr.expr, &low_list_expr.expr),
                );

                let mut stmts = low_list_expr.stmts;
                stmts.append(&mut func_expr.stmts);
                SMTResult::new(stmts, expr)
            }
            IRExpr::AppendL(_, l, r) => {
                let left = self.lower_expr(target, l);
                let right = self.lower_expr(target, r);
                let expr = format!("(or {} {})", &left.expr, &right.expr);

                let mut stmts = left.stmts;
                stmts.extend(right.stmts);
                SMTResult::new(stmts, expr)
            }
            IRExpr::DiffL(_, l, r) => {
                let left = self.lower_expr(target, l);
                let right = self.lower_expr(target, r);
                let expr = format!("(and {} (not {}))", &left.expr, &right.expr);

                let mut stmts = left.stmts;
                stmts.extend(right.stmts);
                SMTResult::new(stmts, expr)
            }
            IRExpr::Intersect(_, l, r) => {
                let left = self.lower_expr(target, l);
                let right = self.lower_expr(target, r);
                let expr = format!("(and {} {})", &left.expr, &right.expr);

                let mut stmts = left.stmts;
                stmts.extend(right.stmts);
                SMTResult::new(stmts, expr)
            }
            IRExpr::Set(_, exprs) => {
                let mut stmts = vec![];
                let mut equalities = vec![];
                for expr in exprs.iter() {
                    let elem_expr = match expr.type_of() {
                        ExprType::Id(coll) if *target.1 == ExprType::Principal => {
                            let new_target =
                                (&self.princ_casts[&coll].1, &ExprType::Object(coll.clone()));
                            let low = self.lower_expr(new_target, expr);
                            stmts.extend(low.stmts);
                            format!(
                                "(and (= {} ({} {})) (= {} {}))",
                                ident(&target.0),
                                ident(&self.princ_casts[&coll].0),
                                ident(new_target.0),
                                ident(new_target.0),
                                &low.expr
                            )
                        }
                        _ => {
                            let low = self.lower_expr(target, expr);
                            stmts.extend(low.stmts);
                            format!("(= {} {})", ident(target.0), low.expr)
                        }
                    };

                    equalities.push(elem_expr)
                }

                let expr = if equalities.len() == 0 {
                    "false".to_string()
                } else {
                    format!("(or {})", spaced(equalities.into_iter()))
                };
                SMTResult::new(stmts, expr)
            }
            IRExpr::If(_, c, t, e) => self.simple_nary_op("ite", target, &[c, t, e]),
            IRExpr::Public => SMTResult::expr("true"),
            IRExpr::None(ty) => SMTResult::expr(format!("(as none (Option {}))", type_name(&ty))),
            IRExpr::Some(_ty, inner_expr) => {
                let elem_expr = self.lower_expr(target, inner_expr);
                SMTResult::new(elem_expr.stmts, format!("(some {})", &elem_expr.expr))
            }
            IRExpr::Match(_ty, opt_expr, var, some_expr, none_expr) => {
                let mut stmts = Vec::new();
                let opt_expr = self.lower_expr(target, opt_expr);
                let some_expr = self.lower_expr(target, some_expr);
                let none_expr = self.lower_expr(target, none_expr);
                stmts.extend(opt_expr.stmts);
                stmts.extend(some_expr.stmts);
                stmts.extend(none_expr.stmts);

                let expr = format!(
                    "(match {} (((some {}) {}) (none {})))",
                    &opt_expr.expr,
                    ident(&var),
                    &some_expr.expr,
                    none_expr.expr
                );
                SMTResult::new(stmts, expr)
            }
        }
    }

    /// Lowers the schema sorts to a String containing an SMT2LIB script
    fn lower_schema_sorts(&mut self, schema: &Schema) -> Vec<Statement> {
        let princ_ids: Vec<_> = schema
            .dynamic_principals
            .iter()
            .map(|princ_coll| {
                (
                    Ident::new(format!("princ_{}", &princ_coll.orig_name)),
                    Ident::new(format!("princ_{}", &princ_coll.orig_name)),
                    princ_coll.clone(),
                )
            })
            .collect();
        let princ_decl = Statement::Hack(format!(
            "(declare-datatypes () ((Principal unauthenticated {} {})))",
            schema
                .static_principals
                .iter()
                .map(ident)
                .collect::<Vec<_>>()
                .join(" "),
            princ_ids
                .iter()
                .map(|(princ_cons, _princ_obj, princ_coll)| format!(
                    "({} ({1} {}))",
                    ident(&princ_cons),
                    ident(princ_coll)
                ))
                .collect::<Vec<_>>()
                .join(" ")
        ));
        for (princ_cons, princ_obj, princ_coll) in princ_ids.iter() {
            self.princ_casts
                .insert(princ_coll.clone(), (princ_cons.clone(), princ_obj.clone()));
        }

        let colls = schema
            .collections
            .iter()
            .map(|c| self.lower_collection_sorts(c));

        let mut out: Vec<_> = colls
            .flatten()
            .chain(iter::once(princ_decl))
            .chain(iter::once(Statement::Hack("(push 1)".into())))
            .collect();

        for (_princ_cons, princ_obj, princ_coll) in princ_ids.iter() {
            let princ_obj_decl =
                declare(princ_obj.clone(), &[], ExprType::Object(princ_coll.clone()));
            out.push(princ_obj_decl);
        }
        out
    }
    /// Lowers the schema fields to a String containing an SMT2LIB script
    fn lower_schema_fields(&mut self, schema: &Schema) -> Vec<Statement> {
        schema
            .collections
            .iter()
            .map(|c| self.lower_collection_fields(c))
            .collect::<Vec<_>>()
            .concat()
    }

    fn lower_collection_sorts(&mut self, coll: &Collection) -> Vec<Statement> {
        let mut sorts = vec![Statement::DeclSort {
            id: coll.name.coerce(),
        }];

        for f in coll.fields() {
            if let ExprType::Set(ref inner_ty) = f.typ {
                let coll_name = Ident::new(coll.name.orig_name.clone() + &f.name.orig_name);
                let from_name = Ident::new("from");
                let to_name = Ident::new("to");
                self.join_tables.insert(
                    f.name.clone(),
                    (
                        coll_name.clone(),
                        from_name.clone(),
                        to_name.clone(),
                        inner_ty.as_ref().clone(),
                    ),
                );

                sorts.push(Statement::DeclSort {
                    id: coll_name.coerce(),
                })
            }
        }

        sorts
    }
    fn lower_collection_fields(&mut self, coll: &Collection) -> Vec<Statement> {
        coll.fields()
            .flat_map(move |f| {
                if f.is_id() {
                    let id = Ident::new("id");
                    return vec![define(
                        f.name.coerce(),
                        &[(id.clone(), ExprType::Object(coll.name.clone()))],
                        f.typ.clone(),
                        ident(&id),
                    )];
                }

                match self.join_tables.get(&f.name) {
                    Some((join_coll, from, to, inner_ty)) => {
                        let ty = ExprType::Object(join_coll.clone());
                        vec![
                            declare(
                                from.coerce(),
                                &[ty.clone()],
                                ExprType::Object(coll.name.clone()),
                            ),
                            declare(to.coerce(), &[ty.clone()], inner_ty.clone()),
                        ]
                    }
                    None => {
                        vec![declare(
                            f.name.coerce(),
                            &[ExprType::Object(coll.name.clone())],
                            f.typ.clone(),
                        )]
                    }
                }
            })
            .collect()
    }

    fn simple_nary_op(
        &self,
        op: &str,
        target: (&Ident<SMTVar>, &ExprType),
        exprs: &[&IRExpr],
    ) -> SMTResult {
        let results: Vec<SMTResult> = exprs
            .into_iter()
            .map(|e| self.lower_expr(target, e))
            .collect();
        let exprs = results.iter().map(|r| r.expr.clone());
        let stmt_lsts: Vec<Vec<Statement>> = results.iter().map(|r| r.stmts.clone()).collect();
        let body = format!("({} {})", op, spaced(exprs));
        SMTResult::new(stmt_lsts.concat(), body)
    }

    fn lower_equivs(&self, equivs: &[Equiv], schema: &Schema) -> Vec<Statement> {
        let mut stmts = vec![];
        for eq in equivs {
            let typ = schema[&eq.0].typ.clone();
            match typ {
                ExprType::Set(set_ty) => {
                    let to_id: Ident<SMTVar> = Ident::new("to_assert");
                    let join_id: Ident<SMTVar> = Ident::new("join_var");
                    let lowered = self.lower_expr((&to_id, &set_ty), &eq.1.body);
                    let (join_coll, from_f, to_f, ..) = self.join_tables[&eq.0].clone();
                    stmts.push(Statement::Assert(format!(
                        "(forall (({from_id} {from_typ}) ({to_id} {to_typ}))
                            (=
                                (exists (({join_id} {join_typ}))
                                    (and
                                        (= ({from_f} {join_id}) {from_id})
                                        (= ({to_f} {join_id}) {to_id})))
                                 {low_expr}))",
                        from_id = &ident(&eq.1.param),
                        from_typ = type_name(&eq.1.param_type),
                        to_id = &ident(&to_id),
                        to_typ = type_name(&set_ty),
                        join_id = &ident(&join_id),
                        join_typ = type_name(&ExprType::Object(join_coll.clone())),
                        to_f = &ident(&to_f),
                        from_f = &ident(&from_f),
                        low_expr = &lowered.expr
                    )));
                }
                _ => {
                    let lowered = self.lower_expr((&eq.1.param.coerce(), &typ), &eq.1.body);
                    stmts.push(Statement::Assert(format!(
                        "(forall (({} {})) (= ({} {0}) {}))",
                        &ident(&eq.1.param),
                        type_name(&eq.1.param_type),
                        &ident(&eq.0),
                        &lowered.expr
                    )))
                }
            };
        }
        stmts
    }
}

pub fn ident<T>(ident: &Ident<T>) -> String {
    format!("{}_i{}", ident.orig_name, ident.index)
}

pub fn type_name(typ: &ExprType) -> String {
    match typ {
        ExprType::String => "String".to_owned(),
        ExprType::I64 => "(_ BitVec 64)".to_owned(),
        ExprType::F64 => "Float64".to_owned(),
        ExprType::Bool => "Bool".to_owned(),
        ExprType::DateTime => "Int".to_owned(),
        ExprType::Set(t) => format!("(Array {} Bool)", type_name(t)),
        ExprType::Option(t) => format!("(Option {})", type_name(t)),
        ExprType::Unknown(_) => panic!("Set(Unknown)s should never be serialized"),

        // Ids and objects are the same in SMT land
        ExprType::Id(t) | ExprType::Object(t) => ident(t),
        ExprType::Principal => "Principal".to_owned(),
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
        | ExprType::Principal
        | ExprType::Bool => false,
        ExprType::Unknown(_) => true,
        ExprType::Set(t) | ExprType::Option(t) => contains_unknown(t),
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

fn exists(var: &Ident<SMTVar>, typ: &ExprType, body: &str) -> String {
    format!("(exists (({} {})) {})", ident(&var), type_name(&typ), body)
}
