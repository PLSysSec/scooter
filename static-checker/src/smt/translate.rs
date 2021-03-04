use policy_lang::ir::{
    expr::{ExprType, FieldComparison, IRExpr, Var},
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
    let princ = ctx.declare_in_domain(ExprType::Principal, princ_id.clone());
    let rec = ctx.declare_in_domain(ExprType::Object(coll.clone()), rec_id.clone());

    // Declare the now constant for datetimes
    let now = declare(NOW_IDENT.clone(), &[], ExprType::DateTime);

    // Declare the option datatype
    let option_datatype =
        Statement::Hack("(declare-datatypes (T) ((Option none (some (v T)))))".to_string());

    // Predeclare the functions
    let mut before_decl = ctx.predeclare(before);
    let mut after_decl = ctx.predeclare(after);

    // Lower the fields
    let mut low_schema_fields = ctx.lower_schema_fields(equivs, schema);

    // Create initial variable mapping
    let var_map = VarMap::from_schema(schema);

    // Lower the functions
    let fields_with_equivs = equivs.iter().map(|equiv| equiv.0.clone()).collect();
    let mut before = ctx.lower_policy(&princ_id, &rec_id, &var_map, before, &fields_with_equivs);
    let mut after = ctx.lower_policy(&princ_id, &rec_id, &var_map, after, &fields_with_equivs);

    let safety_assertion =
        Statement::Assert(format!("(and {} (not {}))", &after.expr, &before.expr,));
    let mut out = low_schema_sorts;
    out.append(&mut low_schema_fields);
    out.insert(0, option_datatype);
    out.append(&mut before_decl);
    out.append(&mut after_decl);
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
        join_tables: ctx.join_tables,
    }
}

#[derive(Debug, Copy, Clone)]
pub(crate) struct SMTVar;

struct SMTResult {
    stmts: Vec<Statement>,
    expr: String,
    domain_exprs: Vec<(String, ExprType)>,
    validity_predicates: Vec<String>,
}

impl SMTResult {
    fn expr(e: impl ToString) -> Self {
        Self {
            stmts: vec![],
            expr: e.to_string(),
            domain_exprs: vec![],
            validity_predicates: vec![],
        }
    }

    fn new(
        stmts: Vec<Statement>,
        expr: impl ToString,
        domain_exprs: Vec<(String, ExprType)>,
        validity_predicates: Vec<String>,
    ) -> Self {
        Self {
            stmts,
            expr: expr.to_string(),
            domain_exprs,
            validity_predicates,
        }
    }
}

#[derive(Default)]
struct VarMap(HashMap<Ident<Var>, Ident<SMTVar>>);

impl VarMap {
    fn lookup(&self, var: &Ident<Var>) -> Ident<SMTVar> {
        self.0
            .get(var)
            .expect(&format!("Couldn't find var {:?}", *var))
            .clone()
    }

    fn from_schema(schema: &Schema) -> Self {
        Self(
            schema
                .static_principals
                .iter()
                .map(|id| (id.clone(), id.coerce()))
                .collect(),
        )
    }

    fn extend(&self, var: Ident<Var>, smtvar: Ident<SMTVar>) -> Self {
        let mut hm = self.0.clone();
        hm.insert(var, smtvar);
        VarMap(hm)
    }
}

#[derive(Default)]
struct SMTContext {
    princ_casts: HashMap<Ident<Collection>, (Ident<SMTVar>, Ident<SMTVar>)>,
    domains: HashMap<ExprType, Vec<Ident<SMTVar>>>,
    join_tables: HashMap<Ident<Field>, (Ident<Collection>, Ident<Field>, Ident<Field>, ExprType)>,
}

struct LoweredColl {
    sorts: Vec<Statement>,
    body: Vec<Statement>,
}

impl SMTContext {
    fn lower_policy(
        &self,
        princ: &Ident<SMTVar>,
        rec: &Ident<SMTVar>,
        var_map: &VarMap,
        pol: &Policy,
        fields_with_equivs: &Vec<Ident<Field>>,
    ) -> SMTResult {
        let id = Ident::new("policy");
        eprintln!("----POLICY-----");
        let stmts = match pol {
            Policy::None => vec![define(id.clone(), &[], ExprType::Bool, false)],
            Policy::Anyone => vec![define(id.clone(), &[], ExprType::Bool, true)],
            Policy::Func(f) => {
                let vm = var_map.extend(f.param.clone(), rec.clone());
                let f = self.lower_expr(
                    (princ, &ExprType::Principal),
                    &f.body,
                    &vm,
                    fields_with_equivs,
                );
                let func = define(id.clone(), &[], ExprType::Bool, &f.expr);

                let mut out: Vec<Statement> = f
                    .domain_exprs
                    .into_iter()
                    .map(|(d_expr, ty)| {
                        Statement::Assert(format!(
                            "(or {})",
                            match self.domains.get(&ty) {
                                Some(domain_vars) =>
                                    spaced(domain_vars.iter().map(|d_id| format!(
                                        "(= {} {})",
                                        d_expr,
                                        ident(d_id)
                                    ))),
                                None => "false".to_string(),
                            }
                        ))
                    })
                    .collect();
                out.extend(f.stmts.into_iter());
                out.extend(
                    f.validity_predicates
                        .into_iter()
                        .map(|pred| Statement::Assert(pred)),
                );
                out.push(func);
                out
            }
        };

        SMTResult::new(stmts, ident(&id), vec![], vec![])
    }

    fn lower_expr(
        &self,
        target: (&Ident<SMTVar>, &ExprType),
        body: &IRExpr,
        vm: &VarMap,
        fields_with_equivs: &Vec<Ident<Field>>,
    ) -> SMTResult {
        debug_assert!(!contains_unknown(&body.type_of()));

        // We need to downcast if target is a Principal and body is a list of concrete type
        match body.type_of() {
            ExprType::Set(id) if *target.1 == ExprType::Principal => {
                eprintln!("SHIFT!");
                if let ExprType::Id(ref id) = *id {
                    let new_target = (&self.princ_casts[id].1, &ExprType::Object(id.clone()));
                    let low = self.lower_expr(new_target, body, vm, fields_with_equivs);
                    let expr = format!(
                        "(and (= {} ({} {})) {})",
                        ident(&target.0),
                        ident(&self.princ_casts[id].0),
                        ident(new_target.0),
                        &low.expr
                    );
                    return SMTResult::new(
                        low.stmts,
                        expr,
                        low.domain_exprs,
                        low.validity_predicates,
                    );
                }
            }
            _ => eprintln!("{:?}", body.type_of()),
        };

        match body {
            IRExpr::AppendS(l, r) => {
                self.simple_nary_op("str.++", target, &[l, r], vm, fields_with_equivs)
            }
            IRExpr::AddI(l, r) => {
                self.simple_nary_op("bvadd", target, &[l, r], vm, fields_with_equivs)
            }
            IRExpr::AddD(l, r) => self.simple_nary_op("+", target, &[l, r], vm, fields_with_equivs),
            IRExpr::AddF(l, r) => {
                self.simple_nary_op("fp.add", target, &[l, r], vm, fields_with_equivs)
            }
            IRExpr::SubI(l, r) => {
                self.simple_nary_op("bvsub", target, &[l, r], vm, fields_with_equivs)
            }
            IRExpr::SubD(l, r) => self.simple_nary_op("-", target, &[l, r], vm, fields_with_equivs),
            IRExpr::SubF(l, r) => {
                self.simple_nary_op("fp.sub", target, &[l, r], vm, fields_with_equivs)
            }
            IRExpr::IsEq(ExprType::F64, l, r) => {
                self.simple_nary_op("fp.eq", target, &[l, r], vm, fields_with_equivs)
            }
            // In policylang, equality is not defined for lists so no special handling is needed
            IRExpr::IsEq(_, l, r) => {
                self.simple_nary_op("=", target, &[l, r], vm, fields_with_equivs)
            }
            IRExpr::Not(b) => self.simple_nary_op("not", target, &[b], vm, fields_with_equivs),
            IRExpr::IsLessI(l, r) => {
                self.simple_nary_op("bvslt", target, &[l, r], vm, fields_with_equivs)
            }
            IRExpr::IsLessD(l, r) => {
                self.simple_nary_op("<", target, &[l, r], vm, fields_with_equivs)
            }
            IRExpr::IsLessF(l, r) => {
                self.simple_nary_op("fp.lt", target, &[l, r], vm, fields_with_equivs)
            }
            IRExpr::IntToFloat(b) => self.simple_nary_op(
                "(_ to_fp 11 53) roundNearestTiesToEven",
                target,
                &[b],
                vm,
                fields_with_equivs,
            ),
            IRExpr::Path(ty, obj, f) => match ty {
                ExprType::Set(ref _inner_ty) => {
                    let lower = self.lower_expr(target, obj, vm, fields_with_equivs);
                    let (coll, from, to, _typ) = self.join_tables[f].clone();
                    let domain_ids = self.domains[&ExprType::Object(coll.clone())].clone();
                    let domain_clauses: Vec<_> = domain_ids
                        .into_iter()
                        .map(|id| {
                            format!(
                                "(and (= ({} {}) {}) (= ({} {}) {}))",
                                ident(&from),
                                ident(&id),
                                &lower.expr,
                                ident(&to),
                                ident(&id),
                                ident(&target.0)
                            )
                        })
                        .collect();
                    let expr = format!("(or {})", domain_clauses.join(" "));
                    let mut validity_predicates = lower.validity_predicates;
                    if fields_with_equivs.contains(&f) {
                        validity_predicates.push(format!(
                            "({} {})",
                            ident(&validity_function_ident(f)),
                            lower.expr
                        ))
                    }
                    // TODO: This might not be the right set of domain_exprs
                    SMTResult::new(lower.stmts, expr, lower.domain_exprs, validity_predicates)
                }
                _ => {
                    let lowered = self.lower_expr(target, obj, vm, fields_with_equivs);

                    let mut validity_predicates = lowered.validity_predicates;
                    if fields_with_equivs.contains(&f) {
                        validity_predicates.push(format!(
                            "({} {})",
                            ident(&validity_function_ident(f)),
                            lowered.expr
                        ))
                    }
                    SMTResult::new(
                        lowered.stmts,
                        format!("({} {})", &ident(f), lowered.expr),
                        lowered.domain_exprs,
                        validity_predicates,
                    )
                }
            },
            IRExpr::Var(_, i) => SMTResult::expr(ident(&vm.lookup(i))),
            // Because id's and object types are the same, find is a no-op
            IRExpr::LookupById(coll, b) => {
                let lower = self.lower_expr(target, b, vm, fields_with_equivs);
                let mut out_domain_exprs = lower.domain_exprs;
                out_domain_exprs.push((format!("{}", &lower.expr), ExprType::Object(coll.clone())));

                SMTResult::new(
                    lower.stmts,
                    lower.expr,
                    out_domain_exprs,
                    lower.validity_predicates,
                )
            }
            IRExpr::Now => SMTResult::expr(ident(&NOW_IDENT)),
            IRExpr::DateTimeConst(datetime) => SMTResult::expr(datetime.timestamp()),
            //IRExpr::IntConst(i) => SMTResult::expr(format!("#x{:x}", i)),
            IRExpr::IntConst(i) => SMTResult::expr(format!("(_ bv{} 64)", i)),
            IRExpr::FloatConst(f) => {
                SMTResult::expr(format!("((_ to_fp 11 53) roundNearestTiesToEven {})", f))
            }
            IRExpr::StringConst(s) => SMTResult::expr(format!("\"{}\"", s)),
            IRExpr::BoolConst(b) => SMTResult::expr(b),
            IRExpr::Find(_coll, fields) => {
                let mut stmts = vec![];
                let mut field_checks = vec![];
                let mut domain_exprs = vec![];
                let mut validity_predicates = vec![];
                for (comp, f, fty, expr) in fields.iter() {
                    let field_expr = self.lower_expr(target, expr, vm, fields_with_equivs);
                    stmts.extend(field_expr.stmts);
                    domain_exprs.extend(field_expr.domain_exprs);
                    validity_predicates.extend(field_expr.validity_predicates);
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
                            let ids = self.domains[&ExprType::Object(coll)].iter();
                            let mut join_eqs = Vec::new();
                            for id in ids {
                                join_eqs.push(format!(
                                    "(and (= ({} {}) {}) (= ({} {}) {}))\n",
                                    ident(&from),
                                    ident(id),
                                    ident(&target.0),
                                    ident(&to),
                                    ident(id),
                                    &field_expr.expr
                                ));
                            }
                            field_checks.push(format!("(or {})", spaced(join_eqs.into_iter())));
                        }
                    }
                }

                let anded_eqs = format!("(and {} true)", spaced(field_checks.into_iter()));

                SMTResult::new(stmts, anded_eqs, domain_exprs, validity_predicates)
            }
            IRExpr::Object(coll, fields, template) => {
                let obj_id = Ident::new("obj_lit");
                let obj = declare(obj_id.clone(), &[], ExprType::Object(coll.clone()));
                let template_expr = template
                    .as_ref()
                    .map(|t| self.lower_expr(target, t, vm, fields_with_equivs));

                let mut stmts = vec![obj];
                let mut exprs = vec![];
                let mut domain_exprs = vec![];
                let mut validity_predicates = vec![];
                for (_f_id, f_expr) in fields.iter() {
                    if let Some(e) = f_expr {
                        let low_e = self.lower_expr(target, e, vm, fields_with_equivs);
                        exprs.push(format!("(= {} {})", ident(&obj_id), &low_e.expr));
                        stmts.extend(low_e.stmts);
                        domain_exprs.extend(low_e.domain_exprs);
                        validity_predicates.extend(low_e.validity_predicates)
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

                SMTResult::new(stmts, ident(&obj_id), domain_exprs, validity_predicates)
            }
            IRExpr::Map(list_expr, func) => {
                let mut elems = vec![];
                let mut preamble = vec![];
                let mut domain_exprs = vec![];
                let mut validity_predicates = vec![];
                let ids: Box<dyn Iterator<Item = Ident<SMTVar>>> = match func.param_type {
                    ExprType::Object(ref coll) | ExprType::Id(ref coll) => Box::new(
                        self.domains
                            .get(&ExprType::Object(coll.clone()))
                            .expect(&format!(
                                "Couldn't find domain for object of type {}",
                                coll.orig_name
                            ))
                            .iter()
                            .cloned(),
                    ),
                    _ => {
                        let id = Ident::new("map_var");
                        preamble.push(declare(id.clone(), &[], func.param_type.clone()));
                        Box::new(iter::once(id))
                    }
                };
                for id in ids {
                    let list_expr = self.lower_expr(
                        (&id, &func.param_type),
                        &list_expr,
                        &vm,
                        fields_with_equivs,
                    );
                    preamble.extend(list_expr.stmts);
                    let func_expr = self.lower_expr(
                        target,
                        &func.body,
                        &vm.extend(func.param.clone(), id.clone()),
                        fields_with_equivs,
                    );
                    preamble.extend(func_expr.stmts);
                    let elem = format!(
                        "(and {} (= {} {}))",
                        &list_expr.expr,
                        &func_expr.expr,
                        ident(target.0)
                    );
                    elems.push(elem);
                    domain_exprs.extend(list_expr.domain_exprs);
                    validity_predicates.extend(list_expr.validity_predicates);

                    domain_exprs.extend(func_expr.domain_exprs);
                    validity_predicates.extend(func_expr.validity_predicates);
                }

                let expr = format!("(or {})", spaced(elems.into_iter()));
                SMTResult::new(preamble, expr, domain_exprs, validity_predicates)
            }
            IRExpr::FlatMap(set_expr, func) => {
                let mut elems = vec![];
                let mut preamble = vec![];
                let mut domain_exprs = vec![];
                let mut validity_predicates = vec![];
                let ids: Box<dyn Iterator<Item = Ident<SMTVar>>> = match func.param_type {
                    ExprType::Object(ref coll) | ExprType::Id(ref coll) => Box::new(
                        self.domains[&ExprType::Object(coll.clone())]
                            .iter()
                            .cloned(),
                    ),
                    _ => {
                        let id = Ident::new("map_var");
                        preamble.push(declare(id.clone(), &[], func.param_type.clone()));
                        Box::new(iter::once(id))
                    }
                };
                for id in ids {
                    let set_expr = self.lower_expr(
                        (&id, &func.param_type),
                        &set_expr,
                        &vm,
                        fields_with_equivs,
                    );
                    preamble.extend(set_expr.stmts);
                    domain_exprs.extend(set_expr.domain_exprs);
                    validity_predicates.extend(set_expr.validity_predicates);
                    let func_expr = self.lower_expr(
                        target,
                        &func.body,
                        &vm.extend(func.param.clone(), id.clone()),
                        fields_with_equivs,
                    );
                    preamble.extend(func_expr.stmts);

                    domain_exprs.extend(func_expr.domain_exprs);
                    validity_predicates.extend(func_expr.validity_predicates);

                    let elem = format!("(and {} {})", &set_expr.expr, &func_expr.expr,);
                    elems.push(elem);
                }

                let expr = format!("(or {})", spaced(elems.into_iter()));
                SMTResult::new(preamble, expr, domain_exprs, validity_predicates)
            }
            IRExpr::AppendL(_, l, r) => {
                let left = self.lower_expr(target, l, vm, fields_with_equivs);
                let right = self.lower_expr(target, r, vm, fields_with_equivs);
                let expr = format!("(or {} {})", &left.expr, &right.expr);

                let mut stmts = left.stmts;
                stmts.extend(right.stmts);
                let mut domain_exprs = left.domain_exprs;
                domain_exprs.extend(right.domain_exprs);
                let mut validity_predicates = left.validity_predicates;
                validity_predicates.extend(right.validity_predicates);
                SMTResult::new(stmts, expr, domain_exprs, validity_predicates)
            }
            IRExpr::DiffL(_, l, r) => {
                let left = self.lower_expr(target, l, vm, fields_with_equivs);
                let right = self.lower_expr(target, r, vm, fields_with_equivs);
                let expr = format!("(and {} (not {}))", &left.expr, &right.expr);

                let mut stmts = left.stmts;
                stmts.extend(right.stmts);
                let mut domain_exprs = left.domain_exprs;
                domain_exprs.extend(right.domain_exprs);
                let mut validity_predicates = left.validity_predicates;
                validity_predicates.extend(right.validity_predicates);
                SMTResult::new(stmts, expr, domain_exprs, validity_predicates)
            }
            IRExpr::Intersect(_, l, r) => {
                let left = self.lower_expr(target, l, vm, fields_with_equivs);
                let right = self.lower_expr(target, r, vm, fields_with_equivs);
                let expr = format!("(and {} {})", &left.expr, &right.expr);

                let mut stmts = left.stmts;
                stmts.extend(right.stmts);
                let mut domain_exprs = left.domain_exprs;
                domain_exprs.extend(right.domain_exprs);
                let mut validity_predicates = left.validity_predicates;
                validity_predicates.extend(right.validity_predicates);
                SMTResult::new(stmts, expr, domain_exprs, validity_predicates)
            }
            IRExpr::Set(_, exprs) => {
                let mut stmts = vec![];
                let mut equalities = vec![];
                let mut domain_exprs = vec![];
                let mut validity_predicates = vec![];
                for expr in exprs.iter() {
                    let elem_expr = match expr.type_of() {
                        ExprType::Id(coll) if *target.1 == ExprType::Principal => {
                            let new_target =
                                (&self.princ_casts[&coll].1, &ExprType::Object(coll.clone()));
                            let low = self.lower_expr(new_target, expr, vm, fields_with_equivs);
                            stmts.extend(low.stmts);
                            domain_exprs.extend(low.domain_exprs);
                            validity_predicates.extend(low.validity_predicates);
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
                            let low = self.lower_expr(target, expr, vm, fields_with_equivs);
                            stmts.extend(low.stmts);
                            domain_exprs.extend(low.domain_exprs);
                            validity_predicates.extend(low.validity_predicates);
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
                SMTResult::new(stmts, expr, domain_exprs, validity_predicates)
            }
            IRExpr::If(_, c, t, e) => {
                self.simple_nary_op("ite", target, &[c, t, e], vm, fields_with_equivs)
            }
            IRExpr::Public => SMTResult::expr("true"),
            IRExpr::None(ty) => SMTResult::expr(format!("(as none (Option {}))", type_name(&ty))),
            IRExpr::Some(_ty, inner_expr) => {
                let elem_expr = self.lower_expr(target, inner_expr, vm, fields_with_equivs);
                SMTResult::new(
                    elem_expr.stmts,
                    format!("(some {})", &elem_expr.expr),
                    elem_expr.domain_exprs,
                    elem_expr.validity_predicates,
                )
            }
            IRExpr::Match(_ty, opt_expr, var, some_expr, none_expr) => {
                let mut stmts = Vec::new();
                let mut domain_exprs = Vec::new();
                let mut validity_predicates = Vec::new();
                let match_smt_var = Ident::new("match_var");
                stmts.push(declare(
                    match_smt_var.clone(),
                    &[],
                    match opt_expr.type_of() {
                        ExprType::Option(t) => t.as_ref().clone(),
                        _ => panic!("Type error"),
                    },
                ));
                let opt_expr = self.lower_expr(target, opt_expr, vm, fields_with_equivs);
                let some_expr = self.lower_expr(
                    target,
                    some_expr,
                    &vm.extend(var.clone(), match_smt_var.clone()),
                    fields_with_equivs,
                );
                let none_expr = self.lower_expr(target, none_expr, vm, fields_with_equivs);
                stmts.extend(opt_expr.stmts);
                stmts.extend(some_expr.stmts);
                stmts.extend(none_expr.stmts);
                domain_exprs.extend(opt_expr.domain_exprs);
                domain_exprs.extend(some_expr.domain_exprs);
                domain_exprs.extend(none_expr.domain_exprs);
                validity_predicates.extend(opt_expr.validity_predicates);
                validity_predicates.extend(some_expr.validity_predicates);
                validity_predicates.extend(none_expr.validity_predicates);

                let expr = format!(
                    "(match {} (((some {}) {}) (none {})))",
                    &opt_expr.expr,
                    ident(&match_smt_var),
                    &some_expr.expr,
                    none_expr.expr
                );
                SMTResult::new(stmts, expr, domain_exprs, validity_predicates)
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
            "(declare-datatypes () ((Principal unauth {} {})))",
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

        let (sorts, bodies): (Vec<_>, Vec<_>) = colls.map(|lc| (lc.sorts, lc.body)).unzip();
        let mut out: Vec<_> = sorts
            .into_iter()
            .flatten()
            .chain(bodies.into_iter().flatten())
            .chain(iter::once(princ_decl))
            .collect();
        for (_princ_cons, princ_obj, princ_coll) in princ_ids.iter() {
            let princ_obj_decl =
                self.declare_in_domain(ExprType::Object(princ_coll.clone()), princ_obj.clone());
            out.push(princ_obj_decl);
        }
        out
    }
    /// Lowers the schema fields to a String containing an SMT2LIB script
    fn lower_schema_fields(&mut self, equivs: &[Equiv], schema: &Schema) -> Vec<Statement> {
        schema
            .collections
            .iter()
            .map(|c| self.lower_collection_fields(equivs, c))
            .collect::<Vec<_>>()
            .concat()
    }

    fn lower_collection_sorts(&mut self, coll: &Collection) -> LoweredColl {
        let mut sorts = vec![Statement::DeclSort {
            id: coll.name.coerce(),
        }];

        let joins = coll.fields().filter_map(|f| {
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
                return Some(self.lower_collection(
                    &[],
                    &Collection {
                        name: coll_name,
                        fields: vec![
                            Field {
                                name: from_name,
                                typ: ExprType::Id(coll.name.clone()),
                            },
                            Field {
                                name: to_name,
                                typ: inner_ty.as_ref().clone(),
                            },
                        ],
                    },
                ));
            }
            None
        });

        let (join_sorts, join_bodies): (Vec<_>, Vec<_>) =
            joins.map(|lc| (lc.sorts, lc.body)).unzip();
        sorts.extend(join_sorts.into_iter().flatten());
        LoweredColl {
            sorts,
            body: join_bodies.concat(),
        }
    }
    fn lower_collection_fields(&mut self, equivs: &[Equiv], coll: &Collection) -> Vec<Statement> {
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

                let equiv = equivs
                    .iter()
                    .find(|Equiv(e, _)| e == &f.name)
                    .map(|Equiv(_, l)| l);
                match equiv {
                    None => vec![declare(
                        f.name.coerce(),
                        &[ExprType::Object(coll.name.clone())],
                        f.typ.clone(),
                    )],
                    Some(lambda) => {
                        let varmap =
                            VarMap::default().extend(lambda.param.clone(), lambda.param.coerce());
                        let body = self.lower_expr(
                            (&Ident::new("bogus"), &ExprType::Bool),
                            &lambda.body,
                            &varmap,
                            &equivs.iter().map(|equiv| equiv.0.clone()).collect(),
                        );

                        let mut out = body.stmts;
                        out.push(define(
                            validity_function_ident(&f.name).coerce(),
                            &[(lambda.param.coerce(), ExprType::Object(coll.name.clone()))],
                            ExprType::Bool,
                            format!(
                                "(and (and {}) (and {}))",
                                if body.domain_exprs.len() == 0 {
                                    "true".to_string()
                                } else {
                                    spaced(body.domain_exprs.into_iter().map(|(dexpr, ty)| {
                                        format!(
                                            "(or {})",
                                            match self.domains.get(&ty) {
                                                Some(vec) => spaced(vec.iter().map(
                                                    |d_id| format!("(= {} {})", dexpr, ident(d_id))
                                                )),
                                                None => "false".to_string(),
                                            }
                                        )
                                    }))
                                },
                                if body.validity_predicates.len() == 0 {
                                    "true".to_string()
                                } else {
                                    spaced(body.validity_predicates.into_iter())
                                }
                            ),
                        ));

                        out.push(define(
                            f.name.coerce(),
                            &[(lambda.param.coerce(), ExprType::Object(coll.name.clone()))],
                            f.typ.clone(),
                            body.expr,
                        ));
                        out
                    }
                }
            })
            .collect()
    }

    /// Lowers each collection one by one.
    /// Each collection gets its own sort named after its Ident,
    /// and each field is a function mapping that sort to either a native
    /// SMT sort or to another sort.
    fn lower_collection(&mut self, equivs: &[Equiv], coll: &Collection) -> LoweredColl {
        let sorts = self.lower_collection_sorts(coll);
        let fields = self.lower_collection_fields(equivs, coll);
        LoweredColl {
            sorts: sorts.sorts,
            body: sorts.body.into_iter().chain(fields.into_iter()).collect(),
        }
    }

    fn simple_nary_op(
        &self,
        op: &str,
        target: (&Ident<SMTVar>, &ExprType),
        exprs: &[&IRExpr],
        vm: &VarMap,
        fields_with_equivs: &Vec<Ident<Field>>,
    ) -> SMTResult {
        let results: Vec<SMTResult> = exprs
            .into_iter()
            .map(|e| self.lower_expr(target, e, vm, fields_with_equivs))
            .collect();
        let exprs = results.iter().map(|r| r.expr.clone());
        let stmt_lsts: Vec<Vec<Statement>> = results.iter().map(|r| r.stmts.clone()).collect();
        let dexpr_lsts: Vec<Vec<(String, ExprType)>> =
            results.iter().map(|r| r.domain_exprs.clone()).collect();
        let vpred_lsts: Vec<Vec<String>> = results
            .iter()
            .map(|r| r.validity_predicates.clone())
            .collect();
        let body = format!("({} {})", op, spaced(exprs));
        SMTResult::new(
            stmt_lsts.concat(),
            body,
            dexpr_lsts.concat(),
            vpred_lsts.concat(),
        )
    }

    fn predeclare_expr(&mut self, e: &IRExpr) -> Vec<Statement> {
        let mut out = vec![];
        for se in e.subexprs_preorder() {
            match se {
                IRExpr::LookupById(coll, ..) => {
                    out.push(self.declare_in_domain(
                        ExprType::Object(coll.clone()),
                        Ident::new("domain_var"),
                    ));
                }
                IRExpr::Path(ExprType::Set(_inner_ty), _obj, f) => {
                    let (coll, _from, _to, _typ) = self
                        .join_tables
                        .get(f)
                        .expect(&format!(
                            "Couldn't find a join table for field {}",
                            f.orig_name
                        ))
                        .clone();
                    out.push(self.declare_in_domain(
                        ExprType::Object(coll.clone()),
                        Ident::new("domain_var"),
                    ));
                }
                IRExpr::Find(coll, fields) => {
                    out.push(self.declare_in_domain(
                        ExprType::Object(coll.clone()),
                        Ident::new("domain_var"),
                    ));
                    for (comp, field, _fty, _expr) in fields.iter() {
                        if *comp == FieldComparison::Contains {
                            let (coll, _from, _to, _typ) = self.join_tables[field].clone();
                            out.push(self.declare_in_domain(
                                ExprType::Object(coll.clone()),
                                Ident::new("join_var"),
                            ));
                        }
                    }
                }
                _ => {}
            }
        }
        out
    }

    fn predeclare(&mut self, pol: &Policy) -> Vec<Statement> {
        match pol {
            Policy::None | Policy::Anyone => vec![],
            Policy::Func(f) => self.predeclare_expr(&f.body),
        }
    }

    fn declare_in_domain(&mut self, typ: ExprType, id: Ident<SMTVar>) -> Statement {
        if !self.domains.contains_key(&typ) {
            self.domains.insert(typ.clone(), vec![]);
        }
        self.domains.get_mut(&typ).unwrap().push(id.clone());

        declare(id, &[], typ)
    }

    #[allow(dead_code)]
    fn domain_ident(&self, id: Ident<SMTVar>, typ: ExprType) -> Vec<Statement> {
        let expr = format!(
            "(or {})",
            spaced(
                self.domains
                    .get(&typ)
                    .expect(&format!("Cannot find domain for type {}", typ))
                    .iter()
                    .map(|d_id| format!("(= {} {})", ident(&id), ident(d_id)))
            )
        );
        let decl = declare(id.clone(), &[], typ);
        let ass = Statement::Assert(expr);

        vec![decl, ass]
    }
}

pub fn ident<T>(ident: &Ident<T>) -> String {
    format!("{}_i{}", ident.orig_name, ident.index)
}

pub fn validity_function_ident<T>(id: &Ident<T>) -> Ident<T> {
    Ident::unsafe_construct(0, format!("{}_valid", ident(id)))
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
