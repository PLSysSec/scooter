use id_arena::Id;

use crate::ast;
use super::expr::*;
use super::*;

#[derive(Debug, Default)]
pub struct CompletePolicy {
    fields: HashMap<Id<Def>, FieldPolicy>,
    colls: HashMap<Id<Collection>, CollectionPolicy>,
}

#[derive(Debug)]
pub struct CollectionPolicy {
    create: Policy,
    delete: Policy,
}

#[derive(Debug)]
pub struct FieldPolicy {
    field_id: Id<Def>,
    read: Policy,
    edit: Policy,
}

#[derive(Debug)]
pub enum Policy {
    Public,
    None,
    Func(Lambda)
}

pub(crate) struct Lowerer<'a> {
    pub(crate) ird: &'a mut IrData,
    pub(crate) def_map: HashMap<String, Id<Def>>,
}

impl Lowerer<'_> {
    fn get_def(&self, name: &String) -> Id<Def> {
        *self.def_map.get(name).expect(&format!("Use of undeclared identifier '{}' in policy", name))
    }

    pub fn lower_policies(&mut self, gp: &ast::GlobalPolicy) -> CompletePolicy {
        let mut comp_policy = CompletePolicy::default();

        for ast_coll_pol in gp.collections.iter() {
            let (id, c_typ) = {
                let (id, c) = self.ird.collections().find(|(_, c)| c.name.eq_str(&ast_coll_pol.name)).unwrap();
                (id, c.typ())
            };
            let coll_pol = CollectionPolicy {
                create: self.lower_field_policy(c_typ.clone(), &ast_coll_pol.create),
                delete: self.lower_field_policy(c_typ.clone(), &ast_coll_pol.delete),
            };

            comp_policy.colls.insert(id, coll_pol);

            for (n, p) in ast_coll_pol.fields.iter() {
                let field_id = self.ird.field(id, n);

                let fp = FieldPolicy {
                    field_id,
                    read: self.lower_field_policy(c_typ.clone(), &p.read),
                    edit: self.lower_field_policy(c_typ.clone(), &p.write),
                };

                comp_policy.fields.insert(field_id, fp);
            }
        }

        comp_policy
    }

    fn lower_field_policy(&mut self, param_type: Type, p: &ast::Policy) -> Policy {
        match p {
            ast::Policy::Public => Policy::Public,
            ast::Policy::None => Policy::None,
            ast::Policy::Func(f) => Policy::Func(self.lower_policy_func(param_type, f))
        }
    }

    // TODO: update to be more generic when parser gets lambdas
    fn lower_policy_func(&mut self, param_type: Type, pf: &ast::PolicyFunc) -> Lambda {
        let param = self.ird.create_def(&pf.param, param_type);
        let old_mapping = self.def_map.insert(pf.param.clone(), param);
        let body = self.lower_expr(&pf.expr);
        match old_mapping {
            Some(did) => {
                self.def_map.insert(pf.param.clone(), did);
            }
            None => {
                self.def_map.remove(&pf.param).expect("This should be unreachable");
            }
        }

        Lambda {
            param,
            body
        }
    }

    fn lower_expr(&mut self, qe: &ast::QueryExpr) -> Id<Expr> {
        let kind = match qe {
            ast::QueryExpr::Or(le1, le2) => {
                ExprKind::Or(self.lower_expr(le1), self.lower_expr(le2))
            },
            ast::QueryExpr::Path(p) => {
                match p.as_slice() {
                    [v] => ExprKind::Var(self.get_def(&v)),
                    [v, m] => ExprKind::Path(self.get_def(&v), self.get_def(&m)),
                    _ => unreachable!("Longer paths can never be valid by construction")
                }
            }
        };

        self.ird.exprs.alloc_with_id(|id| Expr {
            id,
            kind,
        })
    }
}