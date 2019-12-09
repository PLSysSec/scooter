pub use id_arena::Id;

use super::expr::*;
use super::*;
use crate::ast;

#[derive(Debug, Default)]
pub struct CompletePolicy {
    fields: HashMap<Id<Def>, FieldPolicy>,
    colls: HashMap<Id<Collection>, CollectionPolicy>,
}

impl CompletePolicy {
    pub fn collection_policy(&self, cid: Id<Collection>) -> &CollectionPolicy {
        &self.colls[&cid]
    }

    pub fn field_policy(&self, fid: Id<Def>) -> &FieldPolicy {
        &self.fields[&fid]
    }
}

#[derive(Debug)]
pub struct CompleteMigration(pub Vec<CompleteMigrationCommand>);

#[derive(Debug)]
pub struct CompleteMigrationCommand {
    pub table: Id<Collection>,
    pub action: CompleteMigrationAction,
}
#[derive(Debug)]
pub enum CompleteMigrationAction {
    RemoveField {
        field: Id<Def>,
    },
    AddField {
        field: Id<Def>,
        ty: Type,
        init: Lambda,
    },
}

#[derive(Debug)]
pub struct CollectionPolicy {
    pub create: Policy,
    pub delete: Policy,
}

#[derive(Debug)]
pub struct FieldPolicy {
    pub field_id: Id<Def>,
    pub read: Policy,
    pub edit: Policy,
}

#[derive(Debug)]
pub enum Policy {
    Public,
    None,
    Func(Lambda),
}

pub(crate) struct Lowerer<'a> {
    pub(crate) ird: &'a mut IrData,
    pub(crate) def_map: HashMap<String, Id<Def>>,
}

impl Lowerer<'_> {
    fn get_def(&self, name: &String) -> Id<Def> {
        *self.def_map.get(name).expect(&format!(
            "Use of undeclared identifier '{}' in policy",
            name
        ))
    }

    fn resolve_collection(&self, name: &String) -> (Id<Collection>, Type) {
        let c = self
            .ird
            .collections()
            .find(|c| c.name.eq_str(name))
            .expect(&format!("Unknown collection {}", name));
        (c.id, c.typ())
    }

    pub fn lower_policies(&mut self, gp: &ast::GlobalPolicy) -> CompletePolicy {
        let mut comp_policy = CompletePolicy::default();

        for ast_coll_pol in gp.collections.iter() {
            let (id, c_typ) = self.resolve_collection(&ast_coll_pol.name);
            let coll_pol = CollectionPolicy {
                create: self.lower_field_policy(c_typ.clone(), &ast_coll_pol.create),
                delete: self.lower_field_policy(c_typ.clone(), &ast_coll_pol.delete),
            };

            comp_policy.colls.insert(id, coll_pol);

            for (n, p) in ast_coll_pol.fields.iter() {
                let field_id = self.ird.field(id, n).id;

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
            ast::Policy::Func(f) => Policy::Func(self.lower_policy_func(param_type, f)),
        }
    }

    // TODO: update to be more generic when parser gets lambdas
    fn lower_policy_func(&mut self, param_type: Type, pf: &ast::Func) -> Lambda {
        let param = self.ird.create_def(&pf.param, param_type);
        let old_mapping = self.def_map.insert(pf.param.clone(), param);
        let body = self.lower_expr(&pf.expr);
        match old_mapping {
            Some(did) => {
                self.def_map.insert(pf.param.clone(), did);
            }
            None => {
                self.def_map
                    .remove(&pf.param)
                    .expect("This should be unreachable");
            }
        }

        Lambda { param, body }
    }

    fn lower_expr(&mut self, qe: &ast::QueryExpr) -> Id<Expr> {
        let kind = match qe {
            ast::QueryExpr::Or(le1, le2) => {
                ExprKind::Or(self.lower_expr(le1), self.lower_expr(le2))
            }
            ast::QueryExpr::Path(p) => match p.as_slice() {
                [v] => ExprKind::Var(self.get_def(v.into())),
                [v, m] => {
                    let obj = self.get_def(&v);
                    let cid = match self.ird.type_of(obj) {
                        Type::Collection(cid) => *cid,
                        _ => panic!(
                            "Attempted to access field {} of {} which is not an object",
                            &m, &v
                        ),
                    };
                    let field = self.ird.field(cid, &m).id;
                    ExprKind::Path(cid, obj, field)
                }
                _ => unreachable!("Longer paths can never be valid by construction"),
            },
            ast::QueryExpr::IntConst(i) => ExprKind::IntConst(i.clone()),
            ast::QueryExpr::FloatConst(f) => ExprKind::FloatConst(f.clone()),
            ast::QueryExpr::StringConst(s) => ExprKind::StringConst(s.clone()),
        };

        self.ird.exprs.alloc_with_id(|id| Expr { id, kind })
    }

    /// Turn a migration with string identifiers into one with resolved Id objects
    pub fn lower_migration_commands(&mut self, mig: ast::Migration) -> CompleteMigration {
        let mut complete_cmds = vec![];
        // Iterate over the migrations, where each lowering might
        // change the type environment.
        for ast::MigrationCommand { table, action } in mig.0.into_iter() {
            let (id, coll_typ) = self.resolve_collection(&table);
            let lowered_action = self.lower_migration_action(id, coll_typ.clone(), action);
            complete_cmds.push(CompleteMigrationCommand {
                table: id,
                action: lowered_action,
            });
        }
        CompleteMigration(complete_cmds)
    }

    fn lower_migration_action(
        &mut self,
        collection_id: Id<Collection>,
        collection_type: Type,
        action: ast::MigrationAction,
    ) -> CompleteMigrationAction {
        match action {
            ast::MigrationAction::RemoveField { field } => CompleteMigrationAction::RemoveField {
                field: self.ird.field(collection_id, &field).id,
            },
            ast::MigrationAction::AddField { field, ty, init } => {
                let lowered_ty = self.lower_type(ty);
                self.ird.add_field(collection_id, field.clone(), lowered_ty.clone());
                CompleteMigrationAction::AddField {
                field: self.ird.field(collection_id, &field).id,
                ty: lowered_ty.clone(),
                init: self.lower_func(collection_type, lowered_ty, &init),
                }
            },
        }
    }
    fn lower_func(&mut self, param_type: Type, expected_return_type: Type, pf: &ast::Func) -> Lambda {
        let param = self.ird.create_def(&pf.param, param_type);
        let old_mapping = self.def_map.insert(pf.param.clone(), param);
        let body = self.lower_expr(&pf.expr);
        self.typecheck_expr(body, expected_return_type);
        match old_mapping {
            Some(did) => {
                self.def_map.insert(pf.param.clone(), did);
            }
            None => {
                self.def_map
                    .remove(&pf.param)
                    .expect("This should be unreachable");
            }
        }

        Lambda { param, body }
    }
    fn typecheck_expr(&self, expr_id: Id<Expr>, expected_type: Type) {
        let expr = &self.ird[expr_id];
        match expr.kind {
            ExprKind::IntConst(_) => assert_eq!(expected_type, Type::Prim(Prim::I64)),
            ExprKind::FloatConst(_) => assert_eq!(expected_type, Type::Prim(Prim::F64)),
            ExprKind::StringConst(_) => assert_eq!(expected_type, Type::Prim(Prim::String)),
            ExprKind::Path(_collection, _obj, field) => {
                assert_eq!(expected_type, *self.ird.def_type(field));
            },
            _ => unimplemented!("Cannot typecheck complex expressions yet!"),
        };
    }
    fn lower_type(&mut self, ty: ast::FieldType) -> Type {
        match ty {
            ast::FieldType::String => Type::Prim(Prim::String),
            ast::FieldType::I64 => Type::Prim(Prim::I64),
            ast::FieldType::F64 => Type::Prim(Prim::F64),
            ast::FieldType::Id(s) => {
                let (id, _coll_typ) = self.resolve_collection(&s);
                Type::Id(id)
            },
        }
    }
}
