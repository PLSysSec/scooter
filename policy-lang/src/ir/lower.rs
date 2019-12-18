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
pub enum CompleteMigrationCommand {
    CollAction {
        table: Id<Collection>,
        action: CompleteMigrationAction,
    },
    Create {
        table_id: Id<Collection>,
    },
    Delete {
        table_id: Id<Collection>,
    },
}

#[derive(Debug)]
pub enum CompleteObjectCommand {
    CreateObject {
        collection: Id<Collection>,
        value: Id<Expr>,
    },
    DeleteObject {
        collection: Id<Collection>,
        id_expr: Id<Expr>,
    },
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
    ChangeField {
        field: Id<Def>,
        new_ty: Type,
        new_init: Lambda,
    },
    RenameField {
        field_id: Id<Def>,
        old_name: String,
        new_name: String,
    },
    ForEach {
        param: Id<Def>,
        body: CompleteObjectCommand,
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
            .active_collections()
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
        self.typecheck_expr(body, Type::List(Box::new(Type::IdAny)));
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
            ast::QueryExpr::Minus(le1, le2) => {
                let lowered1 = self.lower_expr(le1);
                let lowered2 = self.lower_expr(le2);
                match (
                    self.infer_expr_type(lowered1),
                    self.infer_expr_type(lowered2),
                ) {
                    (Type::Prim(Prim::I64), Type::Prim(Prim::I64)) => {
                        ExprKind::SubI(lowered1, lowered2)
                    }
                    (Type::Prim(Prim::F64), Type::Prim(Prim::I64)) => {
                        let converted = self.ird.exprs.alloc_with_id(|id| Expr {
                            id,
                            kind: ExprKind::IntToFloat(lowered2),
                        });
                        ExprKind::SubF(lowered1, converted)
                    }
                    (Type::Prim(Prim::I64), Type::Prim(Prim::F64)) => {
                        println!("rhs: {:?}", self.ird[lowered2]);
                        let converted = self.ird.exprs.alloc_with_id(|id| Expr {
                            id,
                            kind: ExprKind::IntToFloat(lowered1),
                        });
                        ExprKind::SubF(converted, lowered2)
                    }
                    (Type::Prim(Prim::F64), Type::Prim(Prim::F64)) => {
                        ExprKind::SubF(lowered1, lowered2)
                    }
                    (ty1, ty2) => unimplemented!(
                        "Cannot resolve + operator for types {:?} and {:?}",
                        ty1,
                        ty2
                    ),
                }
            }
            ast::QueryExpr::Plus(le1, le2) => {
                let lowered1 = self.lower_expr(le1);
                let lowered2 = self.lower_expr(le2);

                match (
                    self.infer_expr_type(lowered1),
                    self.infer_expr_type(lowered2),
                ) {
                    (Type::Prim(Prim::String), Type::Prim(Prim::String)) => {
                        ExprKind::AppendS(lowered1, lowered2)
                    }
                    (Type::List(t1), Type::List(t2)) => {
                        if *t1 == *t2 {
                            ExprKind::AppendL(*t1, lowered1, lowered2)
                        } else {
                            ExprKind::AppendL(Type::Any, lowered1, lowered2)
                        }
                    }
                    (Type::Id(coll1), Type::Id(coll2)) => {
                        assert_eq!(coll1, coll2, "Heterogenous ORs not allowed");
                        ExprKind::Or(lowered1, lowered2)
                    }
                    (Type::Prim(Prim::I64), Type::Prim(Prim::I64)) => {
                        ExprKind::AddI(lowered1, lowered2)
                    }
                    (Type::Prim(Prim::F64), Type::Prim(Prim::I64)) => {
                        let converted = self.ird.exprs.alloc_with_id(|id| Expr {
                            id,
                            kind: ExprKind::IntToFloat(lowered2),
                        });
                        ExprKind::AddF(lowered1, converted)
                    }
                    (Type::Prim(Prim::I64), Type::Prim(Prim::F64)) => {
                        println!("rhs: {:?}", self.ird[lowered2]);
                        let converted = self.ird.exprs.alloc_with_id(|id| Expr {
                            id,
                            kind: ExprKind::IntToFloat(lowered1),
                        });
                        ExprKind::AddF(converted, lowered2)
                    }
                    (Type::Prim(Prim::F64), Type::Prim(Prim::F64)) => {
                        ExprKind::AddF(lowered1, lowered2)
                    }
                    (ty1, ty2) => unimplemented!(
                        "Cannot resolve + operator for types {:?} and {:?}",
                        ty1,
                        ty2
                    ),
                }
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
            ast::QueryExpr::Object(ast::ObjectLiteral {
                coll: coll_name,
                fields,
                template_obj,
            }) => {
                let coll = self
                    .ird
                    .active_collections()
                    .find(|c| c.name.eq_str(coll_name))
                    .expect(&format!("Unknown collection {}", coll_name));
                let coll_id = coll.id.clone();
                let resolved_field_ids: Vec<Id<Def>> = fields
                    .iter()
                    .map(|(name, _expr)| {
                        coll.lookup_field(name)
                            .expect(&format!("Couldn't find field {}", name))
                            .clone()
                    })
                    .collect();
                if template_obj.is_none() {
                    for (field_name, field_id) in coll.fields() {
                        if field_name == "id" {
                            continue;
                        }
                        assert!(
                            resolved_field_ids.contains(field_id),
                            format!(
                                "Initializer for {} doesn't contain field {}",
                                coll_name, field_name
                            )
                        );
                    }
                }
                let lowered_template_obj = template_obj.as_ref().map(|expr| self.lower_expr(expr));
                let lowered_exprs: Vec<Id<Expr>> = fields
                    .into_iter()
                    .map(|(_name, expr)| self.lower_expr(expr))
                    .collect();
                ExprKind::Object(
                    coll_id,
                    resolved_field_ids
                        .into_iter()
                        .zip(lowered_exprs.into_iter())
                        .collect(),
                    lowered_template_obj,
                )
            }
            ast::QueryExpr::List(exprs) => {
                ExprKind::List(exprs.iter().map(|expr| self.lower_expr(expr)).collect())
            }
        };

        self.ird.exprs.alloc_with_id(|id| Expr { id, kind })
    }

    /// Turn a migration with string identifiers into one with resolved Id objects
    pub fn lower_migration_commands(&mut self, mig: ast::Migration) -> CompleteMigration {
        let mut complete_cmds = vec![];
        // Iterate over the migrations, where each lowering might
        // change the type environment.
        for cmd in mig.0.into_iter() {
            match cmd {
                ast::MigrationCommand::CollAction { table, action } => {
                    let (id, coll_typ) = self.resolve_collection(&table);
                    let lowered_action = self.lower_migration_action(id, coll_typ.clone(), action);
                    complete_cmds.push(CompleteMigrationCommand::CollAction {
                        table: id,
                        action: lowered_action,
                    });
                }
                ast::MigrationCommand::Create { table_name, layout } => {
                    let lowered_layout = layout
                        .into_iter()
                        .map(|(name, fty)| (name, self.lower_type(fty)))
                        .collect();
                    let coll_id = self.ird.add_collection(&table_name, lowered_layout);
                    complete_cmds.push(CompleteMigrationCommand::Create { table_id: coll_id });
                }
                ast::MigrationCommand::Delete { table_name } => {
                    let (coll_id, _coll_typ) = self.resolve_collection(&table_name);
                    self.ird.retire_collection(coll_id);
                    complete_cmds.push(CompleteMigrationCommand::Delete { table_id: coll_id });
                }
            }
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
            ast::MigrationAction::RemoveField { field } => {
                let field_id = self.ird.field(collection_id, &field).id;
                self.ird.colls[collection_id].retire_field(&field_id);
                CompleteMigrationAction::RemoveField { field: field_id }
            }
            ast::MigrationAction::AddField { field, ty, init } => {
                let lowered_ty = self.lower_type(ty);
                self.ird
                    .add_field(collection_id, field.clone(), lowered_ty.clone());
                CompleteMigrationAction::AddField {
                    field: self.ird.field(collection_id, &field).id,
                    ty: lowered_ty.clone(),
                    init: self.lower_func(collection_type, lowered_ty, &init),
                }
            }
            ast::MigrationAction::ChangeField {
                field,
                new_ty,
                new_init,
            } => {
                let lowered_ty = self.lower_type(new_ty);
                let field_id = self.ird.field(collection_id, &field).id;
                let lowered_init = self.lower_func(collection_type, lowered_ty.clone(), &new_init);
                self.ird.change_def_type(field_id, lowered_ty.clone());
                CompleteMigrationAction::ChangeField {
                    field: field_id,
                    new_ty: lowered_ty,
                    new_init: lowered_init,
                }
            }
            ast::MigrationAction::RenameField {
                old_field,
                new_field,
            } => {
                let field_id = self.ird.field(collection_id, &old_field).id;
                self.ird.colls[collection_id].retire_field(&field_id);
                let field_ty = self.ird.def_type(field_id.clone()).clone();
                self.ird
                    .add_field(collection_id, new_field.clone(), field_ty);

                CompleteMigrationAction::RenameField {
                    field_id: field_id,
                    old_name: old_field,
                    new_name: new_field,
                }
            }
            ast::MigrationAction::ForEach { param, body } => {
                let param_id = self.ird.create_def(&param, collection_type.clone());
                let old_mapping = self.def_map.insert(param.clone(), param_id);
                let lowered_action = CompleteMigrationAction::ForEach {
                    param: param_id,
                    body: self.lower_object_command(body),
                };
                match old_mapping {
                    Some(did) => {
                        self.def_map.insert(param.clone(), did);
                    }
                    None => {
                        self.def_map
                            .remove(&param)
                            .expect("This should be unreachable");
                    }
                }
                lowered_action
            }
        }
    }
    fn lower_object_command(&mut self, body: ast::ObjectCommand) -> CompleteObjectCommand {
        match body {
            ast::ObjectCommand::CreateObject {
                collection,
                value: body,
            } => {
                let value = self.lower_expr(&body);
                let coll_id = self
                    .ird
                    .active_collections()
                    .find(|c| c.name.eq_str(&collection))
                    .expect(&format!("Unknown collection {}", collection))
                    .id;
                self.typecheck_expr(value, Type::Collection(coll_id));
                CompleteObjectCommand::CreateObject {
                    collection: coll_id,
                    value: value,
                }
            }
            ast::ObjectCommand::DeleteObject {
                collection,
                id_expr,
            } => {
                let id_expr_id = self.lower_expr(&id_expr);
                let coll_id = self
                    .ird
                    .active_collections()
                    .find(|c| c.name.eq_str(&collection))
                    .expect(&format!("Unknown collection {}", collection))
                    .id;
                self.typecheck_expr(id_expr_id, Type::Id(coll_id));
                CompleteObjectCommand::DeleteObject {
                    collection: coll_id,
                    id_expr: id_expr_id,
                }
            }
        }
    }
    fn lower_func(
        &mut self,
        param_type: Type,
        expected_return_type: Type,
        pf: &ast::Func,
    ) -> Lambda {
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
    fn infer_expr_type(&self, expr_id: Id<Expr>) -> Type {
        let expr = &self.ird[expr_id];
        match &expr.kind {
            ExprKind::IntConst(_) => Type::Prim(Prim::I64),
            ExprKind::FloatConst(_) => Type::Prim(Prim::F64),
            ExprKind::StringConst(_) => Type::Prim(Prim::String),
            ExprKind::Path(_collection, _obj, field) => self.ird.def_type(*field).clone(),
            ExprKind::Var(m) => self.ird.def_type(*m).clone(),
            ExprKind::Object(collection, _fields, _t_obj) => Type::Collection(*collection),
            ExprKind::AddI(_, _) => Type::Prim(Prim::I64),
            ExprKind::AddF(_, _) => Type::Prim(Prim::F64),
            ExprKind::SubI(_, _) => Type::Prim(Prim::I64),
            ExprKind::SubF(_, _) => Type::Prim(Prim::F64),
            ExprKind::AppendS(_, _) => Type::Prim(Prim::String),
            ExprKind::AppendL(ty, _, _) => Type::List(Box::new(ty.clone())),
            ExprKind::IntToFloat(_) => Type::Prim(Prim::F64),
            ExprKind::List(exprs) => {
                let expr_type = self.infer_expr_type(exprs[0]);
                let mut result_type = expr_type.clone();
                for expr in exprs.into_iter() {
                    if self.infer_expr_type(*expr) != expr_type {
                        result_type = Type::Any;
                    }
                }
                Type::List(Box::new(result_type))
            },
            ExprKind::Or(_, _) => unimplemented!("Cannot yet typecheck OR's"),
        }
    }
    fn typecheck_expr(&self, expr_id: Id<Expr>, expected_type: Type) {
        let inferred_type = self.infer_expr_type(expr_id);
        assert!(
            is_subtype(&inferred_type, &expected_type),
            "Static type error: expected {:?}, found {:?}",
            expected_type,
            inferred_type
        );
    }
    fn lower_type(&mut self, ty: ast::FieldType) -> Type {
        match ty {
            ast::FieldType::String => Type::Prim(Prim::String),
            ast::FieldType::I64 => Type::Prim(Prim::I64),
            ast::FieldType::F64 => Type::Prim(Prim::F64),
            ast::FieldType::Id(s) => {
                let (id, _coll_typ) = self.resolve_collection(&s);
                Type::Id(id)
            }
            ast::FieldType::List(s) => Type::List(Box::new(self.lower_type(*s))),
        }
    }
}

fn is_subtype(t1: &Type, t2: &Type) -> bool {
    match t2 {
        _ if t1 == t2 => true,
        Type::Any => true,
        Type::IdAny => match t1 {
            Type::Id(_) => true,
            _ => false,
        },
        Type::List(inner_type2) => match t1 {
            Type::List(inner_type1) => is_subtype(inner_type1, inner_type2),
            Type::Id(coll) => match **inner_type2 {
                Type::Id(coll2) => *coll == coll2,
                Type::IdAny => true,
                _ => false,
            }
            _ => false,
        },
        _ => false
    }
}
