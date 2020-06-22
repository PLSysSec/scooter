use super::{
    expr::{extract_func, extract_ir_expr, DefMap, ExprType, Func, IRExpr, Var},
    policy::{
        extract_partial_schema_policy, extract_policy, Policy, SchemaPolicy,
    },
    schema::{extract_type, Collection, Field, Schema},
    Ident,
};
use crate::ast;

/// Because a `MigrationCommand` can:
///     - contain an expression
///     - modify the schema
///     - modify the policy
///     - reference the policy
/// Each command can only be lowered after the effects of the command on both
/// the schema and the policy have been determined.

#[derive(Debug)]
pub enum MigrationCommand {
    RemoveField {
        coll: Ident<Collection>,
        field: Ident<Field>,
    },
    AddField {
        coll: Ident<Collection>,
        field: Ident<Field>,
        ty: ExprType,
        init: Func,
    },
    ChangeField {
        coll: Ident<Collection>,
        field: Ident<Field>,
        new_ty: ExprType,
    },
    RenameField {
        coll: Ident<Collection>,
        field: Ident<Field>,
        new_name: Ident<Field>,
    },
    LoosenFieldPolicy {
        coll: Ident<Collection>,
        field: Ident<Field>,
        kind: FieldPolicyKind,
        new_policy: Policy,
    },
    TightenFieldPolicy {
        coll: Ident<Collection>,
        field: Ident<Field>,
        kind: FieldPolicyKind,
        new_policy: Policy,
    },
    LoosenCollectionPolicy {
        coll: Ident<Collection>,
        kind: CollectionPolicyKind,
        new_policy: Policy,
    },
    TightenCollectionPolicy {
        coll: Ident<Collection>,
        kind: CollectionPolicyKind,
        new_policy: Policy,
    },
    DataCommand(DataCommand),
    Create {
        pol: SchemaPolicy,
    },
    Delete {
        name: Ident<Collection>,
    },
}

#[derive(Debug)]
pub enum FieldPolicyKind {
    Read,
    Edit,
}

#[derive(Debug)]
pub enum CollectionPolicyKind {
    Create,
    Delete,
}

#[derive(Debug)]
pub enum DataCommand {
    ForEach {
        param: Ident<Var>,
        coll: Ident<Collection>,
        body: Box<DataCommand>,
    },
    CreateObject {
        collection: Ident<Collection>,
        value: IRExpr,
    },
    DeleteObject {
        collection: Ident<Collection>,
        id_expr: IRExpr,
    },
}

/// Interprets the affect of a migration command on a schema
/// This is a useful primitive for any analysis being done on migrations
/// and it's important that everyone agrees on what those effects are,
/// so the logic is centralized here.
pub fn interpret_command(schema: &Schema, mc: &MigrationCommand) -> Schema {
    let mut output = schema.clone();
    match mc {
        MigrationCommand::RemoveField { coll, field } => {
            output[coll].fields = output[coll]
                .fields
                .iter()
                .filter(|f| f.name != *field)
                .cloned()
                .collect();
            output
        }
        MigrationCommand::AddField {
            coll, field, ty, ..
        } => {
            output[coll].fields.push(Field {
                name: field.clone(),
                typ: ty.clone(),
            });
            output
        }
        MigrationCommand::ChangeField {
            coll,
            field,
            new_ty,
        } => {
            let old_field = output[coll]
                .fields
                .iter_mut()
                .find(|f| f.name != *field)
                .unwrap();
            old_field.typ = new_ty.clone();
            output
        }
        MigrationCommand::RenameField {
            coll,
            field,
            new_name,
        } => {
            let old_field = output[coll]
                .fields
                .iter_mut()
                .find(|f| f.name != *field)
                .unwrap();
            old_field.name = new_name.clone();
            output
        }
        MigrationCommand::Create { pol } => {
            output.collections.push(pol.schema.collections[0].clone());
            output
        }
        MigrationCommand::Delete { name } => {
            output.collections = output
                .collections
                .into_iter()
                .filter(|c| c.name == *name)
                .collect();
            output
        }
        MigrationCommand::LoosenFieldPolicy { .. }
        | MigrationCommand::TightenFieldPolicy { .. }
        | MigrationCommand::LoosenCollectionPolicy { .. }
        | MigrationCommand::TightenCollectionPolicy { .. }
        | MigrationCommand::DataCommand(_) => output,
    }
}

/// Converts an ast to the lowered representation where Idents and Types (among other things) are resolved.
pub fn extract_migration_command(
    schema: &Schema,
    cmd: ast::MigrationCommand,
) -> MigrationCommand {
    match cmd {
        ast::MigrationCommand::CollAction { table, action } => {
            let coll = schema.find_collection(&table).expect(&format!(
                "Unable to delete collection `{}` because it does not exist.",
                &table
            ));

            match action {
                ast::MigrationAction::RemoveField { field } => {
                    let field = coll.find_field(&field).expect(&format!(
                        "Unable to delete field {}::{} because it does not exist",
                        &table, &field
                    ));

                    MigrationCommand::RemoveField {
                        coll: coll.name.clone(),
                        field: field.name.clone(),
                    }
                }
                ast::MigrationAction::AddField { field, ty, init } => {
                    let field = Ident::new(field);
                    let ty = extract_type(schema, &ty);
                    let init = extract_func(
                        schema,
                        ExprType::Object(coll.name.clone()),
                        &ty,
                        &init,
                    );

                    MigrationCommand::AddField {
                        coll: coll.name.clone(),
                        field,
                        ty,
                        init,
                    }
                }
                ast::MigrationAction::ChangeField { field, new_ty } => {
                    let field = coll.find_field(&field).expect(&format!(
                        "Unable to change field {}::{} because it does not exist",
                        &table, &field
                    ));
                    let new_ty = extract_type(schema, &new_ty);

                    MigrationCommand::ChangeField {
                        coll: coll.name.clone(),
                        field: field.name.clone(),
                        new_ty,
                    }
                }
                ast::MigrationAction::RenameField {
                    old_field,
                    new_field,
                } => {
                    let field = coll.find_field(&old_field).expect(&format!(
                        "Unable to rename field {}::{} because it does not exist",
                        &table, &new_field
                    ));
                    MigrationCommand::RenameField {
                        coll: coll.name.clone(),
                        field: field.name.clone(),
                        new_name: Ident::new(new_field),
                    }
                }
                ast::MigrationAction::LoosenFieldPolicy { field, kind, pol } => {
                    let field = coll.find_field(&field).expect(&format!(
                        "Unable to loosen field policy {}::{} because it does not exist",
                        &table, &field
                    ));
                    let kind = extract_field_policy_kind(&kind);
                    let pol = extract_policy(schema, &coll.name, &pol);

                    MigrationCommand::LoosenFieldPolicy {
                        coll: coll.name.clone(),
                        field: field.name.clone(),
                        kind,
                        new_policy: pol,
                    }
                }
                ast::MigrationAction::TightenFieldPolicy { field, kind, pol } => {
                    let field = coll.find_field(&field).expect(&format!(
                        "Unable to loosen field policy {}::{} because it does not exist",
                        &table, &field
                    ));
                    let kind = extract_field_policy_kind(&kind);
                    let pol = extract_policy(schema, &coll.name, &pol);

                    MigrationCommand::LoosenFieldPolicy {
                        coll: coll.name.clone(),
                        field: field.name.clone(),
                        kind,
                        new_policy: pol,
                    }
                }
                ast::MigrationAction::LoosenCollectionPolicy { kind, pol } => {
                    let kind = extract_coll_policy_kind(&kind);
                    let pol = extract_policy(schema, &coll.name, &pol);

                    MigrationCommand::LoosenCollectionPolicy {
                        coll: coll.name.clone(),
                        kind,
                        new_policy: pol,
                    }
                }
                ast::MigrationAction::TightenCollectionPolicy { kind, pol } => {
                    let kind = extract_coll_policy_kind(&kind);
                    let pol = extract_policy(schema, &coll.name, &pol);

                    MigrationCommand::TightenCollectionPolicy {
                        coll: coll.name.clone(),
                        kind,
                        new_policy: pol,
                    }
                }
            }
        }
        ast::MigrationCommand::Create { collection } => {
            let pol = extract_partial_schema_policy(&ast::GlobalPolicy {
                collections: vec![collection],
            });

            MigrationCommand::Create { pol }
        }
        ast::MigrationCommand::Delete { table_name } => {
            let coll = schema.find_collection(&table_name).expect(&format!(
                "Unable to delete collection `{}` because it does not exist.",
                table_name
            ));

            MigrationCommand::Delete {
                name: coll.name.clone(),
            }
        }

        ast::MigrationCommand::ObjectCommand(oc) => {
            MigrationCommand::DataCommand(extract_data_command(schema, DefMap::empty(), oc))
        }
    }
}

fn extract_data_command(schema: &Schema, def_map: DefMap, oc: ast::ObjectCommand) -> DataCommand {
    match oc {
        ast::ObjectCommand::ForEach {
            collection,
            param,
            body,
        } => {
            let coll = schema.find_collection(&collection).expect(&format!(
                "Unable to loop over collection `{}` because it does not exist.",
                &collection
            ));
            let param_id = Ident::new(&param);
            let ty = ExprType::id(coll.name.clone());
            DataCommand::ForEach {
                coll: coll.name.clone(),
                param: param_id.clone(),
                body: Box::new(extract_data_command(
                    schema,
                    def_map.extend(&param, param_id, ty),
                    *body,
                )),
            }
        }
        ast::ObjectCommand::CreateObject { collection, value } => {
            let coll = schema.find_collection(&collection).expect(&format!(
                "Unable to create `{}` because it does not exist.",
                &collection
            ));
            let value = extract_ir_expr(schema, def_map.clone(), &value);
            if value.type_of() != ExprType::Object(coll.name.clone()) {
                panic!(
                    "Attempting to create an object for {} but found type {:?}",
                    &coll.name.orig_name,
                    value.type_of()
                );
            }

            DataCommand::CreateObject {
                collection: coll.name.clone(),
                value: *value,
            }
        }
        ast::ObjectCommand::DeleteObject {
            collection,
            id_expr,
        } => {
            let coll = schema.find_collection(&collection).expect(&format!(
                "Unable to create `{}` because it does not exist.",
                &collection
            ));
            let value = extract_ir_expr(schema, def_map.clone(), &id_expr);
            if value.type_of() != ExprType::id(coll.name.clone()) {
                panic!(
                    "Attempting to delete an object for {} but found type {:?}",
                    &coll.name.orig_name,
                    value.type_of()
                );
            }

            DataCommand::DeleteObject {
                collection: coll.name.clone(),
                id_expr: *value,
            }
        }
    }
}

fn extract_coll_policy_kind(kind: &str) -> CollectionPolicyKind {
    match kind {
        "create" => CollectionPolicyKind::Create,
        "delete" => CollectionPolicyKind::Delete,
        _ => panic!("`{}` is not a valid permission on collections.", kind),
    }
}

fn extract_field_policy_kind(kind: &str) -> FieldPolicyKind {
    match kind {
        "edit" => FieldPolicyKind::Edit,
        "read" => FieldPolicyKind::Read,
        _ => panic!("`{}` is not a valid permission on fields.", kind),
    }
}
