
use super::{Ident, schema::{Collection, Schema, Field, DBType, extract_type}, expr::{Var, IRExpr, ExprType, extract_func, Func, DefMap, extract_ir_expr}, policy::{SchemaPolicy, CollectionPolicy, Policy, extract_policy, extract_schema_policy}};
use crate::ast;

/// MigrationScript captures each step of a migration.
/// Because a `MigrationCommand` can both:
///     - contain an expression
///     - modify the schema
/// Each step of the migration must be paired with the schema
/// available at that point in time.
///
/// This means that lowering a sequence of migration commands,
/// requires interpreting the affects of the migration on the schema.
pub struct MigrationScript {
    commands: Vec<(Schema, MigrationCommand)>,
    final_schema: Schema,
}

#[derive(Debug)]
pub enum MigrationCommand {
    RemoveField {
        coll: Ident<Collection>,
        field: Ident<Field>,
    },
    AddField {
        coll: Ident<Collection>,
        field: Ident<Field>,
        ty: DBType,
        init: Func,
    },
    ChangeField {
        coll: Ident<Collection>,
        field: Ident<Field>,
        new_ty: DBType,
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

pub fn extract_migration_script(schema: &Schema, migration: ast::Migration) -> MigrationScript {
    let mut curr_schema = schema.clone();
    let mut commands = vec![];
    for mc in migration.0.into_iter() {
        let lowered = extract_migration_command(&curr_schema, mc);
        let new_schema = interpret_command(&curr_schema, &lowered);
        
        commands.push((curr_schema, lowered));
        curr_schema = new_schema;
    }

    MigrationScript {
        commands,
        final_schema: curr_schema
    }
}

fn interpret_command(curr_schema: &Schema, lowered: &MigrationCommand) -> Schema {
    todo!()
}

fn extract_migration_command(schema: &Schema, cmd: ast::MigrationCommand) -> MigrationCommand {
    match cmd {
        ast::MigrationCommand::CollAction { table, action } => {
            let coll= schema.find_collection(&table).expect(&format!("Unable to delete collection `{}` because it does not exist.", &table));

            match action {
                ast::MigrationAction::RemoveField { field } => {
                    let field = coll.find_field(&field).expect(&format!("Unable to delete field {}::{} because it does not exist", &table, &field));

                    MigrationCommand::RemoveField {
                        coll: coll.name.clone(),
                        field: field.name.clone(),
                    }
                }
                ast::MigrationAction::AddField { field, ty, init } => {
                    let field = Ident::new(field);
                    let ty = extract_type(schema, &ty);
                    let init = extract_func(schema, ExprType::DBType(ty.clone()), &init);

                    MigrationCommand::AddField {
                        coll: coll.name.clone(),
                        field,
                        ty,
                        init,
                    }
                }
                ast::MigrationAction::ChangeField { field, new_ty} => {
                    let field = coll.find_field(&field).expect(&format!("Unable to change field {}::{} because it does not exist", &table, &field));
                    let new_ty = extract_type(schema, &new_ty);

                    MigrationCommand::ChangeField {
                        coll: coll.name.clone(),
                        field: field.name.clone(),
                        new_ty,
                    }
                    
                }
                ast::MigrationAction::RenameField { old_field, new_field } => {
                    let field = coll.find_field(&old_field).expect(&format!("Unable to rename field {}::{} because it does not exist", &table, &new_field));
                    MigrationCommand::RenameField {
                        coll: coll.name.clone(),
                        field: field.name.clone(), 
                        new_name: Ident::new(new_field),
                    }
                }
                ast::MigrationAction::LoosenFieldPolicy { field, kind, pol} => {
                    let field = coll.find_field(&field).expect(&format!("Unable to loosen field policy {}::{} because it does not exist", &table, &field));
                    let kind = extract_field_policy_kind(&kind);
                    let pol = extract_policy(schema, coll.name.clone(), &pol);

                    MigrationCommand::LoosenFieldPolicy {
                        coll: coll.name.clone(),
                        field: field.name.clone(),
                        kind,
                        new_policy: pol,
                    }
                }
                ast::MigrationAction::TightenFieldPolicy { field, kind, pol} => {
                    let field = coll.find_field(&field).expect(&format!("Unable to loosen field policy {}::{} because it does not exist", &table, &field));
                    let kind = extract_field_policy_kind(&kind);
                    let pol = extract_policy(schema, coll.name.clone(), &pol);

                    MigrationCommand::LoosenFieldPolicy {
                        coll: coll.name.clone(),
                        field: field.name.clone(),
                        kind,
                        new_policy: pol,
                    }
                }
                ast::MigrationAction::LoosenCollectionPolicy { kind, pol} => {
                    let kind = extract_coll_policy_kind(&kind);
                    let pol = extract_policy(schema, coll.name.clone(), &pol);

                    MigrationCommand::LoosenCollectionPolicy {
                        coll: coll.name.clone(),
                        kind,
                        new_policy: pol,
                    }
                }
                ast::MigrationAction::TightenCollectionPolicy { kind, pol} => {
                    let kind = extract_coll_policy_kind(&kind);
                    let pol = extract_policy(schema, coll.name.clone(), &pol);

                    MigrationCommand::TightenCollectionPolicy {
                        coll: coll.name.clone(),
                        kind,
                        new_policy: pol,
                    }
                }
            }
        },
        ast::MigrationCommand::Create { collection } => {
            let pol = extract_schema_policy(&ast::GlobalPolicy {
                collections: vec![collection],
            });

            MigrationCommand::Create { pol }
        },
        ast::MigrationCommand::Delete { table_name } => {
            let coll= schema.find_collection(&table_name).expect(&format!("Unable to delete collection `{}` because it does not exist.", table_name));

            MigrationCommand::Delete {
                name: coll.name.clone(),
            }
        },

        ast::MigrationCommand::ObjectCommand(oc) => {
            MigrationCommand::DataCommand(extract_data_command(schema, DefMap::empty(), oc))
        }
    }
}

fn extract_data_command(schema: &Schema, def_map: DefMap, oc: ast::ObjectCommand) -> DataCommand {
    match oc {
        ast::ObjectCommand::ForEach { collection, param, body } => {
            let coll= schema.find_collection(&collection).expect(&format!("Unable to loop over collection `{}` because it does not exist.", &collection));
            let param_id = Ident::new(&param);
            let ty = ExprType::id(coll.name.clone());
            DataCommand::ForEach {
                coll: coll.name.clone(),
                param: param_id.clone(),
                body: Box::new(extract_data_command(schema, def_map.extend(&param, param_id, ty), *body))
            }
        }
        ast::ObjectCommand::CreateObject { collection, value } => {
            let coll= schema.find_collection(&collection).expect(&format!("Unable to create `{}` because it does not exist.", &collection));
            let value = extract_ir_expr(schema, def_map.clone(), &value);
            if value.type_of() != ExprType::Object(coll.name.clone()) {
                panic!("Attempting to create an object for {} but found type {:?}", &coll.name.orig_name, value.type_of());
            }

            DataCommand::CreateObject {
                collection: coll.name.clone(),
                value: *value
            }
        }
        ast::ObjectCommand::DeleteObject { collection, id_expr } => {
            let coll= schema.find_collection(&collection).expect(&format!("Unable to create `{}` because it does not exist.", &collection));
            let value = extract_ir_expr(schema, def_map.clone(), &id_expr);
            if value.type_of() != ExprType::id(coll.name.clone()) {
                panic!("Attempting to delete an object for {} but found type {:?}", &coll.name.orig_name, value.type_of());
            }

            DataCommand::DeleteObject {
                collection: coll.name.clone(),
                id_expr: *value
            }
        }
    }
}

fn extract_coll_policy_kind(kind: &str) -> CollectionPolicyKind {
    match kind {
        "create" => CollectionPolicyKind::Create,
        "delete" => CollectionPolicyKind::Delete,
        _ => panic!("`{}` is not a valid permission on collections.", kind)
    }
}

fn extract_field_policy_kind(kind: &str) -> FieldPolicyKind {
    match kind {
        "edit" => FieldPolicyKind::Edit,
        "read" => FieldPolicyKind::Read,
        _ => panic!("`{}` is not a valid permission on fields.", kind)
    }
}
