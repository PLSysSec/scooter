use crate::smt::{is_as_strict, Equiv};
use policy_lang::ir::expr::{expr_to_string, ExprType, Func, IRExpr};
use policy_lang::ir::migration::{
    extract_migration_steps, CollectionPolicyKind, DataCommand, FieldPolicyKind, MigrationCommand,
};
use policy_lang::ir::policy::{
    extract_schema_policy, CollectionPolicy, FieldPolicy, Policy, SchemaPolicy,
};
use policy_lang::ir::schema::{Collection, Field, Schema};
use policy_lang::ir::*;
use policy_lang::{parse_migration, parse_policy};

use std::collections::HashMap;
use std::error::Error;
use std::fs::read_to_string;
use std::path::Path;

/// Take two filenames, a policy and a migration, and produce a new
/// policy as a string, by reading those files.
pub fn migrate_policy_from_files(
    policy_path: impl AsRef<Path>,
    migration_path: impl AsRef<Path>,
) -> Result<String, Box<dyn Error>> {
    let policy_path_path = policy_path.as_ref();
    let migration_path_path = migration_path.as_ref();
    migrate_policy(
        &read_to_string(policy_path_path.clone()).expect(&format!(
            "Couldn't read policy file {}",
            policy_path_path.to_str().unwrap()
        )),
        &read_to_string(migration_path_path.clone()).expect(&format!(
            "Couldn't read migration file {}",
            migration_path_path.to_str().unwrap()
        )),
    )
}

/// Take the text of a policy and a migration, and produce a new
/// policy, that doesn't leak any information from the old policy, but
/// is valid post-migration.
pub fn migrate_policy(policy_text: &str, migration_text: &str) -> Result<String, Box<dyn Error>> {
    let parsed_policy = parse_policy(policy_text)?;
    let initial_schema_policy = extract_schema_policy(&parsed_policy)?;
    let parsed_migration = parse_migration(migration_text)?;
    let migration_steps = extract_migration_steps(&initial_schema_policy.schema, parsed_migration)?;
    let resulting_policy = interpret_migration_on_policy(initial_schema_policy, migration_steps)?;
    Ok(policy_to_string(resulting_policy))
}

fn policy_to_string(policy: SchemaPolicy) -> String {
    let mut result = "".to_string();
    for sp in policy.schema.static_principals.iter() {
        result += "@static-principal\n";
        result += &sp.orig_name;
        result += "\n";
    }
    for coll in policy.schema.collections.iter() {
        let coll_policy = policy.collection_policies[&coll.name].clone();
        if policy.schema.dynamic_principals.contains(&coll.name) {
            result += &format!("@principal\n")
        }
        result += &format!("{} {{\n", coll.name.orig_name);
        result += &format!(
            "    create: {},\n",
            policy_value_to_string(coll_policy.create)
        );
        result += &format!(
            "    delete: {},\n",
            policy_value_to_string(coll_policy.delete)
        );
        result += "\n";
        for field in policy.schema[&coll.name].fields() {
            if field.name.orig_name == "id" {
                continue;
            }
            result += &format!(
                "    {} : {} {{\n",
                field.name.orig_name,
                type_to_string(field.typ.clone())
            );
            let field_policy = policy.field_policies[&field.name].clone();
            result += &format!(
                "        read: {},\n",
                policy_value_to_string(field_policy.read)
            );
            result += &format!(
                "        write: {},\n",
                policy_value_to_string(field_policy.edit)
            );
            result += "    },\n";
        }
        result += "}\n";
    }
    result
}

fn policy_value_to_string(policy_value: Policy) -> String {
    match policy_value {
        Policy::Anyone => "public".to_string(),
        Policy::None => "none".to_string(),
        Policy::Func(l) => format!("{} -> {}", l.param.orig_name, expr_to_string(l.body)),
    }
}

fn type_to_string(ty: ExprType) -> String {
    match ty {
        ExprType::Object(_id) => panic!("Can't have a collection type in a policy!"),
        _ => format!("{}", ty),
    }
}

fn interpret_migration_on_policy(
    initial_sp: SchemaPolicy,
    migration_steps: Vec<(Schema, MigrationCommand)>,
) -> Result<SchemaPolicy, String> {
    let final_schema = match migration_steps.last() {
        None => &initial_sp.schema,
        Some((schema, _cmd)) => schema,
    };
    // The policy state we'll return
    let mut result_policy = SchemaPolicy {
        schema: final_schema.clone(),
        collection_policies: initial_sp.collection_policies.clone(),
        field_policies: initial_sp.field_policies.clone(),
    };

    // Keep track of fields that are removed, for invalidating
    // functions that refer to them.
    let mut deleted_fields = Vec::new();
    // Keep track of fields that are renamed, for repairing
    // expressions that referenced the old name.
    let mut renamed_fields: HashMap<Ident<Field>, Ident<Field>> = HashMap::new();
    // Keep track of field definitions that will be useful during policy verification
    let mut equivs = Vec::new();

    // Go over the migration commands (consuming them)
    for (schema, cmd) in migration_steps.into_iter() {
        let cur_schema_policy = SchemaPolicy {
            schema: schema.clone(),
            collection_policies: result_policy.collection_policies.clone(),
            field_policies: result_policy.field_policies.clone(),
        };

        match cmd {
            // For adding fields, just add new policies based on
            // the initializer function
            MigrationCommand::AddField {
                coll,
                field,
                ty: _,
                init,
                pol,
            } => {
                let inferred_policy =
                    get_policy_from_initializer(&cur_schema_policy, field.clone(), init.clone());
                match is_as_strict(&schema, &equivs, &coll, &inferred_policy.read, &pol.read) {
                    Result::Ok(_) => (),
                    Result::Err(e) => {
                        return Err(format!(
                            "Cannot determine that the given field policy \
                                            is tight enough for the values that flow into it.\n \
                                            Counterexample: {}",
                            e
                        ))
                    }
                }
                equivs.push(Equiv(field.clone(), init));
                result_policy.add_field_policy(field, pol)
            }
            // For removing fields, remove the policy data, and
            // add it to a list of deleted fields for invalidating
            // expressions later.
            MigrationCommand::RemoveField { coll: _, field } => {
                result_policy.remove_field_policy(field.clone());
                deleted_fields.push(field.clone());
                if let Some((old_field, _new_field)) =
                    renamed_fields.iter().find(|(_k, v)| **v == field)
                {
                    let old_field_id = old_field.clone();
                    deleted_fields.push(old_field.clone());
                    renamed_fields.remove(&old_field_id);
                }
            }
            MigrationCommand::ChangeField {
                coll: _,
                field,
                new_ty: _,
                new_init,
            } => {
                equivs = vec![];

                result_policy.remove_field_policy(field.clone());
                result_policy.add_field_policy(
                    field.clone(),
                    get_policy_from_initializer(&cur_schema_policy, field.clone(), new_init),
                );
                // Anything that referred to it's old value as a
                // policy isn't going to work anymore.
                deleted_fields.push(field);
            }
            MigrationCommand::RenameField {
                coll: _,
                field: old_field_id,
                new_name: new_field_id,
            } => {
                result_policy.add_field_policy(
                    new_field_id.clone(),
                    result_policy.field_policies[&old_field_id].clone(),
                );
                renamed_fields.insert(old_field_id, new_field_id);
            }
            MigrationCommand::WeakenFieldPolicy {
                coll: _,
                field,
                kind,
                new_policy,
            } => {
                let old_policy = result_policy.remove_field_policy(field.clone());
                result_policy
                    .add_field_policy(field, field_policy_lens_set(old_policy, kind, new_policy));
            }
            MigrationCommand::UpdateFieldPolicy {
                coll,
                field,
                kind,
                new_policy,
            } => {
                let old_policy = result_policy.field_policies[&field].clone();
                let res = match kind {
                    FieldPolicyKind::Read => {
                        is_as_strict(&schema, &equivs, &coll, &old_policy.read, &new_policy)
                    }
                    FieldPolicyKind::Edit => {
                        is_as_strict(&schema, &equivs, &coll, &old_policy.edit, &new_policy)
                    }
                };
                if let Err(model) = res {
                    return Err(
                        format!("Migration unsafe! Cannot determine that the new {} policy for {} is stricter than the old one.\nCOUNTEREXAMPLE:\n{}", kind, &field.orig_name, model)
                    );
                }
                let new_policy = field_policy_lens_set(old_policy.clone(), kind, new_policy);
                result_policy.remove_field_policy(field.clone());
                result_policy.add_field_policy(field, new_policy);
            }
            MigrationCommand::WeakenPolicy {
                coll,
                kind,
                new_policy,
            } => {
                let old_policy = result_policy.remove_collection_policy(coll.clone());
                result_policy.add_collection_policy(
                    coll,
                    coll_policy_lens_set(old_policy, kind, new_policy),
                );
            }
            MigrationCommand::UpdatePolicy {
                coll,
                kind,
                new_policy,
            } => {
                let old_policy = result_policy.collection_policies[&coll].clone();
                match match kind {
                    // The "schema" here is actually the schema
                    // afterwards, which would be a problem except
                    // this command doesb't modify the schema.
                    CollectionPolicyKind::Create => {
                        is_as_strict(&schema, &equivs, &coll, &old_policy.create, &new_policy)
                    }
                    CollectionPolicyKind::Delete => {
                        is_as_strict(&schema, &equivs, &coll, &old_policy.delete, &new_policy)
                    }
                } {
                    Result::Ok(_) => (),
                    Result::Err(model) =>
                        return Err(
                            format!("Migration unsafe! Cannot determine that the new collection policy for {} is stricter than the old one.\nCOUNTEREXAMPLE:\n{}", &coll.orig_name, model)
                        )
                }
                result_policy.remove_collection_policy(coll.clone());
                let new_policy = coll_policy_lens_set(old_policy.clone(), kind, new_policy);
                result_policy.add_collection_policy(coll, new_policy);
            }
            MigrationCommand::DataCommand(DataCommand::ForEach { .. }) => {
                return Err("We don't know how to process foreaches on policies yet".to_string())
            }
            MigrationCommand::DataCommand(DataCommand::CreateObject { .. }) => {
                return Err(
                    "We don't know how to process create objects on policies yet".to_string(),
                )
            }
            MigrationCommand::DataCommand(DataCommand::DeleteObject { .. }) => {
                return Err(
                    "We don't know how to process delete objects on policies yet".to_string(),
                )
            }
            // For creating collections, just create a new create and
            // delete policies.
            MigrationCommand::Create { pol } => {
                // assert!(pol.schema.collections.len() == 1);
                // assert!(pol.collection_policies.len() == 1);
                for collection in pol.schema.collections.iter() {
                    let coll_pol = pol.collection_policies[&collection.name].clone();
                    result_policy.add_collection_policy(collection.name.clone(), coll_pol);
                    for field in collection.fields() {
                        if field.is_id() {
                            continue;
                        }
                        let field_pol = pol.field_policies[&field.name].clone();
                        result_policy.add_field_policy(field.name.clone(), field_pol);
                    }
                }
            }
            // For deleting collections, remove the policy data.
            MigrationCommand::Delete { name } => {
                result_policy.remove_collection_policy(name);
            }
            // The adding of static principals is purely a schema
            // thing, so it's handled before this step.
            MigrationCommand::AddStaticPrincipal { name: _ } => (),
            MigrationCommand::AddPrincipal { table_name: _ } => {}
        }
    }

    remove_invalidated_policies(deleted_fields, &mut result_policy);

    let coll_names: Vec<Ident<Collection>> = result_policy
        .schema
        .collections
        .iter()
        .map(|coll| coll.name.clone())
        .collect();

    for coll_name in coll_names.into_iter() {
        let coll_pol = result_policy
            .collection_policies
            .get_mut(&coll_name)
            .unwrap();
        if let Policy::Func(Func {
            param: p,
            param_type: ty,
            return_type: rty,
            body,
        }) = &coll_pol.create
        {
            coll_pol.create = Policy::Func(Func {
                param: p.clone(),
                param_type: ty.clone(),
                return_type: rty.clone(),
                body: sub_expr(body, &renamed_fields),
            });
        }
        if let Policy::Func(Func {
            param: p,
            param_type: ty,
            return_type: rty,
            body,
        }) = &coll_pol.delete
        {
            coll_pol.delete = Policy::Func(Func {
                param: p.clone(),
                param_type: ty.clone(),
                return_type: rty.clone(),
                body: sub_expr(&body, &renamed_fields),
            });
        }
    }

    let field_names: Vec<Ident<Field>> = result_policy
        .schema
        .collections
        .iter()
        .flat_map(|coll| {
            coll.fields()
                .filter(|field| field.name.orig_name != "id")
                .map(|field| field.name.clone())
        })
        .collect();

    for field_name in field_names.into_iter() {
        let field_pol = result_policy.field_policies.get_mut(&field_name).unwrap();
        if let Policy::Func(Func {
            param: p,
            param_type: ty,
            return_type: rty,
            body,
        }) = &field_pol.read
        {
            field_pol.read = Policy::Func(Func {
                param: p.clone(),
                param_type: ty.clone(),
                return_type: rty.clone(),
                body: sub_expr(body, &renamed_fields),
            });
        }
        if let Policy::Func(Func {
            param: p,
            param_type: ty,
            return_type: rty,
            body,
        }) = &field_pol.edit
        {
            field_pol.edit = Policy::Func(Func {
                param: p.clone(),
                param_type: ty.clone(),
                return_type: rty.clone(),
                body: sub_expr(body, &renamed_fields),
            });
        }
    }

    Ok(result_policy)
}

fn field_policy_lens_set(p: FieldPolicy, k: FieldPolicyKind, policy_val: Policy) -> FieldPolicy {
    match k {
        FieldPolicyKind::Read => FieldPolicy {
            read: policy_val,
            edit: p.edit,
        },
        FieldPolicyKind::Edit => FieldPolicy {
            read: p.read,
            edit: policy_val,
        },
    }
}
fn coll_policy_lens_set(
    p: CollectionPolicy,
    k: CollectionPolicyKind,
    policy_val: Policy,
) -> CollectionPolicy {
    match k {
        CollectionPolicyKind::Create => CollectionPolicy {
            create: policy_val,
            delete: p.delete,
        },
        CollectionPolicyKind::Delete => CollectionPolicy {
            create: p.create,
            delete: policy_val,
        },
    }
}

fn sub_expr(
    body: &Box<IRExpr>,
    renamed_fields: &HashMap<Ident<Field>, Ident<Field>>,
) -> Box<IRExpr> {
    Box::new(body.as_ref().map(&|subexpr| match subexpr {
        IRExpr::Path(coll, obj_expr, fld) => IRExpr::Path(
            coll,
            obj_expr,
            renamed_fields.get(&fld).unwrap_or(&fld).clone(),
        ),
        _ => subexpr,
    }))
}

fn remove_invalidated_policies(
    deleted_fields: Vec<Ident<Field>>,
    result_policy: &mut SchemaPolicy,
) {
    let old_policy = result_policy.clone();
    let coll_policies: Vec<(Ident<Collection>, &CollectionPolicy)> = result_policy
        .schema
        .collections
        .iter()
        .map(|coll| {
            (
                coll.name.clone(),
                &old_policy.collection_policies[&coll.name],
            )
        })
        .collect();

    // Check if an expression contains any references to deleted
    // fields or collections
    fn expr_still_valid(expr: &Box<IRExpr>, deleted_fields: &Vec<Ident<Field>>) -> bool {
        field_lookups_in_expr(expr)
            .into_iter()
            .any(|field_id| deleted_fields.contains(&field_id.1))
    }

    // Get all `create` policies whose body references fields or
    // collections that no longer exist.
    let invalidated_create_policies = coll_policies.iter().filter(|(_coll_id, policy)| {
        if let Policy::Func(lam) = &policy.create {
            expr_still_valid(&lam.body, &deleted_fields)
        } else {
            false
        }
    });
    // Same for the delete policies
    let invalidated_delete_policies = coll_policies.iter().filter(|(_coll_id, policy)| {
        if let Policy::Func(lam) = &policy.delete {
            expr_still_valid(&lam.body, &deleted_fields)
        } else {
            false
        }
    });
    // For all the invalidated create policies, set their new policy value to `None`
    for (coll_id, _old_policy) in invalidated_create_policies {
        // This version of `old policy` contains the edits from
        // previous invalidations.
        let old_policy = result_policy.remove_collection_policy(coll_id.clone());
        result_policy.add_collection_policy(
            coll_id.clone(),
            CollectionPolicy {
                create: Policy::None,
                delete: old_policy.delete.clone(),
            },
        );
    }
    // Same for the delete policies
    for (coll_id, _old_policy) in invalidated_delete_policies {
        // This version of `old policy` contains the edits from
        // previous invalidations.
        let old_policy = result_policy.remove_collection_policy(coll_id.clone());
        result_policy.add_collection_policy(
            coll_id.clone(),
            CollectionPolicy {
                create: old_policy.create.clone(),
                delete: Policy::None,
            },
        );
    }

    let field_policies: Vec<(Ident<Field>, &FieldPolicy)> = result_policy
        .schema
        .collections
        .iter()
        .flat_map(|coll| coll.fields().filter(|field| field.name.orig_name != "id"))
        .map(|field| {
            (
                field.name.clone(),
                old_policy.field_policies.get(&field.name).expect(&format!(
                    "Couldn't find policy for field {}",
                    field.name.orig_name
                )),
            )
        })
        .collect();

    // Get all `read` policies whose body refers to fields or
    // collections that no longer exist.
    let invalidated_read_policies = field_policies.iter().filter(|(_field_id, policy)| {
        if let Policy::Func(lam) = &policy.read {
            expr_still_valid(&lam.body, &deleted_fields)
        } else {
            false
        }
    });

    // Same for edit policies
    let invalidated_edit_policies = field_policies.iter().filter(|(_field_id, policy)| {
        if let Policy::Func(lam) = &policy.edit {
            expr_still_valid(&lam.body, &deleted_fields)
        } else {
            false
        }
    });

    // For all the invalidated read policies, set their new policy value to `None`
    for (field_id, _old_policy) in invalidated_read_policies {
        // This version of `old policy` contains the edits from
        // previous invalidations.
        let old_policy = result_policy.remove_field_policy(field_id.clone());
        result_policy.add_field_policy(
            field_id.clone(),
            FieldPolicy {
                read: Policy::None,
                edit: old_policy.edit.clone(),
            },
        );
    }
    // For all the invalidated edit policies, set their new policy value to `None`
    for (field_id, _old_policy) in invalidated_edit_policies {
        // This version of `old policy` contains the edits from
        // previous invalidations.
        let old_policy = result_policy.remove_field_policy(field_id.clone());
        result_policy.add_field_policy(
            field_id.clone(),
            FieldPolicy {
                read: old_policy.read.clone(),
                edit: Policy::None,
            },
        );
    }
}

fn get_policy_from_initializer(
    old_schema: &SchemaPolicy,
    _field_id: Ident<Field>,
    init: Func,
) -> FieldPolicy {
    let sources = field_lookups_in_expr(&init.body);
    let my_coll = match init.param_type {
        ExprType::Object(coll) => coll,
        _ => panic!("parameter to policy function isn't an object?!?"),
    };
    for source in sources.iter() {
        match old_schema.field_policies[&source.1].read {
            Policy::Anyone => (),
            Policy::None => (),
            _ => assert_eq!(
                source.0, my_coll,
                "Analysis of data flow from foreign objects not supported. \
                 Tried to look up field {} on object of type {}",
                source.1.orig_name, source.0.orig_name
            ),
        };
    }
    let read_policies: Vec<_> = sources
        .iter()
        .map(|s| old_schema.field_policies[&s.1].read.clone())
        .collect();
    let intersect = policy_intersect(read_policies.into_iter());
    return FieldPolicy {
        read: intersect,
        edit: Policy::Anyone,
    };
}
fn policy_intersect(mut pols: impl Iterator<Item = Policy>) -> Policy {
    fn policy_intersect_2(pol1: Policy, pol2: Policy) -> Policy {
        match (pol1, pol2) {
            (Policy::None, _) => Policy::None,
            (_, Policy::None) => Policy::None,
            (Policy::Anyone, pol2) => pol2,
            (pol1, Policy::Anyone) => pol1,
            (
                Policy::Func(Func {
                    param: p1,
                    param_type: pty1,
                    return_type: rty1,
                    body: e1,
                }),
                Policy::Func(Func {
                    param: p2,
                    param_type: pty2,
                    return_type: rty2,
                    body: e2,
                }),
            ) => {
                assert_eq!(pty1, pty2);
                assert_eq!(rty1, rty2);
                let e2_subst = e2.map(&|e| match e {
                    IRExpr::Var(ref ty, ref v) => {
                        if *v == p2 {
                            IRExpr::Var(ty.clone(), p1.clone())
                        } else {
                            e
                        }
                    }
                    _ => e,
                });

                Policy::Func(Func {
                    param: p1,
                    param_type: pty1,
                    return_type: rty1.clone(),
                    body: Box::new(IRExpr::Intersect(rty1, e1, Box::new(e2_subst))),
                })
            }
        }
    }
    match pols.next() {
        None => Policy::Anyone,
        Some(p) => {
            let result = policy_intersect_2(p, policy_intersect(pols));
            return result;
        }
    }
}

fn field_lookups_in_expr(expr: &Box<IRExpr>) -> Vec<(Ident<Collection>, Ident<Field>)> {
    expr.subexprs_preorder()
        .flat_map(|se| match se {
            IRExpr::Path(_, obj, def) => {
                if def.is_id() {
                    vec![]
                } else {
                    if let ExprType::Object(coll) = obj.type_of() {
                        vec![(coll, def.clone())]
                    } else {
                        vec![]
                    }
                }
            }
            IRExpr::Object(coll, field_exprs, _template_expr) => field_exprs
                .iter()
                .flat_map(|(k, e)| match e {
                    Some(_) => None,
                    None => Some((coll.clone(), k.clone())),
                })
                .collect(),
            _ => vec![],
        })
        .collect()
}

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn parse_and_print() {
        let policy_text = r"@principal
User {
    create: none,
    delete: none,

    username : String {
        read: none,
        write: none,
    },
}
";
        let out_text = migrate_policy(policy_text, "").unwrap();
        assert_eq!(policy_text, out_text);
    }

    #[test]
    fn add_const_field() {
        let policy_text = r"@principal
User {
    create: none,
    delete: none,

    username : String {
        read: none,
        write: none,
    },
}
";
        let migration_text = r#"User::AddField(pass_hash: String {read: none, write: u -> [u.id],}, u -> "default_hash")"#;
        let out_text = migrate_policy(policy_text, migration_text).unwrap();

        let expected_result_text = r"@principal
User {
    create: none,
    delete: none,

    username : String {
        read: none,
        write: none,
    },
    pass_hash : String {
        read: none,
        write: u -> [u.id],
    },
}
";
        assert_eq!(out_text, expected_result_text);
    }

    #[test]
    fn add_private_depends_field() {
        let policy_text = r"@principal
User {
    create: none,
    delete: none,

    username : String {
        read: none,
        write: none,
    },
}
";
        let migration_text = r#"User::AddField(pass_hash: String {read: none, write: public,}, u -> u.username + "_hash")"#;
        let out_text = migrate_policy(policy_text, migration_text).unwrap();

        let expected_result_text = r"@principal
User {
    create: none,
    delete: none,

    username : String {
        read: none,
        write: none,
    },
    pass_hash : String {
        read: none,
        write: public,
    },
}
";
        assert_eq!(out_text, expected_result_text);
    }

    #[test]
    fn remove_policy_field_dependency() {
        let policy_text = r"@principal
User {
    create: public,
    delete: u -> [u.owner],

    owner : Id(User) {
        read: none,
        write: none,
    },

    username : String {
        read: public,
        write: u -> [u.owner],
    },
}
";
        let migration_text = r#"User::RemoveField(owner)"#;
        let out_text = migrate_policy(policy_text, migration_text).unwrap();

        let expected_result_text = r"@principal
User {
    create: public,
    delete: none,

    username : String {
        read: public,
        write: none,
    },
}
";
        assert_eq!(out_text, expected_result_text);
    }
    #[test]
    fn rename_policy_field_dependency() {
        let policy_text = r"@principal
User {
    create: public,
    delete: u -> [u.owner],

    owner : Id(User) {
        read: none,
        write: none,
    },

    username : String {
        read: public,
        write: u -> [u.owner],
    },
}
";
        let migration_text = r#"User::RenameField(owner, manager)"#;
        let out_text = migrate_policy(policy_text, migration_text).unwrap();

        let expected_result_text = r"@principal
User {
    create: public,
    delete: u -> [u.manager],

    manager : Id(User) {
        read: none,
        write: none,
    },
    username : String {
        read: public,
        write: u -> [u.manager],
    },
}
";
        assert_eq!(out_text, expected_result_text);
    }

    #[test]
    fn loosen_field_policy() {
        let policy_text = r"@principal
User {
    create: none,
    delete: none,

    username : String {
        read: none,
        write: none,
    },
}
";
        let migration_text = r#"User::WeakenFieldPolicy(username, read, public)
User::WeakenFieldPolicy(username, write, public)"#;
        let out_text = migrate_policy(policy_text, migration_text).unwrap();
        let expected_result_text = r"@principal
User {
    create: none,
    delete: none,

    username : String {
        read: public,
        write: public,
    },
}
";
        assert_eq!(expected_result_text, out_text);
    }
    #[test]
    fn simple_tighten_field_policy() {
        let policy_text = r"@principal
User {
    create: none,
    delete: none,

    username : String {
        read: public,
        write: none,
    },
}
";
        let migration_text = r#"User::UpdateFieldPolicy(username, read, none)
User::UpdateFieldPolicy(username, write, none)"#;
        let out_text = migrate_policy(policy_text, migration_text).unwrap();
        let expected_result_text = r"@principal
User {
    create: none,
    delete: none,

    username : String {
        read: none,
        write: none,
    },
}
";
        assert_eq!(expected_result_text, out_text);
    }
    #[test]
    fn tighten_field_policy() {
        let policy_text = r"@principal
User {
    create: none,
    delete: none,

    username : String {
        read: public,
        write: none,
    },
}
Message {
    create: public,
    delete: none,

    to : Id(User) {
        read: public,
        write: none,
    },
    from : Id(User) {
        read: public,
        write: none,
    },
    contents : String {
        read: m -> [m.to, m.from],
        write: none,
    },
}
";
        let migration_text = r#"Message::UpdateFieldPolicy(contents, read, m -> [m.from])"#;
        let out_text = migrate_policy(policy_text, migration_text).unwrap();
        let expected_result_text = r"@principal
User {
    create: none,
    delete: none,

    username : String {
        read: public,
        write: none,
    },
}
Message {
    create: public,
    delete: none,

    to : Id(User) {
        read: public,
        write: none,
    },
    from : Id(User) {
        read: public,
        write: none,
    },
    contents : String {
        read: m -> [m.from],
        write: none,
    },
}
";
        assert_eq!(expected_result_text, out_text);
    }
    #[test]
    fn loosen_collection_policy() {
        let policy_text = r"@principal
User {
    create: none,
    delete: none,

    username : String {
        read: none,
        write: none,
    },
}
";
        let migration_text = r#"User::WeakenPolicy(create, public)
User::WeakenPolicy(delete, public)"#;
        let out_text = migrate_policy(policy_text, migration_text).unwrap();
        let expected_result_text = r"@principal
User {
    create: public,
    delete: public,

    username : String {
        read: none,
        write: none,
    },
}
";
        assert_eq!(expected_result_text, out_text);
    }
    #[test]
    fn simple_tighten_collection_policy() {
        let policy_text = r"@principal
User {
    create: public,
    delete: public,

    username : String {
        read: none,
        write: none,
    },
}
";
        let migration_text = r#"User::UpdatePolicy(create, none)"#;
        let out_text = migrate_policy(policy_text, migration_text).unwrap();
        let expected_result_text = r"@principal
User {
    create: none,
    delete: public,

    username : String {
        read: none,
        write: none,
    },
}
";
        assert_eq!(expected_result_text, out_text);
    }
    #[test]
    fn add_collections() {
        let before_policy = r#"
        @principal
        User {
            create: public,
            delete: none,

            name: String {
                read: none,
                write: none,
            },
        }
    "#;
        let migration = r#"
        CreateCollection(Phone {create: public, delete: public, owner: Id(User) { read: public, write: none,},})
        CreateCollection(Laptop {create: public, delete: public, owner: Id(User) { read: public, write: none,},})
        "#;

        let after_policy = migrate_policy(before_policy, migration).expect("Couldn't migrate!");

        let expected_after_policy = r#"@principal
User {
    create: public,
    delete: none,

    name : String {
        read: none,
        write: none,
    },
}
Phone {
    create: public,
    delete: public,

    owner : Id(User) {
        read: public,
        write: none,
    },
}
Laptop {
    create: public,
    delete: public,

    owner : Id(User) {
        read: public,
        write: none,
    },
}
"#;
        assert_eq!(expected_after_policy, after_policy);
    }

    #[test]
    fn to_privilege() {
        let before_policy = r#"@principal
User {
    create: public,
    delete: none,

    name : String {
        read: public,
        write: u -> User::Find({is_admin: true}).map(u -> u.id),
    },
    is_admin : Bool {
        read: public,
        write: none,
    },
}"#;
        let migration = r#"
            User::AddField(privilege: I64 {read: public, write: none,},
                           p -> (if p.is_admin then 3 else 1))
            User::UpdateFieldPolicy(name, write, u -> User::Find({privilege: 3}).map(u -> u.id))
            User::RemoveField(is_admin)
            "#;
        let after_policy = migrate_policy(before_policy, migration).unwrap();
        let expected_after_policy = r#"@principal
User {
    create: public,
    delete: none,

    name : String {
        read: public,
        write: u -> User::Find({privilege : 3}).map(u -> u.id),
    },
    privilege : I64 {
        read: public,
        write: none,
    },
}
"#;
        assert_eq!(expected_after_policy, after_policy);
    }

    #[test]
    fn to_optional() {
        let before_policy = r#"@principal
User {
    create: public,
    delete: none,

    name : String {
        read: none,
        write: none,
    },
}
Phone {
    create: public,
    delete: none,

    owner : Id(User) {
        read: public,
        write: none,
    },
    secret : String {
        read: p -> [p.owner],
        write: none,
    },
}"#;
        let migration = r#"
            # Allow for the possibility of phone liberation
            Phone::AddField(owner_1: Option(Id(User)) {read: public, write: none,},
                            p -> Some(p.owner))
            Phone::UpdateFieldPolicy(secret, read, p -> (match p.owner_1 as o in
                                                          [o] else []))
            Phone::RemoveField(owner)
            Phone::RenameField(owner_1, owner)
            "#;
        let after_policy = migrate_policy(before_policy, migration).unwrap();
        let expected_after_policy = r#"@principal
User {
    create: public,
    delete: none,

    name : String {
        read: none,
        write: none,
    },
}
Phone {
    create: public,
    delete: none,

    secret : String {
        read: p -> (match p.owner as o in [o] else []),
        write: none,
    },
    owner : Option(Id(User)) {
        read: public,
        write: none,
    },
}
"#;
        assert_eq!(expected_after_policy, after_policy);
    }
    #[test]
    fn pass_read_to_authenticator() {
        let before_policy = r#"@static-principal
Authenticator
@principal
User {
    create: public,
    delete: none,

    pass_hash : String {
        read: u -> [u.id, Authenticator],
        write: u -> [u.id],
    },

    name : String {
        read: none,
        write: none,
    },
}"#;
        let migration = r#"User::UpdateFieldPolicy(pass_hash, read, u -> [Authenticator])"#;
        let after_policy = migrate_policy(before_policy, migration).unwrap();
        let expected_after_policy = r#"@static-principal
Authenticator
@principal
User {
    create: public,
    delete: none,

    pass_hash : String {
        read: u -> [Authenticator],
        write: u -> [u.id],
    },
    name : String {
        read: none,
        write: none,
    },
}
"#;
        assert_eq!(expected_after_policy, after_policy);
    }

    #[test]
    fn add_principals_field() {
        let policy_text = r"User {
    create: none,
    delete: none,

    username : String {
        read: public,
        write: none,
    },
    pass_hash : String {
        read: public,
        write: none,
    },
}
";
        let migration_text = r#"AddStaticPrincipal(Authenticator)
AddPrincipal(User)
User::WeakenFieldPolicy(pass_hash, write, u -> [u.id])
User::UpdateFieldPolicy(pass_hash, read, u -> [Authenticator])"#;
        let out_text = migrate_policy(policy_text, migration_text).unwrap();

        let expected_result_text = r"@static-principal
Authenticator
@principal
User {
    create: none,
    delete: none,

    username : String {
        read: public,
        write: none,
    },
    pass_hash : String {
        read: u -> [Authenticator],
        write: u -> [u.id],
    },
}
";
        assert_eq!(expected_result_text, out_text);
    }

    #[test]
    fn domain_constraints() {
        let policy_text = r"@principal
User {
    create: none,
    delete: none,

    username : String {
        read: public,
        write: none,
    },
}
Message {
    create: m -> [m.from],
    delete: none,

    to : Id(User) {
        read: public,
        write: none,
    },
    from : Id(User) {
        read: m -> User::Find({}).map(u -> u.id),
        write: none,
    },
    contents : String {
        read: m -> [m.to, m.from],
        write: none,
    },
}
";
        let migration_text =
            r#"Message::UpdateFieldPolicy(from, read, m -> Message::Find({}).map(m -> m.from))"#;
        let out_text = migrate_policy(policy_text, migration_text).unwrap();

        let expected_result_text = r"@principal
User {
    create: none,
    delete: none,

    username : String {
        read: public,
        write: none,
    },
}
Message {
    create: m -> [m.from],
    delete: none,

    to : Id(User) {
        read: public,
        write: none,
    },
    from : Id(User) {
        read: m -> Message::Find({}).map(m -> m.from),
        write: none,
    },
    contents : String {
        read: m -> [m.to,m.from],
        write: none,
    },
}
";
        assert_eq!(expected_result_text, out_text);
    }
    #[test]
    #[should_panic = "Migration unsafe!"]
    fn constraints_test() {
        let policy_text = r"@principal
User {
    create: none,
    delete: none,
}
Post {
    create: none,
    delete: none,

    author: Id(User) {
        read: public,
        write: none,
    },
    coauthor: Id(User) {
        read: public,
        write: none,
    },
    secret: String {
        read: p -> [p.author],
        write: none,
    },
}
";
        let migration = r#"
Post::UpdateFieldPolicy(secret, read, p -> [p.author, p.coauthor].map(u -> User::ById(u).id))
"#;
        let out_text = migrate_policy(policy_text, migration).unwrap();
        let expected_out_text = r"@principle
User {
    create: none,
    delete: none,
}
Post {
    create: none,
    delete: none,

    author: Id(User) {
        read: public,
        write: none,
    },
    coauthor: Id(User) {
        read: public,
        write: none,
    },
    secret: String {
        read: p -> [p.author, p.coauthor].map(u -> User::ById(u).id),
        write: none,
    },
}
";
        assert_eq!(expected_out_text, out_text);
    }

    #[test]
    fn equivalences_crash() {
        let policy_text = r"@principal
User {
    create: none,
    delete: none,

    username : String {
        read: public,
        write: none,
    },
}
Post {
    create: none,
    delete: none,

    author : Id(User) {
        read: public,
        write: none,
    },
}
";
        let migration_text = r#"
Post::AddField(summary: String {
    read: public,
    write: p -> [p.author],
}, p -> "Post by " + User::ById(p.author).username)
Post::UpdateFieldPolicy(summary, read, public)
"#;
        let out_text = migrate_policy(policy_text, migration_text).unwrap();

        let expected_result_text = r"@principal
User {
    create: none,
    delete: none,

    username : String {
        read: public,
        write: none,
    },
}
Post {
    create: none,
    delete: none,

    author : Id(User) {
        read: public,
        write: none,
    },
    summary : String {
        read: public,
        write: p -> [p.author],
    },
}
";

        assert_eq!(out_text, expected_result_text)
    }

    #[test]
    #[should_panic = "Migration unsafe!"]
    fn find_equivalences_crash() {
        let policy_text = r"@principal
User {
    create: public,
    delete: u -> [u.id],

    is_admin : Bool {
        read: public,
        write: none,
    },
    site : Id(Site) {
        read: public,
        write: none,
    },
}
Site {
    create: public,
    delete: none,

    name : String {
        read: public,
        write: s -> User::Find({site: s.id, is_admin: true}).map(u -> u.id),
    },
    owner : Id(User) {
        read: public,
        write: none,
    },
}
";
        let migration_text = r#"
Site::AddField(admins: Set(Id(User)) {
  read: public,
  write: s -> s.admins,
},
  s -> User::Find({is_admin: true}).map(u -> u.id)
)
Site::UpdateFieldPolicy(name, write, s -> s.admins)
"#;
        let out_text = migrate_policy(policy_text, migration_text).unwrap();

        let expected_result_text = r"@principal
User {
    create: public,
    delete: u -> [u.id],

    is_admin : Bool {
        read: public,
        write: none,
    },
    site : Id(Site) {
        read: public,
        write: none,
    },
}
Site {
    create: public,
    delete: none,

    name : String {
        read: public,
        write: s -> s.admins,
    },
    owner : Id(User) {
        read: public,
        write: none,
    },
    admins : Set(Id(User)) {
        read: public,
        write: s -> s.admins,
    },
}
";
        assert_eq!(out_text, expected_result_text)
    }
}
