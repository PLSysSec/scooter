use policy_lang::ir::*;
use policy_lang::{parse_migration, parse_policy};

use std::collections::HashMap;
use std::fs::read_to_string;
use std::path::Path;

/// Take two filenames, a policy and a migration, and produce a new
/// policy as a string, by reading those files.
pub fn migrate_policy_from_files(
    policy_path: impl AsRef<Path>,
    migration_path: impl AsRef<Path>,
) -> String {
    migrate_policy(
        &read_to_string(policy_path).expect("Couldn't read policy file"),
        &read_to_string(migration_path).expect("Couldn't read migration file"),
    )
}

/// Take the text of a policy and a migration, and produce a new
/// policy, that doesn't leak any information from the old policy, but
/// is valid post-migration.
pub fn migrate_policy(policy_text: &str, migration_text: &str) -> String {
    let parsed_policy = parse_policy(policy_text).expect("Couldn't parse policy");
    let parsed_migration = parse_migration(migration_text).expect("Couldn't parse migration");
    let mut ird = extract_types(&parsed_policy);
    let lowered_policy = ird.lower(&parsed_policy);
    let lowered_migration = ird.lower_migration(parsed_migration);
    let resulting_policy =
        interpret_migration_on_policy(&mut ird, lowered_policy, lowered_migration);
    policy_to_string(&ird, resulting_policy)
}

fn policy_to_string(ird: &IrData, policy: CompletePolicy) -> String {
    let mut result = "".to_string();
    for coll in ird.collections() {
        result += &format!("{} {{\n", coll.name.1);
        let col_policy = policy.collection_policy(coll.id);
        result += &format!(
            "    create: {},\n",
            policy_value_to_string(ird, col_policy.create.clone())
        );
        result += &format!(
            "    delete: {},\n",
            policy_value_to_string(ird, col_policy.delete.clone())
        );
        result += "\n";
        for (field_name, field_id) in coll.fields() {
            if field_name == "id" {
                continue;
            }
            result += &format!(
                "    {} : {} {{\n",
                field_name,
                type_to_string(ird, ird.def_type(*field_id).clone())
            );
            let field_policy = policy.field_policy(*field_id);
            result += &format!(
                "        read: {},\n",
                policy_value_to_string(ird, field_policy.read.clone())
            );
            result += &format!(
                "        write: {},\n",
                policy_value_to_string(ird, field_policy.edit.clone())
            );
            result += "    },\n";
        }
        result += "}\n";
    }
    result
}

fn policy_value_to_string(ird: &IrData, policy_value: Policy) -> String {
    match policy_value {
        Policy::Public => "public".to_string(),
        Policy::None => "none".to_string(),
        Policy::Func(l) => format!("{} -> {}", ird[l.param].name.1, expr_to_string(ird, l.body)),
    }
}

fn type_to_string(ird: &IrData, ty: Type) -> String {
    match ty {
        Type::Prim(p) => format!("{}", p),
        Type::Id(id) => format!("Id({})", ird[id].name.1),
        Type::List(ty) => format!("[{}]", type_to_string(ird, *ty)),
        Type::Collection(_id) => panic!("Can't have a colletion type in a policy!"),
        Type::ListAny => panic!("Can't have a listany type in a policy!"),
        Type::ListId => panic!("Can't have a listid type in a policy!"),
    }
}

fn expr_to_string(ird: &IrData, e_id: Id<Expr>) -> String {
    let expr = &ird[e_id];
    match &expr.kind {
        ExprKind::AppendS(e1_id, e2_id)
        | ExprKind::AppendL(_, e1_id, e2_id)
        | ExprKind::AddI(e1_id, e2_id)
        | ExprKind::AddF(e1_id, e2_id) => format!(
            "({} + {})",
            expr_to_string(ird, *e1_id),
            expr_to_string(ird, *e2_id)
        ),

        ExprKind::SubI(e1_id, e2_id) | ExprKind::SubF(e1_id, e2_id) => format!(
            "({} - {})",
            expr_to_string(ird, *e1_id),
            expr_to_string(ird, *e2_id)
        ),
        ExprKind::IsEq(_, e1_id, e2_id) => format!(
            "({} == {})",
            expr_to_string(ird, *e1_id),
            expr_to_string(ird, *e2_id)
        ),
        ExprKind::Not(e_id) => format!("!({})", expr_to_string(ird, *e_id)),
        ExprKind::IsLessI(e1_id, e2_id) | ExprKind::IsLessF(e1_id, e2_id) => format!(
            "({} < {})",
            expr_to_string(ird, *e1_id),
            expr_to_string(ird, *e2_id)
        ),
        // These don't appear in concrete syntax, but will be inserted
        // where needed during lowering.
        ExprKind::IntToFloat(e_id) => expr_to_string(ird, *e_id),
        ExprKind::Path(_, e_id, f_id) => {
            format!("{}.{}", expr_to_string(ird, *e_id), ird[*f_id].name.1)
        }
        ExprKind::Var(v_id) => ird[*v_id].name.1.clone(),
        ExprKind::Object(coll, field_vals, template_obj) => {
            let fields = field_vals
                .iter()
                .map(|(f_id, e_id)| {
                    format!("{}: {},", ird[*f_id].name.1, expr_to_string(ird, *e_id))
                })
                .collect::<Vec<String>>()
                .join("");
            match template_obj {
                Some(obj) => format!(
                    "{} {{ {} ..{} }}",
                    ird[*coll].name.1,
                    fields,
                    expr_to_string(ird, *obj)
                ),
                None => format!("{} {{ {} }}", ird[*coll].name.1, fields),
            }
        }
        ExprKind::LookupById(coll, e_id) => format!(
            "{}::ById({})",
            ird[*coll].name.1,
            expr_to_string(ird, *e_id)
        ),
        ExprKind::List(exprs) => format!(
            "[{}]",
            exprs
                .iter()
                .map(|e_id| expr_to_string(ird, *e_id))
                .collect::<Vec<String>>()
                .join(",")
        ),
        ExprKind::If(_, cond, iftrue, iffalse) => format!(
            "(if {} then {} else {})",
            expr_to_string(ird, *cond),
            expr_to_string(ird, *iftrue),
            expr_to_string(ird, *iffalse)
        ),
        ExprKind::IntConst(i) => format!("{}", i),
        ExprKind::FloatConst(f) => format!("{}", f),
        ExprKind::StringConst(s) => format!("\"{}\"", s),
        ExprKind::BoolConst(b) => format!("{}", b),
    }
}

fn interpret_migration_on_policy(
    ird: &mut IrData,
    policy: CompletePolicy,
    migration: CompleteMigration,
) -> CompletePolicy {
    // The policy state we'll return
    let mut result_policy = policy.clone();

    // Keep track of fields that are removed, for invalidating
    // functions that refer to them.
    let mut deleted_fields = Vec::new();
    // Keep track of fields that are renamed, for repairing
    // expressions that referenced the old name.
    let mut renamed_fields: HashMap<Id<Def>, Id<Def>> = HashMap::new();

    // Go over the migration commands (consuming them)
    for cmd in migration.0.into_iter() {
        match cmd {
            CompleteMigrationCommand::CollAction { table: _, action } => match action {
                // For adding fields, just add new policies based on
                // the initializer function
                CompleteMigrationAction::AddField { field, ty: _, init } => result_policy
                    .add_field_policy(
                        field,
                        get_policy_from_initializer(ird, &policy, field, init),
                    ),
                // For removing fields, remove the policy data, and
                // add it to a list of deleted fields for invalidating
                // expressions later.
                CompleteMigrationAction::RemoveField { field } => {
                    result_policy.remove_field_policy(field);
                    deleted_fields.push(field);
                    if let Some((old_field, _new_field)) =
                        renamed_fields.iter().find(|(_k, v)| **v == field)
                    {
                        let old_field_id = old_field.clone();
                        deleted_fields.push(*old_field);
                        renamed_fields.remove(&old_field_id);
                    }
                }
                CompleteMigrationAction::ChangeField {
                    field,
                    new_ty: _,
                    new_init,
                } => {
                    result_policy.remove_field_policy(field);
                    result_policy.add_field_policy(
                        field,
                        get_policy_from_initializer(ird, &policy, field, new_init),
                    );
                    // Anything that referred to it's old value as a
                    // policy isn't going to work anymore.
                    deleted_fields.push(field);
                }
                // Don't need to do anything here, because renamed
                // fields keep their old ids.
                CompleteMigrationAction::RenameField {
                    old_field_id,
                    new_field_id,
                    old_name: _,
                    new_name: _,
                } => {
                    result_policy.add_field_policy(
                        new_field_id,
                        result_policy.field_policy(old_field_id).clone(),
                    );
                    renamed_fields.insert(old_field_id, new_field_id);
                }
                CompleteMigrationAction::ForEach { param: _, body: _ } => {
                    panic!("We don't know how to process foreaches on policies yet")
                }
                CompleteMigrationAction::LoosenFieldPolicy { new_field_policy } => {
                    result_policy.remove_field_policy(new_field_policy.field_id);
                    result_policy.add_field_policy(
                        new_field_policy.field_id,
                        new_field_policy);
                }
            },
            // For creating collections, just create a new create and
            // delete policies. Since being able to create and delete
            // from a collection can't leak any info, we can give it
            // public policies.
            CompleteMigrationCommand::Create { table_id } => {
                let public_pol = CollectionPolicy {
                    create: Policy::Public,
                    delete: Policy::Public,
                };
                result_policy.add_collection_policy(table_id, public_pol);
            }
            // For deleting collections, remove the policy data.
            CompleteMigrationCommand::Delete { table_id } => {
                result_policy.remove_collection_policy(table_id);
            }
        }
    }

    remove_invalidated_policies(ird, deleted_fields, &mut result_policy);

    let coll_ids: Vec<Id<Collection>> = ird.collections().map(|coll| coll.id).collect();

    for coll_id in coll_ids.into_iter() {
        let coll_pol = result_policy.collection_policy_mut(coll_id);
        if let Policy::Func(Lambda { param: p, body }) = coll_pol.create {
            coll_pol.create = Policy::Func(Lambda {
                param: p,
                body: sub_expr(ird, body, &renamed_fields),
            });
        }
        if let Policy::Func(Lambda { param: p, body }) = coll_pol.delete {
            coll_pol.delete = Policy::Func(Lambda {
                param: p,
                body: sub_expr(ird, body, &renamed_fields),
            });
        }
    }

    let field_ids: Vec<Id<Def>> = ird
        .collections()
        .flat_map(|coll| {
            coll.fields()
                .filter(|(name, _id)| *name != "id")
                .map(|(_name, id)| *id)
        })
        .collect();

    for field_id in field_ids.into_iter() {
        let field_pol = result_policy.field_policy_mut(field_id);
        if let Policy::Func(Lambda { param: p, body }) = field_pol.read {
            field_pol.read = Policy::Func(Lambda {
                param: p,
                body: sub_expr(ird, body, &renamed_fields),
            });
        }
        if let Policy::Func(Lambda { param: p, body }) = field_pol.edit {
            field_pol.edit = Policy::Func(Lambda {
                param: p,
                body: sub_expr(ird, body, &renamed_fields),
            });
        }
    }

    result_policy
}

fn sub_expr(
    ird: &mut IrData,
    body: Id<Expr>,
    renamed_fields: &HashMap<Id<Def>, Id<Def>>,
) -> Id<Expr> {
    expr_map(
        ird,
        &|subexpr| match &subexpr.kind {
            ExprKind::Path(coll, expr, def) => {
                ExprKind::Path(*coll, *expr, *renamed_fields.get(&def).unwrap_or(&def))
            }
            _ => subexpr.kind.clone(),
        },
        body,
    )
}

fn remove_invalidated_policies(
    ird: &IrData,
    deleted_fields: Vec<Id<Def>>,
    result_policy: &mut CompletePolicy,
) {
    let old_policy = result_policy.clone();
    let coll_policies: Vec<(Id<Collection>, &CollectionPolicy)> = ird
        .collections()
        .map(|coll| (coll.id, old_policy.collection_policy(coll.id)))
        .collect();

    // Check if an expression contains any references to deleted
    // fields or collections
    fn expr_still_valid(ird: &IrData, e_id: Id<Expr>, deleted_fields: &Vec<Id<Def>>) -> bool {
        field_lookups_in_expr(ird, e_id)
            .into_iter()
            .any(|field_id| deleted_fields.contains(&field_id))
    }

    // Get all `create` policies whose body references fields or
    // collections that no longer exist.
    let invalidated_create_policies = coll_policies.iter().filter(|(_coll_id, policy)| {
        if let Policy::Func(lam) = &policy.create {
            expr_still_valid(ird, lam.body, &deleted_fields)
        } else {
            false
        }
    });
    // Same for the delete policies
    let invalidated_delete_policies = coll_policies.iter().filter(|(_coll_id, policy)| {
        if let Policy::Func(lam) = &policy.delete {
            expr_still_valid(ird, lam.body, &deleted_fields)
        } else {
            false
        }
    });
    // For all the invalidated create policies, set their new policy value to `None`
    for (coll_id, _old_policy) in invalidated_create_policies {
        // This version of `old policy` contains the edits from
        // previous invalidations.
        let old_policy = result_policy.remove_collection_policy(*coll_id);
        result_policy.add_collection_policy(
            *coll_id,
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
        let old_policy = result_policy.remove_collection_policy(*coll_id);
        result_policy.add_collection_policy(
            *coll_id,
            CollectionPolicy {
                create: old_policy.create.clone(),
                delete: Policy::None,
            },
        );
    }

    let field_policies: Vec<(Id<Def>, &FieldPolicy)> = ird
        .collections()
        .flat_map(|coll| {
            coll.fields()
                .filter(|(field_name, _field_id)| *field_name != "id")
        })
        .map(|(_field_name, field_id)| (*field_id, old_policy.field_policy(*field_id)))
        .collect();

    // Get all `read` policies whose body refers to fields or
    // collections that no longer exist.
    let invalidated_read_policies = field_policies.iter().filter(|(_field_id, policy)| {
        if let Policy::Func(lam) = &policy.read {
            expr_still_valid(ird, lam.body, &deleted_fields)
        } else {
            false
        }
    });

    // Same for edit policies
    let invalidated_edit_policies = field_policies.iter().filter(|(_field_id, policy)| {
        if let Policy::Func(lam) = &policy.edit {
            expr_still_valid(ird, lam.body, &deleted_fields)
        } else {
            false
        }
    });

    // For all the invalidated read policies, set their new policy value to `None`
    for (field_id, _old_policy) in invalidated_read_policies {
        // This version of `old policy` contains the edits from
        // previous invalidations.
        let old_policy = result_policy.remove_field_policy(*field_id);
        result_policy.add_field_policy(
            *field_id,
            FieldPolicy {
                field_id: *field_id,
                read: Policy::None,
                edit: old_policy.edit.clone(),
            },
        );
    }
    // For all the invalidated edit policies, set their new policy value to `None`
    for (field_id, _old_policy) in invalidated_edit_policies {
        // This version of `old policy` contains the edits from
        // previous invalidations.
        let old_policy = result_policy.remove_field_policy(*field_id);
        result_policy.add_field_policy(
            *field_id,
            FieldPolicy {
                field_id: *field_id,
                read: old_policy.read.clone(),
                edit: Policy::None,
            },
        );
    }
}

fn get_policy_from_initializer(
    ird: &IrData,
    _old_policy: &CompletePolicy,
    field_id: Id<Def>,
    init: Lambda,
) -> FieldPolicy {
    let sources = field_lookups_in_expr(ird, init.body);
    if sources.is_empty() {
        FieldPolicy {
            field_id,
            read: Policy::Public,
            edit: Policy::Public,
        }
    } else {
        FieldPolicy {
            field_id,
            read: Policy::None,
            edit: Policy::None,
        }
    }
}

fn field_lookups_in_expr(ird: &IrData, e_id: Id<Expr>) -> Vec<Id<Def>> {
    expr_to_all_subexprs(ird, e_id)
        .flat_map(|se_id| match &ird[*se_id].kind {
            ExprKind::Path(_, _, def) => vec![*def],
            ExprKind::Object(coll, field_exprs, template_expr) => {
                if template_expr.is_some() {
                    ird[*coll]
                        .fields()
                        .map(|(_name, field_id)| *field_id)
                        .filter(|field_id| {
                            field_exprs
                                .iter()
                                .find(|(init_fid, _expr)| init_fid == field_id)
                                .is_some()
                        })
                        .collect()
                } else {
                    vec![]
                }
            }
            _ => vec![],
        })
        .collect()
}

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn parse_and_print() {
        let policy_text = r"User {
    create: none,
    delete: none,

    username : String {
        read: none,
        write: none,
    },
}
";
        let out_text = migrate_policy(policy_text, "");
        assert_eq!(policy_text, out_text);
    }

    #[test]
    fn add_const_field() {
        let policy_text = r"User {
    create: none,
    delete: none,

    username : String {
        read: none,
        write: none,
    },
}
";
        let migration_text = r#"User::AddField(pass_hash, String, u -> "default_hash")"#;
        let out_text = migrate_policy(policy_text, migration_text);

        let expected_result_text = r"User {
    create: none,
    delete: none,

    username : String {
        read: none,
        write: none,
    },
    pass_hash : String {
        read: public,
        write: public,
    },
}
";
        assert_eq!(out_text, expected_result_text);
    }

    #[test]
    fn add_private_depends_field() {
        let policy_text = r"User {
    create: none,
    delete: none,

    username : String {
        read: none,
        write: none,
    },
}
";
        let migration_text = r#"User::AddField(pass_hash, String, u -> u.username + "_hash")"#;
        let out_text = migrate_policy(policy_text, migration_text);

        let expected_result_text = r"User {
    create: none,
    delete: none,

    username : String {
        read: none,
        write: none,
    },
    pass_hash : String {
        read: none,
        write: none,
    },
}
";
        assert_eq!(out_text, expected_result_text);
    }

    #[test]
    fn remove_policy_field_dependency() {
        let policy_text = r"User {
    create: public,
    delete: u -> u.owner,

    owner : Id(User) {
        read: none,
        write: none,
    },

    username : String {
        read: public,
        write: u -> u.owner,
    },
}
";
        let migration_text = r#"User::RemoveField(owner)"#;
        let out_text = migrate_policy(policy_text, migration_text);

        let expected_result_text = r"User {
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
        let policy_text = r"User {
    create: public,
    delete: u -> u.owner,

    owner : Id(User) {
        read: none,
        write: none,
    },

    username : String {
        read: public,
        write: u -> u.owner,
    },
}
";
        let migration_text = r#"User::RenameField(owner, manager)"#;
        let out_text = migrate_policy(policy_text, migration_text);

        let expected_result_text = r"User {
    create: public,
    delete: u -> u.manager,

    username : String {
        read: public,
        write: u -> u.manager,
    },
    manager : Id(User) {
        read: none,
        write: none,
    },
}
";
        assert_eq!(out_text, expected_result_text);
    }

    #[test]
    fn loosen_policy() {
        let policy_text = r"User {
    create: none,
    delete: none,

    username : String {
        read: none,
        write: none,
    },
}
";
        let migration_text = r#"User::LoosenFieldPolicy(username : String { read: public, write: public, },)"#;
        let out_text = migrate_policy(policy_text, migration_text);
        let expected_result_text = r"User {
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
}
