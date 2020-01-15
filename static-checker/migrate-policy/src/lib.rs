use policy_lang::ir::*;
use policy_lang::{parse_migration, parse_policy};

use std::io::{self, Read};

/// Take two filenames, a policy and a migration, and produce a new
/// policy as a string, by reading those files.
pub fn migrate_policy_from_files(
    policy_path: impl ToString,
    migration_path: impl ToString,
) -> String {
    migrate_policy(
        &get_contents(&policy_path.to_string()).expect("Couldn't read policy file"),
        &get_contents(&migration_path.to_string()).expect("Couldn't read migration file"),
    )
}
fn get_contents(fname: &str) -> io::Result<String> {
    let mut out = String::new();
    std::fs::File::open(fname)?.read_to_string(&mut out)?;
    Ok(out)
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
    let resulting_policy = interpret_migration_on_policy(&ird, lowered_policy, lowered_migration);
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
    ird: &IrData,
    policy: CompletePolicy,
    migration: CompleteMigration,
) -> CompletePolicy {
    let mut result_policy = policy.clone();

    for cmd in migration.0.into_iter() {
        match cmd {
            CompleteMigrationCommand::CollAction { table: _, action } => match action {
                CompleteMigrationAction::AddField { field, ty: _, init } => result_policy
                    .add_field_policy(
                        field,
                        get_policy_from_initializer(ird, &policy, field, init),
                    ),
                _ => panic!("todo: other migration actions"),
            },
            _ => panic!("todo: Create and delete"),
        }
    }

    result_policy
}

fn get_policy_from_initializer(
    ird: &IrData,
    _old_policy: &CompletePolicy,
    field_id: Id<Def>,
    init: Lambda,
) -> FieldPolicy {
    let sources = defs_in_expr(ird, init.body);
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

fn defs_in_expr(ird: &IrData, e_id: Id<Expr>) -> Vec<Id<Def>> {
    let expr = &ird[e_id];
    match &expr.kind {
        ExprKind::AppendS(e1_id, e2_id)
        | ExprKind::AppendL(_, e1_id, e2_id)
        | ExprKind::AddI(e1_id, e2_id)
        | ExprKind::AddF(e1_id, e2_id)
        | ExprKind::SubI(e1_id, e2_id)
        | ExprKind::SubF(e1_id, e2_id)
        | ExprKind::IsEq(_, e1_id, e2_id)
        | ExprKind::IsLessI(e1_id, e2_id)
        | ExprKind::IsLessF(e1_id, e2_id) => defs_in_expr(ird, *e1_id)
            .into_iter()
            .chain(defs_in_expr(ird, *e2_id).into_iter())
            .collect(),
        ExprKind::Not(se_id) | ExprKind::IntToFloat(se_id) => defs_in_expr(ird, *se_id),
        ExprKind::If(_, e1_id, e2_id, e3_id) => defs_in_expr(ird, *e1_id)
            .into_iter()
            .chain(defs_in_expr(ird, *e2_id).into_iter())
            .chain(defs_in_expr(ird, *e3_id))
            .collect(),
        ExprKind::List(exprs) => exprs
            .iter()
            .flat_map(|expr| defs_in_expr(ird, *expr))
            .collect(),
        ExprKind::Object(_, field_exprs, template_expr) => field_exprs
            .iter()
            .flat_map(|(_ident, expr)| defs_in_expr(ird, *expr))
            .chain(
                template_expr
                    .map(|expr| defs_in_expr(ird, expr))
                    .unwrap_or(vec![]),
            )
            .collect(),
        ExprKind::IntConst(_)
        | ExprKind::FloatConst(_)
        | ExprKind::StringConst(_)
        | ExprKind::BoolConst(_) => vec![],
        ExprKind::Var(_) => vec![],
        ExprKind::LookupById(_coll, se_id) => defs_in_expr(ird, *se_id),
        ExprKind::Path(_coll, se_id, def) => defs_in_expr(ird, *se_id)
            .into_iter()
            .chain(vec![*def])
            .collect(),
    }
}

mod test {
    use crate::*;

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
}
