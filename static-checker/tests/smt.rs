use static_checker::smt::*;
use policy_lang::ir::{schema::Schema, policy::{SchemaPolicy, Policy, extract_schema_policy}, expr::{extract_func, ExprType}};

fn schema_policy(pol: &str) -> SchemaPolicy {
    let pol = policy_lang::parse_policy(pol).unwrap();
    extract_schema_policy(&pol)
}

fn func(schema: &Schema, func: &str, from: ExprType, to: ExprType) -> Policy {
    let func = policy_lang::parse_func(func).unwrap();
    Policy::Func(extract_func(schema, from, &to, &func))
}


#[test]
fn foo() {
    let before_policy = schema_policy(
        r#"
        @principle
        User {
            create: public,
            delete: none,

            name: String {
                read: none,
                write: none, 
            },
        }

    "#,
    );

    let schema = before_policy.schema;
    let user = schema.find_collection("User").unwrap();
    let before = func(&schema, "u -> []", ExprType::Object(user.name.clone()), ExprType::list(ExprType::Id(user.name.clone())));
    let after = func(&schema, "u -> [u.id]", ExprType::Object(user.name.clone()), ExprType::list(ExprType::Id(user.name.clone())));

    assert!(!is_as_strict(&schema, &user.name, &before, &after));
    assert!(is_as_strict(&schema, &user.name, &before, &Policy::None));
}

#[test]
fn find() {
    let before_policy = schema_policy(
        r#"
        @principle
        User {
            create: public,
            delete: none,

            name: String {
                read: none,
                write: none, 
            },
        }

    "#,
    );

    let schema = before_policy.schema;
    let user = schema.find_collection("User").unwrap();
    let before = func(&schema, "u -> User::Find({ name: \"John\" })", ExprType::Object(user.name.clone()), ExprType::list(ExprType::Object(user.name.clone())));
    let after = func(&schema, "u -> (if u.name == (\"Jo\" + \"hn\") then [u.id] else [])", ExprType::Object(user.name.clone()), ExprType::list(ExprType::Id(user.name.clone())));

    assert!(is_as_strict(&schema, &user.name, &before, &after))
}