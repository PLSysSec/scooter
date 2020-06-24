use static_checker::smt::*;
use policy_lang::ir::{schema::Schema, policy::{SchemaPolicy, extract_schema_policy}, expr::{extract_func, ExprType, Func}};

fn schema_policy(pol: &str) -> SchemaPolicy {
    let pol = policy_lang::parse_policy(pol).unwrap();
    extract_schema_policy(&pol)
}

fn func(schema: &Schema, func: &str, from: ExprType, to: ExprType) -> Func {
    let func = policy_lang::parse_func(func).unwrap();
    extract_func(schema, from, &to, &func)
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

    assert!(is_as_strict(&schema, &after, &before))
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
    let after = func(&schema, "u -> (if u.name == \"John\" then [u.id] else [])", ExprType::Object(user.name.clone()), ExprType::list(ExprType::Id(user.name.clone())));

    assert!(is_as_strict(&schema, &before, &after))
}