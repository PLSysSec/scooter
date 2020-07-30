use policy_lang::ir::{
    expr::{extract_func, ExprType},
    policy::{extract_schema_policy, Policy, SchemaPolicy},
    schema::Schema,
};
use static_checker::smt::*;

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
    let before = func(
        &schema,
        "u -> []",
        ExprType::Object(user.name.clone()),
        ExprType::list(ExprType::Id(user.name.clone())),
    );
    let after = func(
        &schema,
        "u -> [u.id]",
        ExprType::Object(user.name.clone()),
        ExprType::list(ExprType::Id(user.name.clone())),
    );

    eprintln!(
        "{}",
        is_as_strict(&schema, &vec![], &user.name, &before, &after)
            .expect_err("strictness check should fail")
    );
    assert!(is_as_strict(&schema, &vec![], &user.name, &before, &Policy::None).is_ok());
}

#[test]
fn unauth() {
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
    let before = func(
        &schema,
        "u -> User::Find({}).map(u -> u.id)",
        ExprType::Object(user.name.clone()),
        ExprType::list(ExprType::Id(user.name.clone())),
    );
    let after = Policy::Anyone;

    eprintln!(
        "{}",
        is_as_strict(&schema, &vec![], &user.name, &before, &after)
            .expect_err("strictness check should fail")
    );
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

            age: I64 {
                read: none,
                write: none,
            },
        }

    "#,
    );

    let schema = before_policy.schema;
    let user = schema.find_collection("User").unwrap();
    let before = func(
        &schema,
        "u -> User::Find({ name: \"John\" }).map(u -> u.id)",
        ExprType::Object(user.name.clone()),
        ExprType::list(ExprType::Id(user.name.clone())),
    );
    let after1 = func(
        &schema,
        "u -> User::Find({ name: \"John\", age: 7 }).map(u -> u.id)",
        ExprType::Object(user.name.clone()),
        ExprType::list(ExprType::Id(user.name.clone())),
    );
    let after = func(
        &schema,
        "u -> (if u.name == (\"Jo\" + \"hn\") then [u.id] else [])",
        ExprType::Object(user.name.clone()),
        ExprType::list(ExprType::Id(user.name.clone())),
    );

    is_as_strict(&schema, &vec![], &user.name, &before, &after).unwrap();
    eprintln!(
        "{}",
        is_as_strict(&schema, &vec![], &user.name, &after, &before)
            .expect_err("strictness check should fail")
    );

    is_as_strict(&schema, &vec![], &user.name, &before, &after1).unwrap();
    eprintln!(
        "{}",
        is_as_strict(&schema, &vec![], &user.name, &after1, &before)
            .expect_err("strictness check should fail")
    );
}

#[test]
fn friends() {
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

        Friendship {
            create: none,
            delete: none,
            from: Id(User) {
                read: none,
                write: none,
            },
            to: Id(User){
                read: none,
                write:none,
            },
        }

    "#,
    );

    let schema = before_policy.schema;
    let user = schema.find_collection("User").unwrap();
    let before = func(
        &schema,
        "u -> [u.id] + (Friendship::Find({ from: u.id }).map(f -> f.to))",
        ExprType::Object(user.name.clone()),
        ExprType::list(ExprType::Id(user.name.clone())),
    );
    let after = func(
        &schema,
        "u -> [u.id]",
        ExprType::Object(user.name.clone()),
        ExprType::list(ExprType::Id(user.name.clone())),
    );
    let after1 = func(&schema, "u -> [u.id] + (Friendship::Find({ from: u.id }).map(f -> f.to).map(u -> User::ById(u)).map(u -> u.id))", ExprType::Object(user.name.clone()), ExprType::list(ExprType::Id(user.name.clone())));

    is_as_strict(&schema, &vec![], &user.name, &before, &after).unwrap();
    is_as_strict(&schema, &vec![], &user.name, &before, &after1).unwrap();
}

#[test]
fn static_princ() {
    let before_policy = schema_policy(
        r#"
        @static-principle
        Authenticator

        @principle
        User {
            create: public,
            delete: none,

            pass: String {
                read: public,
                write: none,
            },
        }
    "#,
    );

    let schema = before_policy.schema;
    let user = schema.find_collection("User").unwrap();
    let before = func(
        &schema,
        "u -> [Authenticator, u.id]",
        ExprType::Object(user.name.clone()),
        ExprType::list(ExprType::Principle),
    );
    let after = func(
        &schema,
        "u -> [u.id]",
        ExprType::Object(user.name.clone()),
        ExprType::list(ExprType::Id(user.name.clone())),
    );

    is_as_strict(&schema, &vec![], &user.name, &before, &after).unwrap();
    eprintln!(
        "{}",
        is_as_strict(&schema, &vec![], &user.name, &after, &before)
            .expect_err("strictness check should fail")
    );
}

#[test]
fn domains() {
    let before_policy = schema_policy(
        r#"
        @principle
        User {
            create: public,
            delete: none,

            other: Id(User) {
                read: public,
                write: none,
            },
        }
    "#,
    );

    let schema = before_policy.schema;
    let user = schema.find_collection("User").unwrap();
    let before = func(
        &schema,
        "u -> User::Find({}).map(u -> u.id)",
        ExprType::Object(user.name.clone()),
        ExprType::list(ExprType::Principle),
    );
    let after = func(
        &schema,
        "u -> [User::ById(u.other).id]",
        ExprType::Object(user.name.clone()),
        ExprType::list(ExprType::Id(user.name.clone())),
    );

    is_as_strict(&schema, &vec![], &user.name, &before, &after).unwrap();
    eprintln!(
        "{}",
        is_as_strict(&schema, &vec![], &user.name, &after, &before)
            .expect_err("strictness check should fail")
    );
}
