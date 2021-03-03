use policy_lang::{
    self,
    ir::policy::{extract_schema_policy, SchemaPolicy},
};

fn test_policy(pol: &str) -> SchemaPolicy {
    let pol = policy_lang::parse_policy(pol).unwrap();
    extract_schema_policy(&pol)
}

#[test]
fn simple_valid() {
    let policy = test_policy(
        r#"
        @principal
        User {
            create: public,
            delete: none,

            name: String {
                read: u -> [u.id] + public,
                write: none,
            },
        }
    "#,
    );

    assert_eq!(policy.schema.collections[0].name.orig_name, "User");
    assert_eq!(
        policy
            .schema
            .dynamic_principals
            .iter()
            .map(|dp| dp.orig_name.clone())
            .collect::<Vec<_>>(),
        vec!["User"]
    );
}
#[test]
fn two_principals() {
    let policy = test_policy(
        r#"
        @principal
        Service {
            create: public,
            delete: s -> [s.owner, s.id],

            owner: Id(User) {
                read: public,
                write: s -> [s.owner],
            },
        }
        @principal
        User {
            create: public,
            delete: none,

            name: String {
                read: u -> [u.id] + public,
                write: none,
            },
        }
    "#,
    );

    assert_eq!(
        policy
            .schema
            .collections
            .iter()
            .map(|coll| coll.name.orig_name.clone())
            .collect::<Vec<_>>(),
        vec!["Service", "User"]
    );
    assert_eq!(
        policy
            .schema
            .dynamic_principals
            .iter()
            .map(|dp| dp.orig_name.clone())
            .collect::<Vec<_>>(),
        vec!["Service", "User"]
    );
}

#[test]
#[should_panic(expected = "Type error: unable to coerce Set(Id(User)) to Set(Principal)")]
fn wrong_principal() {
    test_policy(
        r"User {
    create: none,
    delete: none,

    username : String {
        read: public,
        write: none,
    },
    pass_hash : String {
        read: public,
        write: u -> [u.id],
    },
}
",
    );
}
#[test]
fn big() {
    test_policy(
        r#"
    @principal
    User {
        create: public,
        delete: none,

        trustworthyness : I64 {
            read: m -> [m.id],
            write: none,
        },
    }
    Message {
        create: public,
        delete: none,
        from : Id(User) {
            read: m -> [m.from, m.to],
            write: none,
        },

        to : Id(User) {
            read: m -> [m.to, m.from],
            write: m -> (if User::ById(m.to).trustworthyness > 20 then [m.to] else []),
        },

        text : String {
            read: m -> [(if true then m.from else m.to)],
            write: m -> (if m.to != m.from then [] else [m.to]),
        },
    }"#,
    );
}
