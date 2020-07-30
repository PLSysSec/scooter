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
        @principle
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
    assert_eq!(policy.schema.principle.unwrap().orig_name, "User");
}

#[test]
#[should_panic(expected = "Type error: unable to coerce List(Id(User)) to List(Principle)")]
fn wrong_principle() {
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
    @principle
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
