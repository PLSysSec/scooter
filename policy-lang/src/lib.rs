pub mod ast;
pub mod ir;

use lalrpop_util::lalrpop_mod;

#[allow(dead_code, unused_parens)]
lalrpop_mod!(parser);

pub type GlobalPolicyParseTree = ast::GlobalPolicy;
pub fn parse_policy<'a>(input: &'a str) -> Result<GlobalPolicyParseTree, String> {
    let stripped_input = input
        .lines()
        .filter(|line| line.split("#").next().unwrap().trim() != "")
        .collect::<Vec<&str>>()
        .join("\n");
    parser::GlobalPolicyParser::new()
        .parse(&stripped_input)
        .map_err::<String, _>(|e| format!("{}", e))
}
pub fn parse_migration<'a>(input: &'a str) -> Result<ast::Migration, String> {
    let stripped_input = input
        .lines()
        .filter(|line| line.split("#").next().unwrap().trim() != "")
        .collect::<Vec<&str>>()
        .join("\n");
    parser::MigrationParser::new()
        .parse(&stripped_input)
        .map_err::<String, _>(|e| format!("{}", e))
}

pub fn parse_func<'a>(input: &'a str) -> Result<ast::Func, String> {
    let stripped_input = input
        .lines()
        .filter(|line| line.split("#").next().unwrap().trim() != "")
        .collect::<Vec<&str>>()
        .join("\n");
    parser::FuncParser::new()
        .parse(&stripped_input)
        .map_err::<String, _>(|e| format!("{}", e))
}

#[cfg(test)]
mod tests {
    use super::*;
    use ast::*;

    #[test]
    fn simple_policy() {
        let p = parse_policy(
            r#"
            # This is a static principal for authentication
            @static-principal
            Authenticator
            # This is the user principal
            @principal
            User {
                create: public,
                delete: none,
                name : String {
                    read: public,
                    write: none,
                },

                pass_hash : String {
                    read: u -> [u.id],
                    write: u -> [u.id],
                },
            }
        "#,
        )
        .unwrap();

        assert_eq!(
            p,
            GlobalPolicy {
                static_principals: vec![StaticPrincipal {
                    name: "Authenticator".to_string()
                }],
                collections: vec![CollectionPolicy {
                    name: "User".to_string(),
                    create: Policy::Public,
                    delete: Policy::None,
                    annotations: vec![Annotation::Principal],
                    fields: {
                        vec![
                            (
                                "name".to_string(),
                                FieldPolicy {
                                    ty: FieldType::String,
                                    read: Policy::Public,
                                    write: Policy::None,
                                },
                            ),
                            (
                                "pass_hash".to_string(),
                                FieldPolicy {
                                    ty: FieldType::String,
                                    read: Policy::Func(Func {
                                        param: "u".to_string(),
                                        expr: Box::new(QueryExpr::Set(vec![Box::new(
                                            QueryExpr::FieldAccess(
                                                Box::new(QueryExpr::Var("u".to_string())),
                                                "id".to_string(),
                                            ),
                                        )])),
                                    }),
                                    write: Policy::Func(Func {
                                        param: "u".to_string(),
                                        expr: Box::new(QueryExpr::Set(vec![Box::new(
                                            QueryExpr::FieldAccess(
                                                Box::new(QueryExpr::Var("u".to_string())),
                                                "id".to_string(),
                                            ),
                                        )])),
                                    }),
                                },
                            ),
                        ]
                    }
                }]
            }
        )
    }
    #[test]
    fn simple_migration() {
        let p = parse_migration(
            r#"
            User::RemoveField(num_followers)
            "#,
        )
        .unwrap();

        assert_eq!(
            p,
            Migration(vec![MigrationCommand::CollAction {
                table: "User".to_string(),
                action: MigrationAction::RemoveField {
                    field: "num_followers".to_string()
                }
            }])
        );
    }
}
