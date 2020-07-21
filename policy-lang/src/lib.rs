pub mod ast;
pub mod ir;

use lalrpop_util::lalrpop_mod;
use std::error::Error;

#[allow(dead_code, unused_parens)]
lalrpop_mod!(parser);

pub type GlobalPolicyParseTree = ast::GlobalPolicy;
pub fn parse_policy<'a>(input: &'a str) -> Result<GlobalPolicyParseTree, String> {
    let stripped_input = input.lines().filter(
        |line|
        line.split("#").next().unwrap().trim() != "").collect::<Vec<&str>>().join("\n");
    parser::GlobalPolicyParser::new()
        .parse(&stripped_input)
        .map_err::<String, _>(|e| format!("{}", e))
}
pub fn parse_migration<'a>(input: &'a str) -> Result<ast::Migration, Box<dyn Error + 'a>> {
    parser::MigrationParser::new()
        .parse(input)
        .map_err::<Box<dyn Error>, _>(|e| Box::new(e))
}

pub fn parse_func<'a>(input: &'a str) -> Result<ast::Func, Box<dyn Error + 'a>> {
    parser::FuncParser::new()
        .parse(input)
        .map_err::<Box<dyn Error>, _>(|e| Box::new(e))
}

#[cfg(test)]
mod tests {
    use super::*;
    use ast::*;

    #[test]
    fn simple_policy() {
        let p = parse_policy(
            r#"
            # This is the user principle, and a full line comment
            @principle
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
                collections: vec![CollectionPolicy {
                    name: "User".to_string(),
                    create: Policy::Public,
                    delete: Policy::None,
                    annotations: vec![Annotation::Principle],
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
                                        expr: Box::new(QueryExpr::List(vec![Box::new(
                                            QueryExpr::FieldAccess(
                                                Box::new(QueryExpr::Var("u".to_string())),
                                                "id".to_string(),
                                            ),
                                        )])),
                                    }),
                                    write: Policy::Func(Func {
                                        param: "u".to_string(),
                                        expr: Box::new(QueryExpr::List(vec![Box::new(
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
