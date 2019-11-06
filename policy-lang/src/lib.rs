pub mod ast;
pub mod ir;

use lalrpop_util::lalrpop_mod;
use std::error::Error;

#[allow(dead_code)]
lalrpop_mod!(parser);

pub type GlobalPolicyParseTree = ast::GlobalPolicy;
pub fn parse_policy<'a>(input: &'a str) -> Result<GlobalPolicyParseTree, Box<dyn Error + 'a>> {
    parser::GlobalPolicyParser::new()
        .parse(input)
        .map_err::<Box<dyn Error>, _>(|e| Box::new(e))
}

#[cfg(test)]
mod tests {
    use super::*;
    use ast::*;
    use std::collections::HashMap;

    #[test]
    fn simple_policy() {
        let p = parse_policy(
            r#"
            User {
                name : String {
                    read: public
                    write: none
                }

                pass_hash : String {
                    read: u -> u.id
                    write: u -> u.id
                }
            }
        "#,
        )
        .unwrap();

        assert_eq!(
            p,
            GlobalPolicy {
                collections: vec![CollectionPolicy {
                    name: "User".to_string(),
                    fields: {
                        let mut h = HashMap::new();
                        h.insert(
                            "name".to_string(),
                            FieldPolicy {
                                ty: FieldType::String,
                                read: Policy::Public,
                                write: Policy::None,
                            },
                        );
                        h.insert(
                            "pass_hash".to_string(),
                            FieldPolicy {
                                ty: FieldType::String,
                                read: Policy::Func(PolicyFunc {
                                    param: "u".to_string(),
                                    expr: Box::new(QueryExpr::Path(vec![
                                        "u".to_string(),
                                        "id".to_string(),
                                    ])),
                                }),
                                write: Policy::Func(PolicyFunc {
                                    param: "u".to_string(),
                                    expr: Box::new(QueryExpr::Path(vec![
                                        "u".to_string(),
                                        "id".to_string(),
                                    ])),
                                }),
                            },
                        );
                        h
                    }
                }]
            }
        )
    }
}
