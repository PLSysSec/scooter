pub mod ast;
pub mod ir;

use std::fmt::Display;

use lalrpop_util::{self, lalrpop_mod, state_machine::Token};
use serde::Serialize;

#[allow(dead_code, unused_parens)]
lalrpop_mod!(parser);
pub type GlobalPolicyParseTree = ast::GlobalPolicy;
pub fn parse_policy<'a>(input: &'a str) -> Result<GlobalPolicyParseTree, ParseError> {
    parser::GlobalPolicyParser::new()
        .parse(&input)
        .map_err(|e| error_from_lalr(input, e))
}
pub fn parse_migration<'a>(input: &'a str) -> Result<ast::Migration, ParseError> {
    parser::MigrationParser::new()
        .parse(&input)
        .map_err(|e| error_from_lalr(input, e))
}

pub fn parse_func<'a>(input: &'a str) -> Result<ast::Func, ParseError> {
    parser::FuncParser::new()
        .parse(&input)
        .map_err(|e| error_from_lalr(input, e))
}

#[derive(Debug, Serialize)]
pub struct ParseError {
    pub start: Option<Location>,
    pub end: Option<Location>,
    pub message: String,
}

#[derive(Debug, Serialize)]
pub struct Location {
    pub line: usize,
    pub column: usize,
}

fn error_from_lalr(
    input: &str,
    lalr_err: lalrpop_util::ParseError<usize, parser::Token, &'_ str>,
) -> ParseError {
    let (start, end) = match lalr_err {
        lalrpop_util::ParseError::InvalidToken { location } => (Some(location), None),
        lalrpop_util::ParseError::UnrecognizedEOF { location, .. } => (Some(location), None),
        lalrpop_util::ParseError::UnrecognizedToken { ref token, .. }
        | lalrpop_util::ParseError::ExtraToken { ref token, .. } => (Some(token.0), Some(token.2)),
        lalrpop_util::ParseError::User { .. } => (None, None),
    };

    let offset_to_location = |offset| {
        let (prefix, _) = input.split_at(offset);
        let line = prefix.chars().filter(|c| *c == '\n').count();
        let column = prefix
            .chars()
            .rev()
            .enumerate()
            .find(|(_, c)| *c == '\n')
            .map(|(idx, _)| idx)
            .unwrap_or(prefix.len());

        Location { line, column }
    };

    let start = start.map(offset_to_location);
    let end = end.map(offset_to_location);

    let message = format!("{:?}", lalr_err);

    ParseError {
        start,
        end,
        message,
    }
}

impl Display for ParseError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.message)
    }
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
