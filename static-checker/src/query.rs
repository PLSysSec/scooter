/// This module contains all the logic for query manipulation and generating SMT
/// assertions

use sqlparser::parser::Parser;
use sqlparser::dialect::GenericDialect;
use sqlparser::ast::{Statement, Query, SetExpr, Select};
use std::string::ToString;

/// Converts a SQL query to an SMTLIB expression in our logic
pub fn to_smt(sql: impl ToString) -> String {
    let dialect = GenericDialect {};

    let ast = Parser::parse_sql(&dialect, sql.to_string()).expect("invalid sql query");

    if ast.len() != 1 {
        panic!("Exactly one query required. {} given", ast.len())
    }

    let query = match ast[0] {
        Statement::Query(ref q) => q,
        _ => unimplemented!("Only SELECT queries are supported")
    };

    ast_to_smt(query)
}

pub fn ast_to_smt(query: &Query) -> String {
    let Query {ctes, body, order_by, limit, offset, fetch} = query;
    if !ctes.is_empty() {
        unimplemented!("WITH clauses aren't supported (yet?)")
    }

    if !order_by.is_empty() {
        unimplemented!("ORDER BY is not handled (but should be safe to just omit for policies)")
    }

    if limit.is_some() {
        unimplemented!("LIMIT not supported (by the underlying theory)")
    }

    if offset.is_some() {
        unimplemented!("OFFSET not supported (by the underlying theory)")
    }

    if fetch.is_some() {
        unimplemented!("FETCH not supported (by the underlying theory)")
    }

    match body {
        SetExpr::Query(q) => ast_to_smt(q),
        SetExpr::Select(s) => select_to_smt(s),
        SetExpr::SetOperation {..} => unimplemented!("Set operations not supported"),
        SetExpr::Values(..) => unimplemented!("Raw values not supported")
    }
}

fn select_to_smt(sel: &Select) -> String {
    unimplemented!()
}