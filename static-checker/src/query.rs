use sqlparser::dialect::GenericDialect;
/// This module contains all the logic for query manipulation and generating SMT
/// assertions
use sqlparser::parser::Parser;

use sqlparser::ast::{
    BinaryOperator, ColumnDef, Expr, Query, Select, SelectItem, SetExpr, Statement, TableFactor
};

use std::string::ToString;

/// Converts a SQL query to an SMTLIB expression in our logic
pub fn to_smt(sql: impl ToString, col_defs: Vec<ColumnDef>) -> String {
    let dialect = GenericDialect {};

    let ast = Parser::parse_sql(&dialect, sql.to_string()).expect("invalid sql query");

    if ast.len() != 1 {
        panic!("Exactly one query required. {} given", ast.len())
    }

    let query = match ast[0] {
        Statement::Query(ref q) => q,
        _ => unimplemented!("Only SELECT queries are supported"),
    };

    ast_to_smt(query, col_defs)
}

pub fn ast_to_smt(query: &Query, col_defs: Vec<ColumnDef>) -> String {
    let Query {
        ctes,
        body,
        order_by,
        limit,
        offset,
        fetch,
    } = query;
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
        SetExpr::Query(q) => ast_to_smt(q, col_defs),
        SetExpr::Select(s) => select_to_smt(s, col_defs),
        SetExpr::SetOperation { .. } => unimplemented!("Set operations not supported"),
        SetExpr::Values(..) => unimplemented!("Raw values not supported"),
    }
}

const NUMBERS: [&str; 8] = [
    "zero", "one", "two", "three", "four", "five", "six", "seven",
];

fn id_to_col_num(id: &str, col_defs: Vec<ColumnDef>) -> &str {
    for (idx, col) in col_defs.iter().enumerate() {
        if col.name == *id {
            assert!(idx < NUMBERS.len());
            return NUMBERS[idx];
        }
    }
    unimplemented!()
}

fn select_to_smt(sel: &Select, col_defs: Vec<ColumnDef>) -> String {
    if sel.distinct {
        unimplemented!();
    }
    if sel.projection.len() > 1 {
        unimplemented!();
    }
    match &sel.projection[0] {
        SelectItem::Wildcard => (),
        _ => unimplemented!(),
    };
    if sel.from.len() > 1 {
        unimplemented!();
    }
    let table_name = match &sel.from[0].relation {
        TableFactor::Table { name, .. } => format!("{}", name),
        _ => unimplemented!(),
    };
    if !sel.from[0].joins.is_empty() {
        unimplemented!();
    }
    match &sel.selection {
        None => (),
        Some(e) => match &e {
            Expr::BinaryOp { left, op, right } => match &**left {
                Expr::Identifier(id) => match op {
                    BinaryOperator::Eq => match &**right {
                        Expr::Value(v) => {
                            return format!("(sel-eqv {} {} {})",
                                           id_to_col_num(&id, col_defs),
                                           v, table_name)
                        }
                        _ => unimplemented!(),
                    },
                    _ => unimplemented!(),
                },
                _ => unimplemented!(),
            },
            _ => unimplemented!(),
        },
    };
    if !sel.group_by.is_empty() {
        unimplemented!();
    }
    match &sel.having {
        None => (),
        Some(_) => unimplemented!(),
    };
    table_name
}

#[test]
fn whole_table_select() {
    let sql_stmt = "SELECT * FROM t1";
    let smt = to_smt(sql_stmt, vec!());
    assert!(smt == "t1");
}


// Eventually this should output symbol names instead of strings,
// where we map literal strings to these symbols, but for now just
// outputting the string (which won't typecheck in the theory).
#[test]
fn select_col_value() {
    use sqlparser::ast::DataType;
    let sql_stmt = "SELECT * FROM t1 WHERE name = 'foo'";
    let col_def = ColumnDef{
        name: "name".to_string(),
        data_type: DataType::Text,
        collation: None,
        options: vec!()};
    let smt = to_smt(sql_stmt, vec!(col_def));
    assert_eq!(smt,"(sel-eqv zero 'foo' t1)");
}
