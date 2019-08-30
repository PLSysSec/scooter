use sqlparser::dialect::GenericDialect;
/// This module contains all the logic for query manipulation and generating SMT
/// assertions
use sqlparser::parser::Parser;

use sqlparser::ast::{
    BinaryOperator, Expr, Query, Select, SelectItem, SetExpr, Statement, TableFactor,
};

use crate::Schema;
use std::string::ToString;

/// Converts a SQL query to an SMTLIB expression in our logic
pub fn to_smt(sql: impl ToString, schema: &Schema) -> String {
    let dialect = GenericDialect {};

    let ast = Parser::parse_sql(&dialect, sql.to_string()).expect("invalid sql query");

    if ast.len() != 1 {
        panic!("Exactly one query required. {} given", ast.len())
    }

    let query = match ast[0] {
        Statement::Query(ref q) => q,
        _ => unimplemented!("Only SELECT queries are supported"),
    };

    ast_to_smt(query, schema)
}

pub fn ast_to_smt(query: &Query, schema: &Schema) -> String {
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
        SetExpr::Query(q) => ast_to_smt(q, schema),
        SetExpr::Select(s) => select_to_smt(s, schema),
        SetExpr::SetOperation { .. } => unimplemented!("Set operations not supported"),
        SetExpr::Values(..) => unimplemented!("Raw values not supported"),
    }
}

const NUMBERS: [&str; 8] = [
    "zero", "one", "two", "three", "four", "five", "six", "seven",
];

fn id_to_col_num(id: &str, table_name: &String, schema: &Schema) -> usize {
    schema.tables[&table_name.to_string()]
        .fields
        .iter()
        .position(|field| field.name == id)
        .expect("field does not exist on table")
}

fn select_to_smt(sel: &Select, schema: &Schema) -> String {
    if sel.distinct {
        unimplemented!();
    }
    if sel.projection.len() > 1 {
        unimplemented!();
    }

    if sel.projection[0] != SelectItem::Wildcard {
        unimplemented!("Only wildcard selects are supported");
    }

    if sel.from.len() > 1 {
        unimplemented!();
    }

    if !sel.from[0].joins.is_empty() {
        unimplemented!();
    }

    if !sel.group_by.is_empty() {
        unimplemented!("GROUP BY not supported")
    }

    let table_name = match &sel.from[0].relation {
        TableFactor::Table { name, .. } => format!("{}", name),
        _ => unimplemented!(),
    };

    if sel.selection.is_none() {
        return table_name;
    }

    if let Expr::BinaryOp {
        left,
        op: BinaryOperator::Eq,
        right,
    } = sel.selection.as_ref().unwrap()
    {
        let (id, v) = match (left.as_ref(), right.as_ref()) {
            // Accept things in either order
            (Expr::Identifier(id), Expr::Value(v)) | (Expr::Value(v), Expr::Identifier(id)) => {
                (id, v)
            }
            _ => unimplemented!("Only equalities of identifiers to values are supported"),
        };

        return format!(
            "(sel-eqv {} {} {})",
            NUMBERS[id_to_col_num(&id, &table_name, schema)],
            v,
            table_name
        );
    }

    unimplemented!("Only 'id = value' WHERE clauses are supported");
}

#[test]
fn whole_table_select() {
    let sql_stmt = "SELECT * FROM t1";
    let schema: Schema = toml::from_str(r#"t1 = ["name"]"#).unwrap();
    let smt = to_smt(sql_stmt, &schema);
    assert_eq!(smt, "t1");
}

// Eventually this should output symbol names instead of strings,
// where we map literal strings to these symbols, but for now just
// outputting the string (which won't typecheck in the theory).
#[test]
fn select_col_value() {
    let sql_stmt = "SELECT * FROM t1 WHERE name = 'foo'";
    let schema: Schema = toml::from_str(r#"t1 = ["name"]"#).unwrap();

    let smt = to_smt(sql_stmt, &schema);
    assert_eq!(smt, "(sel-eqv zero 'foo' t1)");
}
