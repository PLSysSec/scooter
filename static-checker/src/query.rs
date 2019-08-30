use sqlparser::dialect::GenericDialect;
/// This module contains all the logic for query manipulation and generating SMT
/// assertions
use sqlparser::parser::Parser;

use sqlparser::ast::{
    BinaryOperator, Expr, Query, Select, SelectItem, SetExpr, Statement, TableFactor,
};

use crate::Schema;
use std::string::ToString;

/// SmtBuilder contains all the information necessary to convert a SQL query into
/// an SMT assertion
pub struct SmtBuilder<'a> {
    schema: &'a Schema,
}

impl Schema {
    /// A convenience method for getting an SmtBuilder for a schema
    pub fn builder(&self) -> SmtBuilder {
        SmtBuilder { schema: self }
    }
}

const NUMBERS: [&str; 8] = [
    "zero", "one", "two", "three", "four", "five", "six", "seven",
];

impl<'a> SmtBuilder<'a> {
    /// Converts a SQL query to an SMTLIB expression in our logic
    pub fn to_smt(&self, sql: impl ToString) -> String {
        let dialect = GenericDialect {};

        let ast = Parser::parse_sql(&dialect, sql.to_string()).expect("invalid sql query");

        if ast.len() != 1 {
            panic!("Exactly one query required. {} given", ast.len())
        }

        let query = match ast[0] {
            Statement::Query(ref q) => q,
            _ => unimplemented!("Only SELECT queries are supported"),
        };

        self.ast_to_smt(query)
    }

    fn ast_to_smt(&self, query: &Query) -> String {
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
            SetExpr::Query(q) => self.ast_to_smt(q),
            SetExpr::Select(s) => self.select_to_smt(s),
            SetExpr::SetOperation { .. } => unimplemented!("Set operations not supported"),
            SetExpr::Values(..) => unimplemented!("Raw values not supported"),
        }
    }

    fn id_to_col_num(&self, id: &str, table_name: &String) -> usize {
        self.schema.tables[&table_name.to_string()]
            .fields
            .iter()
            .position(|field| field.name == id)
            .expect("field does not exist on table")
    }

    fn select_to_smt(&self, sel: &Select) -> String {
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
                NUMBERS[self.id_to_col_num(&id, &table_name)],
                v,
                table_name
            );
        }

        unimplemented!("Only 'id = value' WHERE clauses are supported");
    }
}

#[test]
fn whole_table_select() {
    let sql_stmt = "SELECT * FROM t1";
    let schema: Schema = toml::from_str(r#"t1 = ["name"]"#).unwrap();
    let smt = schema.builder().to_smt(sql_stmt);
    assert_eq!(smt, "t1");
}

// Eventually this should output symbol names instead of strings,
// where we map literal strings to these symbols, but for now just
// outputting the string (which won't typecheck in the theory).
#[test]
fn select_col_value() {
    let schema: Schema = toml::from_str(r#"t1 = ["name"]"#).unwrap();

    let sql_stmt = "SELECT * FROM t1 WHERE name = 'foo'";
    let smt = schema.builder().to_smt(sql_stmt);
    assert_eq!(smt, "(sel-eqv zero 'foo' t1)");


    let sql_stmt_rev = "SELECT * FROM t1 WHERE 'foo' = name";
    let smt = schema.builder().to_smt(sql_stmt_rev);
    assert_eq!(smt, "(sel-eqv zero 'foo' t1)");
}
