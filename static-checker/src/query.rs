use sqlparser::dialect::GenericDialect;
/// This module contains all the logic for query manipulation and generating SMT
/// assertions
use sqlparser::parser::Parser;

use sqlparser::ast::{
    BinaryOperator, Expr, Query, Select, SelectItem, SetExpr, Statement, TableFactor, Value, TableWithJoins
};
use std::collections::HashMap;
use crate::Schema;
use crate::relation::Relation;

use std::string::ToString;

/// ValueMap is used for keeping a record of all encountered literal SQL values, and mapping them
/// to fresh SMT identifiers
#[derive(Debug, Default)]
struct ValueMap {
    values: HashMap<Value, String>,
    val_ct: u32,
}

impl ValueMap {
    fn new() -> Self {
        Default::default()
    }
    /// Attempts to look up the value in the accumulated index of values. Because
    /// values are abstract in SMT we need to produce the same identifier for the
    /// same literal value. This function attempts to look up the value in our
    /// index, inserting it if we've never encountered it before, and returns an
    /// SMT-safe identifier.
    ///
    /// Currently this function emits identifiers like: v1_foo
    fn get_or_insert(&mut self, v: &Value) -> &str {
        let val_ct = &mut self.val_ct;
        self.values.entry(v.clone()).or_insert_with(|| {
            let v_name = format!("v{}_{}", *val_ct, alphanumericize(v.to_string()));
            *val_ct += 1;
            v_name
        })
    }
}

/// Removes all non-alphanumeric characters from a string
fn alphanumericize(mut desc: String) -> String {
    desc.retain(|c| char::is_ascii_alphanumeric(&c));
    desc
}



/// SmtBuilder contains all the information necessary to convert a SQL query into
/// an SMT assertion
#[derive(Debug)]
pub struct SmtBuilder<'a> {
    schema: &'a Schema,
    
    values: ValueMap,
}

impl Schema {
    /// A convenience method for getting an SmtBuilder for a schema
    pub fn builder(&self) -> SmtBuilder {
        SmtBuilder { schema: self, values: ValueMap::new()}
    }
}

const NUMBERS: [&str; 8] = [
    "zero", "one", "two", "three", "four", "five", "six", "seven",
];

impl<'a> SmtBuilder<'a> {
    /// Converts a SQL query to an SMTLIB expression in our logic
    pub fn to_smt(&mut self, sql: impl ToString) -> String {
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

    fn ast_to_smt(&mut self, query: &Query) -> String {
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

    fn from_to_smt(&mut self, from: &[TableWithJoins]) -> String {
        if from.len() != 1 {
            unimplemented!("only selections from single tables are supported");
        }

        if !from[0].joins.is_empty() {
            unimplemented!("JOIN in the from clause is not supported");
        }

        match &from[0].relation {
            TableFactor::Table { name, .. } => format!("{}", name),
            _ => unimplemented!(),
        }
    }

    fn selection_to_smt(&mut self, wher: &Option<Expr>, src: &Vec<TableWithJoins>) -> String {
        // Get the query which we'll be filtering with this WHERE clause
        let relation = self.from_to_smt(&src);

        // If we're not filtering we can just return the underlying relation
        if wher.is_none() {
            relation     
        } else if let Expr::BinaryOp {
            left,
            op: BinaryOperator::Eq,
            right,
        } = wher.as_ref().unwrap()
        {
            let (id, v) = match (left.as_ref(), right.as_ref()) {
                // Accept things in either order
                (Expr::Identifier(id), Expr::Value(v)) | (Expr::Value(v), Expr::Identifier(id)) => {
                    (id, v)
                }
                _ => unimplemented!("Only equalities of identifiers to values are supported"),
            };

            format!(
                "(sel-eqv {} {} {})",
                NUMBERS[src.resolve_name(self.schema, id)],
                self.values.get_or_insert(v),
                relation 
            )
        } else {
            unimplemented!("Only 'id = value' WHERE clauses are supported")
        }
    }

    fn select_to_smt(&mut self, sel: &Select) -> String {
        if sel.distinct {
            unimplemented!("DISTINCT is not supported");
        }

        if !sel.group_by.is_empty() {
            unimplemented!("GROUP BY not supported")
        }

        // Construct the underlying relation
        let relation = self.selection_to_smt(&sel.selection, &sel.from);

        // If we're selecting everything we don't need to project
        if let [SelectItem::Wildcard] = sel.projection.as_slice() {
            return relation;
        }

        let indices: Vec<_> = sel.projection.iter().map(|si| {
            match si {
                SelectItem::UnnamedExpr(Expr::Identifier(i)) => sel.from.resolve_name(&self.schema, &i),
                _ => unimplemented!("Only raw identifiers are allowed for projection")
            }
        }).collect();


        return format!("(proj {} {})", attr_list(&indices), relation);
    }
}

/// Constructs an attr list from a slice of column indices. This is necessary for projection
fn attr_list(indices: &[usize]) -> String {
    indices.iter().fold("l_nil".to_string(), |query, num| {
        format!("(insert {} {})", NUMBERS[*num], query)
    })
}


#[test]
fn whole_table_select() {
    let schema: Schema = toml::from_str(r#"t1 = ["name"]"#).unwrap();

    let sql_stmt = "SELECT * FROM t1";
    let smt = schema.builder().to_smt(sql_stmt);
    assert_eq!(smt, "t1");
}


#[test]
fn field_select() {
    let schema: Schema = toml::from_str(r#"t1 = ["id", "name"]"#).unwrap();

    let sql_stmt = "SELECT name FROM t1";
    let smt = schema.builder().to_smt(sql_stmt);
    assert_eq!(smt, "(proj (insert one l_nil) t1)");
}
        

#[test]
fn select_col_value() {
    let schema: Schema = toml::from_str(r#"t1 = ["name"]"#).unwrap();

    let sql_stmt = "SELECT * FROM t1 WHERE name = 'foo'";
    let smt = schema.builder().to_smt(sql_stmt);
    assert_eq!(smt, "(sel-eqv zero v0_foo t1)");


    let sql_stmt_rev = "SELECT * FROM t1 WHERE 'foo' = name";
    let smt = schema.builder().to_smt(sql_stmt_rev);
    assert_eq!(smt, "(sel-eqv zero v0_foo t1)");
}