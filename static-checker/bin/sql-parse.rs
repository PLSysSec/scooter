use sqlparser::parser::Parser;
use sqlparser::dialect::GenericDialect;

fn main() {
    let mut args = std::env::args();
    let dialect = GenericDialect {};

    let query = args.nth(1).expect("Please supply a query");
    let ast = Parser::parse_sql(&dialect, query.to_string()).expect("invalid sql query");
    println!("{:#?}", ast);
}