pub mod ast;

use lalrpop_util::lalrpop_mod;
use std::error::Error;


#[allow(dead_code)]
lalrpop_mod!(parser);

pub fn parse_migration<'a>(input: &'a str) -> Result<ast::CommandList, Box<dyn Error + 'a>> {
    parser::CommandListParser::new()
        .parse(input)
        .map_err::<Box<dyn Error>, _>(|e| Box::new(e))
}
#[cfg(test)]
mod tests {
    use super::*;
    use ast::*;

    #[test]
    fn simple_migration() {
        let p = parse_migration(
            r#"
            User::RemoveColumn(num_followers)
            "#).unwrap();

        assert_eq!(p,
                   CommandList(vec![Command{
                       table:"User".to_string(),
                       action:CommandAction::RemoveColumn{
                           col:"num_followers".to_string()
                       }}]));
    }
}
