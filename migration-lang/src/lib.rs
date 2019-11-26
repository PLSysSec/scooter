pub mod ast;

use policy_lang::ast as policy_ast;
use policy_lang::*;
use lalrpop_util::lalrpop_mod;
use std::error::Error;
use std::path::Path;
use std::io::{self, Read, Write};
use std::fs::File;
use std::env;

use mongodb::oid::ObjectId;
pub use mongodb::{bson, doc};
use serde::{Serialize, Deserialize};

#[allow(dead_code)]
lalrpop_mod!(parser);


#[derive(Clone, Debug, Eq, PartialEq, Serialize, Deserialize)]
pub struct RecordId(ObjectId);

pub fn parse_migration<'a>(input: &'a str) -> Result<ast::CommandList, Box<dyn Error + 'a>> {
    parser::CommandListParser::new()
        .parse(input)
        .map_err::<Box<dyn Error>, _>(|e| Box::new(e))
}
pub fn translate_migration_file(policy_name: impl ToString,
                                migration_name: impl ToString,
                                out_name: impl ToString){
    let out_dir = env::var("OUT_DIR").unwrap();
    let dest_path = Path::new(&out_dir).join(out_name.to_string());
    let in_dir = env::current_dir().unwrap();
    let policy_path = Path::new(&in_dir).join(policy_name.to_string());
    let migration_path = Path::new(&in_dir).join(migration_name.to_string());
    translate_migration(policy_path, migration_path,
                        dest_path);
}
pub fn translate_migration(policy_path: impl AsRef<Path>, migration_path: impl AsRef<Path>,
                           out_path: impl AsRef<Path>){
    let parsed_policy =
        parse_policy(&get_contents(policy_path.as_ref()).unwrap()).unwrap();
    let parsed_migration =
        parse_migration(&get_contents(migration_path.as_ref()).unwrap()).unwrap();
    let out = gen_migration_macros(parsed_policy, parsed_migration);
    let mut f = File::create(&out_path).unwrap();
    f.write(out.as_bytes()).unwrap();
}
fn get_contents(fname: &Path) -> io::Result<String> {
    let mut out = String::new();
    std::fs::File::open(fname)?.read_to_string(&mut out)?;
    Ok(out)
}
fn gen_migration_macros(policy: policy_ast::GlobalPolicy, migration: ast::CommandList) -> String {
    "".to_string()
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
                   CommandList(vec![Command::RemoveColumn{
                       table:"User".to_string(),
                       col:"num_followers".to_string()
                   }]));
    }
}
