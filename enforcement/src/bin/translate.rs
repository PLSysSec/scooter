use policy_lang::*;
use std::io::{self, Read};

fn get_contents(fname: &str) -> io::Result<String> {
    let mut out = String::new();
    std::fs::File::open(fname)?.read_to_string(&mut out)?;
    Ok(out)
}
fn main() {
    let mut args = std::env::args();
    args.next().unwrap();
    let policy_file_in = args.next().unwrap();
    let parsed_policy = parse_policy(&get_contents(&policy_file_in).unwrap()).unwrap();

    let out = gen_schema_macros(parsed_policy);

    println!("{}", out);
}
fn gen_schema_macros(policy : ast::GlobalPolicy) -> String {
    let mut out = "pub use enforcement_macros::collection;\n".to_string();
    for col in policy.collections.into_iter() {
        let mut col_struct = format!(r#"
#[collection(policy_module="{}_policies")]
pub struct {} {{
"#,
                                     col.name.to_ascii_lowercase(),
                                     col.name).to_string();
        let mut pol_mod = format!(r#"
mod {}_policies {{
    use super::*;
"#,
                                  col.name.to_ascii_lowercase());
        for (field_name, field_policy) in col.fields.into_iter() {
            col_struct += &format!("    {}: String,\n", field_name).to_string();
            pol_mod += &format!("    pub fn {}(u: &{}) -> PolicyValue {{\n",
                                field_name, col.name).to_string();
            match field_policy.read {
                ast::Policy::Public =>
                    pol_mod += &"        PolicyValue::Public\n".to_string(),
                ast::Policy::None =>
                    pol_mod += &"        Ids([])\n".to_string(),
                _ => unimplemented!("No non trivial policies implemented"),
            };
            pol_mod += &"    }\n".to_string();
        }
        col_struct += &"}\n".to_string();
        pol_mod += &"}\n".to_string();
        out += &(col_struct + &pol_mod);
    }
    out
}
