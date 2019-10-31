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
fn policy_binder_var(policy: &ast::Policy) -> String {
    match policy {
        ast::Policy::Func(pfunc) => pfunc.param.clone(),
        _ => "_".to_string(),
    }
}
fn gen_policy_body(policy: ast::Policy) -> String {
    match policy {
        ast::Policy::Public => "        PolicyValue::Public\n    }\n".to_string(),
        ast::Policy::None => "        PolicyValue::Ids(vec![])\n    }\n".to_string(),
        ast::Policy::Func(f) => format!(
            "        PolicyValue::Ids({})\n    }}\n",
            policyfunc_to_idlist(*f.expr)
        ),
    }
}
fn gen_schema_macros(policy: ast::GlobalPolicy) -> String {
    let mut out = "use enforcement::*;\n".to_string();
    for col in policy.collections.into_iter() {
        let mut col_struct = format!(
            r#"
#[collection(policy_module="{}_policies")]
pub struct {} {{
"#,
            col.name.to_ascii_lowercase(),
            col.name
        )
        .to_string();
        let mut pol_mod = format!(
            r#"
mod {}_policies {{
    use super::*;
"#,
            col.name.to_ascii_lowercase()
        );
        for (field_name, field_policy) in col.fields.into_iter() {
            col_struct += &format!("    {}: String,\n", field_name).to_string();
            pol_mod += &format!(
                "    pub fn read_{}({}: &{}) -> PolicyValue {{\n",
                field_name,
                policy_binder_var(&field_policy.read),
                col.name
            )
            .to_string();
            pol_mod += &gen_policy_body(field_policy.read);
            pol_mod += &format!(
                "    pub fn write_{}({}: &{}) -> PolicyValue {{\n",
                field_name,
                policy_binder_var(&field_policy.write),
                col.name
            )
            .to_string();
            pol_mod += &gen_policy_body(field_policy.write);
        }
        col_struct += &"}\n".to_string();
        pol_mod += &"}\n".to_string();
        out += &(col_struct + &pol_mod);

        out += &format!("
#[macro_export]
macro_rules! {} {{
    ($($key:ident : $value:expr),*$(,)?) => {{{{
        {}::new({}Props {{
            $($key : $value),*
        }})
    }}}}
}}", col.name.to_ascii_lowercase(), col.name, col.name);
    }
    out
}
fn policyfunc_to_idlist(f: ast::QueryExpr) -> String {
    match f {
        ast::QueryExpr::Or(q1, q2) => format!(
            "{} + {}",
            policyfunc_to_idlist(*q1),
            policyfunc_to_idlist(*q2)
        ),
        ast::QueryExpr::Path(strings) => format!("{}.iter().cloned().collect()", strings.join(".")),
    }
}