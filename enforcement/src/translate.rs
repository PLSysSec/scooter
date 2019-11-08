use policy_lang::*;
use std::io::{self, Read};
use std::path::Path;
use std::fs::File;
use std::io::Write;
use std::env;

pub fn translate_policy_file(in_name: impl ToString,
                             out_name: impl ToString){
    let out_dir = env::var("OUT_DIR").unwrap();
    let dest_path = Path::new(&out_dir).join(out_name.to_string());
    let in_dir = env::current_dir().unwrap();
    let policy_path = Path::new(&in_dir).join(in_name.to_string());
    // panic!("{}, {}", policy_path.to_str().unwrap(), dest_path.to_str().unwrap());
    translate(policy_path, dest_path);
}

pub fn translate(policy_path: impl AsRef<Path>, out_path: impl AsRef<Path>) {
    let path = policy_path.as_ref();
    let parsed_policy = parse_policy(&get_contents(path).unwrap()).unwrap();
    let out = gen_schema_macros(parsed_policy);
    let mut f = File::create(&out_path).unwrap();
    f.write(out.as_bytes()).unwrap();
}

fn get_contents(fname: &Path) -> io::Result<String> {
    let mut out = String::new();
    std::fs::File::open(fname)?.read_to_string(&mut out)?;
    Ok(out)
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
        pol_mod += &format!(
            "    pub fn create({}: &{}) -> PolicyValue {{\n",
            policy_binder_var(&col.create),
            col.name).to_string();
        pol_mod += &gen_policy_body(col.create);
        pol_mod += &format!(
            "    pub fn delete({}: &{}) -> PolicyValue {{\n",
            policy_binder_var(&col.delete),
            col.name).to_string();
        pol_mod += &gen_policy_body(col.delete);
        for (field_name, field_policy) in col.fields.into_iter() {
            col_struct += &format!("    {}: {},\n", field_name, lower_ty(field_policy.ty)).to_string();
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
            "{}.into_iter().chain({}).collect()",
            policyfunc_to_idlist(*q1),
            policyfunc_to_idlist(*q2)
        ),
        ast::QueryExpr::Path(strings) => format!("{}.to_record_id_vec()", strings.join(".")),
    }
}

fn lower_ty(ty : ast::FieldType) -> String {
    match ty {
        ast::FieldType::Id(ty) => format!("TypedRecordId<{}>", ty).to_string(),
        _ => format!("{}", ty).to_string(),
    }
}
