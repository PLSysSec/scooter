use policy_lang::ir::expr::{ExprType, FieldComparison, Func, IRExpr};
use policy_lang::ir::policy::*;
use policy_lang::ir::schema::Schema;
use policy_lang::ir::Ident;
use policy_lang::parse_policy;
use std::env;
use std::fs::File;
use std::io::Write;
use std::io::{self, Read};
use std::path::Path;

use chrono::{Datelike, Timelike};

pub fn translate_policy_file(in_name: impl ToString, out_name: impl ToString) {
    let out_dir = env::var("OUT_DIR").unwrap();
    let dest_path = Path::new(&out_dir).join(out_name.to_string());
    let in_dir = env::current_dir().unwrap();
    let policy_path = Path::new(&in_dir).join(in_name.to_string());
    translate(policy_path, dest_path);
}

pub fn translate(policy_path: impl AsRef<Path>, out_path: impl AsRef<Path>) {
    let path = policy_path.as_ref();
    let parsed_policy = parse_policy(&get_contents(path).unwrap()).expect(&format!(
        "Couldn't parse policy at {}",
        path.to_str().unwrap()
    ));
    let schema_policy = extract_schema_policy(&parsed_policy);
    let out = gen_schema_macros(schema_policy);
    let mut f = File::create(&out_path).unwrap();
    f.write(out.as_bytes()).unwrap();
}

fn get_contents(fname: &Path) -> io::Result<String> {
    let mut out = String::new();
    std::fs::File::open(fname)?.read_to_string(&mut out)?;
    Ok(out)
}

fn policy_binder_var(policy: &Policy) -> String {
    match policy {
        Policy::Func(Func { param, .. }) => mangled_ident(param),
        _ => "_".to_string(),
    }
}
fn mangled_ident<T>(ident: &Ident<T>) -> String {
    format!("i_{}_{}", ident.index, ident.orig_name)
}
fn gen_policy_body(schema: &Schema, policy: &Policy) -> String {
    match policy {
        Policy::Anyone => "        PolicyValue::Public\n    }\n".to_string(),
        Policy::None => "        PolicyValue::Set(vec![])\n    }\n".to_string(),
        Policy::Func(Func { body, .. }) => format!(
            "        {}.into()\n    }}\n",
            translate_queryexpr_to_idlist(schema, body)
        ),
    }
}
fn gen_schema_macros(sp: SchemaPolicy) -> String {
    let mut out = "use enforcement::{gen_prelude::*, *};\n".to_string();
    for (coll, coll_policy) in sp.collection_policies.iter() {
        let mut col_struct = format!(
            r#"
#[collection(policy_module="{}_policies")]
pub struct {} {{
"#,
            coll.orig_name.to_ascii_lowercase(),
            coll.orig_name
        )
        .to_string();
        let mut pol_mod = format!(
            r#"
mod {}_policies {{
    use super::*;
"#,
            coll.orig_name.to_ascii_lowercase()
        );
        pol_mod += &format!("    #[allow(unused_variables)]").to_string();

        pol_mod += &format!(
            "    pub fn create({}: &{}, conn: &AuthConn) -> PolicyValue {{\n",
            policy_binder_var(&coll_policy.create),
            coll.orig_name
        )
        .to_string();
        pol_mod += &gen_policy_body(&sp.schema, &coll_policy.create);
        pol_mod += &format!("    #[allow(unused_variables)]").to_string();
        pol_mod += &format!(
            "    pub fn delete({}: &{}, conn: &AuthConn) -> PolicyValue {{\n",
            policy_binder_var(&coll_policy.delete),
            coll.orig_name
        )
        .to_string();
        pol_mod += &gen_policy_body(&sp.schema, &coll_policy.delete);
        for field in sp.schema[coll].fields() {
            if field.name.orig_name == "id" {
                continue;
            }
            let field_policy = &sp.field_policies[&field.name];
            col_struct +=
                &format!("    {}: {},\n", field.name.orig_name, lower_ty(&field.typ)).to_string();
            pol_mod += &format!("    #[allow(unused_variables)]").to_string();
            pol_mod += &format!(
                "    pub fn read_{}({}: &{}, conn: &AuthConn) -> PolicyValue {{\n",
                field.name.orig_name,
                policy_binder_var(&field_policy.read),
                coll.orig_name
            )
            .to_string();
            pol_mod += &gen_policy_body(&sp.schema, &field_policy.read);
            pol_mod += &format!("    #[allow(unused_variables)]").to_string();
            pol_mod += &format!(
                "    pub fn write_{}({}: &{}, conn: &AuthConn) -> PolicyValue {{\n",
                field.name.orig_name,
                policy_binder_var(&field_policy.edit),
                coll.orig_name
            )
            .to_string();
            pol_mod += &gen_policy_body(&sp.schema, &field_policy.edit);
        }
        col_struct += &"}\n".to_string();
        pol_mod += &"}\n".to_string();
        out += &(col_struct + &pol_mod);

        out += &format!(
            "
#[macro_export]
macro_rules! {} {{
    ($($key:ident : $value:expr),*$(,)?) => {{{{
        {}::new({}Props {{
            $($key : $value),*
        }})
    }}}}
}}",
            coll.orig_name.to_ascii_lowercase(),
            coll.orig_name,
            coll.orig_name,
        );
    }
    out
}
fn translate_queryexpr_to_idlist(schema: &Schema, expr: &IRExpr) -> String {
    let expr_str = translate_queryexpr(schema, expr);
    format!("{}", expr_str).to_string()
}
fn translate_queryexpr(schema: &Schema, expr: &IRExpr) -> String {
    match expr {
        IRExpr::AppendL(_ty, e1, e2) => format!(
            "{}.into_iter().chain({}).collect::<Vec<_>>()",
            translate_queryexpr(schema, e1),
            translate_queryexpr(schema, e2)
        ),
        IRExpr::AppendS(e1, e2) => format!(
            "({} + {})",
            translate_queryexpr(schema, e1),
            translate_queryexpr(schema, e2)
        ),
        IRExpr::AddI(e1, e2) | IRExpr::AddF(e1, e2) | IRExpr::AddD(e1, e2) => format!(
            "({} + {})",
            translate_queryexpr(schema, e1),
            translate_queryexpr(schema, e2)
        ),
        IRExpr::SubI(e1, e2) | IRExpr::SubF(e1, e2) | IRExpr::SubD(e1, e2) => format!(
            "({} - {})",
            translate_queryexpr(schema, e1),
            translate_queryexpr(schema, e2)
        ),
        IRExpr::IsEq(_, e1, e2) => format!(
            "({} == {})",
            translate_queryexpr(schema, e1),
            translate_queryexpr(schema, e2)
        ),
        IRExpr::Not(e) => format!("(!{})", translate_queryexpr(schema, e)),
        IRExpr::IsLessI(e1, e2) | IRExpr::IsLessF(e1, e2) | IRExpr::IsLessD(e1, e2) => format!(
            "({} < {})",
            translate_queryexpr(schema, e1),
            translate_queryexpr(schema, e2)
        ),
        IRExpr::IntToFloat(e) => format!("({} as f64)", translate_queryexpr(schema, e)),
        IRExpr::Path(_, e, f) => {
            format!("{}.{}.clone()", translate_queryexpr(schema, e), f.orig_name)
        }
        IRExpr::Var(_ty, id) => match schema.static_principles.iter().find(|sp| *sp == id) {
            Some(sp) => format!("Principle::Static(\"{}\")", sp.orig_name),
            None => format!("{}", mangled_ident(id)),
        },
        IRExpr::LookupById(_, id_expr) => format!(
            "{}.lookup(conn).expect(\"Couldn't find user\")",
            translate_queryexpr(schema, id_expr)
        ),
        IRExpr::Find(coll_ident, fields) => {
            let mut out = format!(
                "{}::find_full_by_template(conn, Build{}::new(None)",
                coll_ident.orig_name, coll_ident.orig_name,
            );
            for (op, field, val_expr) in fields.into_iter() {
                out += &format!(
                    ".{}({}, {})",
                    field.orig_name,
                    match op {
                        FieldComparison::Equals => "FieldOp::Equals",
                        FieldComparison::Contains => "FieldOp::Contains",
                    },
                    translate_queryexpr(schema, val_expr)
                );
            }
            out += ".finalize()";
            out
        }
        IRExpr::Map(list_expr, func) => format!(
            "{}.into_iter().map(|{}| {})",
            translate_queryexpr(schema, list_expr),
            mangled_ident(&func.param),
            translate_queryexpr(schema, &func.body)
        ),
        IRExpr::Set(_ty, exprs) => {
            let mut out = "vec![".to_string();
            for expr in exprs.into_iter() {
                out += &translate_queryexpr(schema, expr);
                out += ", ";
            }
            out += "]";
            out
        }
        IRExpr::If(ty, cond, e1, e2) => format!(
            "(if {} {{ {}::from({}) }} else {{ {}::from({}) }})",
            translate_queryexpr(schema, cond),
            lower_ty(ty),
            translate_queryexpr(schema, e1),
            lower_ty(ty),
            translate_queryexpr(schema, e2),
        ),
        IRExpr::Match(ty, opt_expr, var, some_expr, none_expr) => format!(
            "(match {} {{ Some({}) => {}::from({}), None => {}::from({}) }})",
            translate_queryexpr(schema, opt_expr),
            mangled_ident(var),
            lower_ty(ty),
            translate_queryexpr(schema, some_expr),
            lower_ty(ty),
            translate_queryexpr(schema, none_expr)
        ),
        IRExpr::None(_ty) => format!("Poption::None"),
        IRExpr::Some(_ty, e) => format!("Poption::Some({})", translate_queryexpr(schema, e)),
        IRExpr::DateTimeConst(datetime) => format!(
            "DateTime(Utc.ymd({}, {}, {}).and_hms({}, {}, {})",
            datetime.month(),
            datetime.day(),
            datetime.year(),
            datetime.hour(),
            datetime.minute(),
            datetime.second()
        ),
        IRExpr::Now => format!("DateTime.now()"),
        IRExpr::IntConst(i) => format!("{}", i),
        IRExpr::FloatConst(f) => format!("{}", f),
        IRExpr::StringConst(s) => format!("\"{}\".to_string()", s),
        IRExpr::BoolConst(b) => format!("{}", b),
        IRExpr::Object(col_id, fields, None) => {
            let mut out = format!("{}! {{", col_id.orig_name.to_ascii_lowercase()).to_string();
            for (field_id, field_expr) in fields.iter() {
                match field_expr {
                    Some(expr) => {
                        out += &format!(
                            "{}: {},",
                            field_id.orig_name,
                            translate_queryexpr(schema, expr)
                        )
                    }
                    None => panic!(
                        "Invariant violated: fields cannot be none \
                                    when template object is none in object literal"
                    ),
                };
            }
            out += "}";
            out
        }
        IRExpr::Object(col_id, fields, Some(template_obj_expr)) => {
            let mut out = format!(
                "{{ let template_obj_expr = {}; ",
                translate_queryexpr(schema, template_obj_expr)
            );
            out += &format!("{}! {{", col_id.orig_name.to_ascii_lowercase());
            for field in schema[col_id].fields() {
                let found_field = fields.iter().find(|(id, _expr)| *id == field.name);
                out += &format!("{}: ", field.name.orig_name);
                match found_field {
                    Some((_id, Some(expr))) => {
                        out += &format!("{},", translate_queryexpr(schema, expr))
                    }
                    Some((_id, None)) => (),
                    None => panic!(
                        "Couldn't find field {} in object initializer",
                        field.name.orig_name
                    ),
                }
            }
            out += "} }";
            out
        }
        IRExpr::Public => "PolicyValue::Public".to_string(),
    }
}

fn lower_ty(ty: &ExprType) -> String {
    match ty {
        ExprType::Id(coll) => format!("TypedRecordId<{}>", coll.orig_name).to_string(),
        ExprType::Principle => panic!("Cannot convert a principle directly to a rust type"),
        ExprType::String => "String".to_string(),
        ExprType::I64 => "i64".to_string(),
        ExprType::F64 => "f64".to_string(),
        ExprType::Bool => "bool".to_string(),
        ExprType::DateTime => "DateTime".to_string(),
        ExprType::Set(inner_ty) => match inner_ty.as_ref() {
            ExprType::Principle => format!("PolicyValue"),
            _ => format!("Vec::<{}>", lower_ty(inner_ty)).to_string(),
        },
        ExprType::Option(inner_ty) => format!("POption::<{}>", lower_ty(inner_ty)).to_string(),
        ExprType::Unknown(_id) => "_".to_string(),
        ExprType::Object(coll) => coll.orig_name.clone(),
    }
}
