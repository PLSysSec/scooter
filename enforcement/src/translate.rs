use policy_lang::ir::*;
use policy_lang::parse_policy;
use std::env;
use std::fs::File;
use std::io::Write;
use std::io::{self, Read};
use std::path::Path;

pub fn translate_policy_file(in_name: impl ToString, out_name: impl ToString) {
    let out_dir = env::var("OUT_DIR").unwrap();
    let dest_path = Path::new(&out_dir).join(out_name.to_string());
    let in_dir = env::current_dir().unwrap();
    let policy_path = Path::new(&in_dir).join(in_name.to_string());
    translate(policy_path, dest_path);
}

pub fn translate(policy_path: impl AsRef<Path>, out_path: impl AsRef<Path>) {
    let path = policy_path.as_ref();
    let parsed_policy = parse_policy(&get_contents(path).unwrap()).unwrap();
    let mut ird = extract_types(&parsed_policy);
    let lowered_policy = ird.lower(&parsed_policy);
    let out = gen_schema_macros(&ird, lowered_policy);
    let mut f = File::create(&out_path).unwrap();
    f.write(out.as_bytes()).unwrap();
}

fn get_contents(fname: &Path) -> io::Result<String> {
    let mut out = String::new();
    std::fs::File::open(fname)?.read_to_string(&mut out)?;
    Ok(out)
}

fn policy_binder_var(ird: &IrData, policy: &Policy) -> String {
    match policy {
        Policy::Func(pfunc) => mangled_ident(&ird[pfunc.param].name),
        _ => "_".to_string(),
    }
}
fn mangled_ident(ident: &Ident) -> String {
    format!("i_{}_{}", ident.0, ident.1)
}
fn gen_policy_body(ird: &IrData, policy: &Policy) -> String {
    match policy {
        Policy::Public => "        PolicyValue::Public\n    }\n".to_string(),
        Policy::None => "        PolicyValue::Ids(vec![])\n    }\n".to_string(),
        Policy::Func(f) => format!(
            "        PolicyValue::Ids({})\n    }}\n",
            translate_queryexpr_to_idlist(ird, f.body)
        ),
    }
}
fn gen_schema_macros(ird: &IrData, policy: CompletePolicy) -> String {
    let mut out = "use enforcement::*;\n".to_string();
    for col in ird.collections() {
        let coll_policy = policy.collection_policy(col.id);
        let mut col_struct = format!(
            r#"
#[collection(policy_module="{}_policies")]
pub struct {} {{
"#,
            col.name.1.to_ascii_lowercase(),
            col.name.1
        )
        .to_string();
        let mut pol_mod = format!(
            r#"
mod {}_policies {{
    use super::*;
"#,
            col.name.1.to_ascii_lowercase()
        );
        pol_mod += &format!("    #[allow(unused_variables)]").to_string();

        pol_mod += &format!(
            "    pub fn create({}: &{}, conn: &AuthConn) -> PolicyValue {{\n",
            policy_binder_var(&ird, &coll_policy.create),
            col.name.1
        )
        .to_string();
        pol_mod += &gen_policy_body(ird, &coll_policy.create);
        pol_mod += &format!("    #[allow(unused_variables)]").to_string();
        pol_mod += &format!(
            "    pub fn delete({}: &{}, conn: &AuthConn) -> PolicyValue {{\n",
            policy_binder_var(&ird, &coll_policy.delete),
            col.name.1
        )
        .to_string();
        pol_mod += &gen_policy_body(ird, &coll_policy.delete);
        for (field_name, field_id) in col.fields().into_iter() {
            if field_name == "id" {
                continue;
            }
            let field_policy = policy.field_policy(*field_id);
            col_struct += &format!(
                "    {}: {},\n",
                field_name,
                lower_ty(ird, ird.def_type(*field_id))
            )
            .to_string();
            pol_mod += &format!("    #[allow(unused_variables)]").to_string();
            pol_mod += &format!(
                "    pub fn read_{}({}: &{}, conn: &AuthConn) -> PolicyValue {{\n",
                field_name,
                policy_binder_var(&ird, &field_policy.read),
                col.name.1
            )
            .to_string();
            pol_mod += &gen_policy_body(ird, &field_policy.read);
            pol_mod += &format!("    #[allow(unused_variables)]").to_string();
            pol_mod += &format!(
                "    pub fn write_{}({}: &{}, conn: &AuthConn) -> PolicyValue {{\n",
                field_name,
                policy_binder_var(&ird, &field_policy.edit),
                col.name.1
            )
            .to_string();
            pol_mod += &gen_policy_body(ird, &field_policy.edit);
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
            col.name.1.to_ascii_lowercase(),
            col.name.1,
            col.name.1
        );
    }
    out
}
fn translate_queryexpr_to_idlist(ird: &IrData, e_id: Id<Expr>) -> String {
    let expr_str = translate_queryexpr(ird, e_id);
    format!("{}.to_record_id_vec()", expr_str).to_string()
}
fn translate_queryexpr(ird: &IrData, e_id: Id<Expr>) -> String {
    let expr = &ird[e_id];
    match &expr.kind {
        ExprKind::AppendL(ty, e1, e2) => format!(
            "{}.into_iter().chain({}).collect::<Vec<{}>>()",
            translate_queryexpr(ird, *e1),
            translate_queryexpr(ird, *e2),
            lower_ty(ird, ty)
        ),
        ExprKind::AppendS(e1, e2) => format!(
            "({} + {})",
            translate_queryexpr(ird, *e1),
            translate_queryexpr(ird, *e2)
        ),
        ExprKind::AddI(e1, e2) | ExprKind::AddF(e1, e2) => format!(
            "({} + {})",
            translate_queryexpr(ird, *e1),
            translate_queryexpr(ird, *e2)
        ),
        ExprKind::SubI(e1, e2) | ExprKind::SubF(e1, e2) => format!(
            "({} - {})",
            translate_queryexpr(ird, *e1),
            translate_queryexpr(ird, *e2)
        ),
        ExprKind::IsEq(_, e1, e2) => format!(
            "({} == {})",
            translate_queryexpr(ird, *e1),
            translate_queryexpr(ird, *e2)
        ),
        ExprKind::Not(e) => format!("(!{})", translate_queryexpr(ird, *e)),
        ExprKind::IsLessI(e1, e2) | ExprKind::IsLessF(e1, e2) => format!(
            "({} < {})",
            translate_queryexpr(ird, *e1),
            translate_queryexpr(ird, *e2)
        ),
        ExprKind::IntToFloat(e) => format!("({} as f64)", translate_queryexpr(ird, *e)),
        ExprKind::Path(coll_id, e, f) => format!(
            "{}.{}.clone()",
            translate_queryexpr(ird, *e),
            ird[*coll_id].field_name(&f)
        ),
        ExprKind::Var(id) => format!("{}", mangled_ident(&ird[*id].name)),
        ExprKind::LookupById(_, id_expr) => format!(
            "{}.lookup(conn).expect(\"Couldn't find user\")",
            translate_queryexpr(ird, *id_expr)
        ),
        ExprKind::List(exprs) => {
            let mut out = "vec![".to_string();
            for expr in exprs.into_iter() {
                out += &translate_queryexpr(ird, *expr);
                out += ", ";
            }
            out += "]";
            out
        }
        ExprKind::If(_ty, cond, e1, e2) => format!(
            "(if {} then {{ {} }} else {{ {} }})",
            translate_queryexpr(ird, *cond),
            translate_queryexpr(ird, *e1),
            translate_queryexpr(ird, *e2)
        ),
        ExprKind::IntConst(i) => format!("{}", i),
        ExprKind::FloatConst(f) => format!("{}", f),
        ExprKind::StringConst(s) => format!("\"{}\".to_string()", s),
        ExprKind::BoolConst(b) => format!("{}", b),
        ExprKind::Object(col_id, fields, None) => {
            let mut out = format!("{}! {{", ird[*col_id].name.1.to_ascii_lowercase()).to_string();
            for (field_id, field_expr) in fields.iter() {
                out += &format!(
                    "{}: {},",
                    ird[*field_id].name.1,
                    translate_queryexpr(ird, *field_expr)
                );
            }
            out += "}";
            out
        }
        ExprKind::Object(col_id, fields, Some(template_obj_expr)) => {
            let mut out = format!(
                "{{ let template_obj_expr = {}; ",
                translate_queryexpr(ird, *template_obj_expr)
            );
            out += &format!("{}! {{", ird[*col_id].name.1.to_ascii_lowercase());
            for (field_name, field_id) in ird[*col_id].fields() {
                let found_field = fields.iter().find(|(id, _expr)| id == field_id);
                out += &format!("{}: ", field_name);
                match found_field {
                    Some((_id, expr)) => out += &format!("{},", translate_queryexpr(ird, *expr)),
                    None => out += &format!("template_obj_expr.{},", field_name),
                }
            }
            out += "} }";
            out
        }
    }
}

fn lower_ty(ird: &IrData, ty: &Type) -> String {
    match ty {
        Type::Prim(p) => match p {
            Prim::String => "String".to_string(),
            Prim::Bool => "bool".to_string(),
            Prim::I64 => "i64".to_string(),
            Prim::F64 => "f64".to_string(),
        },
        Type::Id(coll) => format!("TypedRecordId<{}>", ird[*coll].name().1).to_string(),
        Type::List(inner_ty) => format!("Vec<{}>", lower_ty(ird, inner_ty)).to_string(),
        _ => panic!("Can't lower {} to rust type", ty),
    }
}
