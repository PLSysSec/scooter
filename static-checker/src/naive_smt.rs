use lazy_static::lazy_static;
use policy_lang::ir::{
    expr::{ExprType, Func},
    policy::Policy,
    schema::{Collection, Field, Schema},
    Ident,
};
use regex::Regex;
use std::{
    collections::{HashMap, HashSet},
    ffi::{CStr, CString},
    fmt::{Debug, Display},
    ptr::{null, null_mut},
};
use z3_sys::{
    Z3_ast, Z3_ast_to_string, Z3_context, Z3_func_decl, Z3_get_decl_name, Z3_get_symbol_string,
    Z3_mk_app, Z3_model, Z3_model_eval, Z3_model_get_func_decl, Z3_sort, Z3_sort_to_string,
};
//use translate::*;
//mod translate;
mod translate;
use translate::*;

#[derive(Clone)]
pub struct Equiv(pub Ident<Field>, pub Func);

pub fn is_as_strict(
    schema: &Schema,
    eqs: &[Equiv],
    coll: &Ident<Collection>,
    before: &Policy,
    after: &Policy,
) -> Result<(), impl Display> {
    let verif_problem = gen_assert(schema, eqs, coll, before, after);
    let assertion = verif_problem
        .stmts
        .iter()
        .map(Statement::to_string)
        .collect::<Vec<_>>()
        .join("");

    unsafe {
        let config = z3_sys::Z3_mk_config();
        let key = CString::new("smtlib2_compliant").unwrap();
        let value = CString::new("true").unwrap();
        z3_sys::Z3_set_param_value(config, key.as_ptr(), value.as_ptr());
        let ctx = z3_sys::Z3_mk_context(config);
        let solver = z3_sys::Z3_mk_solver(ctx);
        z3_sys::Z3_solver_inc_ref(ctx, solver);

        let c_str = CString::new(assertion).unwrap();
        z3_sys::Z3_solver_from_string(ctx, solver, c_str.as_ptr());
        let res = z3_sys::Z3_solver_check(ctx, solver);

        if res == z3_sys::Z3_L_TRUE {
            let model = z3_sys::Z3_solver_get_model(ctx, solver);
            z3_sys::Z3_model_inc_ref(ctx, model);

            let num_consts = z3_sys::Z3_model_get_num_consts(ctx, model);
            let consts = (0..num_consts).map(|i| z3_sys::Z3_model_get_const_decl(ctx, model, i));
            let consts: HashMap<String, Z3_func_decl> = consts
                .map(|decl| {
                    let symbol = Z3_get_decl_name(ctx, decl);
                    let string_name = CStr::from_ptr(Z3_get_symbol_string(ctx, symbol))
                        .to_string_lossy()
                        .to_string();
                    (string_name, decl)
                })
                .collect();

            let rec_decl = consts[&ident(&verif_problem.rec)];
            let rec_app = z3_sys::Z3_mk_app(ctx, rec_decl, 0, null());
            let rec_id = eval(ctx, model, rec_app).unwrap();

            let princ_decl = consts[&ident(&verif_problem.princ)];
            let princ_app = z3_sys::Z3_mk_app(ctx, princ_decl, 0, null());
            let princ_id = eval(ctx, model, princ_app).unwrap();

            let mut output = Model {
                rec_id: parse(&ExprType::Id(coll.clone()), &rec_id),
                princ: parse(&ExprType::Principal, &princ_id),
                objects: Vec::new(),
            };

            let num_decls = z3_sys::Z3_model_get_num_funcs(ctx, model);
            let funcs = (0..num_decls).map(|i| Z3_model_get_func_decl(ctx, model, i));
            let func_map: HashMap<String, Z3_func_decl> = funcs
                .map(|decl| {
                    let symbol = Z3_get_decl_name(ctx, decl);
                    let string_name = CStr::from_ptr(Z3_get_symbol_string(ctx, symbol))
                        .to_string_lossy()
                        .to_string();
                    (string_name, decl)
                })
                .collect();

            let num_sorts = z3_sys::Z3_model_get_num_sorts(ctx, model);
            let sorts = (0..num_sorts).map(|i| z3_sys::Z3_model_get_sort(ctx, model, i));
            let sort_map: HashMap<String, Z3_sort> = sorts
                .map(|sort| {
                    let string_name = CStr::from_ptr(Z3_sort_to_string(ctx, sort))
                        .to_string_lossy()
                        .to_string();
                    (string_name, sort)
                })
                .collect();

            let mut join_vals = Vec::<(Ident<Field>, String, String)>::new();
            for (field, (coll, from, to, inner_ty)) in verif_problem.join_tables.iter() {
                let sort = sort_map[&ident(coll)];
                let (to_decl, from_decl) =
                    match (func_map.get(&ident(&to)), func_map.get(&ident(&from))) {
                        (Some(to_decl), Some(from_decl)) => (*to_decl, *from_decl),
                        _ => continue,
                    };

                let val_vec = z3_sys::Z3_model_get_sort_universe(ctx, model, sort);
                z3_sys::Z3_ast_vector_inc_ref(ctx, val_vec);
                let num_vals = z3_sys::Z3_ast_vector_size(ctx, val_vec);
                let vals = (0..num_vals).map(|i| z3_sys::Z3_ast_vector_get(ctx, val_vec, i));
                for val in vals {
                    let to_app = Z3_mk_app(ctx, to_decl, 1, &val);
                    let to_val = eval(ctx, model, to_app).unwrap();

                    let from_app = Z3_mk_app(ctx, from_decl, 1, &val);
                    let from_val = eval(ctx, model, from_app).unwrap();

                    join_vals.push((field.clone(), from_val, parse(inner_ty, &to_val)));
                }

                z3_sys::Z3_ast_vector_dec_ref(ctx, val_vec);
            }
            for (sort_name, sort) in sort_map.iter() {
                let coll_name: String = {
                    let mut iter = sort_name.split('_');
                    iter.next_back();
                    iter.collect()
                };
                let coll = match schema.find_collection(&coll_name) {
                    Some(coll) => coll,
                    None => continue,
                };

                let val_vec = z3_sys::Z3_model_get_sort_universe(ctx, model, *sort);
                z3_sys::Z3_ast_vector_inc_ref(ctx, val_vec);
                let num_vals = z3_sys::Z3_ast_vector_size(ctx, val_vec);
                let vals = (0..num_vals).map(|i| z3_sys::Z3_ast_vector_get(ctx, val_vec, i));

                for val in vals {
                    let mut object = ModelObject {
                        coll: coll.name.clone(),
                        fields: Vec::new(),
                        complete: true,
                    };
                    let id = CStr::from_ptr(Z3_ast_to_string(ctx, val))
                        .to_string_lossy()
                        .to_string();
                    for field in coll.fields() {
                        if verif_problem.join_tables.contains_key(&field.name) {
                            let vals: Vec<_> = join_vals
                                .iter()
                                .filter_map(|(f, name, val)| {
                                    (&field.name == f && name == &id).then(|| val.to_string())
                                })
                                .collect::<HashSet<_>>()
                                .into_iter()
                                .collect();
                            object
                                .fields
                                .push((field.name.clone(), format!("[{}]", vals.join(", "))));
                        }
                        let func_decl = match func_map.get(&ident(&field.name)) {
                            Some(decl) => *decl,
                            _ => {
                                object.complete = false;
                                continue;
                            }
                        };
                        let app = Z3_mk_app(ctx, func_decl, 1, &val);
                        let value = eval(ctx, model, app).unwrap();
                        object
                            .fields
                            .push((field.name.clone(), parse(&field.typ, &value)));
                    }
                    output.objects.push(object);
                }

                z3_sys::Z3_ast_vector_dec_ref(ctx, val_vec);
            }
            z3_sys::Z3_solver_dec_ref(ctx, solver);
            z3_sys::Z3_model_dec_ref(ctx, model);
            z3_sys::Z3_del_context(ctx);
            z3_sys::Z3_del_config(config);
            Err(output)
        } else {
            z3_sys::Z3_solver_dec_ref(ctx, solver);
            z3_sys::Z3_del_context(ctx);
            z3_sys::Z3_del_config(config);
            Ok(())
        }
    }
}

fn eval(ctx: Z3_context, model: Z3_model, ast: Z3_ast) -> Option<String> {
    let mut result = null_mut();
    unsafe {
        let success = Z3_model_eval(ctx, model, ast, true, &mut result);
        success.then(|| {
            CStr::from_ptr(Z3_ast_to_string(ctx, result))
                .to_string_lossy()
                .to_string()
        })
    }
}

fn parse(typ: &ExprType, text: &str) -> String {
    match typ {
        ExprType::I64 => i64::from_str_radix(text.trim_start_matches("#x"), 16)
            .expect(&format!("Couldn't parse hex from SMT {}", text))
            .to_string(),
        ExprType::Id(_) => {
            lazy_static! {
                static ref ID_RE: Regex = Regex::new(r#"_i\d+!val!(?P<id>\d+)"#).unwrap();
            }
            ID_RE.replace_all(text, "($id)").into()
        }
        ExprType::Principal => {
            lazy_static! {
                static ref ID_PRINC: Regex = Regex::new(r#"\(\S+ (?P<id>[^)]*)\)"#).unwrap();
            }
            if ID_PRINC.is_match(text) {
                parse(
                    &ExprType::Id(Ident::new("dummy")),
                    &ID_PRINC.replace_all(text, "$id"),
                )
            } else {
                text.to_owned()
            }
        }
        _ => text.to_owned(),
    }
}

#[derive(Debug)]
pub struct Model {
    princ: String,
    rec_id: String,
    objects: Vec<ModelObject>,
}

impl Model {
    fn rec(&self) -> &ModelObject {
        self.objects.iter().find(|o| o.id() == self.rec_id).unwrap()
    }
}

impl Display for Model {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let rec = self.rec();
        write!(
            f,
            "Principal: {}\n\nCAN NOW ACCESS:\n\n{:#}\n\n",
            self.princ, rec
        )?;

        if self.objects.len() > 1 {
            write!(f, "OTHER RECORDS:\n\n")?;
        }

        for obj in self.objects.iter() {
            if &obj.id() != &self.rec_id {
                write!(f, "{:#}\n", obj)?;
            }
        }
        Ok(())
    }
}

#[derive(Debug, Eq)]
pub struct ModelObject {
    coll: Ident<Collection>,
    fields: Vec<(Ident<Field>, String)>,
    complete: bool,
}

impl ModelObject {
    fn id(&self) -> String {
        self.fields
            .iter()
            .find(|(ident, _)| ident.orig_name == "id")
            .unwrap()
            .1
            .clone()
    }
}

impl PartialEq for ModelObject {
    fn eq(&self, other: &Self) -> bool {
        if self.coll != other.coll {
            return false;
        }

        for (l, r) in self.fields.iter().zip(other.fields.iter()) {
            if l.0.orig_name == "id" {
                continue;
            }
            if l != r {
                return false;
            }
        }

        return true;
    }
}

impl Display for ModelObject {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{} {{\n", &self.coll.orig_name)?;
        for (f_id, val) in self.fields.iter() {
            write!(f, "\t{}: {:?},\n", &f_id.orig_name, &Literal(val))?;
        }
        if !self.complete {
            write!(f, "\t...\n}}")
        } else {
            write!(f, "}}")
        }
    }
}

struct Literal<'a>(&'a str);
impl<'a> Debug for Literal<'a> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.0)
    }
}
