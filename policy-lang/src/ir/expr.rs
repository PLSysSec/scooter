use super::*;
use id_arena::Id;
use std::iter;

#[derive(Debug, Clone)]
pub struct Expr {
    pub id: Id<Expr>,
    pub kind: ExprKind,
}

/// Possible expression types in our language. By this point, ad-hoc
/// polymorphism/operator overloading has been resolved.
#[derive(Debug, Clone)]
pub enum ExprKind {
    /// String append
    AppendS(Id<Expr>, Id<Expr>),
    /// List append
    AppendL(Type, Id<Expr>, Id<Expr>),
    /// Adding integers
    AddI(Id<Expr>, Id<Expr>),
    /// Adding floats
    AddF(Id<Expr>, Id<Expr>),
    /// Subtracting integers
    SubI(Id<Expr>, Id<Expr>),
    /// Subtracting floats
    SubF(Id<Expr>, Id<Expr>),

    /// Type-annotated equality
    IsEq(Type, Id<Expr>, Id<Expr>),
    /// Negation on bools
    Not(Id<Expr>),
    /// Inequalities on numbers
    IsLessI(Id<Expr>, Id<Expr>),
    IsLessF(Id<Expr>, Id<Expr>),

    /// Convert an integer into a float. These nodes don't appear in
    /// syntax, but are inserted by the typechecker.
    IntToFloat(Id<Expr>),
    /// Field lookup on an object. The collection id is inserted by
    /// the typechecker.
    Path(Id<Collection>, Id<Expr>, Id<Def>),
    /// A variable
    Var(Id<Def>),
    /// An object expression. Made up of the object type, a list of
    /// field specifiers (tuples of identifiers and expressions whose
    /// value is bound to them), and an optional "template
    /// object". When the template object is not specified, the field
    /// list must contain all of the fields in the object; otherwise,
    /// missing fields take their values from the corresponding field
    /// on the template object.
    Object(Id<Collection>, Vec<(Id<Def>, Id<Expr>)>, Option<Id<Expr>>),

    /// Look up an id in a collection
    LookupById(Id<Collection>, Id<Expr>),
    /// A list expression
    List(Vec<Id<Expr>>),
    /// Conditional expression
    If(Type, Id<Expr>, Id<Expr>, Id<Expr>),
    /// Constant primitive values
    IntConst(i64),
    FloatConst(f64),
    StringConst(String),
    BoolConst(bool),
}

#[derive(Debug, Clone)]
enum ExprTemplate {
    /// String append
    AppendS(Box<ExprTemplate>, Box<ExprTemplate>),
    /// List append
    AppendL(Type, Box<ExprTemplate>, Box<ExprTemplate>),
    /// Adding integers
    AddI(Box<ExprTemplate>, Box<ExprTemplate>),
    /// Adding floats
    AddF(Box<ExprTemplate>, Box<ExprTemplate>),
    /// Subtracting integers
    SubI(Box<ExprTemplate>, Box<ExprTemplate>),
    /// Subtracting floats
    SubF(Box<ExprTemplate>, Box<ExprTemplate>),

    /// Type-annotated equality
    IsEq(Type, Box<ExprTemplate>, Box<ExprTemplate>),
    /// Negation on bools
    Not(Box<ExprTemplate>),
    /// Inequalities on numbers
    IsLessI(Box<ExprTemplate>, Box<ExprTemplate>),
    IsLessF(Box<ExprTemplate>, Box<ExprTemplate>),

    /// Convert an integer into a float. These nodes don't appear in
    /// syntax, but are inserted by the typechecker.
    IntToFloat(Box<ExprTemplate>),
    /// Field lookup on an object. The collection id is inserted by
    /// the typechecker.
    Path(Id<Collection>, Box<ExprTemplate>, Id<Def>),
    /// A variable
    Var(Id<Def>),
    /// An object expression. Made up of the object type, a list of
    /// field specifiers (tuples of identifiers and expressions whose
    /// value is bound to them), and an optional "template
    /// object". When the template object is not specified, the field
    /// list must contain all of the fields in the object; otherwise,
    /// missing fields take their values from the corresponding field
    /// on the template object.
    Object(
        Id<Collection>,
        Vec<(Id<Def>, Box<ExprTemplate>)>,
        Option<Box<ExprTemplate>>,
    ),

    /// Look up an id in a collection
    LookupById(Id<Collection>, Box<ExprTemplate>),
    /// A list expression
    List(Vec<Box<ExprTemplate>>),
    /// Conditional expression
    If(
        Type,
        Box<ExprTemplate>,
        Box<ExprTemplate>,
        Box<ExprTemplate>,
    ),
    /// Constant primitive values
    IntConst(i64),
    FloatConst(f64),
    StringConst(String),
    BoolConst(bool),
}

#[derive(Debug, Clone)]
pub struct Lambda {
    pub param: Id<Def>,
    pub body: Id<Expr>,
}

pub fn infer_expr_type(ird: &IrData, expr_id: Id<Expr>) -> Type {
    let expr = &ird[expr_id];
    match &expr.kind {
        ExprKind::IntConst(_) => Type::Prim(Prim::I64),
        ExprKind::FloatConst(_) => Type::Prim(Prim::F64),
        ExprKind::StringConst(_) => Type::Prim(Prim::String),
        ExprKind::BoolConst(_) => Type::Prim(Prim::Bool),
        ExprKind::Path(_collection, _obj, field) => ird.def_type(*field).clone(),
        ExprKind::Var(m) => ird.def_type(*m).clone(),
        ExprKind::Object(collection, _fields, _t_obj) => Type::Collection(*collection),
        ExprKind::LookupById(collection, _id_expr) => Type::Collection(*collection),
        ExprKind::AddI(_, _) => Type::Prim(Prim::I64),
        ExprKind::AddF(_, _) => Type::Prim(Prim::F64),
        ExprKind::SubI(_, _) => Type::Prim(Prim::I64),
        ExprKind::SubF(_, _) => Type::Prim(Prim::F64),
        ExprKind::AppendS(_, _) => Type::Prim(Prim::String),
        ExprKind::AppendL(ty, _, _) => Type::List(Box::new(ty.clone())),
        ExprKind::IsEq(_, _, _) => Type::Prim(Prim::Bool),
        ExprKind::Not(_) => Type::Prim(Prim::Bool),
        ExprKind::IsLessF(_, _) => Type::Prim(Prim::Bool),
        ExprKind::IsLessI(_, _) => Type::Prim(Prim::Bool),
        ExprKind::IntToFloat(_) => Type::Prim(Prim::F64),
        ExprKind::List(exprs) => {
            if exprs.len() == 0 {
                Type::ListAny
            } else {
                let expr_type = infer_expr_type(ird, exprs[0]);
                for expr in exprs.into_iter() {
                    let inferred_type = infer_expr_type(ird, *expr);
                    if inferred_type != expr_type {
                        panic!("Contents of list don't have the same type!")
                    }
                }
                Type::List(Box::new(expr_type.clone()))
            }
        }
        ExprKind::If(ty, _, _, _) => ty.clone(),
    }
}
pub fn typecheck_expr(ird: &IrData, expr_id: Id<Expr>, expected_type: Type) {
    let inferred_type = infer_expr_type(ird, expr_id);
    assert!(
        is_subtype(&inferred_type, &expected_type),
        "Static type error: expected {}, found {}",
        expected_type,
        inferred_type
    );
}
pub fn is_subtype(t1: &Type, t2: &Type) -> bool {
    match t2 {
        _ if t1 == t2 => true,
        Type::List(inner_type2) => match t1 {
            Type::ListAny => true,
            Type::List(inner_type1) => is_subtype(inner_type1, inner_type2),
            _ => false,
        },
        Type::ListId => match t1 {
            Type::ListAny => true,
            Type::List(inner_type1) => match **inner_type1 {
                Type::Id(_) => true,
                _ => false,
            },
            Type::Id(_) => true,
            _ => false,
        },
        _ => false,
    }
}

pub fn expr_map(ird: &mut IrData, f: &dyn Fn(&Expr) -> ExprKind, e_id: Id<Expr>) -> Id<Expr> {
    let template = expr_map_to_template(ird, f, e_id);
    realize_template(ird, template)
}

fn realize_template(ird: &mut IrData, template: Box<ExprTemplate>) -> Id<Expr> {
    match *template {
        ExprTemplate::AppendS(e1_templ, e2_templ) => {
            let arg1 = realize_template(ird, e1_templ);
            let arg2 = realize_template(ird, e2_templ);
            ird.create_expr(ExprKind::AppendS(arg1, arg2))
        }
        ExprTemplate::AppendL(ty, e1_templ, e2_templ) => {
            let arg1 = realize_template(ird, e1_templ);
            let arg2 = realize_template(ird, e2_templ);
            ird.create_expr(ExprKind::AppendL(ty.clone(), arg1, arg2))
        }
        ExprTemplate::AddI(e1_templ, e2_templ) => {
            let arg1 = realize_template(ird, e1_templ);
            let arg2 = realize_template(ird, e2_templ);
            ird.create_expr(ExprKind::AddI(arg1, arg2))
        }
        ExprTemplate::AddF(e1_templ, e2_templ) => {
            let arg1 = realize_template(ird, e1_templ);
            let arg2 = realize_template(ird, e2_templ);
            ird.create_expr(ExprKind::AddF(arg1, arg2))
        }
        ExprTemplate::SubI(e1_templ, e2_templ) => {
            let arg1 = realize_template(ird, e1_templ);
            let arg2 = realize_template(ird, e2_templ);
            ird.create_expr(ExprKind::SubI(arg1, arg2))
        }
        ExprTemplate::SubF(e1_templ, e2_templ) => {
            let arg1 = realize_template(ird, e1_templ);
            let arg2 = realize_template(ird, e2_templ);
            ird.create_expr(ExprKind::SubF(arg1, arg2))
        }
        ExprTemplate::IsEq(ty, e1_templ, e2_templ) => {
            let arg1 = realize_template(ird, e1_templ);
            let arg2 = realize_template(ird, e2_templ);
            ird.create_expr(ExprKind::IsEq(ty.clone(), arg1, arg2))
        }
        ExprTemplate::Not(e_templ) => {
            let arg = realize_template(ird, e_templ);
            ird.create_expr(ExprKind::Not(arg))
        }
        ExprTemplate::IsLessI(e1_templ, e2_templ) => {
            let arg1 = realize_template(ird, e1_templ);
            let arg2 = realize_template(ird, e2_templ);
            ird.create_expr(ExprKind::IsLessI(arg1, arg2))
        }
        ExprTemplate::IsLessF(e1_templ, e2_templ) => {
            let arg1 = realize_template(ird, e1_templ);
            let arg2 = realize_template(ird, e2_templ);
            ird.create_expr(ExprKind::IsLessF(arg1, arg2))
        }
        ExprTemplate::IntToFloat(e_templ) => {
            let arg = realize_template(ird, e_templ);
            ird.create_expr(ExprKind::IntToFloat(arg))
        }
        ExprTemplate::Path(coll, e_templ, field_id) => {
            let arg1 = realize_template(ird, e_templ);
            ird.create_expr(ExprKind::Path(coll.clone(), arg1, field_id.clone()))
        }
        ExprTemplate::Var(v) => ird.create_expr(ExprKind::Var(v.clone())),
        ExprTemplate::Object(coll, fields, template_expr) => {
            let realized_fields = fields
                .into_iter()
                .map(|(field_id, texpr)| (field_id, realize_template(ird, texpr)))
                .collect();
            let realized_expr = template_expr.map(|expr| realize_template(ird, expr));
            ird.create_expr(ExprKind::Object(
                coll.clone(),
                realized_fields,
                realized_expr,
            ))
        }
        ExprTemplate::LookupById(coll, id_expr_t) => {
            let arg1 = realize_template(ird, id_expr_t);
            ird.create_expr(ExprKind::LookupById(coll.clone(), arg1))
        }
        ExprTemplate::List(expr_ids) => {
            let args = expr_ids
                .into_iter()
                .map(|expr_id| realize_template(ird, expr_id))
                .collect();
            ird.create_expr(ExprKind::List(args))
        }
        ExprTemplate::If(ty, cond_templ, true_templ, false_templ) => {
            let cond_arg = realize_template(ird, cond_templ);
            let true_arg = realize_template(ird, true_templ);
            let false_arg = realize_template(ird, false_templ);
            ird.create_expr(ExprKind::If(ty.clone(), cond_arg, true_arg, false_arg))
        }
        ExprTemplate::IntConst(i) => ird.create_expr(ExprKind::IntConst(i)),
        ExprTemplate::FloatConst(f) => ird.create_expr(ExprKind::FloatConst(f)),
        ExprTemplate::StringConst(s) => ird.create_expr(ExprKind::StringConst(s)),
        ExprTemplate::BoolConst(b) => ird.create_expr(ExprKind::BoolConst(b)),
    }
}

fn expr_map_to_template(
    ird: &IrData,
    f: &dyn Fn(&Expr) -> ExprKind,
    e_id: Id<Expr>,
) -> Box<ExprTemplate> {
    match f(&ird[e_id]) {
        ExprKind::AppendS(e1_id, e2_id) => Box::new(ExprTemplate::AppendS(
            expr_map_to_template(ird, f, e1_id),
            expr_map_to_template(ird, f, e2_id),
        )),
        ExprKind::AppendL(ty, e1_id, e2_id) => Box::new(ExprTemplate::AppendL(
            ty.clone(),
            expr_map_to_template(ird, f, e1_id),
            expr_map_to_template(ird, f, e2_id),
        )),
        ExprKind::AddI(e1_id, e2_id) => Box::new(ExprTemplate::AddI(
            expr_map_to_template(ird, f, e1_id),
            expr_map_to_template(ird, f, e2_id),
        )),
        ExprKind::AddF(e1_id, e2_id) => Box::new(ExprTemplate::AddF(
            expr_map_to_template(ird, f, e1_id),
            expr_map_to_template(ird, f, e2_id),
        )),
        ExprKind::SubI(e1_id, e2_id) => Box::new(ExprTemplate::SubI(
            expr_map_to_template(ird, f, e1_id),
            expr_map_to_template(ird, f, e2_id),
        )),
        ExprKind::SubF(e1_id, e2_id) => Box::new(ExprTemplate::SubF(
            expr_map_to_template(ird, f, e1_id),
            expr_map_to_template(ird, f, e2_id),
        )),
        ExprKind::IsEq(ty, e1_id, e2_id) => Box::new(ExprTemplate::IsEq(
            ty.clone(),
            expr_map_to_template(ird, f, e1_id),
            expr_map_to_template(ird, f, e2_id),
        )),
        ExprKind::Not(e_id) => Box::new(ExprTemplate::Not(expr_map_to_template(ird, f, e_id))),
        ExprKind::IsLessI(e1_id, e2_id) => Box::new(ExprTemplate::IsLessI(
            expr_map_to_template(ird, f, e1_id),
            expr_map_to_template(ird, f, e2_id),
        )),
        ExprKind::IsLessF(e1_id, e2_id) => Box::new(ExprTemplate::IsLessF(
            expr_map_to_template(ird, f, e1_id),
            expr_map_to_template(ird, f, e2_id),
        )),
        ExprKind::IntToFloat(e_id) => {
            Box::new(ExprTemplate::IntToFloat(expr_map_to_template(ird, f, e_id)))
        }
        ExprKind::Path(coll, expr, field) => Box::new(ExprTemplate::Path(
            coll.clone(),
            expr_map_to_template(ird, f, expr),
            field.clone(),
        )),
        ExprKind::Var(v) => Box::new(ExprTemplate::Var(v.clone())),
        ExprKind::Object(coll, fields, template_expr) => Box::new(ExprTemplate::Object(
            coll.clone(),
            fields
                .iter()
                .map(|(field_id, expr_id)| (*field_id, expr_map_to_template(ird, f, *expr_id)))
                .collect(),
            template_expr.map(|e_id| expr_map_to_template(ird, f, e_id)),
        )),
        ExprKind::LookupById(coll, id_expr) => Box::new(ExprTemplate::LookupById(
            coll.clone(),
            expr_map_to_template(ird, f, id_expr),
        )),
        ExprKind::List(expr_ids) => Box::new(ExprTemplate::List(
            expr_ids
                .iter()
                .map(|expr_id| expr_map_to_template(ird, f, *expr_id))
                .collect(),
        )),
        ExprKind::If(ty, cond_id, true_id, false_id) => Box::new(ExprTemplate::If(
            ty.clone(),
            expr_map_to_template(ird, f, cond_id),
            expr_map_to_template(ird, f, true_id),
            expr_map_to_template(ird, f, false_id),
        )),
        ExprKind::IntConst(i) => Box::new(ExprTemplate::IntConst(i)),
        ExprKind::FloatConst(f) => Box::new(ExprTemplate::FloatConst(f)),
        ExprKind::StringConst(s) => Box::new(ExprTemplate::StringConst(s.clone())),
        ExprKind::BoolConst(b) => Box::new(ExprTemplate::BoolConst(b)),
    }
}

/// Preorder traversal
pub fn expr_to_all_subexprs<'a>(
    ird: &'a IrData,
    e_id: Id<Expr>,
) -> Box<dyn Iterator<Item = &'a Id<Expr>> + 'a> {
    let expr = &ird[e_id];
    match &expr.kind {
        ExprKind::AppendS(e1_id, e2_id)
        | ExprKind::AppendL(_, e1_id, e2_id)
        | ExprKind::AddI(e1_id, e2_id)
        | ExprKind::AddF(e1_id, e2_id)
        | ExprKind::SubI(e1_id, e2_id)
        | ExprKind::SubF(e1_id, e2_id)
        | ExprKind::IsEq(_, e1_id, e2_id)
        | ExprKind::IsLessI(e1_id, e2_id)
        | ExprKind::IsLessF(e1_id, e2_id) => Box::new(
            iter::once(&expr.id)
                .chain(expr_to_all_subexprs(ird, *e1_id))
                .chain(expr_to_all_subexprs(ird, *e2_id)),
        ),
        ExprKind::Not(se_id) | ExprKind::IntToFloat(se_id) => {
            Box::new(iter::once(&expr.id).chain(expr_to_all_subexprs(ird, *se_id)))
        }
        ExprKind::If(_, e1_id, e2_id, e3_id) => Box::new(
            iter::once(&expr.id)
                .chain(expr_to_all_subexprs(ird, *e1_id))
                .chain(expr_to_all_subexprs(ird, *e2_id))
                .chain(expr_to_all_subexprs(ird, *e3_id)),
        ),
        ExprKind::List(exprs) => Box::new(
            iter::once(&expr.id).chain(
                exprs
                    .iter()
                    .flat_map(move |expr| expr_to_all_subexprs(ird, *expr)),
            ),
        ),
        ExprKind::Object(_, field_exprs, template_expr) => Box::new(
            iter::once(&expr.id)
                .chain(
                    field_exprs
                        .iter()
                        .flat_map(move |(_ident, expr)| expr_to_all_subexprs(ird, *expr)),
                )
                .chain(if let Some(texpr) = template_expr {
                    expr_to_all_subexprs(ird, *texpr)
                } else {
                    Box::new(iter::empty())
                }),
        ),
        ExprKind::IntConst(_)
        | ExprKind::FloatConst(_)
        | ExprKind::StringConst(_)
        | ExprKind::BoolConst(_) => Box::new(iter::once(&expr.id)),
        ExprKind::Var(_) => Box::new(iter::once(&expr.id)),
        ExprKind::LookupById(_coll, se_id) => {
            Box::new(iter::once(&expr.id).chain(expr_to_all_subexprs(ird, *se_id)))
        }
        ExprKind::Path(_coll, se_id, _def) => {
            Box::new(iter::once(&expr.id).chain(expr_to_all_subexprs(ird, *se_id)))
        }
    }
}
