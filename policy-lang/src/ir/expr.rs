use super::*;
use id_arena::Id;
#[derive(Debug)]
pub struct Expr {
    pub id: Id<Expr>,
    pub kind: ExprKind,
}

/// Possible expression types in our language. By this point, ad-hoc
/// polymorphism/operator overloading has been resolved.
#[derive(Debug)]
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
    IsNeq(Type, Id<Expr>, Id<Expr>),
    /// Negation on bools
    Not(Id<Expr>),

    /// Convert an integer into a float. These nodes don't appear in
    /// syntax, but are inserted by the typechecker.
    IntToFloat(Id<Expr>),
    /// Field lookup on an object. The collection id is inserted by
    /// the typechecker.
    Path(Id<Collection>, Id<Def>, Id<Def>),
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

#[derive(Debug)]
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
        ExprKind::AddI(_, _) => Type::Prim(Prim::I64),
        ExprKind::AddF(_, _) => Type::Prim(Prim::F64),
        ExprKind::SubI(_, _) => Type::Prim(Prim::I64),
        ExprKind::SubF(_, _) => Type::Prim(Prim::F64),
        ExprKind::AppendS(_, _) => Type::Prim(Prim::String),
        ExprKind::AppendL(ty, _, _) => Type::List(Box::new(ty.clone())),
        ExprKind::IsEq(_, _, _) => Type::Prim(Prim::Bool),
        ExprKind::IsNeq(_, _, _) => Type::Prim(Prim::Bool),
        ExprKind::Not(_) => Type::Prim(Prim::Bool),
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
            }
            Type::Id(_) => true,
            _ => false,
        }
        _ => false
    }
}
