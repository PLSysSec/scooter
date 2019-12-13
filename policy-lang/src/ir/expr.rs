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
    /// Or of two ids, producing an id list with both.
    Or(Id<Expr>, Id<Expr>),
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
    /// Constant primitive values
    IntConst(i64),
    FloatConst(f64),
    StringConst(String),
}

#[derive(Debug)]
pub struct Lambda {
    pub param: Id<Def>,
    pub body: Id<Expr>,
}
