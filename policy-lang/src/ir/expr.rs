use super::*;
use id_arena::Id;
#[derive(Debug)]
pub struct Expr {
    pub id: Id<Expr>,
    pub kind: ExprKind,
}

#[derive(Debug)]
pub enum ExprKind {
    Or(Id<Expr>, Id<Expr>),
    Append(Id<Expr>, Id<Expr>),
    AddI(Id<Expr>, Id<Expr>),
    AddF(Id<Expr>, Id<Expr>),
    IntToFloat(Id<Expr>),
    Path(Id<Collection>, Id<Def>, Id<Def>),
    Var(Id<Def>),
    IntConst(i64),
    FloatConst(f64),
    StringConst(String),
    Object(Id<Collection>, Vec<(Id<Def>, Id<Expr>)>, Option<Id<Expr>>),
    List(Vec<Id<Expr>>),
}

#[derive(Debug)]
pub struct Lambda {
    pub param: Id<Def>,
    pub body: Id<Expr>,
}
