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
    Path(Id<Def>, Id<Def>),
    Var(Id<Def>),
    IntConst(i64),
    FloatConst(f64),
    StringConst(String),
}

#[derive(Debug)]
pub struct Lambda {
    pub param: Id<Def>,
    pub body: Id<Expr>,
}
