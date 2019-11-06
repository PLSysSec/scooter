use id_arena::Id;
use super::*;
#[derive(Debug)]
pub struct Expr {
    pub(crate) id: Id<Expr>,
    pub(crate) kind: ExprKind
}

#[derive(Debug)]
pub enum ExprKind {
    Or(Id<Expr>, Id<Expr>),
    Path(Id<Def>, Id<Def>),
    Var(Id<Def>),
}

#[derive(Debug)]
pub struct Lambda {
    pub(crate) param: Id<Def>,
    pub(crate) body: Id<Expr>,
}