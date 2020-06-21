use super::{
    schema::{Collection, Field, Schema},
    Ident,
};
use crate::ast;
use std::{fmt, rc::Rc};

/// A marker struct used to distinguise Ident<Var> from other idents.
#[derive(Debug, Clone, Copy)]
pub struct Var;

#[derive(Debug, Clone)]
pub struct DefMap(Option<Rc<DefMapNode>>);

#[derive(Debug, Clone)]
struct DefMapNode {
    prev: DefMap,
    var: String,
    id: Ident<Var>,
    typ: ExprType,
}

impl DefMap {
    pub fn empty() -> DefMap {
        DefMap(None)
    }

    pub fn extend(&self, var: &str, id: Ident<Var>, typ: ExprType) -> DefMap {
        DefMap(Some(Rc::new(DefMapNode {
            prev: self.clone(),
            id,
            var: var.to_string(),
            typ,
        })))
    }

    fn lookup(&self, search_var: &str) -> Option<(Ident<Var>, ExprType)> {
        match self.0.as_ref() {
            None => None,
            Some(node) if search_var == node.var => Some((node.id.clone(), node.typ.clone())),
            Some(node) => node.prev.lookup(search_var),
        }
    }
}

/// Describes a type that can exist during execution of the policy.
/// This is a superset of the types available in the database
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ExprType {
    Id(Ident<Collection>),
    String,
    I64,
    F64,
    Bool,
    List(Box<ExprType>),
    ListUnknown,
    Object(Ident<Collection>),
}

impl ExprType {
    pub fn list(elem: Self) -> Self {
        Self::List(Box::new(elem))
    }

    pub fn bool() -> Self {
        Self::Bool
    }

    pub fn id(ident: Ident<Collection>) -> Self {
        Self::Id(ident)
    }
}

impl fmt::Display for ExprType {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            ExprType::Id(ident) => write!(f, "Id({})", ident.orig_name),
            ExprType::String => write!(f, "String"),
            ExprType::I64 => write!(f, "I64"),
            ExprType::F64 => write!(f, "F64"),
            ExprType::Bool => write!(f, "Bool"),
            ExprType::List(ty) => write!(f, "List({})", ty),
            ExprType::Object(coll) => write!(f, "{}", coll.orig_name),
            ExprType::ListUnknown => write!(f, "ListUnknown"),
        }
    }
}

#[derive(Debug)]
pub struct Func {
    pub param: Ident<Var>,
    pub param_type: ExprType,
    pub body: Box<IRExpr>,
}

pub fn extract_func(
    schema: &Schema,
    param_type: ExprType,
    exp_ret_type: &ExprType,
    func: &ast::Func,
) -> Func {
    let param_id = Ident::new(&func.param);
    let def_map = DefMap::empty().extend(&func.param, param_id.clone(), param_type.clone());
    let body = extract_ir_expr(schema, def_map, &func.expr);

    if body.type_of() != *exp_ret_type {
        panic!(
            "Expected function return type: `{}`. Found: `{}`",
            exp_ret_type,
            body.type_of(),
        )
    }

    Func {
        param: param_id,
        param_type,
        body,
    }
}

/// Possible expression types in our language. By this point, ad-hoc
/// polymorphism/operator overloading has been resolved. Every IRExpr node is
/// monomorphic and should have O(1) type resolution time. For fully polymorphic
/// operations, the monomorphized type is present as a member of the node. For
/// overloaded operations which only support certain types, there is a separate
/// instruction per type.
///
/// The rule of thumb is that you shouldn't need to call `type_of` to understand
/// the operational semantic of the instruction.
#[derive(Debug, Clone)]
pub enum IRExpr {
    /// String append
    AppendS(Box<IRExpr>, Box<IRExpr>),
    /// List append. The type denotes the unified type from the operation
    AppendL(ExprType, Box<IRExpr>, Box<IRExpr>),
    /// Adding integers
    AddI(Box<IRExpr>, Box<IRExpr>),
    /// Adding floats
    AddF(Box<IRExpr>, Box<IRExpr>),
    /// Subtracting integers
    SubI(Box<IRExpr>, Box<IRExpr>),
    /// Subtracting floats
    SubF(Box<IRExpr>, Box<IRExpr>),

    /// Equality
    IsEq(ExprType, Box<IRExpr>, Box<IRExpr>),
    /// Negation on bools
    Not(Box<IRExpr>),
    /// Inequalities on numbers
    IsLessI(Box<IRExpr>, Box<IRExpr>),
    IsLessF(Box<IRExpr>, Box<IRExpr>),

    /// Convert an integer into a float. These nodes don't appear in
    /// syntax, but are inserted by the typechecker.
    IntToFloat(Box<IRExpr>),

    /// Field lookup on an object. The DBType is inserted by the
    /// typechecker for convenience
    Path(ExprType, Box<IRExpr>, Ident<Field>),

    /// A variable
    Var(ExprType, Ident<Var>),

    /// An object expression. Made up of the object type, a list of
    /// field specifiers (tuples of identifiers and expressions whose
    /// value is bound to them), and an optional "template
    /// object". When the template object is not specified, the field
    /// list must contain all of the fields in the object; otherwise,
    /// missing fields take their values from the corresponding field
    /// on the template object.
    Object(
        Ident<Collection>,
        Vec<(Ident<Field>, Box<IRExpr>)>,
        Option<Box<IRExpr>>,
    ),

    /// Look up an id in a collection
    LookupById(Ident<Collection>, Box<IRExpr>),
    /// Look up an object in a collection by some template
    Find(Ident<Collection>, Vec<(Ident<Field>, Box<IRExpr>)>),
    /// A list expression
    List(ExprType, Vec<Box<IRExpr>>),
    /// Conditional expression
    If(ExprType, Box<IRExpr>, Box<IRExpr>, Box<IRExpr>),
    /// Constant primitive values
    IntConst(i64),
    FloatConst(f64),
    StringConst(String),
    BoolConst(bool),
}

pub fn extract_ir_expr(schema: &Schema, def_map: DefMap, expr: &ast::QueryExpr) -> Box<IRExpr> {
    let ir_expr = match expr {
        ast::QueryExpr::Plus(l, r) => {
            let left = extract_ir_expr(schema, def_map.clone(), l);
            let right = extract_ir_expr(schema, def_map.clone(), r);
            let (left, right) = align_types(left, right);

            match left.type_of() {
                ExprType::I64 => IRExpr::AddI(left, right),
                ExprType::F64 => IRExpr::AddF(left, right),
                ExprType::ListUnknown | ExprType::List(_) => {
                    let typ = if is_subtype(&left.type_of(), &right.type_of()) {
                        left.type_of()
                    } else {
                        right.type_of()
                    };
                    IRExpr::AppendL(typ, left, right)
                }
                ExprType::String => IRExpr::AppendS(left, right),
                _ => panic!(
                    "`+` operation not defined for types: {} + {}",
                    left.type_of(),
                    right.type_of()
                ),
            }
        }
        ast::QueryExpr::Minus(l, r) => {
            let left = extract_ir_expr(schema, def_map.clone(), l);
            let right = extract_ir_expr(schema, def_map.clone(), r);
            let (left, right) = align_types(left, right);

            match left.type_of() {
                ExprType::I64 => IRExpr::SubI(left, right),
                ExprType::F64 => IRExpr::SubF(left, right),
                _ => panic!(
                    "`-` operation not defined for types: {} + {}",
                    left.type_of(),
                    right.type_of()
                ),
            }
        }
        ast::QueryExpr::IsEq(l, r) => {
            let left = extract_ir_expr(schema, def_map.clone(), l);
            let right = extract_ir_expr(schema, def_map.clone(), r);
            let (left, right) = align_types(left, right);

            let typ = left.type_of();
            match &typ {
                ExprType::I64 | ExprType::F64 => {
                    IRExpr::IsEq(typ, left, right)
                }
                _ => panic!(
                    "`==` operation not defined for types: {} + {}",
                    left.type_of(),
                    right.type_of()
                ),
            }
        }
        ast::QueryExpr::IsNeq(l, r) => {
            let left = extract_ir_expr(schema, def_map.clone(), l);
            let right = extract_ir_expr(schema, def_map.clone(), r);
            let (left, right) = align_types(left, right);

            let typ = left.type_of();
            match &typ {
                ExprType::I64
                | ExprType::F64
                | ExprType::Id(_) => {
                    IRExpr::Not(Box::new(IRExpr::IsEq(typ, left, right)))
                }
                _ => panic!(
                    "`!=` operation not defined for types: {} + {}",
                    left.type_of(),
                    right.type_of()
                ),
            }
        }
        ast::QueryExpr::Not(e) => {
            let inner = extract_ir_expr(schema, def_map, e);

            match inner.type_of() {
                ExprType::Bool => IRExpr::Not(inner),
                _ => panic!("`not` operation not defined for type: {}", inner.type_of()),
            }
        }

        ast::QueryExpr::IsLess(l, r) => {
            let left = extract_ir_expr(schema, def_map.clone(), l);
            let right = extract_ir_expr(schema, def_map.clone(), r);
            let (left, right) = align_types(left, right);

            match &left.type_of() {
                ExprType::I64 => IRExpr::IsLessI(left, right),
                ExprType::F64 => IRExpr::IsLessF(left, right),
                _ => panic!(
                    "`<` operation not defined for types: {} + {}",
                    left.type_of(),
                    right.type_of()
                ),
            }
        }
        ast::QueryExpr::IsLessOrEq(l, r) => {
            let left = extract_ir_expr(schema, def_map.clone(), l);
            let right = extract_ir_expr(schema, def_map.clone(), r);
            let (left, right) = align_types(left, right);

            match &left.type_of() {
                ExprType::I64 => {
                    IRExpr::Not(Box::new(IRExpr::IsLessI(right, left)))
                }
                ExprType::F64 => {
                    IRExpr::Not(Box::new(IRExpr::IsLessF(right, left)))
                }
                _ => panic!(
                    "`<=` operation not defined for types: {} + {}",
                    left.type_of(),
                    right.type_of()
                ),
            }
        }
        ast::QueryExpr::IsGreater(l, r) => {
            let left = extract_ir_expr(schema, def_map.clone(), l);
            let right = extract_ir_expr(schema, def_map.clone(), r);
            let (left, right) = align_types(left, right);

            match &left.type_of() {
                ExprType::I64 => IRExpr::IsLessI(right, left),
                ExprType::F64 => IRExpr::IsLessF(right, left),
                _ => panic!(
                    "`>` operation not defined for types: {} + {}",
                    left.type_of(),
                    right.type_of()
                ),
            }
        }
        ast::QueryExpr::IsGreaterOrEq(l, r) => {
            let left = extract_ir_expr(schema, def_map.clone(), l);
            let right = extract_ir_expr(schema, def_map.clone(), r);
            let (left, right) = align_types(left, right);

            match &left.type_of() {
                ExprType::I64 => {
                    IRExpr::Not(Box::new(IRExpr::IsLessI(left, right)))
                }
                ExprType::F64 => {
                    IRExpr::Not(Box::new(IRExpr::IsLessF(left, right)))
                }
                _ => panic!(
                    "`>=` operation not defined for types: {} + {}",
                    left.type_of(),
                    right.type_of()
                ),
            }
        }
        ast::QueryExpr::Var(v) => {
            let (ident, typ) = def_map
                .lookup(v)
                .expect(&format!("Use of undefined variable: {}", v));
            IRExpr::Var(typ, ident)
        }
        ast::QueryExpr::IntConst(val) => IRExpr::IntConst(*val),
        ast::QueryExpr::FloatConst(val) => IRExpr::FloatConst(*val),
        ast::QueryExpr::StringConst(val) => IRExpr::StringConst(val.clone()),
        ast::QueryExpr::BoolConst(val) => IRExpr::BoolConst(*val),
        ast::QueryExpr::If(cond, then, els) => {
            let cond = extract_ir_expr(schema, def_map.clone(), cond);
            let then = extract_ir_expr(schema, def_map.clone(), then);
            let els = extract_ir_expr(schema, def_map.clone(), els);

            let cond = coerce(&ExprType::bool(), cond);
            let (then, els) = align_types(then, els);

            let typ = if is_subtype(&then.type_of(), &els.type_of()) {
                then.type_of()
            } else {
                els.type_of()
            };

            IRExpr::If(typ, cond, then, els)
        }
        ast::QueryExpr::FieldAccess(obj_expr, elem) => {
            let obj_expr = extract_ir_expr(schema, def_map, obj_expr);

            let coll = match obj_expr.type_of() {
                // Unwrap is safe unless we screwed up lowering
                ExprType::Object(ref coll) => &schema[coll],
                typ @ _ => panic!(
                    "Field access (`.`) operator requires an Object. Found: {}",
                    typ
                ),
            };

            let field = coll.find_field(elem).expect(&format!(
                "Field `{}` not found on collection `{}`",
                elem, coll.name.orig_name
            ));

            IRExpr::Path(field.typ.clone(), obj_expr, field.name.clone())
        }
        ast::QueryExpr::Object(obj_lit) => {
            let coll = schema.find_collection(&obj_lit.coll).expect(&format!(
                "Unable to construct object literal because collection `{}` does not exist",
                obj_lit.coll
            ));

            // All the present fields, lowered.
            let mut ir_fields = vec![];
            for (fname, fexpr) in obj_lit.fields.iter() {
                let field = coll.find_field(fname).expect(&format!(
                    "Unable to find field {} on collection {}",
                    fname, &coll.name.orig_name
                ));
                let fexpr = coerce(
                    &field.typ,
                    extract_ir_expr(schema, def_map.clone(), fexpr),
                );

                ir_fields.push((field.name.clone(), fexpr));
            }

            let template = obj_lit.template_obj.as_ref().map(|texpr| {
                let expr = extract_ir_expr(schema, def_map.clone(), texpr);
                coerce(&ExprType::Object(coll.name.clone()), expr)
            });

            // If there's no template we have to verify that all the fields are present
            if template.is_none() {
                for field in coll.fields() {
                    // Id's should come from the DB
                    if field.is_id() {
                        continue;
                    }
                    if !ir_fields
                        .iter()
                        .find(|(ident, _)| *ident == field.name)
                        .is_none()
                    {
                        panic!(
                            "Object literal for type `{}` missing field `{}`",
                            &coll.name.orig_name, &field.name.orig_name
                        );
                    }
                }
            }

            IRExpr::Object(coll.name.clone(), ir_fields, template)
        }
        ast::QueryExpr::Find(coll_name, fields) => {
            let coll = schema.find_collection(coll_name).expect(&format!(
                "Unable to lookup by id because collection `{}` does not exist",
                coll_name
            ));
            // All the present fields, lowered.
            let mut ir_fields = vec![];
            for (fname, fexpr) in fields.iter() {
                let field = coll.find_field(fname).expect(&format!(
                    "Unable to find field {} on collection {}",
                    fname, &coll.name.orig_name
                ));
                let fexpr = coerce(
                    &field.typ,
                    extract_ir_expr(schema, def_map.clone(), fexpr),
                );

                ir_fields.push((field.name.clone(), fexpr));
            }
            IRExpr::Find(coll.name.clone(), ir_fields)
        }
        ast::QueryExpr::LookupById(coll_name, id_expr) => {
            let coll = schema.find_collection(coll_name).expect(&format!(
                "Unable to lookup by id because collection `{}` does not exist",
                coll_name
            ));
            let id_expr = extract_ir_expr(schema, def_map, id_expr);
            let id_expr = coerce(&ExprType::id(coll.name.clone()), id_expr);

            IRExpr::LookupById(coll.name.clone(), id_expr)
        }
        ast::QueryExpr::List(elems) => {
            if elems.len() == 0 {
                IRExpr::List(ExprType::ListUnknown, vec![])
            } else {
                let lowered_elems: Vec<_> = elems
                    .iter()
                    .map(|expr| extract_ir_expr(schema, def_map.clone(), expr))
                    .collect();
                let mut most_specific_type = lowered_elems[0].type_of();

                for expr in lowered_elems.iter() {
                    if is_subtype(&expr.type_of(), &most_specific_type) {
                        most_specific_type = expr.type_of();
                    }
                }

                let lowered_elems: Vec<_> = lowered_elems
                    .into_iter()
                    .map(|expr| coerce(&most_specific_type, expr))
                    .collect();

                IRExpr::List(ExprType::list(most_specific_type.clone()), lowered_elems)
            }
        }
    };

    return Box::new(ir_expr);
}

fn is_subtype(typ1: &ExprType, typ2: &ExprType) -> bool {
    match (typ1, typ2) {
        (ExprType::List(inner1), ExprType::List(inner2)) => is_subtype(inner1, inner2),
        (ExprType::List(_), ExprType::ListUnknown) => true,
        _ => typ1 == typ2,
    }
}

fn coerce(typ: &ExprType, expr: Box<IRExpr>) -> Box<IRExpr> {
    let expr_typ = expr.type_of();
    if expr_typ == *typ {
        return expr;
    }
    match (typ, expr_typ) {
        (ExprType::F64, ExprType::I64) => {
            Box::new(IRExpr::IntToFloat(expr))
        }
        _ => panic!("Unable to coerce to type {}\n expr {:#?}", typ, expr),
    }
}

/// Handles coercions favoring Int->Float conversion and List<Unknown> -> List<Foo>
fn align_types(left: Box<IRExpr>, right: Box<IRExpr>) -> (Box<IRExpr>, Box<IRExpr>) {
    // They already match
    if is_subtype(&left.type_of(), &right.type_of())
        || is_subtype(&right.type_of(), &left.type_of())
    {
        return (left, right);
    }

    let float = ExprType::F64;

    match (left.type_of(), right.type_of()) {
        // Upgrade the non-float expr to an expr
        (ExprType::F64, ExprType::I64)
        | (ExprType::I64, ExprType::F64) => {
            (coerce(&float, left), coerce(&float, right))
        }
        (l_typ, r_typ) => panic!("Unable to reconcile types {}, {}", l_typ, r_typ),
    }
}

impl IRExpr {
    pub fn type_of(&self) -> ExprType {
        match self {
            IRExpr::AddI(..) | IRExpr::SubI(..) | IRExpr::IntConst(_) => {
                ExprType::I64
            }

            IRExpr::IntToFloat(_) | IRExpr::FloatConst(_) | IRExpr::AddF(..) | IRExpr::SubF(..) => {
                ExprType::F64
            }

            IRExpr::StringConst(_) => ExprType::String,
            IRExpr::AppendS(..) => ExprType::String,

            IRExpr::IsEq(..)
            | IRExpr::Not(..)
            | IRExpr::IsLessF(..)
            | IRExpr::BoolConst(..)
            | IRExpr::IsLessI(..) => ExprType::Bool,

            IRExpr::Path(typ, ..) => typ.clone(),
            IRExpr::Object(coll, ..) | IRExpr::LookupById(coll, ..) | IRExpr::Find(coll, ..) => {
                ExprType::Object(coll.clone())
            }

            IRExpr::Var(typ, ..)
            | IRExpr::AppendL(typ, ..)
            | IRExpr::List(typ, ..)
            | IRExpr::If(typ, ..) => typ.clone()
        }
    }
}
