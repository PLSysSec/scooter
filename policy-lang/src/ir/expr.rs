use super::{
    schema::{Collection, Field, Schema},
    Ident,
};
use crate::ast;
use chrono::{DateTime, TimeZone, Utc};
use std::iter;
use std::{collections::HashMap, fmt, rc::Rc};

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
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum ExprType {
    Id(Ident<Collection>),
    Principle,
    String,
    I64,
    F64,
    Bool,
    DateTime,
    List(Box<ExprType>),
    Option(Box<ExprType>),
    Object(Ident<Collection>),
    /// Represents an unresolved type. These won't exist after lowering
    Unknown(Ident<ExprType>),
}

impl ExprType {
    pub fn list(elem: Self) -> Self {
        Self::List(Box::new(elem))
    }
    pub fn option(elem: Self) -> Self {
        Self::Option(Box::new(elem))
    }

    pub fn bool() -> Self {
        Self::Bool
    }

    pub fn id(ident: Ident<Collection>) -> Self {
        Self::Id(ident)
    }

    pub fn new_unknown() -> Self {
        ExprType::Unknown(Ident::new("unknown"))
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
            ExprType::DateTime => write!(f, "DateTime"),
            ExprType::List(ty) => write!(f, "List({})", ty),
            ExprType::Option(ty) => write!(f, "Option({})", ty),
            ExprType::Object(coll) => write!(f, "{}", coll.orig_name),
            ExprType::Unknown(id) => write!(f, "{}_{}", &id.orig_name, id.index),
            ExprType::Principle => write!(f, "Principle"),
        }
    }
}

#[derive(Debug, Clone)]
pub struct Func {
    pub param: Ident<Var>,
    pub param_type: ExprType,
    pub return_type: ExprType,
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
    let body = extract_ir_expr(schema, def_map, &func.expr, Some(exp_ret_type.clone()));

    Func {
        param: param_id,
        param_type,
        return_type: exp_ret_type.clone(),
        body,
    }
}

pub fn extract_ir_expr(
    schema: &Schema,
    def_map: DefMap,
    expr: &ast::QueryExpr,
    expected_ty: Option<ExprType>,
) -> Box<IRExpr> {
    let mut ctx = LoweringContext {
        type_map: Default::default(),
    };
    let mut expr = ctx.extract_ir_expr(schema, def_map, expr);
    if let Some(ref ty) = expected_ty {
        ctx.is_subtype(schema, &expr.type_of(), ty);
    }

    resolve_types(&ctx.type_map, &mut expr);

    if let Some(ref ty) = expected_ty {
        expr = ctx.coerce(schema, ty, expr);
    }

    expr
}

fn resolve_types(type_map: &HashMap<Ident<ExprType>, ExprType>, expr: &mut IRExpr) {
    match expr {
        IRExpr::AppendL(ref mut ty, l, r)
        | IRExpr::IsEq(ref mut ty, l, r) => {
            *ty = apply_ty(type_map, ty);
            resolve_types(type_map, l);
            resolve_types(type_map, r);
        }
        IRExpr::AppendS(l, r)
        | IRExpr::IsLessI(l, r)
        | IRExpr::IsLessF(l, r)
        | IRExpr::IsLessD(l, r)
        | IRExpr::AddI(l, r)
        | IRExpr::AddF(l, r)
        | IRExpr::AddD(l, r)
        | IRExpr::SubI(l, r)
        | IRExpr::SubF(l, r)
        | IRExpr::SubD(l, r) => {
            resolve_types(type_map, l);
            resolve_types(type_map, r);
        }
        IRExpr::Not(i)
        | IRExpr::IntToFloat(i)
        | IRExpr::LookupById(_, i)
        // NOTE: The type inference algorithm does not handle field accesses currently
        | IRExpr::Path(_, i, _) => {
            resolve_types(type_map, i)
        }

        IRExpr::Var(ty, _) => {
            *ty = apply_ty(type_map, ty);
        }
        IRExpr::Object(_, fields, _template) => {
            for (_, field) in fields.iter_mut() {
                if let Some(ref mut field) = field {
                    resolve_types(type_map, field);
                }
            }
        }
        IRExpr::Map(list_expr, func) => {
            func.param_type = apply_ty(type_map, &func.param_type);
            func.return_type = apply_ty(type_map, &func.return_type);
            resolve_types(type_map, &mut func.body);
            resolve_types(type_map, list_expr);
        }
        IRExpr::Find(_, fields) => {
            for (_, field) in fields.iter_mut() {
                resolve_types(type_map, field);
            }
        }
        IRExpr::List(ref mut ty, elems) => {
            *ty = apply_ty(type_map, ty);
            for elem in elems.iter_mut() {
                resolve_types(type_map, elem)
            }
        }
        IRExpr::If(ref mut ty, c, t, e) => {
            *ty = apply_ty(type_map, ty);
            resolve_types(type_map, c);
            resolve_types(type_map, t);
            resolve_types(type_map, e);
        }

        IRExpr::Match(ref mut ty, opt, _ident, e_some, e_none) => {
            *ty = apply_ty(type_map, ty);
            resolve_types(type_map, opt);
            resolve_types(type_map, e_some);
            resolve_types(type_map, e_none);
        }

        IRExpr::Some(ref mut ty, val) => {
            *ty = apply_ty(type_map, ty);
            resolve_types(type_map, val);
        }


        IRExpr::Now
        | IRExpr::DateTimeConst(..)
        | IRExpr::IntConst(_)
        | IRExpr::FloatConst(_)
        | IRExpr::StringConst(_)
        | IRExpr::BoolConst(_)
        | IRExpr::None(_) => {}
        IRExpr::Public => {}
    };
}

fn apply_ty(type_map: &HashMap<Ident<ExprType>, ExprType>, ty: &ExprType) -> ExprType {
    match ty {
        ExprType::Id(_)
        | ExprType::Principle
        | ExprType::String
        | ExprType::I64
        | ExprType::F64
        | ExprType::Object(_)
        | ExprType::DateTime
        | ExprType::Bool => ty.clone(),
        ExprType::List(lty) => ExprType::list(apply_ty(type_map, lty)),
        ExprType::Option(lty) => ExprType::option(apply_ty(type_map, lty)),
        ExprType::Unknown(id) => apply_ty(type_map, &type_map[id]),
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
    /// Adding dates and intervals
    AddD(Box<IRExpr>, Box<IRExpr>),
    /// Subtracting integers
    SubI(Box<IRExpr>, Box<IRExpr>),
    /// Subtracting floats
    SubF(Box<IRExpr>, Box<IRExpr>),
    /// Subtracting dates and intervals
    SubD(Box<IRExpr>, Box<IRExpr>),

    /// Equality
    IsEq(ExprType, Box<IRExpr>, Box<IRExpr>),
    /// Negation on bools
    Not(Box<IRExpr>),
    /// Inequalities on numbers
    IsLessI(Box<IRExpr>, Box<IRExpr>),
    IsLessF(Box<IRExpr>, Box<IRExpr>),
    /// Inequalities on dates
    IsLessD(Box<IRExpr>, Box<IRExpr>),

    /// Convert an integer into a float. These nodes don't appear in
    /// syntax, but are inserted by the typechecker.
    IntToFloat(Box<IRExpr>),

    /// Field lookup on an object.
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
        Vec<(Ident<Field>, Option<Box<IRExpr>>)>,
        Option<Box<IRExpr>>,
    ),

    /// Functional map across lists
    Map(Box<IRExpr>, Func),

    /// Look up an id in a collection
    LookupById(Ident<Collection>, Box<IRExpr>),
    /// Look up an object in a collection by some template
    Find(Ident<Collection>, Vec<(Ident<Field>, Box<IRExpr>)>),
    /// A list expression
    List(ExprType, Vec<Box<IRExpr>>),
    /// Conditional expression
    If(ExprType, Box<IRExpr>, Box<IRExpr>, Box<IRExpr>),
    /// Matching on option values
    Match(ExprType, Box<IRExpr>, Ident<Var>, Box<IRExpr>, Box<IRExpr>),

    /// Date values
    Now,
    DateTimeConst(DateTime<Utc>),

    /// Constant primitive values
    IntConst(i64),
    FloatConst(f64),
    StringConst(String),
    BoolConst(bool),
    Public,

    /// Option constructors
    None(ExprType),
    Some(ExprType, Box<IRExpr>),
}

struct LoweringContext {
    type_map: HashMap<Ident<ExprType>, ExprType>,
}

impl LoweringContext {
    pub fn extract_ir_expr(
        &mut self,
        schema: &Schema,
        def_map: DefMap,
        expr: &ast::QueryExpr,
    ) -> Box<IRExpr> {
        let ir_expr = match expr {
            ast::QueryExpr::Plus(l, r) => {
                let left = self.extract_ir_expr(schema, def_map.clone(), l);
                let right = self.extract_ir_expr(schema, def_map.clone(), r);
                let (left, right) = self.align_types(schema, left, right);

                match left.type_of() {
                    ExprType::I64 => IRExpr::AddI(left, right),
                    ExprType::F64 => IRExpr::AddF(left, right),
                    ExprType::DateTime => IRExpr::AddD(left, right),
                    ExprType::List(_) => {
                        let typ = if self.is_subtype(schema, &left.type_of(), &right.type_of()) {
                            right.type_of()
                        } else {
                            left.type_of()
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
                let left = self.extract_ir_expr(schema, def_map.clone(), l);
                let right = self.extract_ir_expr(schema, def_map.clone(), r);
                let (left, right) = self.align_types(schema, left, right);

                match left.type_of() {
                    ExprType::I64 => IRExpr::SubI(left, right),
                    ExprType::F64 => IRExpr::SubF(left, right),
                    ExprType::DateTime => IRExpr::SubD(left, right),
                    _ => panic!(
                        "`-` operation not defined for types: {} + {}",
                        left.type_of(),
                        right.type_of()
                    ),
                }
            }
            ast::QueryExpr::IsEq(l, r) => {
                let left = self.extract_ir_expr(schema, def_map.clone(), l);
                let right = self.extract_ir_expr(schema, def_map.clone(), r);
                let (left, right) = self.align_types(schema, left, right);

                let typ = left.type_of();
                match &typ {
                    ExprType::I64
                    | ExprType::F64
                    | ExprType::String
                    | ExprType::DateTime
                    | ExprType::Id(_)
                    | ExprType::Bool => IRExpr::IsEq(typ, left, right),
                    _ => panic!(
                        "`==` operation not defined for types: {} + {}",
                        left.type_of(),
                        right.type_of()
                    ),
                }
            }
            ast::QueryExpr::IsNeq(l, r) => {
                let left = self.extract_ir_expr(schema, def_map.clone(), l);
                let right = self.extract_ir_expr(schema, def_map.clone(), r);
                let (left, right) = self.align_types(schema, left, right);

                let typ = left.type_of();
                match &typ {
                    ExprType::I64
                    | ExprType::F64
                    | ExprType::String
                    | ExprType::DateTime
                    | ExprType::Id(_)
                    | ExprType::Bool => IRExpr::Not(Box::new(IRExpr::IsEq(typ, left, right))),
                    _ => panic!(
                        "`!=` operation not defined for types: {} + {}",
                        left.type_of(),
                        right.type_of()
                    ),
                }
            }
            ast::QueryExpr::Not(e) => {
                let inner = self.extract_ir_expr(schema, def_map, e);

                match inner.type_of() {
                    ExprType::Bool => IRExpr::Not(inner),
                    _ => panic!("`not` operation not defined for type: {}", inner.type_of()),
                }
            }

            ast::QueryExpr::IsLess(l, r) => {
                let left = self.extract_ir_expr(schema, def_map.clone(), l);
                let right = self.extract_ir_expr(schema, def_map.clone(), r);
                let (left, right) = self.align_types(schema, left, right);

                match &left.type_of() {
                    ExprType::I64 => IRExpr::IsLessI(left, right),
                    ExprType::F64 => IRExpr::IsLessF(left, right),
                    ExprType::DateTime => IRExpr::IsLessD(left, right),
                    _ => panic!(
                        "`<` operation not defined for types: {} + {}",
                        left.type_of(),
                        right.type_of()
                    ),
                }
            }
            ast::QueryExpr::IsLessOrEq(l, r) => {
                let left = self.extract_ir_expr(schema, def_map.clone(), l);
                let right = self.extract_ir_expr(schema, def_map.clone(), r);
                let (left, right) = self.align_types(schema, left, right);

                match &left.type_of() {
                    ExprType::I64 => IRExpr::Not(Box::new(IRExpr::IsLessI(right, left))),
                    ExprType::F64 => IRExpr::Not(Box::new(IRExpr::IsLessF(right, left))),
                    ExprType::DateTime => IRExpr::Not(Box::new(IRExpr::IsLessD(right, left))),
                    _ => panic!(
                        "`<=` operation not defined for types: {} + {}",
                        left.type_of(),
                        right.type_of()
                    ),
                }
            }
            ast::QueryExpr::IsGreater(l, r) => {
                let left = self.extract_ir_expr(schema, def_map.clone(), l);
                let right = self.extract_ir_expr(schema, def_map.clone(), r);
                let (left, right) = self.align_types(schema, left, right);

                match &left.type_of() {
                    ExprType::I64 => IRExpr::IsLessI(right, left),
                    ExprType::F64 => IRExpr::IsLessF(right, left),
                    ExprType::DateTime => IRExpr::IsLessD(right, left),
                    _ => panic!(
                        "`>` operation not defined for types: {} + {}",
                        left.type_of(),
                        right.type_of()
                    ),
                }
            }
            ast::QueryExpr::IsGreaterOrEq(l, r) => {
                let left = self.extract_ir_expr(schema, def_map.clone(), l);
                let right = self.extract_ir_expr(schema, def_map.clone(), r);
                let (left, right) = self.align_types(schema, left, right);

                match &left.type_of() {
                    ExprType::I64 => IRExpr::Not(Box::new(IRExpr::IsLessI(left, right))),
                    ExprType::F64 => IRExpr::Not(Box::new(IRExpr::IsLessF(left, right))),
                    ExprType::DateTime => IRExpr::Not(Box::new(IRExpr::IsLessD(left, right))),
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
                    .or_else(|| {
                        schema
                            .static_principles
                            .iter()
                            .find(|sp| sp.orig_name == *v)
                            .map(|sp| (sp.clone(), ExprType::Principle))
                    })
                    .expect(&format!("Use of undefined variable: {}", v));
                IRExpr::Var(typ, ident)
            }
            ast::QueryExpr::IntConst(val) => IRExpr::IntConst(*val),
            ast::QueryExpr::FloatConst(val) => IRExpr::FloatConst(*val),
            ast::QueryExpr::StringConst(val) => IRExpr::StringConst(val.clone()),
            ast::QueryExpr::BoolConst(val) => IRExpr::BoolConst(*val),
            ast::QueryExpr::DateTimeConst(mo, d, y, h, mi, s) => {
                IRExpr::DateTimeConst(Utc.ymd(*y as i32, *mo, *d).and_hms(*h, *mi, *s))
            }
            ast::QueryExpr::Now => IRExpr::Now,
            ast::QueryExpr::None => IRExpr::None(ExprType::new_unknown()),
            ast::QueryExpr::Some(e) => {
                let inner = self.extract_ir_expr(schema, def_map, e);
                IRExpr::Some(inner.type_of(), inner)
            }
            ast::QueryExpr::If(cond, then, els) => {
                let cond = self.extract_ir_expr(schema, def_map.clone(), cond);
                let then = self.extract_ir_expr(schema, def_map.clone(), then);
                let els = self.extract_ir_expr(schema, def_map.clone(), els);

                let cond = self.coerce(schema, &ExprType::bool(), cond);
                let (then, els) = self.align_types(schema, then, els);

                let typ = if self.is_subtype(schema, &then.type_of(), &els.type_of()) {
                    els.type_of()
                } else {
                    then.type_of()
                };

                IRExpr::If(typ, cond, then, els)
            }
            ast::QueryExpr::Match(opt, ident, e_some, e_none) => {
                let var_ty = ExprType::Unknown(Ident::new("match_var"));
                let opt_expr = self.extract_ir_expr(schema, def_map.clone(), opt);
                let opt_expr = self.coerce(schema, &ExprType::option(var_ty.clone()), opt_expr);
                let var_ty = match opt_expr.type_of() {
                    ExprType::Option(ty) => *ty,
                    _ => unreachable!("We just set the type"),
                };
                let var_ident = Ident::new(ident.clone());
                let some_expr = self.extract_ir_expr(
                    schema,
                    def_map.extend(&var_ident.orig_name, var_ident.clone(), var_ty.clone()),
                    e_some,
                );
                let none_expr = self.extract_ir_expr(schema, def_map, e_none);

                let (some_expr, none_expr) = self.align_types(schema, some_expr, none_expr);

                let body_type =
                    if self.is_subtype(schema, &some_expr.type_of(), &none_expr.type_of()) {
                        some_expr.type_of()
                    } else {
                        none_expr.type_of()
                    };

                IRExpr::Match(body_type, opt_expr, var_ident, some_expr, none_expr)
            }
            ast::QueryExpr::FieldAccess(obj_expr, elem) => {
                let obj_expr = self.extract_ir_expr(schema, def_map, obj_expr);

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

                    if field.is_id() {
                        panic!("id not allowed on object literals");
                    }
                    let fexpr = self.extract_ir_expr(schema, def_map.clone(), fexpr);
                    let fexpr = self.coerce(schema, &field.typ, fexpr);

                    ir_fields.push((field.name.clone(), Some(fexpr)));
                }

                let missing_fields: Vec<_> = coll
                    .fields()
                    .filter(|f| {
                        ir_fields
                            .iter()
                            .find(|(ident, _)| *ident == f.name)
                            .is_none()
                    })
                    .collect();

                let texpr = match obj_lit.template_obj {
                    None => {
                        // The 1 is id which should be missing
                        if missing_fields.len() != 1 {
                            panic!(
                                "Object literal for type `{}` missing field(s) `{}`",
                                &coll.name.orig_name,
                                &missing_fields
                                    .iter()
                                    .map(|i| i.name.orig_name.clone())
                                    .collect::<Vec<_>>()
                                    .join(", "),
                            );
                        }
                        None
                    }
                    Some(ref texpr) => {
                        let expr = self.extract_ir_expr(schema, def_map.clone(), texpr);
                        let expr = self.coerce(schema, &ExprType::Object(coll.name.clone()), expr);

                        for field in missing_fields {
                            if field.is_id() {
                                continue;
                            }
                            ir_fields.push((field.name.clone(), None));
                        }

                        Some(expr)
                    }
                };

                IRExpr::Object(coll.name.clone(), ir_fields, texpr)
            }
            ast::QueryExpr::Map(list_expr, func) => {
                let param_ty = ExprType::Unknown(Ident::new("map_param"));
                let list_ir_expr = self.extract_ir_expr(schema, def_map.clone(), list_expr);
                let list_ir_expr =
                    self.coerce(schema, &ExprType::list(param_ty.clone()), list_ir_expr);
                let param_ty = match list_ir_expr.type_of() {
                    ExprType::List(p) => *p,
                    _ => unreachable!("We just set the type"),
                };
                let param_ident = Ident::new(func.param.clone());
                let body_expr = self.extract_ir_expr(
                    schema,
                    def_map.extend(
                        &param_ident.orig_name,
                        param_ident.clone(),
                        param_ty.clone(),
                    ),
                    &func.expr,
                );
                IRExpr::Map(
                    list_ir_expr,
                    Func {
                        param: param_ident,
                        param_type: param_ty,
                        return_type: body_expr.type_of(),
                        body: body_expr,
                    },
                )
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
                    let fexpr = self.extract_ir_expr(schema, def_map.clone(), fexpr);
                    let fexpr = self.coerce(schema, &field.typ, fexpr);

                    ir_fields.push((field.name.clone(), fexpr));
                }
                IRExpr::Find(coll.name.clone(), ir_fields)
            }
            ast::QueryExpr::LookupById(coll_name, id_expr) => {
                let coll = schema.find_collection(coll_name).expect(&format!(
                    "Unable to lookup by id because collection `{}` does not exist",
                    coll_name
                ));
                let id_expr = self.extract_ir_expr(schema, def_map, id_expr);
                let id_expr = self.coerce(schema, &ExprType::id(coll.name.clone()), id_expr);

                IRExpr::LookupById(coll.name.clone(), id_expr)
            }
            ast::QueryExpr::List(elems) => {
                if elems.len() == 0 {
                    IRExpr::List(ExprType::new_unknown(), vec![])
                } else {
                    let lowered_elems: Vec<_> = elems
                        .iter()
                        .map(|expr| self.extract_ir_expr(schema, def_map.clone(), expr))
                        .collect();
                    let mut most_general_type = lowered_elems[0].type_of();

                    for expr in lowered_elems.iter() {
                        if self.is_subtype(schema, &most_general_type, &expr.type_of()) {
                            most_general_type = expr.type_of();
                        }
                    }

                    let lowered_elems: Vec<_> = lowered_elems
                        .into_iter()
                        .map(|expr| self.coerce(schema, &most_general_type, expr))
                        .collect();

                    IRExpr::List(most_general_type.clone(), lowered_elems)
                }
            }
            ast::QueryExpr::Public => IRExpr::Public,
        };

        return Box::new(ir_expr);
    }

    fn is_subtype(&mut self, schema: &Schema, typ1: &ExprType, typ2: &ExprType) -> bool {
        match (typ1, typ2) {
            (ExprType::List(inner1), ExprType::List(inner2))
            | (ExprType::Option(inner1), ExprType::Option(inner2)) => {
                self.is_subtype(schema, inner1, inner2)
            }
            (ExprType::Unknown(id), l) | (l, ExprType::Unknown(id)) => {
                if !self.type_map.contains_key(&id) {
                    self.type_map.insert(id.clone(), l.clone());
                    true
                } else {
                    self.is_subtype(schema, l, &self.type_map[&id].clone())
                }
            }
            (ExprType::Id(coll), ExprType::Principle) => schema.principle.as_ref().unwrap() == coll,
            _ => typ1 == typ2,
        }
    }

    pub fn coerce(&mut self, schema: &Schema, typ: &ExprType, expr: Box<IRExpr>) -> Box<IRExpr> {
        let expr_typ = expr.type_of();
        if self.is_subtype(schema, &expr_typ, typ) {
            return expr;
        }
        match (typ, &expr_typ) {
            (ExprType::F64, ExprType::I64) => Box::new(IRExpr::IntToFloat(expr)),
            _ => panic!(
                "Unable to coerce to type {}\n expr {:#?}\nexpr_type {:?}",
                typ, expr, expr_typ
            ),
        }
    }

    /// Handles coercions favoring Int->Float conversion and List<Unknown> -> List<Foo>
    fn align_types(
        &mut self,
        schema: &Schema,
        left: Box<IRExpr>,
        right: Box<IRExpr>,
    ) -> (Box<IRExpr>, Box<IRExpr>) {
        // They already match
        if self.is_subtype(schema, &left.type_of(), &right.type_of())
            || self.is_subtype(schema, &right.type_of(), &left.type_of())
        {
            return (left, right);
        }

        let float = ExprType::F64;

        match (left.type_of(), right.type_of()) {
            // Upgrade the non-float expr to an expr
            (ExprType::F64, ExprType::I64) | (ExprType::I64, ExprType::F64) => (
                self.coerce(schema, &float, left),
                self.coerce(schema, &float, right),
            ),
            (l_typ, r_typ) => panic!("Unable to reconcile types {}, {}", l_typ, r_typ),
        }
    }
}

impl IRExpr {
    pub fn type_of(&self) -> ExprType {
        match self {
            IRExpr::Public => ExprType::list(ExprType::Principle),
            IRExpr::AddI(..) | IRExpr::SubI(..) | IRExpr::IntConst(_) => ExprType::I64,

            IRExpr::IntToFloat(_) | IRExpr::FloatConst(_) | IRExpr::AddF(..) | IRExpr::SubF(..) => {
                ExprType::F64
            }

            IRExpr::DateTimeConst(..) | IRExpr::Now | IRExpr::AddD(..) | IRExpr::SubD(..) => {
                ExprType::DateTime
            }

            IRExpr::StringConst(_) => ExprType::String,
            IRExpr::AppendS(..) => ExprType::String,

            IRExpr::IsEq(..)
            | IRExpr::Not(..)
            | IRExpr::IsLessF(..)
            | IRExpr::IsLessD(..)
            | IRExpr::BoolConst(..)
            | IRExpr::IsLessI(..) => ExprType::Bool,

            IRExpr::Path(typ, ..) => typ.clone(),
            IRExpr::Object(coll, ..) | IRExpr::LookupById(coll, ..) => {
                ExprType::Object(coll.clone())
            }
            IRExpr::Map(_list_expr, func) => ExprType::list(func.return_type.clone()),

            IRExpr::Find(coll, ..) => ExprType::list(ExprType::Object(coll.clone())),

            IRExpr::Var(typ, ..)
            | IRExpr::AppendL(typ, ..)
            | IRExpr::If(typ, ..)
            | IRExpr::Match(typ, ..) => typ.clone(),
            IRExpr::List(typ, ..) => ExprType::list(typ.clone()),
            IRExpr::None(typ) | IRExpr::Some(typ, ..) => ExprType::option(typ.clone()),
        }
    }
    pub fn map(&self, f: &dyn Fn(IRExpr) -> IRExpr) -> IRExpr {
        match self {
            IRExpr::AppendS(l, r) => f(IRExpr::AppendS(
                Box::new(l.as_ref().map(f)),
                Box::new(r.as_ref().map(f)),
            )),
            IRExpr::AppendL(ty, l, r) => f(IRExpr::AppendL(
                ty.clone(),
                Box::new(l.as_ref().map(f)),
                Box::new(r.as_ref().map(f)),
            )),
            IRExpr::AddI(l, r) => f(IRExpr::AddI(
                Box::new(l.as_ref().map(f)),
                Box::new(r.as_ref().map(f)),
            )),
            IRExpr::AddF(l, r) => f(IRExpr::AddF(
                Box::new(l.as_ref().map(f)),
                Box::new(r.as_ref().map(f)),
            )),
            IRExpr::AddD(l, r) => f(IRExpr::AddF(
                Box::new(l.as_ref().map(f)),
                Box::new(r.as_ref().map(f)),
            )),
            IRExpr::SubI(l, r) => f(IRExpr::SubI(
                Box::new(l.as_ref().map(f)),
                Box::new(r.as_ref().map(f)),
            )),
            IRExpr::SubF(l, r) => f(IRExpr::SubF(
                Box::new(l.as_ref().map(f)),
                Box::new(r.as_ref().map(f)),
            )),
            IRExpr::SubD(l, r) => f(IRExpr::SubD(
                Box::new(l.as_ref().map(f)),
                Box::new(r.as_ref().map(f)),
            )),
            IRExpr::IsEq(ty, l, r) => f(IRExpr::IsEq(
                ty.clone(),
                Box::new(l.as_ref().map(f)),
                Box::new(r.as_ref().map(f)),
            )),
            IRExpr::Not(b) => f(IRExpr::Not(Box::new(b.as_ref().map(f)))),
            IRExpr::IsLessI(l, r) => f(IRExpr::IsLessI(
                Box::new(l.as_ref().map(f)),
                Box::new(r.as_ref().map(f)),
            )),
            IRExpr::IsLessF(l, r) => f(IRExpr::IsLessF(
                Box::new(l.as_ref().map(f)),
                Box::new(r.as_ref().map(f)),
            )),
            IRExpr::IsLessD(l, r) => f(IRExpr::IsLessD(
                Box::new(l.as_ref().map(f)),
                Box::new(r.as_ref().map(f)),
            )),
            IRExpr::IntToFloat(i) => f(IRExpr::IntToFloat(Box::new(i.as_ref().map(f)))),
            IRExpr::Path(ty, o, fld) => f(IRExpr::Path(
                ty.clone(),
                Box::new(o.as_ref().map(f)),
                fld.clone(),
            )),
            IRExpr::Var(_ty, _name) => f(self.clone()),
            IRExpr::Public => f(self.clone()),
            IRExpr::Object(coll, fields, template) => f(IRExpr::Object(
                coll.clone(),
                fields
                    .iter()
                    .map(|(fld, opt_val)| {
                        (fld.clone(), opt_val.as_ref().map(|fe| Box::new(fe.map(f))))
                    })
                    .collect(),
                template.as_ref().map(|te| Box::new(te.map(f))),
            )),
            IRExpr::Map(list_expr, func) => f(IRExpr::Map(
                Box::new(list_expr.map(f)),
                Func {
                    param: func.param.clone(),
                    param_type: func.param_type.clone(),
                    return_type: func.return_type.clone(),
                    body: Box::new(func.body.map(f)),
                },
            )),
            IRExpr::LookupById(coll, id_expr) => f(IRExpr::LookupById(
                coll.clone(),
                Box::new(id_expr.as_ref().map(f)),
            )),
            IRExpr::Find(coll, query_fields) => f(IRExpr::Find(
                coll.clone(),
                query_fields
                    .iter()
                    .map(|(fld, val)| (fld.clone(), Box::new(val.map(f))))
                    .collect(),
            )),
            IRExpr::List(ty, items) => f(IRExpr::List(
                ty.clone(),
                items.iter().map(|item| Box::new(item.map(f))).collect(),
            )),
            IRExpr::If(ty, cond, iftrue, iffalse) => f(IRExpr::If(
                ty.clone(),
                Box::new(cond.as_ref().map(f)),
                Box::new(iftrue.as_ref().map(f)),
                Box::new(iffalse.as_ref().map(f)),
            )),
            IRExpr::Match(ty, opt_expr, var, some_expr, none_expr) => f(IRExpr::Match(
                ty.clone(),
                Box::new(opt_expr.as_ref().map(f)),
                var.clone(),
                Box::new(some_expr.as_ref().map(f)),
                Box::new(none_expr.as_ref().map(f)),
            )),
            IRExpr::None(_) => f(self.clone()),
            IRExpr::Some(ty, inner) => f(IRExpr::Some(ty.clone(), Box::new(inner.as_ref().map(f)))),

            IRExpr::DateTimeConst(..)
            | IRExpr::Now
            | IRExpr::IntConst(_)
            | IRExpr::FloatConst(_)
            | IRExpr::StringConst(_)
            | IRExpr::BoolConst(_) => f(self.clone()),
        }
    }
    pub fn subexprs_preorder<'a>(&'a self) -> impl Iterator<Item = &'a Self> {
        match self {
            IRExpr::Var(_, _)
            | IRExpr::Public
            | IRExpr::DateTimeConst(..)
            | IRExpr::Now
            | IRExpr::IntConst(_)
            | IRExpr::FloatConst(_)
            | IRExpr::StringConst(_)
            | IRExpr::BoolConst(_)
            | IRExpr::None(_) => vec![self].into_iter(),
            IRExpr::AppendS(l, r)
            | IRExpr::AppendL(_, l, r)
            | IRExpr::AddI(l, r)
            | IRExpr::AddF(l, r)
            | IRExpr::AddD(l, r)
            | IRExpr::SubI(l, r)
            | IRExpr::SubF(l, r)
            | IRExpr::SubD(l, r)
            | IRExpr::IsEq(_, l, r)
            | IRExpr::IsLessI(l, r)
            | IRExpr::IsLessF(l, r)
            | IRExpr::IsLessD(l, r) => iter::once(self)
                .chain(l.subexprs_preorder())
                .chain(r.subexprs_preorder())
                .collect::<Vec<_>>()
                .into_iter(),
            IRExpr::Not(e)
            | IRExpr::IntToFloat(e)
            | IRExpr::Path(_, e, _)
            | IRExpr::LookupById(_, e)
            | IRExpr::Some(_, e) => iter::once(self)
                .chain(e.subexprs_preorder())
                .collect::<Vec<_>>()
                .into_iter(),
            IRExpr::Object(_, fields, template_obj) => {
                let field_subexprs = fields
                    .iter()
                    .flat_map(|(_fld, val)| val)
                    .flat_map(|val| val.subexprs_preorder());
                let template_subexprs = match template_obj {
                    Some(obj) => obj.subexprs_preorder().collect::<Vec<_>>().into_iter(),
                    None => Vec::new().into_iter(),
                };
                iter::once(self)
                    .chain(field_subexprs)
                    .chain(template_subexprs)
                    .collect::<Vec<_>>()
                    .into_iter()
            }
            IRExpr::Map(list_expr, func) => iter::once(self)
                .chain(list_expr.subexprs_preorder())
                .chain(func.body.subexprs_preorder())
                .collect::<Vec<_>>()
                .into_iter(),
            IRExpr::Find(_, fields) => iter::once(self)
                .chain(
                    fields
                        .iter()
                        .flat_map(|(_fld, val)| val.subexprs_preorder()),
                )
                .collect::<Vec<_>>()
                .into_iter(),
            IRExpr::List(_ty, items) => iter::once(self)
                .chain(items.iter().flat_map(|item| item.subexprs_preorder()))
                .collect::<Vec<_>>()
                .into_iter(),
            IRExpr::If(_ty, cond, iftrue, iffalse) => iter::once(self)
                .chain(cond.subexprs_preorder())
                .chain(iftrue.subexprs_preorder())
                .chain(iffalse.subexprs_preorder())
                .collect::<Vec<_>>()
                .into_iter(),
            IRExpr::Match(_ty, opt_expr, _var, some_expr, none_expr) => iter::once(self)
                .chain(opt_expr.subexprs_preorder())
                .chain(some_expr.subexprs_preorder())
                .chain(none_expr.subexprs_preorder())
                .collect::<Vec<_>>()
                .into_iter(),
        }
    }
}
