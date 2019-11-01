use crate::ast;
use std::collections::HashMap;

#[derive(Debug)]
pub enum Type {
    Prim(Prim),
    Id(TypeId),
    Collection(Collection),
}

#[derive(Debug)]
pub enum Prim {
    Any,
}

#[derive(Debug)]
pub struct Collection {
    pub name: IdentId,
    pub fields: HashMap<String, Field>,
}

#[derive(Debug)]
pub struct Field(IdentId, TypeId);
impl Field {
    pub fn ident(&self) -> IdentId {
        self.0
    }

    pub fn type_id(&self) -> TypeId {
        self.1
    }
}

#[derive(Debug)]
pub struct TyCtx {
    types: Vec<Type>,
    idents: Vec<Ident>,
    ident_types: HashMap<IdentId, TypeId>,
}

/// A default TyCtx already contains the primitive types
impl Default for TyCtx {
    fn default() -> TyCtx {
        TyCtx {
            types: vec![Type::Prim(Prim::Any)],
            idents: Default::default(),
            ident_types: Default::default(),
        }
    }
}

impl TyCtx {
    pub fn collections(&self) -> impl Iterator<Item=&Collection> {
        self.types.iter().filter_map(|t| match t {
            Type::Collection(c) => Some(c),
            _ => None
        })
    }

    pub fn all_types(&self) -> impl Iterator<Item=&Type> {
        self.types.iter()
    }

    fn new_type(&mut self, typ: Type) {
        self.types.push(typ);
    }

    fn new_ident(&mut self, s: impl ToString) -> IdentId {
        self.idents.push(Ident(s.to_string()));
        IdentId(self.idents.len() - 1)
    }

    fn ascribe_type(&mut self, id: IdentId, tid: TypeId) {
        assert!(id.0 < self.idents.len());
        assert!(tid.0 < self.types.len());

        self.ident_types.insert(id, tid);
    }

    pub fn get_type(&self, tid: TypeId) -> &Type {
        &self.types[tid.0]
    }

    pub fn get_ident(&self, id: IdentId) -> &Ident {
        &self.idents[id.0]
    }

    pub fn type_of(&self, id: IdentId) -> &Ident {
        &self.idents[id.0]
    }

    pub fn get_type_name(&self, t: &Type) -> String {
        match t {
            Type::Prim(Prim::Any) => "Any".to_string(),
            Type::Id(tid) => format!("Id({})", self.get_type_name(self.get_type(*tid))),
            Type::Collection(c) => self.get_ident(c.name).0.clone(),
        }
    }

    pub fn field(&self, tid: TypeId, fname: &str)  -> &Field {
        match self.get_type(tid) {
            Type::Collection(Collection { fields, ..}) => &fields[fname],
            _ => panic!("Only collections types have fields")
        }
    }
}

struct LocalCtx {
    pub name_to_ident: HashMap<String, IdentId>,
    pub name_to_type: HashMap<String, TypeId>,
}

impl LocalCtx {
    pub fn from_ty_ctx(ty_ctx: &TyCtx) -> LocalCtx {
        let mut name_to_type = HashMap::<String, TypeId>::new();
        for (i, t) in ty_ctx.types.iter().enumerate() {
            name_to_type.insert(ty_ctx.get_type_name(t), TypeId(i));
        }

        LocalCtx {
            name_to_ident: Default::default(),
            name_to_type,
        }
    }
}

pub fn extract_types(gp: &ast::GlobalPolicy<String>) -> TyCtx {
    let mut ty_ctx = Default::default();
    let mut ctx = LocalCtx::from_ty_ctx(&ty_ctx);

    // Pre-populate name_to_type.
    //
    // Consider this example:
    //
    // User {
    //    best_friend: Id(User)
    // }
    //
    // To describe the best_friend field, we need the TypeId for User. This
    // means we need to pregenerate the TypeIds for all types before we generate
    // the Type object. This works out because TypeIds correspond to indices in
    // declaration order.
    for (i, coll_pol) in gp.collections.iter().enumerate() {
        ctx.name_to_type
            // We add the types len since it is prepopulated with built-in types
            // If we didn't add this, our collection names would map to built-ins
            .insert(coll_pol.name.clone(), TypeId(i + ty_ctx.types.len()));
    }

    // Generate the actual collection types
    for coll_pol in gp.collections.iter() {
        let mut coll = Collection {
            name: ty_ctx.new_ident(coll_pol.name.clone()),
            fields: HashMap::new(),
        };

        coll.fields.insert("id".to_string(), Field(ty_ctx.new_ident("id".to_string()), TypeId(0)));

        // Populate the fields
        for (fname, _) in coll_pol.fields.iter() {
            coll.fields.insert(
                fname.clone(),
                // The field ident should be fresh and we can rely on our prepopulated name -> type mapping
                // TODO: Make this use real types
                Field(ty_ctx.new_ident(format!("{}.{}", &coll_pol.name, &fname)), TypeId(0)),
                
            );
        }

        // We don't need the tid back, since we manually calculated it earlier
        let _ = ty_ctx.new_type(Type::Collection(coll));
    }

    ty_ctx
}

#[derive(Copy, Clone, Debug, Eq, PartialEq, Hash)]
pub struct IdentId(usize);
impl From<IdentId> for usize {
    fn from(id: IdentId) -> usize {
        id.0
    }
}
#[derive(Copy, Clone, Debug, Eq, PartialEq, Hash)]
pub struct TypeId(usize);
impl From<TypeId> for usize {
    fn from(tid: TypeId) -> usize {
        tid.0
    }
}

#[derive(Debug)]
pub struct Ident(String);
impl Ident {
    pub fn raw(&self) -> &str {
        &self.0
    }
}
pub type CompletePolicy = HashMap<TypeId, CollectionPolicy>;
pub struct CollectionPolicy {
    pub type_id: TypeId,
    pub fields: HashMap<IdentId, ast::FieldPolicy<IdentId>>,
}

pub type PolicyFunc = ast::PolicyFunc<IdentId>;
pub type Policy = ast::Policy<IdentId>;
pub type QueryExpr = ast::QueryExpr<IdentId>;

pub fn resolve(ty_ctx: &mut TyCtx, gp: ast::GlobalPolicy<String>) -> CompletePolicy {
    let mut ctx = LocalCtx::from_ty_ctx(ty_ctx);

    gp.collections
        .into_iter()
        .map(|cp| {
            (
                ctx.name_to_type[&cp.name],
                resolve_collection_policy(ty_ctx, &mut ctx, cp),
            )
        })
        .collect()
}

fn resolve_collection_policy(
    ty_ctx: &mut TyCtx,
    ctx: &mut LocalCtx,
    cp: ast::CollectionPolicy<String>,
) -> CollectionPolicy {
    let type_id = ctx.name_to_type[&cp.name];

    let fields = cp.fields.iter().map(|(fname, fpolicy)| {
        (ty_ctx.field(type_id, &fname).ident(), ast::FieldPolicy {
            ty: fpolicy.ty.clone(),
            read: resolve_policy(ty_ctx, ctx, type_id, &fpolicy.read),
            write: resolve_policy(ty_ctx, ctx, type_id, &fpolicy.write),
        })
    }).collect();

    CollectionPolicy {
        type_id,
        fields
    }
}

fn resolve_policy(
    ty_ctx: &mut TyCtx,
    ctx: &mut LocalCtx,
    coll_tid: TypeId,
    p: &ast::Policy<String>,
) -> ast::Policy<IdentId> {
    use ast::Policy;

    match p {
        Policy::Public => Policy::Public,
        Policy::None => Policy::None,
        Policy::Func(pf) => Policy::Func(resolve_policy_func(ty_ctx, ctx, coll_tid, pf))
    }
}

fn resolve_policy_func(
    ty_ctx: &mut TyCtx,
    ctx: &mut LocalCtx,
    coll_tid: TypeId,
    pf: &ast::PolicyFunc<String>,
) -> ast::PolicyFunc<IdentId> {
    use ast::PolicyFunc;

    let param = ty_ctx.new_ident(pf.param.clone());
    ctx.name_to_ident.insert(pf.param.clone(), param);
    ty_ctx.ascribe_type(param, coll_tid);

    PolicyFunc {
        param,
        expr: resolve_query_expr(ty_ctx, ctx, &pf.expr)
    }
}

fn resolve_query_expr(
    ty_ctx: &mut TyCtx,
    ctx: &mut LocalCtx,
    qe: &ast::QueryExpr<String>,
) -> Box<ast::QueryExpr<IdentId>> {
    use ast::QueryExpr;

    let low_expr = match qe {
        QueryExpr::Or(l, r) => QueryExpr::Or(
            resolve_query_expr(ty_ctx, ctx, &l), 
            resolve_query_expr(ty_ctx, ctx, &r)
        ),
        QueryExpr::Path(p) => {
            let mut low_p = Vec::with_capacity(p.len());

            let mut segs = p.into_iter();
            let first_seg = segs.next().unwrap();
            let first_ident = ctx.name_to_ident[first_seg];

            low_p.push(first_ident);

            let mut curr_type = ty_ctx.ident_types[&first_ident];

            while let Some(seg) = segs.next() {
                let Field(id, tid) = ty_ctx.field(curr_type, seg);
                low_p.push(*id);
                curr_type = *tid;
            }

            QueryExpr::Path(low_p)
        }
    };

    Box::new(low_expr)
}
