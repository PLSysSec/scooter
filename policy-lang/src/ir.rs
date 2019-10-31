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


/*
pub struct LowAst {
    pub res: Resolutions,
    pub policy: CompletePolicy,
}

pub type CompletePolicy = Vec<Model>;

pub struct Model {
    name: IdentId,
    typ: TypeId,
    field_policies: HashMap<IdentId, FieldPolicy<IdentId>>,
}

#[derive(Debug)]
pub enum Type {
    Prim,
    Id(TypeId),
    Collection(HashMap<String, IdentId>),
}

pub fn lower(gp: GlobalPolicy<String>) -> LowAst {
    let mut r: Resolver = Default::default();
    r.new_type("".into(), Type::Prim);

    let cp = r.lower_gp(gp);

    LowAst {
        res: r.res,
        policy: cp,
    }
}

#[derive(Default, Debug)]
pub struct Resolver {
    mappings: Mappings,
    res: Resolutions,
}

impl Resolver {
    fn prim(&self) -> TypeId {
        TypeId(0)
    }

    fn field_ident(&self, t: TypeId, s: String) -> IdentId {
        match self.res.types[&t] {
            Type::Collection(ref f) => f[&s],
            _ => panic!("Type was not a collection"),
        }
    }

    fn new_ident(&mut self, s: String, t: TypeId) -> IdentId {
        let id = self.res.gen_ident(s);
        self.res.type_of.insert(id, t);
        id
    }

    fn new_type(&mut self, _type_name: String, t: Type) -> TypeId {
        let type_id = TypeId(self.type_ct);
        self.type_ct += 1;

        self.res.types.insert(type_id, t);
        type_id
    }

    fn lower_gp(&mut self, gp: GlobalPolicy<String>) -> CompletePolicy {
        for coll in gp.collections.iter() {
            let typ = {
                let mut fields = HashMap::<String, IdentId>::new();
                for (n, _p) in coll.fields.iter() {
                    fields.insert(n.clone(), self.new_ident(n.clone(), self.prim()));
                }
                Type::Collection(fields)
            };

            self.new_type(coll.name.clone(), typ);
        }

        gp.collections
            .into_iter()
            .map(|c| self.lower_coll(c))
            .collect()
    }

    fn lower_coll(&mut self, cp: CollectionPolicy<String>) -> Model {
        let tid = self.mappings.type_ids[&cp.name];
        let id = self.new_ident(cp.name, tid);
        let mut low_cp = Model {
            name: id,
            typ: tid,
            field_policies: HashMap::new(),
        };

        for (name, pol) in cp.fields {
            low_cp
                .field_policies
                .insert(self.field_ident(tid, name), self.lower_field_pol(tid, pol));
        }

        low_cp
    }

    fn lower_field_pol(&mut self, tid: TypeId, fp: FieldPolicy<String>) -> FieldPolicy<IdentId> {
        FieldPolicy {
            read: self.lower_policy(tid, fp.read),
            write: self.lower_policy(tid, fp.write),
        }
    }

    fn lower_policy(&mut self, tid: TypeId, p: Policy<String>) -> Policy<IdentId> {
        match p {
            Policy::Public => Policy::Public,
            Policy::None => Policy::None,
            Policy::Func(pf) => Policy::Func(self.lower_pol_func(tid, pf)),
        }
    }

    fn lower_pol_func(&mut self, tid: TypeId, pf: PolicyFunc<String>) -> PolicyFunc<IdentId> {
        let param = self.new_ident(pf.param.clone(), tid);
        self.mappings.ident_ids.insert(pf.param, param);

        let expr = self.lower_expr(pf.expr);

        PolicyFunc { param, expr }
    }

    fn lower_expr(&mut self, expr: Box<QueryExpr<String>>) -> Box<QueryExpr<IdentId>> {
        let low_expr = match *expr {
            QueryExpr::Or(l, r) => QueryExpr::Or(self.lower_expr(l), self.lower_expr(r)),
            QueryExpr::Path(p) => {
                let mut low_p = Vec::with_capacity(p.len());

                let first_ident = self.mappings.ident_ids[&p[0]];
                let mut segs = p.into_iter();
                let mut curr_type = self.res.type_of[&first_ident];
                low_p.push(first_ident);

                while let Some(seg) = segs.next() {
                    let ident = self.field_ident(curr_type, seg);
                    low_p.push(ident);

                    curr_type = self.res.type_of[&ident];
                }

                QueryExpr::Path(low_p)
            }
        };

        Box::new(low_expr)
    }
}
*/
