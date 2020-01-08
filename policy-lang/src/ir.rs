use crate::ast;
use id_arena::Arena;
pub use id_arena::Id;
use std::collections::HashMap;
use std::fmt;

mod lower;
pub use lower::*;

mod expr;
pub use expr::*;

#[derive(Debug)]
pub struct Ident(pub u32, pub String);
static mut IDENT_CT: u32 = 0;

impl Ident {
    fn new(s: impl ToString) -> Self {
        unsafe {
            IDENT_CT += 1;
            Ident(IDENT_CT, s.to_string())
        }
    }

    fn eq_str(&self, s: impl AsRef<str>) -> bool {
        self.1 == s.as_ref()
    }
}

/// Describes a variable definition
#[derive(Debug)]
pub struct Def {
    pub id: Id<Def>,
    pub name: Ident,
}

/// Describes a database collection
#[derive(Debug)]
pub struct Collection {
    pub id: Id<Collection>,
    pub name: Ident,
    fields: Vec<(String, (Id<Def>, bool))>,
}

impl Collection {
    fn typ(&self) -> Type {
        Type::Collection(self.id)
    }

    pub fn name(&self) -> &Ident {
        &self.name
    }

    pub fn lookup_field(&self, name: &str) -> Option<Id<Def>> {
        self.fields
            .iter()
            .find(|(fname, (_id, is_retired))| fname == name && !is_retired)
            .map(|(_fname, (id, _is_retired))| id.clone())
    }

    pub fn fields(&self) -> impl Iterator<Item = (&String, &Id<Def>)> {
        self.fields
            .iter()
            .filter(|(_name, (_id, retired))| !retired)
            .map(|(name, (id, _retired))| (name, id))
    }
    pub fn field_name(&self, field_id: &Id<Def>) -> String {
        self.fields
            .iter()
            .find(|(_string_name, (id, _is_retired))| id == field_id)
            .expect(&format!("Couldn't find field {:?} on object", field_id))
            .0
            .clone()
    }
    pub fn add_field(&mut self, name: String, id: Id<Def>) {
        self.fields.push((name, (id, false)));
    }
    pub fn retire_field(&mut self, id: &Id<Def>) {
        let mut field_entry = self
            .fields
            .iter_mut()
            .find(|(_fname, (fid, _is_retired))| fid == id)
            .expect("Couldn't find field to retire");
        assert!(!((field_entry.1).1));
        (field_entry.1).1 = true;
    }
}

/// Describes a type such as "String" or "Id(User)"
#[derive(Debug, Clone, PartialEq)]
pub enum Type {
    Prim(Prim),
    Id(Id<Collection>),
    Collection(Id<Collection>),
    List(Box<Type>),
    ListAny,
    ListId,
}
#[derive(Debug, Clone, PartialEq)]
pub enum Prim {
    String,
    I64,
    F64,
    Bool,
}

impl fmt::Display for Type {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Type::Prim(p) => write!(f, "{}", p),
            Type::Id(id) => write!(f, "Id({:?})", id),
            Type::Collection(id) => write!(f, "Coll({:?})", id),
            Type::List(bty) => write!(f, "List({})", *bty),
            Type::ListAny => write!(f, "List(Any)"),
            Type::ListId => write!(f, "ListId"),
        }
    }
}
impl fmt::Display for Prim {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Prim::String => write!(f, "String"),
            Prim::I64 => write!(f, "I64"),
            Prim::F64 => write!(f, "F64"),
            Prim::Bool => write!(f, "Bool"),
        }
    }
}


/// IrData contains the type and name resolution data resulting from lowering the AST to a CompletePolicy.
/// When comparing policies, you'll use the same IrData to analyze both of them
/// so that all the type resolutions line up.
#[derive(Debug, Default)]
pub struct IrData {
    colls: Arena<Collection>,
    retired_colls: Vec<Id<Collection>>,
    defs: Arena<Def>,
    exprs: Arena<Expr>,
    expr_types: HashMap<Id<Expr>, Type>,
    def_types: HashMap<Id<Def>, Type>,
}

impl IrData {
    /// Creates an iterator of all the collections within the IrData
    pub fn collections(&self) -> impl Iterator<Item = &Collection> {
        self.colls.iter().map(|(_, c)| c)
    }

    pub fn active_collections(&self) -> impl Iterator<Item = &Collection> {
        self.colls
            .iter()
            .filter(|(id, _c)| !self.retired_colls.contains(id))
            .collect::<Vec<(Id<Collection>, &Collection)>>()
            .into_iter()
            .map(|(_, c)| c)
    }

    /// Resolves an Id<Collection>. It's identical to running `&ird[coll_id]`
    pub fn collection(&self, cid: Id<Collection>) -> &Collection {
        &self.colls[cid]
    }

    pub fn add_collection(&mut self, name: &str, layout: Vec<(String, Type)>) -> Id<Collection> {
        let coll_id = self.colls.alloc_with_id(|id| Collection {
            id,
            name: Ident::new(&name),
            fields: vec![],
        });
        for (field_name, field_type) in layout {
            self.add_field(coll_id, field_name, field_type);
        }
        coll_id
    }
    pub fn retire_collection(&mut self, id: Id<Collection>) {
        self.retired_colls.push(id);
    }

    /// Resolves an Id<Def>. It's identical to running `&ird[def_id]`
    pub fn def(&self, did: Id<Def>) -> &Def {
        &self.defs[did]
    }

    /// Resolves an Id<Expr>. It's identical to running `&ird[expr_id]`
    pub fn expr(&self, eid: Id<Expr>) -> &Expr {
        &self.exprs[eid]
    }

    /// Finds the type of a given def
    pub fn def_type(&self, did: Id<Def>) -> &Type {
        &self
            .def_types
            .get(&did)
            .expect("Unable to find type for def")
    }

    fn create_def(&mut self, name: impl ToString, typ: Type) -> Id<Def> {
        let did = self.defs.alloc_with_id(|id| Def {
            id,
            name: Ident::new(name.to_string()),
        });
        self.def_types.insert(did, typ);
        did
    }
    pub fn change_def_type(&mut self, def: Id<Def>, new_type: Type) {
        assert!(self.def_types.insert(def, new_type).is_some());
    }

    /// A convenience method that handles the multiple lookups required to get the field definition
    pub fn field(&self, cid: Id<Collection>, fname: &str) -> &Def {
        &self[self[cid]
            .lookup_field(fname)
            .expect(&format!("Couldn't find field {}", fname))]
    }

    pub fn add_field(&mut self, cid: Id<Collection>, fname: String, ftype: Type) {
        let field_def = self.create_def(fname.clone(), ftype);
        self.colls[cid].add_field(fname, field_def);
    }

    /// Lowers the ast to its IR representation, accruing information into the IrData struct
    pub fn lower(&mut self, gp: &ast::GlobalPolicy) -> CompletePolicy {
        let mut l = Lowerer {
            ird: self,
            def_map: HashMap::new(),
        };

        l.lower_policies(gp)
    }

    pub fn lower_migration(&mut self, mig: ast::Migration) -> CompleteMigration {
        let mut l = Lowerer {
            ird: self,
            def_map: HashMap::new(),
        };
        l.lower_migration_commands(mig)
    }
}

/// Creates an IrData based around the types present in a single AST.
/// This step is separated from the lower phase so that we can resolve each AST relative to the same set of types.
pub fn extract_types(gp: &ast::GlobalPolicy) -> IrData {
    // Due to mutability shenanigancs, we have to use an deconstructed IrDatat
    // that we will assemble at the end of the function
    let mut colls = Arena::<Collection>::new();
    let mut defs = Arena::<Def>::new();
    let mut def_types = HashMap::<Id<Def>, Type>::new();

    let mut name_to_coll = HashMap::<String, Id<Collection>>::new();

    // Create a collection for each collection definition, but without any of the fields
    // Consider this example:
    //
    // User {
    //    contact: Id(Email)
    // }
    //
    // Email {}
    //
    // To fully define User, we'll require a stable reference to the Email collection, which is defined later.
    // This is why we first create each collection as if it had no fields, then go back later and insert the fields
    // once every collection has an id
    for coll_pol in gp.collections.iter() {
        let coll_id = colls.alloc_with_id(|id| Collection {
            id,
            name: Ident::new(&coll_pol.name),
            fields: vec![],
        });

        name_to_coll.insert(coll_pol.name.clone(), coll_id);
    }

    for coll_pol in gp.collections.iter() {
        let coll_id = name_to_coll[&coll_pol.name];
        // Unwrap is safe here because of our mapping we stored
        let coll = colls.get_mut(coll_id).unwrap();

        // The id field is inferred
        let id_field = defs.alloc_with_id(|id| Def {
            id,
            name: Ident::new("id"),
        });
        def_types.insert(id_field, Type::Id(coll_id));
        coll.add_field("id".to_string(), id_field);

        // Populate the fields
        for (fname, fpol) in coll_pol.fields.iter() {
            let field_did = defs.alloc_with_id(|id| Def {
                id,
                name: Ident::new(fname),
            });

            let field_type = lower_type_with_table(&name_to_coll, &fpol.ty);
            def_types.insert(field_did, field_type);
            coll.add_field(fname.clone(), field_did);
        }
    }

    IrData {
        colls,
        defs,
        def_types,
        ..Default::default()
    }
}

fn lower_type_with_table(table: &HashMap<String, Id<Collection>>, ty: &ast::FieldType) -> Type {
    match ty {
        ast::FieldType::String => Type::Prim(Prim::String),
        ast::FieldType::Id(cname) => Type::Id(table[cname]),
        ast::FieldType::I64 => Type::Prim(Prim::I64),
        ast::FieldType::F64 => Type::Prim(Prim::F64),
        ast::FieldType::List(inner_type) => {
            Type::List(Box::new(lower_type_with_table(table, inner_type)))
        }
        ast::FieldType::Bool => Type::Prim(Prim::Bool),
    }
}

macro_rules! impl_index {
    ($t:ty, $coll:ident) => {
        impl std::ops::Index<Id<$t>> for IrData {
            type Output = $t;

            fn index(&self, id: Id<$t>) -> &Self::Output {
                &self.$coll[id]
            }
        }
    };
}

impl_index!(Def, defs);
impl_index!(Expr, exprs);
impl_index!(Collection, colls);

trait TypeResolver<T> {
    fn type_of(&self, id: Id<T>) -> &Type;
}

impl TypeResolver<Expr> for IrData {
    fn type_of(&self, id: Id<Expr>) -> &Type {
        &self.expr_types[&id]
    }
}

impl TypeResolver<Def> for IrData {
    fn type_of(&self, id: Id<Def>) -> &Type {
        &self.def_types[&id]
    }
}
