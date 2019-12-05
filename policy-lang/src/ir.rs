use crate::ast;
use id_arena::Arena;
pub use id_arena::Id;
use std::collections::HashMap;


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
    fields: HashMap<String, Id<Def>>,
}

impl Collection {
    fn typ(&self) -> Type {
        Type::Collection(self.id)
    }

    pub fn name(&self) -> &Ident {
        &self.name
    }

    pub fn fields(&self) -> impl Iterator<Item=(&String, &Id<Def>)> {
        self.fields.iter()
    }
}

/// Describes a type such as "String" or "Id(User)"
#[derive(Debug, Clone)]
pub enum Type {
    String,
    Id(Id<Collection>),
    Collection(Id<Collection>),
}

/// IrData contains the type and name resolution data resulting from lowering the AST to a CompletePolicy.
/// When comparing policies, you'll use the same IrData to analyze both of them
/// so that all the type resolutions line up.
#[derive(Debug, Default)]
pub struct IrData {
    colls: Arena<Collection>,
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

    /// Resolves an Id<Collection>. It's identical to running `&ird[coll_id]`
    pub fn collection(&self, cid: Id<Collection>) -> &Collection {
        &self.colls[cid]
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
        &self.def_types.get(&did).expect("Unable to find type for def")
    }

    fn create_def(&mut self, name: impl ToString, typ: Type) -> Id<Def> {
        let did = self.defs.alloc_with_id(|id| Def {
            id,
            name: Ident::new(name.to_string()),
        });
        self.def_types.insert(did, typ);
        did
    }
    

    /// A convenience method that handles the multiple lookups required to get the field definition
    pub fn field(&self, cid: Id<Collection>, fname: &str) -> &Def {
        &self[self[cid].fields[fname]]
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
            fields: HashMap::new(),
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
        coll.fields.insert("id".to_string(), id_field);

        // Populate the fields
        for (fname, fpol) in coll_pol.fields.iter() {
            let field_did = defs.alloc_with_id(|id| Def {
                id,
                name: Ident::new(fname),
            });

            let field_type = match &fpol.ty {
                ast::FieldType::String => Type::String,
                ast::FieldType::Id(cname) => Type::Id(name_to_coll[cname]),
                _ => unimplemented!("Field type {:?} not supported by ir", fpol.ty)
            };

            def_types.insert(id_field, field_type);
            coll.fields.insert(fname.clone(), field_did);
        }
    }

    IrData {
        colls,
        defs,
        def_types,
        ..Default::default()
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
    }
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