use crate::ast;
use std::collections::HashMap;
use id_arena::{Arena, Id};
use std::rc::Rc;

mod lower;
pub use lower::*;

mod expr;
use expr::*;

#[derive(Debug)]
pub struct Ident(Rc<(u32, String)>);
static mut IDENT_CT: u32 = 0;

impl Ident {
    fn new(s: impl ToString) -> Self {
        unsafe {
            IDENT_CT += 1;
            Ident(Rc::new((IDENT_CT, s.to_string())))
        }
    }

    fn eq_str(&self, s: impl AsRef<str>) -> bool {
        (self.0).1 == s.as_ref()
    }
}



/// Describes a variable definition
#[derive(Debug)]
pub struct Def(Id<Def>, Ident);

/// Describes a database collection
#[derive(Debug)]
pub struct Collection {
    id: Id<Collection>,
    name: Ident,
    fields: HashMap<String, Id<Def>>,
}

impl Collection {
    fn typ(&self) -> Type {
        Type::Collection(self.id)
    }
}

/// Describes a type such as "String" or "Id(User)"
#[derive(Debug, Clone)]
pub enum Type {
    /// Right now, the IR doesn't model primitive types like "String"
    Value,
    Id(Id<Collection>),
    Collection(Id<Collection>),
}


#[derive(Debug, Default)]
pub struct IrData {
    colls: Arena<Collection>,
    defs: Arena<Def>,
    exprs: Arena<Expr>,
    expr_types: HashMap<Id<Expr>, Type>,
    def_types: HashMap<Id<Def>, Type>,
}

impl IrData {
    pub fn collections(&self) -> impl Iterator<Item=(Id<Collection>, &Collection)> {
        self.colls.iter()
    }

    fn create_def(&mut self, name: impl ToString, typ: Type) -> Id<Def>{
        let did = self.defs.alloc_with_id(|id| Def(id, Ident::new(name.to_string())));
        self.def_types.insert(did, typ);
        did
    }

    // pub fn get_type_name(&self, t: &Type) -> String {
    //     match t {
    //         Type::Prim(Prim::Any) => "Any".to_string(),
    //         Type::Id(tid) => format!("Id({})", self.get_type_name(self.get_type(*tid))),
    //         Type::Collection(c) => self.get_ident(c.name).0.clone(),
    //     }
    // }

    pub fn field(&self, cid: Id<Collection>, fname: &str)  -> Id<Def> {
        match self.colls.get(cid) {
            Some(Collection { fields, ..}) => fields[fname],
            _ => panic!("Only collections types have fields")
        }
    }

    pub fn lower(&mut self, gp: &ast::GlobalPolicy) -> CompletePolicy {
        let mut l = Lowerer {
            ird: self,
            def_map: HashMap::new()
        };

        l.lower_policies(gp)
    }
}

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
            fields: HashMap::new()
        });

        name_to_coll.insert(coll_pol.name.clone(), coll_id);
    }

    for coll_pol in gp.collections.iter() {
        let coll_id = name_to_coll[&coll_pol.name];
        // Unwrap is safe here because of our mapping we stored
        let coll = colls.get_mut(coll_id).unwrap();

        // The id field is inferred
        let id_field = defs.alloc_with_id(|id| Def(id, Ident::new("id")));
        def_types.insert(id_field, Type::Id(coll_id));
        coll.fields.insert("id".to_string(), id_field);

        // Populate the fields
        for (fname, _) in coll_pol.fields.iter() {
            let field_did = defs.alloc_with_id(|id| Def(id, Ident::new(fname)));
            def_types.insert(id_field, Type::Value);
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
