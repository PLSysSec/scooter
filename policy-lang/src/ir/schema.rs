use super::Ident;
use crate::ast;
use std::{collections::HashMap, ops::Index};

#[derive(Debug, PartialEq, Eq)]
pub struct Schema {
    collections: Vec<Collection>,
}

impl Schema {
    pub fn find_collection(&self, name: &str) -> Option<&Collection> {
        self.collections.iter().find(|c| c.name.eq_str(name))
    }
}

impl Index<Ident<Collection>> for Schema {
    type Output = Collection;
    fn index(&self, ident: Ident<Collection>) -> &Self::Output {
        self.collections
            .iter()
            .find(|c| c.name == ident)
            .expect(&format!(
                "Internal error: ident {:?} not found in schema",
                ident
            ))
    }
}

impl Index<Ident<Field>> for Schema {
    type Output = Field;
    fn index(&self, ident: Ident<Field>) -> &Self::Output {
        for c in self.collections.iter() {
            for (_, f) in c.fields.iter() {
                if f.name == ident {
                    return f;
                }
            }
        }
        panic!("Internal error: ident {:?} not found in schema", ident);
    }
}

/// Describes a database collection
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Collection {
    pub name: Ident<Self>,
    fields: Vec<(String, Field)>,
}

impl Collection {
    pub fn fields(&self) -> impl Iterator<Item = &(String, Field)> {
        self.fields.iter()
    }
    pub fn find_field(&self, fname: &str) -> Option<&Field> {
        self.fields.iter().find(|(n, _)| n == fname).map(|(_, f)| f)
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Field {
    pub name: Ident<Self>,
    pub typ: DBType,
}

impl Field {
    pub fn is_id(&self) -> bool {
        self.name.eq_str("id")
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum DBType {
    Id(Ident<Collection>),
    String,
    I64,
    F64,
    Bool,
}

pub fn extract_schema(gp: &ast::GlobalPolicy) -> Schema {
    ExtractionContext::new(gp).extract_schema(gp)
}

struct ExtractionContext {
    coll_idents: HashMap<String, Ident<Collection>>,
}

impl ExtractionContext {
    /// Because Schemas are self-referential, (that is the `Foo::bar` can be of type `Id(Foo)`)
    /// we first have to create an index of all the type names so we can have stable identifiers
    fn new(gp: &ast::GlobalPolicy) -> Self {
        let mut coll_idents = HashMap::new();
        for cp in gp.collections.iter() {
            coll_idents.insert(cp.name.clone(), Ident::new(&cp.name));
        }

        Self { coll_idents }
    }

    fn extract_schema(&mut self, gp: &ast::GlobalPolicy) -> Schema {
        Schema {
            collections: gp
                .collections
                .iter()
                .map(|cp| self.extract_collection(cp))
                .collect(),
        }
    }

    fn extract_collection(&self, cp: &ast::CollectionPolicy) -> Collection {
        Collection {
            name: self.coll_idents[&cp.name].clone(),
            fields: cp
                .fields
                .iter()
                .map(|(fname, fp)| (fname.clone(), self.extract_field(fname, fp)))
                .collect(),
        }
    }

    fn extract_field(&self, fname: &str, fp: &ast::FieldPolicy) -> Field {
        Field {
            name: Ident::new(fname),
            typ: self.extract_type(&fp.ty),
        }
    }

    fn extract_type(&self, ty: &ast::FieldType) -> DBType {
        use ast::FieldType;

        match ty {
            FieldType::String => DBType::String,
            FieldType::I64 => DBType::I64,
            FieldType::F64 => DBType::F64,
            FieldType::Bool => DBType::Bool,
            FieldType::Id(ref name) => DBType::Id(self.coll_idents[name].clone()),
            FieldType::List(_) => unimplemented!("Lowering lists"),
        }
    }
}
