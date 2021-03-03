use super::{expr::ExprType, expr::Var, Ident};
use crate::ast;
use std::{
    collections::{HashMap, HashSet},
    ops::{Index, IndexMut},
};

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Schema {
    pub static_principals: Vec<Ident<Var>>,
    pub dynamic_principals: Vec<Ident<Collection>>,
    pub collections: Vec<Collection>,
}

impl Schema {
    pub fn find_collection(&self, name: &str) -> Option<&Collection> {
        self.collections.iter().find(|c| c.name.eq_str(name))
    }
    pub fn merge(s1: &Self, s2: &Self) -> Self {
        Schema {
            static_principals: s1
                .static_principals
                .iter()
                .cloned()
                .chain(s2.static_principals.clone().into_iter())
                .collect(),
            dynamic_principals: s1
                .dynamic_principals
                .iter()
                .cloned()
                .chain(s2.dynamic_principals.iter().cloned())
                .collect(),
            collections: s1
                .collections
                .iter()
                .cloned()
                .chain(s2.collections.clone().into_iter())
                .collect(),
        }
    }
}

impl Index<&Ident<Collection>> for Schema {
    type Output = Collection;
    fn index(&self, ident: &Ident<Collection>) -> &Self::Output {
        self.collections
            .iter()
            .find(|c| c.name == *ident)
            .expect(&format!(
                "Internal error: ident {:?} not found in schema",
                ident
            ))
    }
}

impl IndexMut<&Ident<Collection>> for Schema {
    fn index_mut(&mut self, ident: &Ident<Collection>) -> &mut Self::Output {
        self.collections
            .iter_mut()
            .find(|c| c.name == *ident)
            .expect(&format!(
                "Internal error: ident {:?} not found in schema",
                ident
            ))
    }
}

impl Index<&Ident<Field>> for Schema {
    type Output = Field;
    fn index(&self, ident: &Ident<Field>) -> &Self::Output {
        for c in self.collections.iter() {
            for f in c.fields.iter() {
                if f.name == *ident {
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
    pub fields: Vec<Field>,
}

impl Collection {
    pub fn fields(&self) -> impl Iterator<Item = &Field> {
        self.fields.iter()
    }
    pub fn find_field(&self, fname: &str) -> Option<&Field> {
        self.fields.iter().find(|f| f.name.eq_str(fname))
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Field {
    pub name: Ident<Self>,
    pub typ: ExprType,
}

impl Field {
    pub fn is_id(&self) -> bool {
        self.name.is_id()
    }
}

impl Ident<Field> {
    pub fn is_id(&self) -> bool {
        self.eq_str("id")
    }
}

pub fn extract_schema(gp: &ast::GlobalPolicy) -> Schema {
    let result = ExtractionContext::new(gp, Vec::new()).extract_schema(gp);
    result
}

pub fn extract_partial_schema(
    gp: &ast::GlobalPolicy,
    existing_colls: Vec<Ident<Collection>>,
) -> Schema {
    ExtractionContext::new(gp, existing_colls).extract_schema(gp)
}

struct ExtractionContext {
    coll_idents: HashMap<String, Ident<Collection>>,
}

impl ExtractionContext {
    /// Because Schemas are self-referential, (that is the `Foo::bar` can be of type `Id(Foo)`)
    /// we first have to create an index of all the type names so we can have stable identifiers
    fn new(gp: &ast::GlobalPolicy, extra_colls: Vec<Ident<Collection>>) -> Self {
        let mut coll_idents = HashMap::new();
        for cp in gp.collections.iter() {
            coll_idents.insert(cp.name.clone(), Ident::new(&cp.name));
        }
        for coll_name in extra_colls {
            coll_idents.insert(coll_name.orig_name.clone(), coll_name);
        }

        Self { coll_idents }
    }

    fn find_principals(gp: &ast::GlobalPolicy) -> Vec<String> {
        let mut principals = Vec::new();
        for cp in gp.collections.iter() {
            match cp.annotations.as_slice() {
                [ast::Annotation::Principal] => principals.push(cp.name.clone()),
                [] => {}
                _ => panic!(
                    "Error on {}. Only a single annotation (`@principal`) is allowed.",
                    &cp.name
                ),
            }
        }
        principals
    }

    fn extract_schema(&mut self, gp: &ast::GlobalPolicy) -> Schema {
        let colls: Vec<_> = gp
            .collections
            .iter()
            .map(|cp| self.extract_collection(cp))
            .collect();
        let static_principals = gp
            .static_principals
            .iter()
            .map(|sp| Ident::new(&sp.name))
            .collect();
        let dynamic_principals = Self::find_principals(gp)
            .iter()
            .map(|name| {
                colls
                    .iter()
                    .find(|coll| coll.name.orig_name == *name)
                    .unwrap()
                    .name
                    .clone()
            })
            .collect();
        Schema {
            static_principals: static_principals,
            dynamic_principals: dynamic_principals,
            collections: colls,
        }
    }

    fn extract_collection(&self, cp: &ast::CollectionPolicy) -> Collection {
        let mut field_names = HashSet::new();

        // Automatically create the id field
        let mut fields = vec![Field {
            name: Ident::new("id"),
            typ: ExprType::Id(self.coll_idents[&cp.name].clone()),
        }];
        field_names.insert("id".to_string());

        // Insert all the fields defined in the file
        for (fname, fp) in cp.fields.iter() {
            if field_names.contains(fname) {
                panic!(
                    "Duplicate field name {} found in collection {}",
                    fname, cp.name
                )
            }
            fields.push(self.extract_field(fname, fp));
            field_names.insert(fname.to_string());
        }

        Collection {
            name: self.coll_idents[&cp.name].clone(),
            fields: fields,
        }
    }

    fn extract_field(&self, fname: &str, fp: &ast::FieldPolicy) -> Field {
        Field {
            name: Ident::new(fname),
            typ: self.extract_type(&fp.ty),
        }
    }

    fn extract_type(&self, ty: &ast::FieldType) -> ExprType {
        use ast::FieldType;

        match ty {
            FieldType::String => ExprType::String,
            FieldType::I64 => ExprType::I64,
            FieldType::F64 => ExprType::F64,
            FieldType::Bool => ExprType::Bool,
            FieldType::DateTime => ExprType::DateTime,
            FieldType::Id(ref name) => ExprType::Id(
                self.coll_idents
                    .get(name)
                    .expect(&format!(
                        "Bad type Id({}): couldn't find collection {}; collections are {:?}",
                        name, name, self.coll_idents
                    ))
                    .clone(),
            ),
            FieldType::Set(ty) => {
                if let FieldType::Set(_) = **ty {
                    panic!("Schemas may not contain nested lists")
                };

                ExprType::Set(Box::new(self.extract_type(ty)))
            }
            FieldType::Option(ty) => ExprType::Option(Box::new(self.extract_type(ty))),
        }
    }
}

pub(crate) fn extract_type(schema: &Schema, ty: &ast::FieldType) -> ExprType {
    use ast::FieldType;

    match ty {
        FieldType::String => ExprType::String,
        FieldType::I64 => ExprType::I64,
        FieldType::F64 => ExprType::F64,
        FieldType::DateTime => ExprType::DateTime,
        FieldType::Bool => ExprType::Bool,
        FieldType::Id(ref name) => {
            let coll = schema
                .find_collection(name)
                .expect(&format!("Unable to find collection {} in Id({0})", name));

            ExprType::Id(coll.name.clone())
        }
        FieldType::Set(inner_ty) => ExprType::Set(Box::new(extract_type(schema, inner_ty))),
        FieldType::Option(inner_ty) => ExprType::Option(Box::new(extract_type(schema, inner_ty))),
    }
}
