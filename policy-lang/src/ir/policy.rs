use super::{
    expr::{extract_func, ExprType, Func},
    schema::{Collection, Field, Schema},
    Ident,
};
use crate::ast;
use std::collections::HashMap;
use ast::Annotation;

/// Describes the policy for access of a given schema
#[derive(Debug)]
pub struct SchemaPolicy {
    pub schema: Schema,
    pub collection_policies: HashMap<Ident<Collection>, CollectionPolicy>,
    pub field_policies: HashMap<Ident<Field>, FieldPolicy>,
    pub principle: Ident<Collection>,
}


#[derive(Debug)]
pub struct FieldPolicy {
    pub read: Policy,
    pub edit: Policy,
}

#[derive(Debug)]
pub enum Policy {
    None,
    Anyone,
    Func(Func),
}

#[derive(Debug)]
pub struct CollectionPolicy {
    pub create: Policy,
    pub delete: Policy,
}

pub fn extract_schema_policy(gp: &ast::GlobalPolicy) -> SchemaPolicy {
    let schema = super::schema::extract_schema(gp);
    ExtractionContext::new(schema).extract_schema_policy(gp)
}

struct ExtractionContext {
    schema: Schema
}

impl ExtractionContext {
    /// Because Schemas are self-referential, (that is the `Foo::bar` can be of type `Id(Foo)`)
    /// we first have to create an index of all the type names so we can have stable identifiers
    fn new(schema: Schema) -> Self {
        Self { schema }
    }

    fn extract_schema_policy(self, gp: &ast::GlobalPolicy) -> SchemaPolicy {
        let mut collection_policies = HashMap::new();
        let mut field_policies = HashMap::new();
        let mut principle = None;
        for cp in gp.collections.iter() {
            let coll = self.schema.find_collection(&cp.name).unwrap();
            let coll_id = coll.name.clone();
            
            // Extract any annotations
            match cp.annotations.as_slice() {
                [Annotation::Principle] => {
                    if let Some(old) = principle.replace(coll_id.clone()) {
                        panic!("Multiple collections cannot be marked as principles: {}, {}", &old.orig_name, &coll_id.orig_name)
                    }
                },
                [] => {},
                _ => panic!("Error on {}. Only a single annotation (`@principle`) is allowed.", &cp.name),
            };

            collection_policies.insert(coll_id, self.extract_coll_policy(cp));

            for (fname, fp) in cp.fields.iter() {
                // Should be safe because policy lang ensures policies are only on existing fields
                let fid = coll.find_field(fname).unwrap().name.clone();
                field_policies.insert(fid, self.extract_field_policy(&cp.name, &fp));
            }
        }

        SchemaPolicy {
            collection_policies,
            field_policies,
            principle: principle.expect("No `@principle` found in policy."),
            schema: self.schema,
        }
    }

    fn extract_coll_policy(&self, cp: &ast::CollectionPolicy) -> CollectionPolicy {
        let coll = self.schema.find_collection(&cp.name).unwrap();

        CollectionPolicy {
            create: extract_policy(&self.schema, coll.name.clone(), &cp.create),
            delete: extract_policy(&self.schema, coll.name.clone(), &cp.delete),
        }
    }

    fn extract_field_policy(&self, coll_name: &str, fp: &ast::FieldPolicy) -> FieldPolicy {
        let coll = self.schema.find_collection(coll_name).unwrap();

        FieldPolicy {
            // TODO: Bring AST names inline
            edit: extract_policy(&self.schema, coll.name.clone(), &fp.write),
            read: extract_policy(&self.schema, coll.name.clone(), &fp.read),
        }
    }
}

/// Extracs a policy for the specified collection. The collection ident is used
/// to set the expected type of the policy function (if present)
pub fn extract_policy(schema: &Schema, coll: Ident<Collection>, p: &ast::Policy) -> Policy {
    match p {
        ast::Policy::Public => Policy::Anyone,
        ast::Policy::None => Policy::None,
        ast::Policy::Func(e) => {
            Policy::Func(extract_func(schema, ExprType::id(coll), e))
        }
    }
}
