use super::{
    expr::{extract_policy_func, IRExpr, Var},
    schema::{Collection, Field, Schema},
    Ident,
};
use crate::ast;
use std::collections::HashMap;
use ast::Annotation;

/// Describes the policy for access of a given schema
pub struct SchemaPolicy {
    pub schema: Schema,
    pub collection_policies: HashMap<Ident<Collection>, CollectionPolicy>,
    pub field_policies: HashMap<Ident<Field>, FieldPolicy>,
    pub principle: Ident<Collection>,
}

pub struct FieldPolicy {
    pub read: Policy,
    pub edit: Policy,
}

pub enum Policy {
    None,
    Anyone,
    Func(Ident<Var>, IRExpr),
}

pub struct CollectionPolicy {
    pub create: Policy,
    pub delete: Policy,
}

pub fn extract_policy(gp: &ast::GlobalPolicy) -> SchemaPolicy {
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
        CollectionPolicy {
            create: self.extract_policy(&cp.name, &cp.create),
            delete: self.extract_policy(&cp.name, &cp.delete),
        }
    }

    fn extract_field_policy(&self, coll_name: &str, fp: &ast::FieldPolicy) -> FieldPolicy {
        FieldPolicy {
            // TODO: Bring AST names inline
            edit: self.extract_policy(&coll_name, &fp.write),
            read: self.extract_policy(&coll_name, &fp.read),
        }
    }

    fn extract_policy(&self, coll_name: &str, p: &ast::Policy) -> Policy {
        match p {
            ast::Policy::Public => Policy::Anyone,
            ast::Policy::None => Policy::None,
            ast::Policy::Func(f) => {
                let coll = self.schema.find_collection(coll_name).unwrap();
                extract_policy_func(&self.schema, coll.name.clone(), f)
            }
        }
    }
}
