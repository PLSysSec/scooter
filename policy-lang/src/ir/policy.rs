use super::{
    expr::{extract_func, ExprType, Func},
    schema::{Collection, Field, Schema},
    Ident,
};
use crate::ast;
use std::collections::HashMap;

/// Describes the policy for access of a given schema
#[derive(Debug)]
pub struct SchemaPolicy {
    pub schema: Schema,
    pub collection_policies: HashMap<Ident<Collection>, CollectionPolicy>,
    pub field_policies: HashMap<Ident<Field>, FieldPolicy>,
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

pub fn extract_partial_schema_policy(
    gp: &ast::GlobalPolicy,
) -> SchemaPolicy {
    let schema = super::schema::extract_schema(gp);
    ExtractionContext {
        schema,
    }
    .extract_schema_policy(gp)
}

struct ExtractionContext {
    pub(crate) schema: Schema,
}

impl ExtractionContext {
    /// Because Schemas are self-referential, (that is the `Foo::bar` can be of type `Id(Foo)`)
    /// we first have to create an index of all the type names so we can have stable identifiers
    fn new(schema: Schema) -> Self {
        Self {
            schema,
        }
    }

    fn extract_schema_policy(self, gp: &ast::GlobalPolicy) -> SchemaPolicy {
        let mut collection_policies = HashMap::new();
        let mut field_policies = HashMap::new();

        for cp in gp.collections.iter() {
            let coll = self.schema.find_collection(&cp.name).unwrap();
            let coll_id = coll.name.clone();

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
            schema: self.schema,
        }
    }

    fn extract_coll_policy(&self, cp: &ast::CollectionPolicy) -> CollectionPolicy {
        let coll = self.schema.find_collection(&cp.name).unwrap();

        CollectionPolicy {
            create: extract_policy(
                &self.schema,
                &coll.name,
                &cp.create,
            ),
            delete: extract_policy(
                &self.schema,
                &coll.name,
                &cp.delete,
            ),
        }
    }

    fn extract_field_policy(&self, coll_name: &str, fp: &ast::FieldPolicy) -> FieldPolicy {
        let coll = self.schema.find_collection(coll_name).unwrap();

        FieldPolicy {
            // TODO: Bring AST names inline
            edit: extract_policy(
                &self.schema,
                &coll.name,
                &fp.write,
            ),
            read: extract_policy(
                &self.schema,
                &coll.name,
                &fp.read,
            ),
        }
    }
}

/// Extracs a policy for the specified collection. The collection ident is used
/// to set the expected type of the policy function (if present)
pub fn extract_policy(
    schema: &Schema,
    coll: &Ident<Collection>,
    p: &ast::Policy,
) -> Policy {
    match p {
        ast::Policy::Public => Policy::Anyone,
        ast::Policy::None => Policy::None,
        ast::Policy::Func(e) => Policy::Func(extract_func(
            schema,
            ExprType::Object(coll.clone()),
            &ExprType::list(ExprType::id(schema.principle.clone())),
            e,
        )),
    }
}
