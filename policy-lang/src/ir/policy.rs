use super::{
    expr::{expr_to_string, extract_func, ExprType, Func, IRExpr},
    schema::{Collection, Field, Schema},
    Ident,
};
use crate::ast;
use std::collections::HashMap;
use std::fmt::Display;

/// Describes the policy for access of a given schema
#[derive(Debug, Clone)]
pub struct SchemaPolicy {
    pub schema: Schema,
    pub collection_policies: HashMap<Ident<Collection>, CollectionPolicy>,
    pub field_policies: HashMap<Ident<Field>, FieldPolicy>,
}

impl SchemaPolicy {
    pub fn add_field_policy(&mut self, field_id: Ident<Field>, field_policy: FieldPolicy) {
        self.field_policies.insert(field_id, field_policy);
    }
    pub fn remove_field_policy(&mut self, field_id: Ident<Field>) -> FieldPolicy {
        self.field_policies.remove(&field_id).expect(&format!(
            "Couldn't remove policy for {} because it doesn't exist",
            field_id.orig_name
        ))
    }
    pub fn add_collection_policy(
        &mut self,
        coll_id: Ident<Collection>,
        coll_policy: CollectionPolicy,
    ) {
        self.collection_policies.insert(coll_id, coll_policy);
    }
    pub fn remove_collection_policy(&mut self, coll_id: Ident<Collection>) -> CollectionPolicy {
        self.collection_policies.remove(&coll_id).expect(&format!(
            "Couldn't remove policy for {} because it doesn't exist",
            coll_id.orig_name
        ))
    }
}

#[derive(Debug, Clone)]
pub struct FieldPolicy {
    pub read: Policy,
    pub edit: Policy,
}

#[derive(Debug, Clone)]
pub enum Policy {
    None,
    Anyone,
    Func(Func),
}

impl Display for Policy {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Policy::None => write!(f, "none"),
            Policy::Anyone => write!(f, "public"),
            Policy::Func(Func {
                param: p,
                param_type: _pty,
                return_type: _rty,
                body: e,
            }) => write!(f, "{} -> {}", p.orig_name, expr_to_string(e.clone())),
        }
    }
}
impl Policy {
    pub fn expr_map(&self, f: &dyn Fn(IRExpr) -> IRExpr) -> Policy {
        match self {
            Policy::None | Policy::Anyone => self.clone(),
            Policy::Func(Func{param, param_type, return_type, body}) =>
                Policy::Func(Func{param: param.clone(),
                                  param_type: param_type.clone(),
                                  return_type: return_type.clone(),
                                  body: Box::new(body.map(f))})
        }
    }
}

#[derive(Debug, Clone)]
pub struct CollectionPolicy {
    pub create: Policy,
    pub delete: Policy,
}

pub fn extract_schema_policy(gp: &ast::GlobalPolicy) -> SchemaPolicy {
    let schema = super::schema::extract_schema(gp);
    ExtractionContext::new(schema, None).extract_schema_policy(gp)
}

pub fn extract_partial_schema_policy(
    gp: &ast::GlobalPolicy,
    outer_schema: &Schema,
) -> SchemaPolicy {
    let outer_schema_coll_idents = outer_schema
        .collections
        .iter()
        .map(|col| col.name.clone())
        .collect();
    let schema = super::schema::extract_partial_schema(gp, outer_schema_coll_idents);
    ExtractionContext::new(schema, Some(outer_schema)).extract_schema_policy(gp)
}

struct ExtractionContext {
    pub(crate) schema: Schema,
    pub(crate) total_schema: Schema,
}

impl ExtractionContext {
    /// Because Schemas are self-referential, (that is the `Foo::bar` can be of type `Id(Foo)`)
    /// we first have to create an index of all the type names so we can have stable identifiers
    fn new(schema: Schema, outer_schema: Option<&Schema>) -> Self {
        let total_schema = match outer_schema {
            Some(s) => Schema::merge(&schema, s),
            None => schema.clone(),
        };
        Self {
            schema,
            total_schema,
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
            create: extract_policy(&self.total_schema, &coll.name, &cp.create),
            delete: extract_policy(&self.total_schema, &coll.name, &cp.delete),
        }
    }

    fn extract_field_policy(&self, coll_name: &str, fp: &ast::FieldPolicy) -> FieldPolicy {
        let coll = self.schema.find_collection(coll_name).unwrap();

        FieldPolicy {
            // TODO: Bring AST names inline
            edit: extract_policy(&self.total_schema, &coll.name, &fp.write),
            read: extract_policy(&self.total_schema, &coll.name, &fp.read),
        }
    }
}

/// Extracs a policy for the specified collection. The collection ident is used
/// to set the expected type of the policy function (if present)
pub fn extract_policy(schema: &Schema, coll: &Ident<Collection>, p: &ast::Policy) -> Policy {
    match p {
        ast::Policy::Public => Policy::Anyone,
        ast::Policy::None => Policy::None,
        ast::Policy::Func(e) => Policy::Func(extract_func(
            schema,
            ExprType::Object(coll.clone()),
            &ExprType::set(ExprType::Principle),
            e,
        )),
    }
}
