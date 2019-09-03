use crate::Schema;
use sqlparser::ast::{TableFactor, TableWithJoins};
use std::collections::LinkedList;

pub type Relation = LinkedList<String>;

pub fn get_name(rel: &Relation, name: &str) -> usize {
    rel.iter().position(|n| n == name).unwrap()
}

/// A Relation unifies the concept of tables and joins to simplify serializing
/// queries to SMT
pub trait ToRelation {
    fn to_relation(&self, schema: &Schema) -> Relation;
    fn resolve_name(&self, schema: &Schema, name: &str) -> usize {
        get_name(&self.to_relation(schema), name)
    }
}

impl ToRelation for TableFactor {
    fn to_relation(&self, schema: &Schema) -> Relation {
        let name = match self {
            Self::Table { name, .. } => name,
            _ => unimplemented!("Complex table shenanigans"),
        };

        if name.0.len() != 1 {
            unimplemented!("Look into what this means")
        }

        let id = name.0[0].clone();

        schema.tables[&id]
            .fields
            .iter()
            .map(|f| f.name.to_string())
            .collect()
    }
}

impl ToRelation for TableWithJoins {
    fn to_relation(&self, schema: &Schema) -> Relation {
        if !self.joins.is_empty() {
            unimplemented!("name resolution across joins is unsupported");
        }

        self.relation.to_relation(schema)
    }
}

impl ToRelation for Vec<TableWithJoins> {
    fn to_relation(&self, schema: &Schema) -> Relation {
        if self.len() != 1 {
            unimplemented!("name resolution across multiple tables is unsupported");
        }

        self[0].to_relation(schema)
    }
}
