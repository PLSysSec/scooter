use crate::Schema;
use sqlparser::ast::{TableFactor, TableWithJoins};

/// A Relation unifies the concept of tables and joins to simplify serializing
/// queries to SMT
pub trait Relation {
    fn resolve_name(&self, schema: &Schema, name: &str) -> usize;
}

impl Relation for TableFactor {
    fn resolve_name(&self, schema: &Schema, field_name: &str) -> usize {
        let name = match self {
            Self::Table { name, .. } => name,
            _ => unimplemented!("Complex table shenanigans"),
        };

        if name.0.len() != 1 {
            unimplemented!("Look into what this means")
        }

        let id = name.0[0].clone();

        let idx = schema.tables[&id]
            .fields
            .iter()
            .position(|field| field.name == field_name)
            .expect("unknown field");

        idx
    }
}

impl Relation for TableWithJoins {
    fn resolve_name(&self, schema: &Schema, field_name: &str) -> usize {
        if !self.joins.is_empty() {
            unimplemented!("name resolution across joins is unsupported");
        }
        
        self.relation.resolve_name(schema, field_name)
    }
}

impl Relation for Vec<TableWithJoins> {
    fn resolve_name(&self, schema: &Schema, field_name: &str) -> usize {
        if self.len() != 1 {
            unimplemented!("name resolution across multiple tables is unsupported");
        }
        
        self[0].resolve_name(schema, field_name)
    }
}
