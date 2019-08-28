use crate::Schema;
use sqlparser::ast::{TableFactor};

/// A Relation unifies the concept of tables and joins to simplify serializing
/// queries to SMT
trait Relation {
    fn resolve_name(&self, schema: &Schema, name: &str) -> usize;
}

impl Relation for TableFactor {
    fn resolve_name(&self, schema: &Schema, name: &str) -> usize {
        let name = match self {
            Self::Table {name, ..} => name,
            _ => unimplemented!("Complex table shenanigans")
        };

        if name.0.len() != 1 {
            unimplemented!("Look into what this means")
        }

        let id = name.0[0].clone();

        let idx = schema.tables[&id].fields.iter()
                        .position(|field| field.name == id)
                        .expect("unknown field");

        return idx;
    }
}
