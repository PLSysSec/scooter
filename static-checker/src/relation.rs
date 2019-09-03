use crate::Schema;
use sqlparser::ast::{TableFactor, TableWithJoins};
use std::collections::LinkedList;


pub(crate) type MultiId = Vec<String>;
pub type Relation = LinkedList<MultiId>;

pub(crate) fn get_name(rel: &Relation, name: &dyn Resolvable) -> usize {
    rel.iter().position(|cname| {
        name.matches_name(cname)
    }).unwrap()
}

pub(crate) trait Resolvable {
    fn matches_name(&self, name: &MultiId) -> bool;
}

impl Resolvable for &str {
    fn matches_name(&self, name: &MultiId) -> bool{
        name.last().unwrap() == self
    }
}

impl Resolvable for String {
    fn matches_name(&self, name: &MultiId) -> bool{
        name.last().unwrap() == self
    }
}

impl Resolvable for MultiId {
    fn matches_name(&self, name: &MultiId) -> bool{
        let specificity = self.len();

        name.iter().rev().take(specificity).eq(self.iter().rev())
    }
}

/// A Relation unifies the concept of tables and joins to simplify serializing
/// queries to SMT
pub(crate) trait ToRelation {
    fn to_relation(&self, schema: &Schema) -> Relation;
    fn resolve_name(&self, schema: &Schema, name: &dyn Resolvable) -> usize {
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
            .map(|f| vec![id.to_string(), f.name.to_string()])
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
        let mut rel = Relation::new();
        for twj in self {
            rel.append(&mut twj.to_relation(schema))
        }
        rel
    }
}
