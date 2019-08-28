use std::collections::HashMap;
use serde::Deserialize;

/// Represents a collection of all Tables
#[derive(Debug, Default, Deserialize)]
#[serde(transparent)]
pub struct Schema {
    pub tables: HashMap<String, Table>
}

#[derive(Debug, Default, Deserialize)]
#[serde(transparent)]
pub struct Table {
    pub fields: Vec<Field>
}

#[derive(Debug, Default, Deserialize)]
#[serde(transparent)]
pub struct Field {
    pub name: String
}

#[cfg(test)]
mod test {

    #[test]
    fn json_parse() {
        let schema_def = r#"{ "user": ["id", "name", "email"] }"#;

        let _: super::Schema = serde_json::from_str(schema_def).unwrap();
    }

    #[test]
    fn toml_parse() {
        let schema_def = r#"
        user = [
            "id",
            "name",
            "email"
        ]
        "#;

        let _: super::Schema = toml::from_str(schema_def).unwrap();
    }
}