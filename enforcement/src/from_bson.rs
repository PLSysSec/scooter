use mongodb::Bson;
use serde::Deserialize;

pub trait FromBson {
    fn from_bson(bson : Bson) -> Self;
}

impl <'de, T> FromBson for T where T: Deserialize<'de>{
    fn from_bson(bson: Bson) -> Self {
        mongodb::from_bson(bson).unwrap()
    }
}
