use bson::Bson;
use serde::{Deserialize, Serialize};

pub trait FromBson {
    fn from_bson(bson: Bson) -> Self;
}

impl<'de, T> FromBson for T
where
    T: Deserialize<'de>,
{
    fn from_bson(bson: Bson) -> Self {
        bson::from_bson(bson).unwrap()
    }
}

pub trait ToBson {
    fn to_bson(&self) -> Bson;
}

impl<T> ToBson for T
where
    T: Serialize,
{
    fn to_bson(&self) -> Bson {
        bson::to_bson(self).unwrap()
    }
}
