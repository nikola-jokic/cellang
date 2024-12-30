mod de;
pub mod list;
pub mod map;
mod ser;
pub mod value;

pub use self::list::*;
pub use self::map::*;
pub use self::value::*;

use miette::Error;

use crate::parser::TokenTree;
use crate::Environment;

/// Function is a wrapper for a dynamic function that can be registered in the environment.
pub type Function =
    Box<dyn Fn(&Environment, &[TokenTree]) -> Result<Value, Error>>;

pub fn try_from_value<T>(value: Value) -> Result<T, Error>
where
    T: serde::de::DeserializeOwned,
{
    match T::deserialize(value) {
        Ok(value) => Ok(value),
        Err(err) => miette::bail!("Failed to deserialize value: {}", err),
    }
}

pub fn try_from_map<T>(value: Map) -> Result<T, Error>
where
    T: serde::de::DeserializeOwned,
{
    match T::deserialize(value) {
        Ok(value) => Ok(value),
        Err(err) => miette::bail!("Failed to deserialize value: {}", err),
    }
}

pub fn try_from_list<T>(value: List) -> Result<T, Error>
where
    T: serde::de::DeserializeOwned,
{
    match T::deserialize(value) {
        Ok(value) => Ok(value),
        Err(err) => miette::bail!("Failed to deserialize value: {}", err),
    }
}
