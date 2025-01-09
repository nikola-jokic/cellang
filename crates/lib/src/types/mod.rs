mod de;
pub mod duration;
pub mod dynamic;
pub mod list;
pub mod map;
mod ser;
pub mod value;

use std::sync::Arc;

pub use self::duration::*;
pub use self::list::*;
pub use self::map::*;
pub use self::value::*;

use miette::Error;

use crate::parser::TokenTree;
use crate::Environment;

/// Function is a wrapper for a dynamic function that can be registered in the environment.
pub type Function = Arc<
    dyn Fn(&Environment, &[TokenTree]) -> Result<Value, Error> + Send + Sync,
>;

/// Function is a wrapper for turning Value into any type that implements DeserializeOwned.
pub fn try_from_value<T>(value: Value) -> Result<T, Error>
where
    T: serde::de::DeserializeOwned,
{
    match T::deserialize(value) {
        Ok(value) => Ok(value),
        Err(err) => miette::bail!("Failed to deserialize value: {}", err),
    }
}

/// Function is a wrapper for turning Map into any type that implements DeserializeOwned.
pub fn try_from_map<T>(value: Map) -> Result<T, Error>
where
    T: serde::de::DeserializeOwned,
{
    match T::deserialize(value) {
        Ok(value) => Ok(value),
        Err(err) => miette::bail!("Failed to deserialize value: {}", err),
    }
}

/// Function is a wrapper for turning List into any type that implements DeserializeOwned.
pub fn try_from_list<T>(value: List) -> Result<T, Error>
where
    T: serde::de::DeserializeOwned,
{
    match T::deserialize(value) {
        Ok(value) => Ok(value),
        Err(err) => miette::bail!("Failed to deserialize value: {}", err),
    }
}
