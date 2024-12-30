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
