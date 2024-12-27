pub mod list;
pub mod map;
pub mod value;

pub use self::list::*;
pub use self::map::*;
pub use self::value::*;

use miette::Error;

use crate::parser::TokenTree;
use crate::SealedEnvironment;

/// Function is a wrapper for a dynamic function that can be registered in the environment.
pub type Function = Box<dyn Fn(&SealedEnvironment, &[TokenTree]) -> Result<Value, Error>>;
