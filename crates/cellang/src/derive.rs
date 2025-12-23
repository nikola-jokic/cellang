use crate::env::CelTypeRegistrar;
use crate::error::EnvError;
use crate::types::{NamedType, Type};

/// Trait implemented by structs that expose CEL type metadata.
pub trait CelType {
    const CEL_TYPE_NAME: &'static str;

    fn cel_type() -> Type {
        Type::struct_type(Self::CEL_TYPE_NAME)
    }

    fn cel_named_type() -> NamedType;

    fn register_cel_type<R>(registrar: &mut R) -> Result<(), EnvError>
    where
        R: CelTypeRegistrar,
    {
        registrar.register_type(Self::cel_named_type())
    }
}
