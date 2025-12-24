use crate::error::EnvError;
use serde::{Deserialize, Serialize};
use std::collections::BTreeMap;
use std::fmt;

/// Identifier used to reference named types (structs/enums) within the environment metadata.
#[derive(
    Clone, Debug, PartialEq, Eq, Hash, PartialOrd, Ord, Serialize, Deserialize,
)]
pub struct TypeName(String);

impl TypeName {
    pub fn new(name: impl Into<String>) -> Self {
        TypeName(name.into())
    }

    pub fn as_str(&self) -> &str {
        &self.0
    }
}

impl fmt::Display for TypeName {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(self.as_str())
    }
}

impl From<&str> for TypeName {
    fn from(value: &str) -> Self {
        TypeName::new(value)
    }
}

impl From<String> for TypeName {
    fn from(value: String) -> Self {
        TypeName::new(value)
    }
}

impl From<&TypeName> for TypeName {
    fn from(value: &TypeName) -> Self {
        value.clone()
    }
}

/// High level CEL type metadata.
#[derive(Clone, Debug, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub enum Type {
    Dyn,
    Null,
    Type,
    Bool,
    Int,
    Uint,
    Double,
    String,
    Bytes,
    Timestamp,
    Duration,
    Any,
    List(Box<Type>),
    Map(Box<Type>, Box<Type>),
    Struct(TypeName),
    Enum(TypeName),
    TypeParam(String),
}

impl fmt::Display for Type {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Type::Dyn => write!(f, "dyn"),
            Type::Null => write!(f, "null"),
            Type::Type => write!(f, "type"),
            Type::Bool => write!(f, "bool"),
            Type::Int => write!(f, "int"),
            Type::Uint => write!(f, "uint"),
            Type::Double => write!(f, "double"),
            Type::String => write!(f, "string"),
            Type::Bytes => write!(f, "bytes"),
            Type::Timestamp => write!(f, "timestamp"),
            Type::Duration => write!(f, "duration"),
            Type::Any => write!(f, "any"),
            Type::List(elem) => write!(f, "list<{}>", elem),
            Type::Map(key, value) => write!(f, "map<{}, {}>", key, value),
            Type::Struct(name) => write!(f, "struct {}", name),
            Type::Enum(name) => write!(f, "enum {}", name),
            Type::TypeParam(name) => write!(f, "type_param {}", name),
        }
    }
}

impl Type {
    pub fn list(element: Type) -> Self {
        Type::List(Box::new(element))
    }

    pub fn map(key: Type, value: Type) -> Self {
        Type::Map(Box::new(key), Box::new(value))
    }

    pub fn struct_type(name: impl Into<TypeName>) -> Self {
        Type::Struct(name.into())
    }

    pub fn enum_type(name: impl Into<TypeName>) -> Self {
        Type::Enum(name.into())
    }
}

/// Metadata describing a single field on a struct type declaration.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct FieldDecl {
    pub ty: Type,
    pub doc: Option<String>,
}

impl FieldDecl {
    pub fn new(ty: Type) -> Self {
        Self { ty, doc: None }
    }

    pub fn with_doc(mut self, doc: impl Into<String>) -> Self {
        self.doc = Some(doc.into());
        self
    }
}

/// Struct/Message type descriptor equivalent to CEL-GO's `DeclType`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct StructType {
    pub name: TypeName,
    pub doc: Option<String>,
    pub fields: BTreeMap<String, FieldDecl>,
}

impl StructType {
    pub fn new(name: impl Into<TypeName>) -> Self {
        Self {
            name: name.into(),
            doc: None,
            fields: BTreeMap::new(),
        }
    }

    pub fn with_doc(mut self, doc: impl Into<String>) -> Self {
        self.doc = Some(doc.into());
        self
    }

    pub fn add_field(
        &mut self,
        name: impl Into<String>,
        decl: FieldDecl,
    ) -> Result<(), EnvError> {
        let key = name.into();
        if self.fields.contains_key(&key) {
            return Err(EnvError::new(format!(
                "Field '{key}' already declared on {}",
                self.name
            )));
        }
        self.fields.insert(key, decl);
        Ok(())
    }
}

/// Enum constant metadata.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct EnumValue {
    pub name: String,
    pub number: i32,
    pub doc: Option<String>,
}

impl EnumValue {
    pub fn new(name: impl Into<String>, number: i32) -> Self {
        Self {
            name: name.into(),
            number,
            doc: None,
        }
    }

    pub fn with_doc(mut self, doc: impl Into<String>) -> Self {
        self.doc = Some(doc.into());
        self
    }
}

/// Enum type descriptor.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct EnumType {
    pub name: TypeName,
    pub doc: Option<String>,
    pub values: BTreeMap<String, EnumValue>,
}

impl EnumType {
    pub fn new(name: impl Into<TypeName>) -> Self {
        Self {
            name: name.into(),
            doc: None,
            values: BTreeMap::new(),
        }
    }

    pub fn with_doc(mut self, doc: impl Into<String>) -> Self {
        self.doc = Some(doc.into());
        self
    }

    pub fn add_value(&mut self, value: EnumValue) -> Result<(), EnvError> {
        if self.values.contains_key(&value.name) {
            return Err(EnvError::new(format!(
                "Enum value '{}' already declared on {}",
                value.name, self.name
            )));
        }
        self.values.insert(value.name.clone(), value);
        Ok(())
    }
}

/// Wrapper around supported named type descriptors.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum NamedType {
    Struct(StructType),
    Enum(EnumType),
}

impl NamedType {
    pub fn name(&self) -> &TypeName {
        match self {
            NamedType::Struct(s) => &s.name,
            NamedType::Enum(e) => &e.name,
        }
    }
}

/// Registry of named types available inside the environment.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct TypeRegistry {
    types: BTreeMap<TypeName, NamedType>,
}

impl TypeRegistry {
    pub fn register(&mut self, ty: NamedType) -> Result<(), EnvError> {
        let name = ty.name().clone();
        if self.types.contains_key(&name) {
            return Err(EnvError::new(format!(
                "Type '{name}' already declared"
            )));
        }
        self.types.insert(name, ty);
        Ok(())
    }

    pub fn get(&self, name: &TypeName) -> Option<&NamedType> {
        self.types.get(name)
    }

    pub fn iter(&self) -> impl Iterator<Item = (&TypeName, &NamedType)> {
        self.types.iter()
    }
}

/// Subset of CEL constants supported at declaration time.
#[derive(Clone, Debug, PartialEq)]
pub enum Constant {
    Bool(bool),
    Int(i64),
    Uint(u64),
    Double(f64),
    String(String),
    Bytes(Vec<u8>),
    Null,
}

/// Identifier declaration metadata.
#[derive(Clone, Debug, PartialEq)]
pub struct IdentDecl {
    pub name: String,
    pub ty: Type,
    pub value: Option<Constant>,
    pub doc: Option<String>,
}

impl IdentDecl {
    pub fn new(name: impl Into<String>, ty: Type) -> Self {
        Self {
            name: name.into(),
            ty,
            value: None,
            doc: None,
        }
    }

    pub fn with_doc(mut self, doc: impl Into<String>) -> Self {
        self.doc = Some(doc.into());
        self
    }

    pub fn with_constant(mut self, constant: Constant) -> Self {
        self.value = Some(constant);
        self
    }
}

/// Function overload metadata.
#[derive(Clone, Debug, PartialEq)]
pub struct OverloadDecl {
    pub id: String,
    pub args: Vec<Type>,
    pub result: Type,
    pub receiver: Option<Type>,
    pub doc: Option<String>,
}

impl OverloadDecl {
    pub fn new(id: impl Into<String>, args: Vec<Type>, result: Type) -> Self {
        Self {
            id: id.into(),
            args,
            result,
            receiver: None,
            doc: None,
        }
    }

    pub fn with_receiver(mut self, receiver: Type) -> Self {
        self.receiver = Some(receiver);
        self
    }

    pub fn with_doc(mut self, doc: impl Into<String>) -> Self {
        self.doc = Some(doc.into());
        self
    }
}

/// Function declaration containing one or more overloads.
#[derive(Clone, Debug, PartialEq)]
pub struct FunctionDecl {
    pub name: String,
    pub doc: Option<String>,
    pub overloads: Vec<OverloadDecl>,
}

impl FunctionDecl {
    pub fn new(name: impl Into<String>) -> Self {
        Self {
            name: name.into(),
            doc: None,
            overloads: Vec::new(),
        }
    }

    pub fn with_doc(mut self, doc: impl Into<String>) -> Self {
        self.doc = Some(doc.into());
        self
    }

    pub fn add_overload(
        &mut self,
        overload: OverloadDecl,
    ) -> Result<(), EnvError> {
        if self
            .overloads
            .iter()
            .any(|existing| existing.id == overload.id)
        {
            return Err(EnvError::new(format!(
                "Function '{}' already has overload id '{}'",
                self.name, overload.id
            )));
        }
        self.overloads.push(overload);
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn struct_field_duplicate_errors() {
        let mut user = StructType::new("acme.User");
        user.add_field("id", FieldDecl::new(Type::String)).unwrap();
        let err = user.add_field("id", FieldDecl::new(Type::Int));
        assert!(err.is_err());
    }

    #[test]
    fn enum_duplicate_value_errors() {
        let mut status = EnumType::new("acme.Status");
        status.add_value(EnumValue::new("PENDING", 0)).unwrap();
        let err = status.add_value(EnumValue::new("PENDING", 1));
        assert!(err.is_err());
    }

    #[test]
    fn type_registry_duplicate_type_errors() {
        let mut registry = TypeRegistry::default();
        registry
            .register(NamedType::Struct(StructType::new("acme.User")))
            .unwrap();
        let err =
            registry.register(NamedType::Struct(StructType::new("acme.User")));
        assert!(err.is_err());
    }

    #[test]
    fn function_duplicate_overload_id_errors() {
        let mut decl = FunctionDecl::new("check");
        decl.add_overload(OverloadDecl::new(
            "check_string",
            vec![Type::String],
            Type::Bool,
        ))
        .unwrap();
        let err = decl.add_overload(OverloadDecl::new(
            "check_string",
            vec![Type::Bool],
            Type::Bool,
        ));
        assert!(err.is_err());
    }
}
