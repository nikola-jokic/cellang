use crate::EnvError;
use crate::types::{
    FunctionDecl, IdentDecl, NamedType, TypeName, TypeRegistry,
};
use std::collections::{BTreeMap, btree_map::Entry};
use std::sync::Arc;

/// Immutable environment describing identifiers, functions and named types.
#[derive(Clone, Debug)]
pub struct Env {
    type_registry: Arc<TypeRegistry>,
    identifiers: Arc<BTreeMap<String, IdentDecl>>,
    functions: Arc<BTreeMap<String, FunctionDecl>>,
}

impl Env {
    pub fn builder() -> EnvBuilder {
        EnvBuilder::default()
    }

    pub fn lookup_ident(&self, name: &str) -> Option<&IdentDecl> {
        self.identifiers.get(name)
    }

    pub fn lookup_function(&self, name: &str) -> Option<&FunctionDecl> {
        self.functions.get(name)
    }

    pub fn lookup_type(&self, name: &TypeName) -> Option<&NamedType> {
        self.type_registry.get(name)
    }

    pub fn types(&self) -> &TypeRegistry {
        &self.type_registry
    }

    pub fn idents(&self) -> &BTreeMap<String, IdentDecl> {
        &self.identifiers
    }

    pub fn functions(&self) -> &BTreeMap<String, FunctionDecl> {
        &self.functions
    }
}

impl Default for Env {
    fn default() -> Self {
        EnvBuilder::default().build()
    }
}

/// Builder used to incrementally assemble environments.
#[derive(Clone, Debug, Default)]
pub struct EnvBuilder {
    type_registry: TypeRegistry,
    identifiers: BTreeMap<String, IdentDecl>,
    functions: BTreeMap<String, FunctionDecl>,
}

/// Abstraction over builders capable of accepting named CEL types.
pub trait CelTypeRegistrar {
    fn register_type(&mut self, ty: NamedType) -> Result<(), EnvError>;
}

impl CelTypeRegistrar for EnvBuilder {
    fn register_type(&mut self, ty: NamedType) -> Result<(), EnvError> {
        self.add_type(ty).map(|_| ())
    }
}

impl EnvBuilder {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn add_type(&mut self, ty: NamedType) -> Result<&mut Self, EnvError> {
        self.type_registry.register(ty).map_err(|e| {
            EnvError::new(format!("Type registration error: {}", e))
        })?;
        Ok(self)
    }

    pub fn add_ident(
        &mut self,
        decl: IdentDecl,
    ) -> Result<&mut Self, EnvError> {
        if self.identifiers.contains_key(&decl.name) {
            return Err(EnvError::new(format!(
                "Identifier '{}' already declared",
                decl.name
            )));
        }
        self.identifiers.insert(decl.name.clone(), decl);
        Ok(self)
    }

    pub fn add_function(
        &mut self,
        mut decl: FunctionDecl,
    ) -> Result<&mut Self, EnvError> {
        match self.functions.entry(decl.name.clone()) {
            Entry::Vacant(entry) => {
                entry.insert(decl);
            }
            Entry::Occupied(mut entry) => {
                let existing = entry.get_mut();
                if existing.doc.is_none() {
                    existing.doc = decl.doc.take();
                }
                for overload in decl.overloads.drain(..) {
                    existing.add_overload(overload)?;
                }
            }
        }
        Ok(self)
    }

    pub fn import_env(&mut self, env: &Env) -> Result<&mut Self, EnvError> {
        for (_, ty) in env.types().iter() {
            self.type_registry.register(ty.clone())?;
        }
        for decl in env.idents().values() {
            self.add_ident(decl.clone())?;
        }
        for decl in env.functions().values() {
            self.add_function(decl.clone())?;
        }
        Ok(self)
    }

    pub fn build(self) -> Env {
        Env {
            type_registry: Arc::new(self.type_registry),
            identifiers: Arc::new(self.identifiers),
            functions: Arc::new(self.functions),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::types::{FieldDecl, OverloadDecl, StructType, Type};

    fn build_scan_type() -> StructType {
        let mut scan = StructType::new("acme.Scan");
        scan.add_field("available", FieldDecl::new(Type::Bool))
            .unwrap();
        scan.add_field("level", FieldDecl::new(Type::Int)).unwrap();
        scan
    }

    #[test]
    fn env_registers_structs_and_functions() {
        let scan = build_scan_type();
        let mut builder = Env::builder();
        builder.add_type(NamedType::Struct(scan.clone())).unwrap();
        builder
            .add_ident(
                IdentDecl::new(
                    "scans",
                    Type::list(Type::struct_type(scan.name.clone())),
                )
                .with_doc("All scans available in the current context"),
            )
            .unwrap();

        let mut func = FunctionDecl::new("is_available");
        func.add_overload(OverloadDecl::new(
            "is_available_scan_bool",
            vec![Type::struct_type(scan.name.clone())],
            Type::Bool,
        ))
        .unwrap();
        builder.add_function(func).unwrap();

        let env = builder.build();
        assert!(env.lookup_type(&scan.name).is_some());
        let scans = env.lookup_ident("scans").expect("scans");
        assert!(matches!(
            &scans.ty,
            Type::List(inner) if matches!(**inner, Type::Struct(_))
        ));
        let fn_decl = env.lookup_function("is_available").expect("fn");
        assert_eq!(fn_decl.overloads.len(), 1);
    }

    #[test]
    fn duplicate_identifier_errors() {
        let mut builder = Env::builder();
        builder.add_ident(IdentDecl::new("x", Type::Int)).unwrap();
        let err = builder.add_ident(IdentDecl::new("x", Type::Bool));
        assert!(err.is_err());
    }

    #[test]
    fn duplicate_type_registration_errors() {
        let scan = build_scan_type();
        let mut builder = Env::builder();
        builder.add_type(NamedType::Struct(scan.clone())).unwrap();
        let err = builder.add_type(NamedType::Struct(scan));
        assert!(err.is_err());
    }

    #[test]
    fn duplicate_function_overload_id_errors() {
        let scan = build_scan_type();
        let mut builder = Env::builder();
        builder.add_type(NamedType::Struct(scan.clone())).unwrap();

        let mut initial = FunctionDecl::new("scan_status");
        initial
            .add_overload(OverloadDecl::new(
                "scan_status_overload",
                vec![Type::struct_type(scan.name.clone())],
                Type::Bool,
            ))
            .unwrap();
        builder.add_function(initial).unwrap();

        let mut duplicate = FunctionDecl::new("scan_status");
        duplicate
            .add_overload(OverloadDecl::new(
                "scan_status_overload",
                vec![Type::Bool],
                Type::Bool,
            ))
            .unwrap();
        let err = builder.add_function(duplicate);
        assert!(err.is_err());
    }

    #[test]
    fn merge_existing_env() {
        let scan = build_scan_type();
        let mut base = Env::builder();
        base.add_type(NamedType::Struct(scan.clone())).unwrap();
        base.add_function({
            let mut func = FunctionDecl::new("size");
            func.add_overload(OverloadDecl::new(
                "size_list_int",
                vec![Type::list(Type::Int)],
                Type::Int,
            ))
            .unwrap();
            func
        })
        .unwrap();
        let env = base.build();

        let mut derived = Env::builder();
        derived.import_env(&env).unwrap();
        let merged = derived.build();
        assert!(merged.lookup_function("size").is_some());
        assert!(merged.lookup_type(&scan.name).is_some());
    }
}
