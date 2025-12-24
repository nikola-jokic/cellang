use crate::EnvError;
use crate::ast::TypedExpr;
use crate::error::CompileError;
use crate::macros::MacroRegistry;
use crate::parser::Parser;
use crate::types::{
    FunctionDecl, IdentDecl, NamedType, OverloadDecl, Type, TypeName,
    TypeRegistry,
};
use std::collections::{BTreeMap, btree_map::Entry};
use std::sync::Arc;

/// Immutable environment describing identifiers, functions and named types.
#[derive(Clone, Debug)]
pub struct Env {
    type_registry: Arc<TypeRegistry>,
    identifiers: Arc<BTreeMap<String, IdentDecl>>,
    functions: Arc<BTreeMap<String, FunctionDecl>>,
    macros: Arc<MacroRegistry>,
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

    pub fn macros(&self) -> &MacroRegistry {
        &self.macros
    }

    pub fn compile(&self, src: &str) -> Result<TypedExpr, CompileError> {
        let mut parser = Parser::new(src);
        let token_tree = parser.parse()?;
        let typed = crate::ast::type_check(self, &token_tree)?;
        Ok(typed)
    }
}

impl Default for Env {
    fn default() -> Self {
        EnvBuilder::default().build()
    }
}

/// Builder used to incrementally assemble environments.
#[derive(Clone, Debug)]
pub struct EnvBuilder {
    type_registry: TypeRegistry,
    identifiers: BTreeMap<String, IdentDecl>,
    functions: BTreeMap<String, FunctionDecl>,
    macros: MacroRegistry,
}

impl Default for EnvBuilder {
    fn default() -> Self {
        let mut builder = EnvBuilder::new_empty();
        builder
            .install_builtin_function_decls()
            .expect("builtin declarations must register");
        builder
    }
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

    pub fn new_empty() -> Self {
        Self {
            type_registry: TypeRegistry::new(),
            identifiers: BTreeMap::new(),
            functions: BTreeMap::new(),
            macros: MacroRegistry::standard(),
        }
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

    pub fn macros(&self) -> &MacroRegistry {
        &self.macros
    }

    pub fn macros_mut(&mut self) -> &mut MacroRegistry {
        &mut self.macros
    }

    pub fn set_macros(&mut self, registry: MacroRegistry) -> &mut Self {
        self.macros = registry;
        self
    }

    pub fn import_env(&mut self, env: &Env) -> Result<&mut Self, EnvError> {
        for (_, ty) in env.types().iter() {
            self.type_registry.register(ty.clone())?;
        }
        for decl in env.idents().values() {
            self.add_ident(decl.clone())?;
        }
        for decl in env.functions().values() {
            match self.functions.entry(decl.name.clone()) {
                Entry::Vacant(entry) => {
                    entry.insert(decl.clone());
                }
                Entry::Occupied(mut entry) => {
                    merge_function_decl(entry.get_mut(), decl)?;
                }
            }
        }
        self.macros.merge(env.macros());
        Ok(self)
    }

    pub fn build(self) -> Env {
        Env {
            type_registry: Arc::new(self.type_registry),
            identifiers: Arc::new(self.identifiers),
            functions: Arc::new(self.functions),
            macros: Arc::new(self.macros),
        }
    }

    fn install_builtin_function_decls(&mut self) -> Result<(), EnvError> {
        for decl in builtin_function_decls() {
            self.add_function(decl)?;
        }
        Ok(())
    }
}

fn merge_function_decl(
    existing: &mut FunctionDecl,
    incoming: &FunctionDecl,
) -> Result<(), EnvError> {
    if existing.doc.is_none() {
        existing.doc = incoming.doc.clone();
    }
    for overload in &incoming.overloads {
        if let Some(current) = existing
            .overloads
            .iter()
            .find(|item| item.id == overload.id)
        {
            if current != overload {
                return Err(EnvError::new(format!(
                    "Function '{}' overload id '{}' conflicts with existing declaration",
                    existing.name, overload.id
                )));
            }
            continue;
        }
        existing.overloads.push(overload.clone());
    }
    Ok(())
}

fn builtin_function_decls() -> Vec<FunctionDecl> {
    vec![
        builtin_size_decl(),
        builtin_contains_decl(),
        builtin_string_binary_decl("startsWith"),
        builtin_string_binary_decl("endsWith"),
        builtin_string_binary_decl("matches"),
        builtin_unary_decl("type", Type::String),
        builtin_unary_decl("string", Type::String),
        builtin_unary_decl("int", Type::Int),
        builtin_unary_decl("uint", Type::Uint),
        builtin_unary_decl("timestamp", Type::Timestamp),
        builtin_unary_decl("duration", Type::Duration),
    ]
}

fn builtin_size_decl() -> FunctionDecl {
    let mut decl = FunctionDecl::new("size");
    for (label, ty) in [
        ("string", Type::String),
        ("bytes", Type::Bytes),
        ("list", Type::list(Type::Dyn)),
        ("map", Type::map(Type::Dyn, Type::Dyn)),
    ] {
        push_overload(
            &mut decl,
            format!("size_{label}_function"),
            vec![ty.clone()],
            Type::Int,
        );
        push_method_overload(
            &mut decl,
            format!("size_{label}_method"),
            ty,
            Vec::new(),
            Type::Int,
        );
    }
    decl
}

fn builtin_contains_decl() -> FunctionDecl {
    let mut decl = FunctionDecl::new("contains");
    for (label, ty) in [("string", Type::String), ("bytes", Type::Bytes)] {
        push_overload(
            &mut decl,
            format!("contains_{label}_function"),
            vec![ty.clone(), ty.clone()],
            Type::Bool,
        );
        let method_arg = ty.clone();
        push_method_overload(
            &mut decl,
            format!("contains_{label}_method"),
            ty,
            vec![method_arg],
            Type::Bool,
        );
    }
    decl
}

fn builtin_string_binary_decl(name: &str) -> FunctionDecl {
    let mut decl = FunctionDecl::new(name);
    push_overload(
        &mut decl,
        format!("{name}_string_function"),
        vec![Type::String, Type::String],
        Type::Bool,
    );
    push_method_overload(
        &mut decl,
        format!("{name}_string_method"),
        Type::String,
        vec![Type::String],
        Type::Bool,
    );
    decl
}

fn builtin_unary_decl(name: &str, result: Type) -> FunctionDecl {
    let mut decl = FunctionDecl::new(name);
    push_overload(&mut decl, format!("{name}_value"), vec![Type::Dyn], result);
    decl
}

fn push_overload(
    decl: &mut FunctionDecl,
    id: String,
    args: Vec<Type>,
    result: Type,
) {
    decl.add_overload(OverloadDecl::new(id, args, result))
        .expect("builtin declaration must register");
}

fn push_method_overload(
    decl: &mut FunctionDecl,
    id: String,
    receiver: Type,
    args: Vec<Type>,
    result: Type,
) {
    decl.add_overload(
        OverloadDecl::new(id, args, result).with_receiver(receiver),
    )
    .expect("builtin declaration must register");
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ast::ExprKind;
    use crate::macros::ComprehensionKind;
    use crate::types::{FieldDecl, OverloadDecl, StructType, Type};

    #[test]
    fn default_env_contains_builtins() {
        let env = Env::builder().build();
        for name in [
            "size",
            "contains",
            "startsWith",
            "endsWith",
            "matches",
            "type",
            "string",
            "int",
            "uint",
            "timestamp",
            "duration",
        ] {
            assert!(
                env.lookup_function(name).is_some(),
                "expected builtin function '{name}' to be registered"
            );
        }
    }

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

    #[test]
    fn compile_supports_standard_macros() {
        let mut builder = Env::builder();
        builder
            .add_ident(IdentDecl::new("roles", Type::list(Type::String)))
            .unwrap();
        let env = builder.build();

        let typed = env
            .compile("roles.exists(role, role == 'admin')")
            .expect("macro compilation");

        assert_eq!(typed.ty, Type::Bool);
        match typed.expr {
            ExprKind::MacroComprehension {
                comprehension, var, ..
            } => {
                assert_eq!(comprehension, ComprehensionKind::Exists);
                assert_eq!(var, "role");
            }
            other => panic!("expected macro comprehension, got {other:?}"),
        }
    }

    #[test]
    fn compile_returns_typed_ast() {
        let mut builder = Env::builder();
        builder.add_ident(IdentDecl::new("x", Type::Int)).unwrap();
        let env = builder.build();
        let typed = env.compile("x + 1").expect("compile result");
        assert_eq!(typed.ty, Type::Int);
    }
}
