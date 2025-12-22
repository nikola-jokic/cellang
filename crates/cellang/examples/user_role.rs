use cellang::Runtime;
use cellang::types::{
    FieldDecl, FunctionDecl, IdentDecl, NamedType, OverloadDecl, StructType,
    Type,
};
use cellang::value::{
    IntoValue, ListValue, StructValue, TryFromValue, Value, ValueError,
};
use miette::Result;

const USER_TYPE: &str = "example.User";

fn main() -> Result<()> {
    let mut builder = Runtime::builder();
    register_user_schema(&mut builder)?;
    builder.set_variable("users", load_users());
    builder.register_function("has_role", has_role)?;

    builder.set_variable("role", "admin");
    let runtime = builder.build();
    let is_admin = runtime.eval("users[0].has_role(role)")?;
    assert_eq!(is_admin, Value::Bool(true));

    let mut scoped = runtime.child_builder();
    scoped.set_variable("role", "user");
    let scoped = scoped.build();
    let is_user = scoped.eval("users[1].has_role(role)")?;
    assert_eq!(is_user, Value::Bool(true));

    Ok(())
}

fn register_user_schema(
    builder: &mut cellang::runtime::RuntimeBuilder,
) -> Result<()> {
    builder.add_type(user_type())?;
    builder.add_ident(
        IdentDecl::new("users", Type::list(Type::struct_type(USER_TYPE)))
            .with_doc("All users loaded from storage"),
    )?;
    builder.add_function_decl(has_role_decl())?;
    Ok(())
}

fn load_users() -> Value {
    let records = vec![
        User::new("Alice", &["admin"]),
        User::new("Bob", &["user"]),
        User::new("Charlie", &["admin", "user"]),
        User::new("David", &["user"]),
    ];
    Value::List(ListValue::from(records))
}

fn has_role(user: User, role: String) -> bool {
    user.roles.iter().any(|current| current == &role)
}

fn user_type() -> NamedType {
    let mut user =
        StructType::new(USER_TYPE).with_doc("Application user record");
    user.add_field("name", FieldDecl::new(Type::String))
        .unwrap();
    user.add_field("roles", FieldDecl::new(Type::list(Type::String)))
        .unwrap();
    NamedType::Struct(user)
}

fn has_role_decl() -> FunctionDecl {
    let mut decl = FunctionDecl::new("has_role")
        .with_doc("Tests whether the user has the specified role");
    decl.add_overload(
        OverloadDecl::new(
            "user_has_role_string",
            vec![Type::struct_type(USER_TYPE), Type::String],
            Type::Bool,
        )
        .with_receiver(Type::struct_type(USER_TYPE)),
    )
    .unwrap();
    decl
}

#[derive(Clone, Debug)]
struct User {
    name: String,
    roles: Vec<String>,
}

impl User {
    fn new(name: &str, roles: &[&str]) -> Self {
        Self {
            name: name.to_string(),
            roles: roles.iter().map(|role| (*role).to_string()).collect(),
        }
    }
}

impl IntoValue for User {
    fn into_value(self) -> Value {
        let mut value = StructValue::new(USER_TYPE);
        value.set_field("name", self.name);
        value.set_field("roles", ListValue::from(self.roles));
        Value::Struct(value)
    }
}

impl TryFromValue for User {
    fn try_from_value(value: &Value) -> Result<Self, ValueError> {
        let Value::Struct(strct) = value else {
            return Err(ValueError::Message("expected a user struct".into()));
        };
        if strct.type_name.as_str() != USER_TYPE {
            return Err(ValueError::Message(format!(
                "expected struct of type '{USER_TYPE}', got '{}'",
                strct.type_name
            )));
        }
        let name_value = strct.get("name").ok_or_else(|| {
            ValueError::Message("user.name is missing".into())
        })?;
        let name = String::try_from_value(name_value)?;
        let roles_value = strct.get("roles").ok_or_else(|| {
            ValueError::Message("user.roles is missing".into())
        })?;
        let roles = Vec::<String>::try_from_value(roles_value)?;
        Ok(User { name, roles })
    }
}
