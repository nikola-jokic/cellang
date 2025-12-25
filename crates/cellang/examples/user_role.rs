#[cfg(not(feature = "derive"))]
fn main() {
    panic!(
        "Enable the `derive` feature to run this example: \
         cargo run --example user_role --features derive"
    );
}

#[cfg(feature = "derive")]
fn main() -> miette::Result<()> {
    example::run()
}

#[cfg(feature = "derive")]
mod example {
    use cellang::CelStruct;
    use cellang::Runtime;
    use cellang::types::{FunctionDecl, IdentDecl, OverloadDecl, Type};
    use cellang::value::{ListValue, Value};
    use miette::Result;

    pub fn run() -> Result<()> {
        let mut builder = Runtime::builder();
        register_user_schema(&mut builder)?;
        builder.set_variable("users", load_users())?;
        builder.register_function("has_role", has_role)?;

        builder.set_variable("role", "admin")?;
        let runtime = builder.build();
        let is_admin = runtime.eval("users[0].has_role(role)")?;
        assert_eq!(is_admin, Value::Bool(true));

        let mut scoped = runtime.child_builder();
        scoped.set_variable("role", "user")?;
        let scoped = scoped.build();
        let is_user = scoped.eval("users[1].has_role(role)")?;
        assert_eq!(is_user, Value::Bool(true));

        Ok(())
    }

    fn register_user_schema(
        builder: &mut cellang::runtime::RuntimeBuilder,
    ) -> Result<()> {
        User::register_cel_type(builder)?;
        builder.add_ident(
            IdentDecl::new("users", Type::list(User::cel_type()))
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

    fn has_role_decl() -> FunctionDecl {
        let mut decl = FunctionDecl::new("has_role")
            .with_doc("Tests whether the user has the specified role");
        decl.add_overload(
            OverloadDecl::new(
                "user_has_role_string",
                vec![User::cel_type(), Type::String],
                Type::Bool,
            )
            .with_receiver(User::cel_type()),
        )
        .unwrap();
        decl
    }

    #[derive(Clone, Debug, CelStruct)]
    #[cel(type = "example.User", doc = "Application user record")]
    struct User {
        #[cel(doc = "Display name")]
        name: String,
        #[cel(doc = "Assigned roles")]
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
}
