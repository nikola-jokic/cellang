use cellang::{Environment, EnvironmentBuilder, Map, TokenTree, Value};
use miette::Error;
use serde::{Deserialize, Serialize};

fn main() {
    // Creates a root environment
    let mut env = EnvironmentBuilder::default();

    // Fetches the required variables from the database
    let users = list_users().unwrap();

    // Adds the users to the environment
    env.set_variable("users", users).unwrap();

    // Add a custom function to the environment
    env.set_function("has_role", Box::new(has_role));

    // Let's say the program tries to get the number of users with particular role
    let program = "size(users.filter(u, u.has_role(role)))";

    // Now, we want to calculate users with role 'admin'
    env.set_variable("role", "admin").unwrap();

    // Get number of admin users
    let n: i64 = cellang::eval(&env.build(), program)
        .expect("Failed to evaluate the expression")
        .into();

    println!("Number of admin users: {}", n);

    // Or role 'user'
    env.set_variable("role", "user").unwrap();

    // Get number of admin users
    let n: i64 = cellang::eval(&env.build(), program)
        .expect("Failed to evaluate the expression")
        .into();

    println!("Number of users: {}", n);
}

#[derive(Debug, Serialize, Deserialize)]
pub struct User {
    pub name: String,
    pub roles: Vec<String>,
}

fn list_users() -> Result<Vec<User>, Error> {
    Ok(vec![
        User {
            name: "Alice".into(),
            roles: vec!["admin".into()],
        },
        User {
            name: "Bob".into(),
            roles: vec!["user".into()],
        },
        User {
            name: "Charlie".into(),
            roles: vec!["admin".into(), "user".into()],
        },
        User {
            name: "David".into(),
            roles: vec!["user".into()],
        },
    ])
}

fn has_role(env: &Environment, tokens: &[TokenTree]) -> Result<Value, Error> {
    if tokens.len() != 2 {
        miette::bail!("Expected 2 arguments, got {}", tokens.len());
    }

    let user: User = match cellang::eval_ast(env, &tokens[0])?.to_value()? {
        Value::Map(m) => cellang::try_from_map(m)?,
        _ => miette::bail!("Expected a map, got something else"),
    };

    let role = match cellang::eval_ast(env, &tokens[1])?.to_value()? {
        Value::String(s) => s,
        _ => miette::bail!("Expected a string, got something else"),
    };

    Ok(user.roles.contains(&role).into())
}
