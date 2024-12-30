use std::sync::Arc;

use cellang::{Environment, EnvironmentBuilder, List, Map, TokenTree, Value};
use miette::Error;

/// Let's create a function to split a string on a given character.
/// By the very nature of CEL, this function can be called like the following:
/// ```
/// 'a,b,c'.split(',')
/// // OR
/// split('a,b,c', ',')
/// // Or by using variables
/// x.split(',')
/// ```
fn split(env: &Environment, tokens: &[TokenTree]) -> Result<Value, Error> {
    // We expect two arguments: the string to split and the character to split on
    //
    // The parser would transform x.split(',') into split(x, ',')
    if tokens.len() != 2 {
        miette::bail!("Expected two arguments");
    }

    // Evaluate the first argument
    // The value of the argument should be of type Value::String
    // However, it may also be a reference to a variable that is of type string
    let string = match cellang::eval_ast(env, &tokens[0])?.to_value()? {
        Value::String(string) => string,
        _ => miette::bail!("Expected a string as the first argument"),
    };

    // Evaluate the second argument
    // The value of the argument should be of type Value::String since there
    // are no character types in CEL
    let character = match cellang::eval_ast(env, &tokens[1])?.to_value()? {
        Value::String(character) if character.len() == 1 => {
            character.chars().next().unwrap()
        }
        _ => miette::bail!("Expected a string as the second argument"),
    };

    // Now, we are in the rust land. We can use the standard library to split the string
    // on the character and return the result
    let result = string
        .split(character)
        .map(|s| s.into())
        .collect::<Vec<Value>>();

    // Now, return the type List of strings
    Ok(Value::List(result.into()))
}

fn main() {
    // Create a new environment with functions but without variables
    let mut env = EnvironmentBuilder::default();

    // Register the function
    env.set_function("split", Arc::new(split));

    // Seal the environment so that it can be used for evaluation
    let env = env.build();

    // Evaluate a simple expression
    let value = cellang::eval(&env, "'a,b,c'.split(',')").unwrap();
    assert_eq!(value, Value::List(List::from(vec!["a", "b", "c",])));

    // Evaluate a simple expression with variables
    let mut variables = Map::new();
    variables.insert("x".into(), "a,b,c".into()).unwrap();
    let mut env = env.child();
    env.set_variables(&variables);
    let value = cellang::eval(&env, "x.split(',')").unwrap();
    assert_eq!(value, Value::List(List::from(vec!["a", "b", "c",])));
}
