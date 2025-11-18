use cellang::{Environment, EnvironmentBuilder, TokenTree, Value};
use std::sync::Arc;
use std::thread;

fn main() {
    let mut env = EnvironmentBuilder::default();
    env.set_function(
        "plus_two",
        Arc::new(|env: &Environment, tokens: &[TokenTree]| {
            if tokens.len() != 1 {
                miette::bail!("Expected one argument");
            }
            let value = cellang::eval_ast(env, &tokens[0])?;
            let result = match value.try_value()? {
                Value::Int(n) => *n + 2,
                Value::Uint(n) => (*n + 2) as i64,
                Value::Double(n) => (*n + 2.0) as i64,
                _ => miette::bail!("Expected a number"),
            };

            Ok(Value::Int(result))
        }),
    );

    let (tx, rx) = std::sync::mpsc::channel();
    let worker_env = env.clone();
    let h = thread::spawn(move || {
        let env = worker_env.build();
        let val: i64 = cellang::eval(&env, "2.plus_two()")
            .unwrap()
            .try_into()
            .unwrap();

        tx.send(val).unwrap();
    });

    let value = rx.recv().unwrap();
    h.join().unwrap();

    assert_eq!(value, 4);
}
