use cellang::types::{FunctionDecl, OverloadDecl, Type};
use cellang::{Runtime, RuntimeError, Value};
use miette::Result;
use std::thread;

fn main() -> Result<()> {
    let mut builder = Runtime::builder();
    builder.add_function_decl(plus_two_decl())?;
    builder.set_function("plus_two", |value: i64| value + 2)?;
    builder.set_variable("base", 2_i64)?;

    let (tx, rx) = std::sync::mpsc::channel();
    let mut handles = Vec::new();
    for offset in 0..4_i64 {
        let tx = tx.clone();
        let mut worker_builder = builder.clone();
        handles.push(thread::spawn(move || {
            worker_builder.set_variable("offset", offset)?;
            let runtime = worker_builder.build();
            let value = runtime.eval("(base + offset).plus_two()")?;
            let number: i64 = value.try_into()?;
            tx.send(number)
                .map_err(|err| RuntimeError::new(err.to_string()))?;
            Ok::<(), RuntimeError>(())
        }));
    }
    drop(tx);

    for handle in handles {
        handle.join().unwrap()?;
    }
    let mut values = rx.into_iter().collect::<Vec<_>>();
    values.sort_unstable();
    assert_eq!(values, vec![4, 5, 6, 7]);

    let runtime = builder.build();
    let direct = runtime.eval("plus_two(base)")?;
    assert_eq!(direct, Value::Int(4));

    Ok(())
}

fn plus_two_decl() -> FunctionDecl {
    let mut decl = FunctionDecl::new("plus_two");
    decl.add_overload(OverloadDecl::new(
        "int_plus_two_function",
        vec![Type::Int],
        Type::Int,
    ))
    .expect("plus_two function overload");
    decl.add_overload(
        OverloadDecl::new("int_plus_two_method", Vec::new(), Type::Int)
            .with_receiver(Type::Int),
    )
    .expect("plus_two method overload");
    decl
}
