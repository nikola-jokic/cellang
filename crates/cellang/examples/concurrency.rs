use cellang::types::{FunctionDecl, OverloadDecl, Type};
use cellang::{Runtime, RuntimeError};
use miette::Result;
use std::thread;

fn main() -> Result<()> {
    let mut builder = Runtime::builder();
    builder.add_function_decl(plus_two_decl())?;
    builder.register_function("plus_two", |value: i64| value + 2)?;

    let (tx, rx) = std::sync::mpsc::channel();
    let worker_builder = builder.clone();
    let handle = thread::spawn(move || {
        let runtime = worker_builder.build();
        let value = runtime.eval("2.plus_two()")?;
        let number: i64 = value.try_into()?;
        tx.send(number)
            .map_err(|err| RuntimeError::new(err.to_string()))?;
        Ok::<(), RuntimeError>(())
    });

    handle.join().unwrap()?;
    let value = rx.recv().unwrap();
    assert_eq!(value, 4);

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
