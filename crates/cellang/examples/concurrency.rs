use cellang::{Runtime, RuntimeError};
use miette::Result;
use std::thread;

fn main() -> Result<()> {
    let mut builder = Runtime::builder();
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
