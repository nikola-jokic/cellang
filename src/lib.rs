#[derive(Debug)]
enum Token<'src> {
    Null,
    Int(i64),
    Uint(u64),
    Double(f64),
    Bool(bool),
    String(&'str str),
    Bytes(&'src [u8]),
    List(&'src [Box<Expr<'src>>]),
    Map(&'src [(MapKey, Box<Expr<'src>>)]),

    Ident(&'src str),
}

#[derive(Debug, Eq, PartialEq)]
enum MapKey {
    Int(i64),
    Uint(u64),
    Bool(bool),
    String(String),
}
