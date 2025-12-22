use cellang::{
    lexer::{Lexer, Token},
    parser::Parser,
    runtime::Runtime,
    value::{ListValue, MapValue, Value},
};
use clap::{Parser as ClapParser, Subcommand, ValueEnum};
use miette::{Error, IntoDiagnostic, WrapErr, miette};
use serde::Serialize;
use serde_json::Value as JsonValue;
use std::fmt;
use std::fs;
use std::path::{Path, PathBuf};

#[derive(ClapParser, Debug)]
#[command(version, about, long_about = None)]
struct Args {
    #[command(subcommand)]
    command: Commands,
}

#[derive(Subcommand, Debug)]
enum Commands {
    #[command(subcommand)]
    Lex(Lex),
    #[command(subcommand)]
    Parse(Parse),
    #[command(subcommand)]
    Eval(Eval),
}

#[derive(Subcommand, Debug)]
enum Lex {
    File {
        #[arg(
            short = 'f',
            long = "format",
            default_value_t = Format::Debug,
            value_enum
        )]
        format: Format,
        path: PathBuf,
    },
    Expr {
        #[arg(
            short = 'f',
            long = "format",
            default_value_t = Format::Debug,
            value_enum
        )]
        format: Format,
        expr: String,
    },
}

impl Lex {
    fn run(&self) -> Result<(), Error> {
        match self {
            Lex::File { path, format } => {
                let source = read_source(path)?;
                print_tokens(&source, *format)
            }
            Lex::Expr { expr, format } => print_tokens(expr, *format),
        }
    }
}

#[derive(Subcommand, Debug)]
enum Parse {
    File {
        #[arg(
            short = 'f',
            long = "format",
            required = false,
            default_value_t = Format::Debug,
            value_enum
        )]
        format: Format,

        path: PathBuf,
    },
    Expr {
        #[arg(
            short = 'f',
            long = "format",
            required = false,
            default_value_t = Format::Debug,
            value_enum
        )]
        format: Format,

        expr: String,
    },
}

#[derive(Debug, Clone, Copy, Default, ValueEnum, PartialEq, Eq)]
pub enum Format {
    Json,
    #[default]
    Debug,
}

impl Format {
    pub fn print<T>(self, value: &T)
    where
        T: fmt::Debug + Serialize,
    {
        match self {
            Format::Json => {
                let json = serde_json::to_string_pretty(value).unwrap();
                println!("{}", json);
            }
            Format::Debug => {
                println!("{:#?}", value);
            }
        }
    }
}

impl From<&str> for Format {
    fn from(s: &str) -> Self {
        match s {
            "json" => Format::Json,
            "debug" => Format::Debug,
            _ => Format::Debug,
        }
    }
}

impl fmt::Display for Format {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Format::Json => write!(f, "json"),
            Format::Debug => write!(f, "debug"),
        }
    }
}

impl Parse {
    fn run(&self) -> Result<(), Error> {
        match self {
            Parse::File { format, path } => {
                let source = read_source(path)?;
                print_ast(&source, *format)
            }
            Parse::Expr { format, expr } => print_ast(expr, *format),
        }
    }
}

#[derive(Subcommand, Debug)]
enum Eval {
    File {
        #[arg(short, long, required = true)]
        path: PathBuf,
        #[arg(short, long, required = true)]
        env_path: PathBuf,
        #[arg(
            short = 'f',
            long = "format",
            default_value_t = Format::Debug,
            value_enum
        )]
        format: Format,
    },
    Expr {
        #[arg(long, required = true)]
        expr: String,
        #[arg(long, required = true)]
        env_path: PathBuf,
        #[arg(
            short = 'f',
            long = "format",
            default_value_t = Format::Debug,
            value_enum
        )]
        format: Format,
    },
}

impl Eval {
    fn run(&self) -> Result<(), Error> {
        match self {
            Eval::File {
                path,
                env_path,
                format,
            } => {
                let source = read_source(path)?;
                evaluate(&source, env_path, *format)
            }
            Eval::Expr {
                expr,
                env_path,
                format,
            } => evaluate(expr, env_path, *format),
        }
    }
}

fn main() -> Result<(), Error> {
    let args = Args::parse();

    match args.command {
        Commands::Lex(lex) => lex.run(),
        Commands::Parse(parse) => parse.run(),
        Commands::Eval(eval) => eval.run(),
    }
}

#[derive(Debug, Serialize)]
struct LexToken {
    kind: String,
    lexeme: String,
    line: usize,
    offset: usize,
    span_len: usize,
}

impl<'src> From<Token<'src>> for LexToken {
    fn from(token: Token<'src>) -> Self {
        LexToken {
            kind: format!("{:?}", token.ty),
            lexeme: token.origin.to_string(),
            line: token.line,
            offset: token.offset,
            span_len: token.span_len,
        }
    }
}

fn read_source(path: &Path) -> Result<String, Error> {
    fs::read_to_string(path)
        .into_diagnostic()
        .wrap_err_with(|| format!("Failed to read {}", path.display()))
}

fn print_tokens(source: &str, format: Format) -> Result<(), Error> {
    let tokens = lex_source(source)?;
    format.print(&tokens);
    Ok(())
}

fn lex_source(source: &str) -> Result<Vec<LexToken>, Error> {
    let lexer = Lexer::new(source);
    let mut tokens = Vec::new();
    for next in lexer {
        tokens.push(next?.into());
    }
    Ok(tokens)
}

fn print_ast(source: &str, format: Format) -> Result<(), Error> {
    let mut parser = Parser::new(source);
    let ast = parser.parse()?;
    format.print(&ast);
    Ok(())
}

fn evaluate(expr: &str, env_path: &Path, format: Format) -> Result<(), Error> {
    let entries = load_env_variables(env_path)?;
    let mut builder = Runtime::builder();
    builder.set_variables(entries);
    let runtime = builder.build();
    let value = runtime.eval(expr)?;
    format.print(&value);
    Ok(())
}

fn load_env_variables(path: &Path) -> Result<Vec<(String, Value)>, Error> {
    let raw = read_source(path)?;
    let json: JsonValue = serde_json::from_str(&raw)
        .into_diagnostic()
        .wrap_err_with(|| {
            format!("Failed to parse JSON from {}", path.display())
        })?;
    let object = json
        .as_object()
        .ok_or_else(|| miette!("Environment file must be a JSON object"))?;
    Ok(object
        .iter()
        .map(|(name, value)| (name.clone(), json_to_value(value)))
        .collect())
}

fn json_to_value(value: &JsonValue) -> Value {
    match value {
        JsonValue::Null => Value::Null,
        JsonValue::Bool(flag) => Value::Bool(*flag),
        JsonValue::Number(num) => {
            if let Some(int) = num.as_i64() {
                Value::Int(int)
            } else if let Some(u) = num.as_u64() {
                Value::Uint(u)
            } else if let Some(float) = num.as_f64() {
                Value::Double(float)
            } else {
                Value::Double(f64::NAN)
            }
        }
        JsonValue::String(text) => Value::String(text.clone()),
        JsonValue::Array(items) => {
            let converted = items.iter().map(json_to_value).collect::<Vec<_>>();
            Value::List(ListValue::from(converted))
        }
        JsonValue::Object(map) => {
            let mut cel_map = MapValue::new();
            for (key, value) in map {
                cel_map.insert(key.clone(), json_to_value(value));
            }
            Value::Map(cel_map)
        }
    }
}
