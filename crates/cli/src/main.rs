use cellang::{EnvironmentBuilder, Lexer, Map, Parser, eval};
use clap::{Parser as ClapParser, Subcommand};
use miette::{Error, IntoDiagnostic, WrapErr};
use serde::Serialize;
use std::fmt;
use std::{fs, path::PathBuf};

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
    File { path: PathBuf },
    Expr { expr: String },
}

impl Lex {
    fn run(&self) -> Result<(), Error> {
        let content = match self {
            Lex::File { path } => fs::read_to_string(path)
                .into_diagnostic()
                .wrap_err("Failed to read file")?,
            Lex::Expr { expr } => expr.clone(),
        };

        let lexer = Lexer::new(&content);
        for token in lexer {
            match token {
                Ok(token) => println!("{:#?}", token),
                Err(err) => return Err(err),
            }
        }
        Ok(())
    }
}

#[derive(Subcommand, Debug)]
enum Parse {
    File {
        #[arg(short, long, required = false, default_value_t = Format::Debug)]
        format: Format,

        path: PathBuf,
    },
    Expr {
        #[arg(short, long, required = false, default_value_t = Format::Debug)]
        format: Format,

        expr: String,
    },
}

#[derive(Debug, Clone, Copy, Default)]
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
        let (content, format) = match self {
            Parse::File { path, format } => (
                fs::read_to_string(path)
                    .into_diagnostic()
                    .wrap_err("Failed to read file")?,
                format,
            ),
            Parse::Expr { expr, format } => (expr.clone(), format),
        };

        let mut parser = Parser::new(&content);
        let ast = parser.parse().wrap_err("Failed to parse")?;

        format.print(&ast);

        Ok(())
    }
}

#[derive(Subcommand, Debug)]
enum Eval {
    File {
        #[arg(short, long, required = true)]
        path: PathBuf,
        #[arg(short, long, required = true)]
        env_path: PathBuf,
    },
    Expr {
        #[arg(long, required = true)]
        expr: String,
        #[arg(long, required = true)]
        env_path: PathBuf,
    },
}

impl Eval {
    fn run(&self) -> Result<(), Error> {
        let (content, env_path) = match self {
            Eval::File { path, env_path } => (
                fs::read_to_string(path)
                    .into_diagnostic()
                    .wrap_err("Failed to read file")?,
                env_path,
            ),
            Eval::Expr { expr, env_path } => (expr.clone(), env_path),
        };

        let variables: Map = serde_json::from_str(
            &fs::read_to_string(env_path)
                .into_diagnostic()
                .wrap_err("Failed to read file")?,
        )
        .into_diagnostic()
        .wrap_err("Failed to deserialize environment")?;

        let env = EnvironmentBuilder::default();
        let mut env = env.build();
        env.set_variables(&variables);
        match eval(&env, &content) {
            Ok(value) => println!("{value:?}"),
            Err(err) => return Err(err),
        }
        Ok(())
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
