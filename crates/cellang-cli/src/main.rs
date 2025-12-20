use clap::{Parser as ClapParser, Subcommand};
use miette::{Error, IntoDiagnostic, Report, WrapErr};
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
        todo!()
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
        todo!()
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
       todo!() 
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
