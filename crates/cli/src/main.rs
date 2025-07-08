use cellang::{EnvironmentBuilder, Lexer, Map, Parser, eval};
use clap::{Parser as ClapParser, Subcommand};
use miette::{Error, IntoDiagnostic, WrapErr};
use std::{fs, path::PathBuf};

#[derive(ClapParser, Debug)]
#[command(version, about, long_about = None)]
struct Args {
    #[command(subcommand)]
    command: Commands,
}

#[derive(Subcommand, Debug)]
enum Commands {
    Lex {
        #[arg(short, long, required = true)]
        filename: PathBuf,
    },
    Parse {
        #[arg(short, long, required = true)]
        filename: PathBuf,
    },
    Eval {
        #[arg(short, long, required = true)]
        filename: PathBuf,

        #[arg(short, long, required = true)]
        env: PathBuf,
    },
}

fn main() -> Result<(), Error> {
    let args = Args::parse();

    match args.command {
        Commands::Lex { filename } => {
            let text = fs::read_to_string(filename)
                .into_diagnostic()
                .wrap_err("Failed to read file")?;

            let lexer = Lexer::new(&text);
            for token in lexer {
                match token {
                    Ok(token) => println!("{token}"),
                    Err(err) => return Err(err),
                }
            }

            Ok(())
        }
        Commands::Parse { filename } => {
            let text = fs::read_to_string(filename)
                .into_diagnostic()
                .wrap_err("Failed to read file")?;

            let mut parser = Parser::new(&text);
            let ast = parser.parse().wrap_err("Failed to parse")?;
            println!("{:#?}", ast);

            Ok(())
        }
        Commands::Eval { filename, env } => {
            let text = fs::read_to_string(filename)
                .into_diagnostic()
                .wrap_err("Failed to read file")?;

            let variables: Map = serde_json::from_str(
                &fs::read_to_string(env)
                    .into_diagnostic()
                    .wrap_err("Failed to read file")?,
            )
            .into_diagnostic()
            .wrap_err("Failed to deserialize environment")?;

            let env = EnvironmentBuilder::default();
            let mut env = env.build();
            env.set_variables(&variables);
            match eval(&env, &text) {
                Ok(value) => println!("{value:?}"),
                Err(err) => return Err(err),
            }
            Ok(())
        }
    }
}
