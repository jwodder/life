use clap::Parser;
use lifelib::{Document, FormatChoice};
use serde::Serialize;
use std::path::PathBuf;
use std::process::ExitCode;

/// Check parseability of Game of Life patterns
///
/// See <https://github.com/jwodder/life/tree/master/crates/parse-check> for
/// more information.
#[derive(Clone, Debug, Eq, Parser, PartialEq)]
struct Arguments {
    /// Report parse failures to stdout as JSON Lines
    #[arg(short = 'J', long)]
    json: bool,

    path: Vec<PathBuf>,
}

#[derive(Clone, Debug, Eq, PartialEq, Serialize)]
struct Failure {
    path: PathBuf,
    traceback: Vec<String>,
}

fn main() -> ExitCode {
    let args = Arguments::parse();
    let mut ok = true;
    for p in args.path {
        if let Err(e) = Document::load_from_file(&p, FormatChoice::Autodetect) {
            if args.json {
                let err = Failure {
                    path: p,
                    traceback: anyhow::Error::new(e)
                        .chain()
                        .map(ToString::to_string)
                        .collect(),
                };
                println!(
                    "{}",
                    serde_json::to_string(&err).expect("JSONification should not fail")
                );
            } else {
                if !ok {
                    eprintln!();
                    eprintln!("---");
                    eprintln!();
                }
                eprintln!(
                    "Failed to parse {}: {:?}",
                    p.display(),
                    anyhow::Error::new(e)
                );
            }
            ok = false;
        }
    }
    if ok {
        ExitCode::SUCCESS
    } else {
        ExitCode::FAILURE
    }
}
