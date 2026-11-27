use clap::Parser;
use either::Either;
use lifelib::{Document, FormatChoice};
use serde::Serialize;
use std::io::{Error, ErrorKind, Write, stderr, stdout};
use std::path::{Path, PathBuf};
use std::process::ExitCode;

/// Check parseability of Game of Life patterns
///
/// See <https://github.com/jwodder/life/tree/master/crates/parse-check> for
/// more information.
#[derive(Clone, Debug, Eq, Parser, PartialEq)]
struct Command {
    /// Report parse failures to stdout as JSON Lines
    #[arg(short = 'J', long)]
    json: bool,

    path: Vec<PathBuf>,
}

impl Command {
    fn run(self) -> anyhow::Result<ExitCode> {
        let mut ok = true;
        let mut out = if self.json {
            Either::Left(stdout().lock())
        } else {
            Either::Right(stderr().lock())
        };
        for p in self.path {
            if let Err(e) = Document::load_from_file(&p, FormatChoice::Autodetect) {
                if self.json {
                    let err = Failure {
                        path: p,
                        traceback: anyhow::Error::new(e)
                            .chain()
                            .map(ToString::to_string)
                            .collect(),
                    };
                    writeln!(
                        &mut out,
                        "{}",
                        serde_json::to_string(&err).expect("JSONification should not fail")
                    )?;
                } else {
                    if !ok {
                        writeln!(&mut out)?;
                        writeln!(&mut out, "---")?;
                        writeln!(&mut out)?;
                    }
                    writeln!(
                        &mut out,
                        "Failed to parse {}: {:?}",
                        p.display(),
                        anyhow::Error::new(e)
                    )?;
                }
                ok = false;
            }
        }
        if ok {
            Ok(ExitCode::SUCCESS)
        } else {
            Ok(ExitCode::FAILURE)
        }
    }
}

#[derive(Clone, Debug, Eq, PartialEq, Serialize)]
struct Failure {
    path: PathBuf,
    traceback: Vec<String>,
}

fn main() -> ExitCode {
    match Command::parse().run() {
        Ok(c) => c,
        Err(e) => {
            for cause in e.chain() {
                if let Some(ioerr) = cause.downcast_ref::<Error>()
                    && ioerr.kind() == ErrorKind::BrokenPipe
                {
                    return ExitCode::SUCCESS;
                }
            }
            let mut err = stderr().lock();
            if let Some(p) = std::env::args_os().next().map(PathBuf::from)
                && let Some(name) = p.file_name()
            {
                let _ = writeln!(&mut err, "{}: ", Path::new(name).display());
            }
            let _ = writeln!(&mut err, "{e:?}");
            ExitCode::FAILURE
        }
    }
}
