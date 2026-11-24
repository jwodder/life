use lifelib::{Document, FormatChoice};
use std::process::ExitCode;

fn main() -> ExitCode {
    let mut ok = true;
    for p in std::env::args_os().skip(1) {
        if let Err(e) = Document::load_from_file(&p, FormatChoice::Autodetect) {
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
            ok = false;
        }
    }
    if ok {
        ExitCode::SUCCESS
    } else {
        ExitCode::FAILURE
    }
}
