use clap::Parser;
use fs_err::File;
use lifelib::{
    formats::{Plaintext, Rle},
    Pattern,
};
use std::io::Write;
use std::path::{Path, PathBuf};

#[derive(Clone, Debug, Eq, Parser, PartialEq)]
struct Arguments {
    #[arg(short, long, default_value_t = 1)]
    number: usize,

    infile: PathBuf,

    outfile: PathBuf,
}

fn main() -> anyhow::Result<()> {
    let args = Arguments::parse();
    let mut pattern = Pattern::from_file(args.infile)?;
    for _ in 0..args.number {
        pattern = pattern.step();
    }
    save_pattern(pattern, args.outfile)?;
    Ok(())
}

fn save_pattern<P: AsRef<Path>>(pattern: Pattern, path: P) -> anyhow::Result<()> {
    let path = path.as_ref();
    match path.extension().and_then(|s| s.to_str()) {
        Some("cells") => {
            let pt = Plaintext {
                name: String::from("Pattern"),
                comments: Vec::new(),
                pattern,
            };
            let mut fp = File::create(path)?;
            write!(fp, "{pt}")?;
        }
        Some("rle") => {
            let rle = Rle {
                comments: Vec::new(),
                pattern,
            };
            let mut fp = File::create(path)?;
            write!(fp, "{rle}")?;
        }
        _ => anyhow::bail!("output path does not have a supported file extension"),
    }
    Ok(())
}
