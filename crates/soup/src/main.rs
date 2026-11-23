use anyhow::Context;
use clap::Parser;
use lifelib::{Pattern, document::Document, formats::Format, utilities::Line};
use patharg::OutputArg;
use rand::distr::{Bernoulli, Distribution};
use std::io::Write;
use thiserror::Error;

#[derive(Clone, Debug, Parser, PartialEq)]
struct Arguments {
    /// Embed the given comment in the output file.
    ///
    /// This option may be specified multiple times.
    #[arg(short, long, value_name = "TEXT")]
    comment: Vec<Line>,

    /// Set the pattern name to embed in the output file.
    #[arg(short = 'N', long, value_name = "TEXT")]
    name: Option<Line>,

    /// Probability of a given cell being alive, as a percentage from 0 to 100
    #[arg(short, long, default_value = "10", value_name = "PERCENTAGE")]
    probabilty: Percent,

    /// Dimensions of the pattern to generate
    #[arg(value_name = "WIDTHxHEIGHT")]
    size: Size,

    /// Path at which to write the pattern.
    ///
    /// The path's file extension must be `.cells` (to produce a plaintext
    /// file) or `.rle` (to produce an RLE file).  Alternatively, the path may
    /// be `-` or omitted to write plaintext to standard output.
    #[arg(default_value_t)]
    outfile: OutputArg,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct Size {
    width: usize,
    height: usize,
}

impl std::str::FromStr for Size {
    type Err = ParseSizeError;

    fn from_str(s: &str) -> Result<Size, ParseSizeError> {
        if let Some((w, h)) = s.split_once('x') {
            let width = w.parse::<usize>()?;
            let height = h.parse::<usize>()?;
            Ok(Size { width, height })
        } else {
            Err(ParseSizeError::Invalid)
        }
    }
}

#[derive(Clone, Debug, Eq, Error, PartialEq)]
enum ParseSizeError {
    #[error("not in WIDTHxHEIGHT format")]
    Invalid,
    #[error("invalid number")]
    ParseInt(#[from] std::num::ParseIntError),
}

#[derive(Clone, Copy, Debug, PartialEq)]
struct Percent(f64);

impl std::str::FromStr for Percent {
    type Err = ParsePercentError;

    fn from_str(s: &str) -> Result<Percent, ParsePercentError> {
        let p = s.parse::<f64>()?;
        if !p.is_finite() {
            Err(ParsePercentError::NotFinite)
        } else if p < 0.0 || p > 100.0 {
            Err(ParsePercentError::OutOfRange)
        } else {
            Ok(Percent(p))
        }
    }
}

#[derive(Clone, Debug, Eq, Error, PartialEq)]
enum ParsePercentError {
    #[error("invalid percentage")]
    NotFinite,
    #[error("percentage must be from 0 to 100")]
    OutOfRange,
    #[error("invalid float")]
    Parse(#[from] std::num::ParseFloatError),
}

fn main() -> anyhow::Result<()> {
    let args = Arguments::parse();
    let mut pattern = Pattern::new(args.size.height, args.size.width);
    let dist =
        Bernoulli::new(args.probabilty.0 / 100.0).expect("probability should be between 0 and 1");
    let mut rng = rand::rng();
    for c in pattern.iter_coords() {
        if dist.sample(&mut rng) {
            pattern.birth(c);
        }
    }
    let doc = Document {
        name: args.name,
        comments: args.comment,
        pattern,
    };
    let format = match args.outfile {
        OutputArg::Stdout => Format::Plaintext,
        OutputArg::Path(ref p) => Format::identify(p).ok_or_else(|| {
            anyhow::Error::msg("output path does not have a supported file extension")
        })?,
    };
    let mut fp = args
        .outfile
        .create()
        .context("failed to open output file")?;
    write!(&mut fp, "{}", doc.display(format)).context("failed to write to output file")?;
    fp.flush().context("failed to write to output file")?;
    Ok(())
}
