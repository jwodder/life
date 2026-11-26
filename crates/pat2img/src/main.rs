use anyhow::Context;
use clap::Parser;
use cmdutils::{DocumentExt, Painter};
use lifelib::Document;
use patharg::InputArg;
use std::path::PathBuf;

/// Render Conway's Game of Life patterns as images
///
/// See <https://github.com/jwodder/life/tree/master/crates/pat2img> for more
/// information.
#[derive(Clone, Debug, Parser, PartialEq)]
struct Arguments {
    #[command(flatten)]
    painter: Painter,

    /// A file containing a Game of Life pattern.
    ///
    /// The file must either be in plaintext format with a `.cells` file
    /// extension or be in Run Length Encoded format with an `.rle` file
    /// extension.  Alternatively, `-` can be specified in order to read from
    /// standard input, in which case the format will be guessed based on
    /// initial content.
    infile: InputArg,

    /// Path at which to write the output image.
    ///
    /// The output format is determined from the file extension.
    outfile: PathBuf,
}

fn main() -> anyhow::Result<()> {
    let args = Arguments::parse();
    let builder = args.painter.build();
    let doc = Document::load_from_input(args.infile)?;
    builder
        .render(&doc.pattern)
        .context("failed to render image")?
        .save(&args.outfile)
        .with_context(|| format!("failed to write image to {}", args.outfile.display()))?;
    Ok(())
}
