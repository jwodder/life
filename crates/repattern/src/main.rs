use clap::Parser;
use cmdutils::DocumentExt;
use lifelib::{Document, FormatChoice, formats::Format};
use patharg::{InputArg, OutputArg};

/// Convert Game of Life patterns between file formats
///
/// See <https://github.com/jwodder/life/tree/master/crates/repattern> for more
/// information.
#[derive(Clone, Debug, Eq, Parser, PartialEq)]
struct Arguments {
    #[arg(short, long)]
    format: Option<Format>,

    /// A file containing a Game of Life pattern.
    ///
    /// The file must either be in plaintext format with a `.cells` file
    /// extension or be in Run Length Encoded format with an `.rle` file
    /// extension.  Alternatively, the path may be `-` or omitted in order to
    /// read from standard input, in which case the format will be guessed
    /// based on initial content.
    #[arg(default_value_t)]
    infile: InputArg,

    /// Path at which to write the pattern.
    ///
    /// The path's file extension must be `.cells` (to produce a plaintext
    /// file) or `.rle` (to produce an RLE file).  Alternatively, the path may
    /// be `-` or omitted to write plaintext to standard output.
    #[arg(default_value_t)]
    outfile: OutputArg,
}

fn main() -> anyhow::Result<()> {
    let args = Arguments::parse();
    let doc = Document::load_from_input(args.infile)?;
    doc.dump_to_output(
        args.outfile,
        args.format
            .map_or(FormatChoice::Autodetect, FormatChoice::Fixed),
    )?;
    Ok(())
}
