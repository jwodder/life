use anyhow::Context;
use clap::Parser;
use lifelib::{Document, FormatChoice, Padding, formats::Format};
use patharg::{InputArg, OutputArg};
use std::io::Write;

/// Pad & crop Game of Life patterns
///
/// See <https://github.com/jwodder/life/tree/master/crates/chbounds> for more
/// information.
#[derive(Clone, Debug, Eq, Parser, PartialEq)]
struct Arguments {
    /// Add/remove <INT> rows to/from the bottom of the pattern
    ///
    /// This overrides any bottom padding amounts set by --uniform or
    /// --vertical.
    #[arg(long, value_name = "INT")]
    bottom: Option<isize>,

    /// Add/remove <INT> columns to/from the left and right sides of the
    /// pattern
    ///
    /// This overrides any horizontal padding amounts set by --uniform.
    #[arg(long, value_name = "INT")]
    horizontal: Option<isize>,

    /// Add/remove <INT> columns to/from the left side of the pattern
    ///
    /// This overrides any left padding amounts set by --uniform or
    /// --horizontal.
    #[arg(long, value_name = "INT")]
    left: Option<isize>,

    /// Crop the pattern to its bounding box.
    ///
    /// This effect is applied before all other options.
    #[arg(long)]
    minimize: bool,

    /// Add/remove <INT> columns to/from the right side of the pattern
    ///
    /// This overrides any right padding amounts set by --uniform or
    /// --horizontal.
    #[arg(long, value_name = "INT")]
    right: Option<isize>,

    /// Add/remove <INT> rows to/from the top of the pattern
    ///
    /// This overrides any top padding amounts set by --uniform or --vertical.
    #[arg(long, value_name = "INT")]
    top: Option<isize>,

    /// Add/remove <INT> cells on all fours sides of the pattern
    #[arg(long, value_name = "INT")]
    uniform: Option<isize>,

    /// Add/remove <INT> columns to/from the top and bottom of the pattern
    ///
    /// This overrides any vertical padding amounts set by --uniform.
    #[arg(long, value_name = "INT")]
    vertical: Option<isize>,

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
    let mut doc = match args.infile {
        stdin @ InputArg::Stdin => {
            let docstr = stdin
                .read_to_string()
                .context("failed to read pattern from standard input")?;
            Document::load_from_str(&docstr, FormatChoice::Autodetect)
                .context("failed to parse input pattern")?
        }
        InputArg::Path(p) => Document::load_from_file(&p, FormatChoice::Autodetect)
            .with_context(|| format!("failed to read pattern from {}", p.display()))?,
    };
    let mut bounds = if args.minimize {
        doc.pattern.bounding_box()
    } else {
        doc.pattern.bounds()
    };
    let mut padding = Padding::uniform(args.uniform.unwrap_or_default());
    if let Some(p) = args.vertical {
        padding.top = p;
        padding.bottom = p;
    }
    if let Some(p) = args.horizontal {
        padding.left = p;
        padding.right = p;
    }
    if let Some(p) = args.top {
        padding.top = p;
    }
    if let Some(p) = args.left {
        padding.left = p;
    }
    if let Some(p) = args.bottom {
        padding.bottom = p;
    }
    if let Some(p) = args.right {
        padding.right = p;
    }
    bounds = bounds
        .padded(padding)
        .context("failed to computed padded dimensions")?;
    doc.pattern = doc.pattern.resize(bounds);
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
