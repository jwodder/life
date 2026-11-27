use anyhow::Context;
use clap::Parser;
use cmdutils::{DocumentExt, io_exit};
use lifelib::{Document, FormatChoice, Padding};
use patharg::{InputArg, OutputArg};

/// Pad & crop Game of Life patterns
///
/// See <https://github.com/jwodder/life/tree/master/crates/chbounds> for more
/// information.
#[derive(Clone, Debug, Eq, Parser, PartialEq)]
struct Command {
    /// Add/remove <INT> rows to/from the bottom of the pattern
    ///
    /// This overrides any bottom padding amounts set by --uniform or
    /// --vertical.
    #[arg(long, allow_negative_numbers = true, value_name = "INT")]
    bottom: Option<isize>,

    /// Add/remove <INT> columns to/from the left and right sides of the
    /// pattern
    ///
    /// This overrides any horizontal padding amounts set by --uniform.
    #[arg(long, allow_negative_numbers = true, value_name = "INT")]
    horizontal: Option<isize>,

    /// Add/remove <INT> columns to/from the left side of the pattern
    ///
    /// This overrides any left padding amounts set by --uniform or
    /// --horizontal.
    #[arg(long, allow_negative_numbers = true, value_name = "INT")]
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
    #[arg(long, allow_negative_numbers = true, value_name = "INT")]
    right: Option<isize>,

    /// Add/remove <INT> rows to/from the top of the pattern
    ///
    /// This overrides any top padding amounts set by --uniform or --vertical.
    #[arg(long, allow_negative_numbers = true, value_name = "INT")]
    top: Option<isize>,

    /// Add/remove <INT> cells on all fours sides of the pattern
    #[arg(long, allow_negative_numbers = true, value_name = "INT")]
    uniform: Option<isize>,

    /// Add/remove <INT> columns to/from the top and bottom of the pattern
    ///
    /// This overrides any vertical padding amounts set by --uniform.
    #[arg(long, allow_negative_numbers = true, value_name = "INT")]
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

impl Command {
    fn run(self) -> anyhow::Result<()> {
        let mut doc = Document::load_from_input(self.infile)?;
        let mut bounds = if self.minimize {
            doc.pattern.bounding_box()
        } else {
            doc.pattern.bounds()
        };
        let mut padding = Padding::uniform(self.uniform.unwrap_or_default());
        if let Some(p) = self.vertical {
            padding.top = p;
            padding.bottom = p;
        }
        if let Some(p) = self.horizontal {
            padding.left = p;
            padding.right = p;
        }
        if let Some(p) = self.top {
            padding.top = p;
        }
        if let Some(p) = self.left {
            padding.left = p;
        }
        if let Some(p) = self.bottom {
            padding.bottom = p;
        }
        if let Some(p) = self.right {
            padding.right = p;
        }
        bounds = bounds
            .padded(padding)
            .context("failed to computed padded dimensions")?;
        doc.pattern = doc.pattern.resize(bounds);
        doc.dump_to_output(self.outfile, FormatChoice::Autodetect)?;
        Ok(())
    }
}

fn main() -> std::process::ExitCode {
    io_exit(Command::parse().run())
}
