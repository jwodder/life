use clap::Parser;
use cmdutils::{DocumentExt, io_exit};
use lifelib::{
    Document, FormatChoice,
    formats::{Format, Letter},
    utilities::Line,
};
use patharg::{InputArg, OutputArg};

/// Convert Game of Life patterns between file formats
///
/// See <https://github.com/jwodder/life/tree/master/crates/patformat> for more
/// information.
#[derive(Clone, Debug, Eq, Parser, PartialEq)]
struct Command {
    /// Remove all comments and hash lines from the input file
    #[arg(short = 'C', long)]
    clear_comments: bool,

    /// Add the given comment to the output file.
    ///
    /// This option may be specified multiple times.
    #[arg(short, long, value_name = "TEXT")]
    comment: Vec<Line>,

    /// Set the output file format.
    ///
    /// If not specified, the output format will be determined from the output
    /// path's file extension, or plaintext when writing to stdout.
    #[arg(short, long, value_name = "plaintext|cells|rle")]
    format: Option<Format>,

    /// Set the pattern name to embed in the output file.
    #[arg(short = 'N', long, value_name = "TEXT")]
    name: Option<Line>,

    /// Add the given hash line to an RLE output file.
    ///
    /// The argument must consist of an optional '#', an ASCII letter, a space,
    /// and then text.
    ///
    /// This option may be specified multiple times.
    #[arg(short = 'R', long, value_name = "LETTER TEXT", value_parser = parse_rle_comment_arg)]
    rle_comment: Vec<(Letter, Line)>,

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
    /// If `--format` is not specified, then the path's file extension must be
    /// `.cells` (to produce a plaintext file) or `.rle` (to produce an RLE
    /// file).  Alternatively, the path may be `-` or omitted to write
    /// to standard output (as plaintext if `--format` is not specified).
    #[arg(default_value_t)]
    outfile: OutputArg,
}

impl Command {
    fn run(self) -> anyhow::Result<()> {
        let mut doc = Document::load_from_input(self.infile)?;
        if self.clear_comments {
            doc.name = None;
            doc.comments.clear();
            doc.rle_comments.clear();
        }
        if let Some(n) = self.name {
            doc.name = Some(n);
        }
        doc.comments.extend(self.comment);
        doc.rle_comments.extend(self.rle_comment);
        doc.dump_to_output(
            self.outfile,
            self.format
                .map_or(FormatChoice::Autodetect, FormatChoice::Fixed),
        )?;
        Ok(())
    }
}

fn main() -> std::process::ExitCode {
    io_exit(Command::parse().run())
}

fn parse_rle_comment_arg(s: &str) -> anyhow::Result<(Letter, Line)> {
    let s = s.strip_prefix('#').unwrap_or(s);
    let Some(ch) = s.chars().next() else {
        anyhow::bail!("empty string");
    };
    let ty = Letter::try_from(ch)?;
    let Some(text) = s[1..].strip_prefix(' ') else {
        anyhow::bail!("no space after type letter");
    };
    let line = text.parse::<Line>()?;
    Ok((ty, line))
}
