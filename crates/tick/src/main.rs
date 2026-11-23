mod tickset;
mod ticktemplate;
use crate::tickset::TickSet;
use crate::ticktemplate::TickTemplate;
use anyhow::Context;
use clap::Parser;
use lifelib::{
    Edges, Pattern,
    document::{Document, FormatChoice},
    formats::Format,
};
use patharg::InputArg;
use std::path::{Path, PathBuf};

/// Advance Conway's Game of Life patterns
///
/// See <https://github.com/jwodder/life/tree/master/crates/tick> for more
/// information.
#[derive(Clone, Debug, Parser, PartialEq)]
struct Arguments {
    /// Embed the given comment in the output file.
    ///
    /// The name may contain `%d` placeholders which will be replaced by the
    /// tick number.
    ///
    /// This option may be specified multiple times.
    #[arg(short, long, value_name = "TEXT")]
    comment: Vec<TickTemplate>,

    /// Configure the behavior of the edges of the pattern's universe.
    ///
    /// Possible values (case insensitive):
    ///
    /// - dead [default]: Cells beyond the universe's bounds are dead and
    ///   cannot come to life
    ///
    /// - wrapx: The universe's x-axis wraps around so that the left edge is
    ///   connected to the right edge
    ///
    /// - wrapy: The universe's y-axis wraps around so that the top edge is
    ///   connected to the bottom edge
    ///
    /// - wrapxy: The universe's x- and y-axes both wrap around
    ///
    /// - growx: The universe's x-axis will be extended to the left or right as
    ///   necessary in order to accomodate new live cells
    ///
    /// - growy: The universe's y-axis will be extended to the top or bottom as
    ///   necessary in order to accomodate new live cells
    ///
    /// - growxy: The universe's x- and y-axes will both be extended as
    ///   necessary
    #[arg(
        short = 'E',
        long,
        default_value_t,
        value_name = "dead|wrapx|wrapy|wrapxy|growx|growy|growxy"
    )]
    edges: Edges,

    /// Set the pattern name to embed in the output file.
    ///
    /// The name may contain `%d` placeholders which will be replaced by the
    /// tick number.
    #[arg(short = 'N', long, value_name = "TEXT")]
    name: Option<TickTemplate>,

    /// Specify the number(s) of ticks to advance the input pattern by in order
    /// to produce the output.
    ///
    /// `NUMBERS` consists of one or more nonnegative integers and/or
    /// hyphenated inclusive ranges of nonnegative integers, all separated by
    /// commas.  If multiple tick numbers are specified, multiple outputs are
    /// produced, one for each specified tick number in the input pattern's
    /// history.
    #[arg(
        short = 'n',
        long = "number",
        default_value = "1",
        value_name = "NUMBERS"
    )]
    ticks: TickSet,

    /// A file containing a Game of Life pattern.
    ///
    /// The file must either be in plaintext format with a `.cells` file
    /// extension or be in Run Length Encoded format with an `.rle` file
    /// extension.  Alternatively, `-` can be specified in order to read from
    /// standard input, in which case the format will be guessed based on
    /// initial content.
    infile: InputArg,

    /// Path at which to write the output pattern(s).
    ///
    /// The path's file extension must be `.cells` (to produce a plaintext
    /// file) or `.rle` (to produce an RLE file).
    ///
    /// The path may contain `%d` placeholders which will be replaced by the
    /// tick number.
    outfile: TickTemplate,
}

impl Arguments {
    fn saver(&mut self) -> anyhow::Result<Saver> {
        if let Some(ext) = self.outfile.extension()
            && let Some(format) = Format::iter().find(|f| f.has_extension(ext))
        {
            Ok(Saver {
                name: self.name.take(),
                comments: std::mem::take(&mut self.comment),
                format,
            })
        } else {
            anyhow::bail!("output path does not have a supported file extension");
        }
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
struct Saver {
    name: Option<TickTemplate>,
    comments: Vec<TickTemplate>,
    format: Format,
}

impl Saver {
    fn save(&self, pattern: Pattern, path: &Path, index: usize) -> anyhow::Result<()> {
        if let Some(parent) = path.parent()
            && parent != Path::new("")
        {
            fs_err::create_dir_all(parent)?;
        }
        let doc = Document {
            name: self.name.as_ref().map(|tmplt| tmplt.render(index)),
            comments: self
                .comments
                .iter()
                .map(|tmplt| tmplt.render(index))
                .collect(),
            pattern,
        };
        doc.dump_to_file(path, FormatChoice::Fixed(self.format))
            .with_context(|| format!("failed to write pattern to {}", path.display()))?;
        Ok(())
    }
}

fn main() -> anyhow::Result<()> {
    let mut args = Arguments::parse();
    if args.outfile.is_literal() && args.ticks.is_more_than_one() {
        eprintln!(
            "tick: warning: multiple tick numbers selected but no placeholders included in output path"
        );
    }
    let saver = args.saver()?;
    let maxtick = args.ticks.maxvalue();
    let doc = match args.infile {
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
    let pattern = doc.pattern.with_edges(args.edges);
    for (i, pat) in pattern
        .into_generations()
        .take(maxtick.saturating_add(1))
        .enumerate()
    {
        if args.ticks.contains(i) {
            let outfile = PathBuf::from(String::from(args.outfile.render(i)));
            saver.save(pat, &outfile, i)?;
        }
    }
    Ok(())
}
