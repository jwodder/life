use anyhow::Context;
use clap::Parser;
use lifelib::{
    document::{Document, FormatChoice},
    image::ImageBuilder,
};
use patharg::InputArg;
use std::num::NonZeroU32;
use std::path::PathBuf;

/// Render Conway's Game of Life patterns as images
///
/// See <https://github.com/jwodder/life/tree/master/crates/pat2img> for more
/// information.
#[derive(Clone, Debug, Parser, PartialEq)]
struct Arguments {
    /// Set the height & width of the cell squares to the given number of
    /// pixels
    #[arg(short = 's', long, default_value = "5", value_name = "INT")]
    cell_size: NonZeroU32,

    /// Set the color of dead cells.
    ///
    /// `COLOR` can be a hex RGB string `#rrggbb` (with or without leading `#`)
    /// or a CSS color name.
    #[arg(short = 'D', long, default_value = "#FFFFFF", value_name = "COLOR")]
    dead_color: csscolorparser::Color,

    /// Insert the given number of pixels as padding between adjacent cell
    /// squares
    #[arg(short, long, default_value_t = 0, value_name = "INT")]
    gutter: u32,

    /// Set the color of the gutter.
    ///
    /// `COLOR` can be a hex RGB string `#rrggbb` (with or without leading `#`)
    /// or a CSS color name.
    #[arg(short = 'G', long, value_name = "COLOR")]
    gutter_color: Option<csscolorparser::Color>,

    /// Set the color of live cells.
    ///
    /// `COLOR` can be a hex RGB string `#rrggbb` (with or without leading `#`)
    /// or a CSS color name.
    #[arg(short = 'C', long, default_value = "#000000", value_name = "COLOR")]
    live_color: csscolorparser::Color,

    /// Add a margin `INT` pixels thick around the image
    #[arg(short, long, default_value_t = 0, value_name = "INT")]
    margin: u32,

    /// Set the color of the margin.
    ///
    /// `COLOR` can be a hex RGB string `#rrggbb` (with or without leading `#`)
    /// or a CSS color name.
    #[arg(short = 'M', long, value_name = "COLOR")]
    margin_color: Option<csscolorparser::Color>,

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
    let [r, g, b, _] = args.live_color.to_rgba8();
    let [dr, dg, db, _] = args.dead_color.to_rgba8();
    let mut builder = ImageBuilder::new()
        .cell_size(args.cell_size)
        .live_color([r, g, b].into())
        .dead_color([dr, dg, db].into())
        .gutter(args.gutter)
        .margin(args.margin);
    if let Some(c) = args.gutter_color {
        let [r, g, b, _] = c.to_rgba8();
        builder = builder.gutter_color([r, g, b].into());
    }
    if let Some(c) = args.margin_color {
        let [r, g, b, _] = c.to_rgba8();
        builder = builder.margin_color([r, g, b].into());
    }
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
    builder
        .render(&doc.pattern)
        .context("failed to render image")?
        .save(&args.outfile)
        .with_context(|| format!("failed to write image to {}", args.outfile.display()))?;
    Ok(())
}
