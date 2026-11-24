use anyhow::Context;
use clap::Parser;
use lifelib::{
    Document, Edges, FormatChoice,
    image::{
        ImageBuilder,
        image::{
            Delay, DynamicImage, Frame, RgbaImage,
            codecs::gif::{GifEncoder, Repeat},
        },
    },
    sync_bounds,
};
use patharg::{InputArg, OutputArg};
use std::io::BufWriter;
use std::num::{NonZeroU32, NonZeroUsize};

/// Generate a GIF of a Game of Life pattern's generations
///
/// See <https://github.com/jwodder/life/tree/master/crates/evolve> for more
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

    /// Set the time between each frame transition as an integer number of
    /// milliseconds
    #[arg(short, long, default_value = "500", value_name = "MILLISECONDS")]
    delay: NonZeroU32,

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

    /// Number of generations to compute, including the initial generation
    generations: NonZeroUsize,

    /// A file containing a Game of Life pattern.
    ///
    /// The file must either be in plaintext format with a `.cells` file
    /// extension or be in Run Length Encoded format with an `.rle` file
    /// extension.  Alternatively, `-` can be specified in order to read from
    /// standard input, in which case the format will be guessed based on
    /// initial content.
    infile: InputArg,

    /// Path at which to write the output image.
    outfile: OutputArg,
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
    let mut states = Vec::with_capacity(args.generations.get());
    for (i, p) in doc
        .pattern
        .with_edges(args.edges)
        .into_try_generations()
        .enumerate()
        .take(args.generations.get())
    {
        let p = p.with_context(|| format!("bounds error while computing generation {i}"))?;
        states.push(p);
    }
    states = sync_bounds(&states);
    let delay = Delay::from_numer_denom_ms(args.delay.get(), 1);
    let fp = BufWriter::new(
        args.outfile
            .create()
            .context("failed to open output file")?,
    );
    let mut enc = GifEncoder::new(fp);
    enc.set_repeat(Repeat::Infinite)
        .context("failed to set repeat")?;
    for p in states {
        let img = builder.render(&p).context("failed to render frame")?;
        let img = RgbaImage::from(DynamicImage::from(img));
        let frame = Frame::from_parts(img, 0, 0, delay);
        enc.encode_frame(frame).context("failed to encode frame")?;
    }
    Ok(())
}
