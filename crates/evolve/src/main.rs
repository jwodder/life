use anyhow::Context;
use clap::Parser;
use cmdutils::{DocumentExt, Painter, io_exit};
use lifelib::{
    Document, Edges,
    image::image::{
        Delay, DynamicImage, Frame, RgbaImage,
        codecs::gif::{GifEncoder, Repeat},
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
struct Command {
    #[command(flatten)]
    painter: Painter,

    /// Set the time between each frame transition as an integer number of
    /// hundredths of a second
    #[arg(short, long, default_value = "50", value_name = "TIME")]
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

impl Command {
    fn run(self) -> anyhow::Result<()> {
        let builder = self.painter.build();
        let doc = Document::load_from_input(self.infile)?;
        let mut states = Vec::with_capacity(self.generations.get());
        for (i, p) in doc
            .pattern
            .with_edges(self.edges)
            .into_try_generations()
            .enumerate()
            .take(self.generations.get())
        {
            let p = p.with_context(|| format!("bounds error while computing generation {i}"))?;
            states.push(p);
        }
        states = sync_bounds(&states).context("failed to synchronize bounds")?;
        let Some(msdelay) = self.delay.get().checked_mul(10) else {
            anyhow::bail!("numeric overflow while computing frame delay");
        };
        let delay = Delay::from_numer_denom_ms(msdelay, 1);
        let fp = BufWriter::new(
            self.outfile
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
}

fn main() -> std::process::ExitCode {
    io_exit(Command::parse().run())
}
