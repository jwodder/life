mod tickset;
use crate::tickset::TickSet;
use anyhow::Context;
use clap::Parser;
use fs_err::File;
use lifelib::{
    formats::{Plaintext, Rle},
    image::{image::ImageFormat, ImageBuilder},
    Edges, Pattern,
};
use std::io::Write;
use std::num::NonZeroU32;
use std::path::PathBuf;

#[derive(Clone, Debug, Parser, PartialEq)]
struct Arguments {
    #[arg(short = 's', long, default_value = "5", value_name = "INT")]
    cell_size: NonZeroU32,

    #[arg(
        short = 'E',
        long,
        default_value_t,
        value_name = "dead|wrapx|wrapy|wrapxy"
    )]
    edges: Edges,

    #[arg(short, long, default_value_t = 0, value_name = "INT")]
    gutter: u32,

    #[arg(short = 'C', long, default_value = "#000000", value_name = "COLOR")]
    live_color: csscolorparser::Color,

    #[arg(short = 'N', long)]
    name: Option<String>,

    #[arg(short = 'n', long = "number", default_value = "1", value_name = "INTS")]
    ticks: TickSet,

    infile: PathBuf,

    outfile: PathBuf,
}

impl Arguments {
    fn save_pattern(&self, pattern: Pattern) -> anyhow::Result<()> {
        match self.outfile.extension().and_then(|s| s.to_str()) {
            Some("cells") => {
                let name = self.name.clone().unwrap_or_else(|| {
                    self.outfile.file_name().map_or_else(
                        || String::from("Pattern"),
                        |oss| oss.to_string_lossy().into_owned(),
                    )
                });
                let pt = Plaintext {
                    name,
                    comments: Vec::new(),
                    pattern,
                };
                let mut fp = File::create(&self.outfile)?;
                write!(fp, "{pt}")?;
            }
            Some("rle") => {
                let comments = if let Some(name) = self.name.clone() {
                    vec![('N', name)]
                } else {
                    Vec::new()
                };
                let rle = Rle { comments, pattern };
                let mut fp = File::create(&self.outfile)?;
                write!(fp, "{rle}")?;
            }
            _ if ImageFormat::from_path(&self.outfile).is_ok() => {
                let [r, g, b, _] = self.live_color.to_rgba8();
                let img = ImageBuilder::new(self.cell_size)
                    .live_color([r, g, b].into())
                    .gutter(self.gutter)
                    .pattern_to_image(&pattern);
                img.save(&self.outfile)
                    .context("failed to write image file")?;
            }
            _ => anyhow::bail!("output path does not have a supported file extension"),
        }
        Ok(())
    }
}

fn main() -> anyhow::Result<()> {
    let args = Arguments::parse();
    let maxtick = args.ticks.maxvalue();
    let pattern = Pattern::from_file(&args.infile)?.with_edges(args.edges);
    for (i, pat) in pattern
        .into_generations()
        .take(maxtick.saturating_add(1))
        .enumerate()
    {
        if args.ticks.contains(i) {
            args.save_pattern(pat)?;
        }
    }
    Ok(())
}
