mod scanner;
mod tickset;
mod ticktemplate;
use crate::tickset::TickSet;
use crate::ticktemplate::TickTemplate;
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
use std::path::{Path, PathBuf};

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
    name: Option<TickTemplate>,

    #[arg(short = 'n', long = "number", default_value = "1", value_name = "INTS")]
    ticks: TickSet,

    infile: PathBuf,

    outfile: TickTemplate,
}

impl Arguments {
    fn saver(&mut self) -> anyhow::Result<Saver> {
        match self.outfile.extension() {
            Some("cells") => Ok(Saver::Plaintext {
                name: self.name.take(),
            }),
            Some("rle") => Ok(Saver::Rle {
                name: self.name.take(),
            }),
            Some(ext) if ImageFormat::from_extension(ext).is_some() => {
                let [r, g, b, _] = self.live_color.to_rgba8();
                let builder = ImageBuilder::new(self.cell_size)
                    .live_color([r, g, b].into())
                    .gutter(self.gutter);
                Ok(Saver::Image { builder })
            }
            _ => anyhow::bail!("output path does not have a supported file extension"),
        }
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
enum Saver {
    Plaintext { name: Option<TickTemplate> },
    Rle { name: Option<TickTemplate> },
    Image { builder: ImageBuilder },
}

impl Saver {
    fn save(&self, pattern: Pattern, path: &Path, index: usize) -> anyhow::Result<()> {
        match self {
            Saver::Plaintext { name } => {
                let name = if let Some(tmplt) = name {
                    tmplt.render(index)
                } else {
                    path.file_name().map_or_else(
                        || String::from("Pattern"),
                        |oss| oss.to_string_lossy().into_owned(),
                    )
                };
                let pt = Plaintext {
                    name,
                    comments: Vec::new(),
                    pattern,
                };
                let mut fp = File::create(path)?;
                write!(fp, "{pt}")?;
            }
            Saver::Rle { name } => {
                let comments = if let Some(tmplt) = name {
                    vec![('N', tmplt.render(index))]
                } else {
                    Vec::new()
                };
                let rle = Rle { comments, pattern };
                let mut fp = File::create(path)?;
                write!(fp, "{rle}")?;
            }
            Saver::Image { builder } => builder
                .pattern_to_image(&pattern)
                .save(path)
                .context("failed to write image file")?,
        }
        Ok(())
    }
}

fn main() -> anyhow::Result<()> {
    let mut args = Arguments::parse();
    let saver = args.saver()?;
    let maxtick = args.ticks.maxvalue();
    let pattern = Pattern::from_file(&args.infile)?.with_edges(args.edges);
    for (i, pat) in pattern
        .into_generations()
        .take(maxtick.saturating_add(1))
        .enumerate()
    {
        if args.ticks.contains(i) {
            let outfile = PathBuf::from(args.outfile.render(i));
            saver.save(pat, &outfile, i)?;
        }
    }
    Ok(())
}
