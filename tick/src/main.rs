use anyhow::Context;
use clap::Parser;
use fs_err::File;
use lifelib::{
    formats::{Plaintext, Rle},
    image::{image::ImageFormat, ImageBuilder},
    Pattern,
};
use std::io::Write;
use std::num::NonZeroU32;
use std::path::PathBuf;

#[derive(Clone, Debug, Eq, Parser, PartialEq)]
struct Arguments {
    #[arg(long, default_value = "5")]
    cell_size: NonZeroU32,

    #[arg(long, default_value_t = 0)]
    gutter: u32,

    #[arg(short = 'N', long)]
    name: Option<String>,

    #[arg(short, long, default_value_t = 1)]
    number: usize,

    infile: PathBuf,

    outfile: PathBuf,
}

impl Arguments {
    fn save_pattern(self, pattern: Pattern) -> anyhow::Result<()> {
        match self.outfile.extension().and_then(|s| s.to_str()) {
            Some("cells") => {
                let name = self.name.unwrap_or_else(|| {
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
                let mut fp = File::create(self.outfile)?;
                write!(fp, "{pt}")?;
            }
            Some("rle") => {
                let comments = if let Some(name) = self.name {
                    vec![('N', name)]
                } else {
                    Vec::new()
                };
                let rle = Rle { comments, pattern };
                let mut fp = File::create(self.outfile)?;
                write!(fp, "{rle}")?;
            }
            _ if ImageFormat::from_path(&self.outfile).is_ok() => {
                let img = ImageBuilder::new(self.cell_size)
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
    let mut pattern = Pattern::from_file(&args.infile)?;
    for _ in 0..args.number {
        pattern = pattern.step();
    }
    args.save_pattern(pattern)?;
    Ok(())
}
