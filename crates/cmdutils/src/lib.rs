#[cfg(feature = "painter")]
mod painter;
#[cfg(feature = "painter")]
pub use crate::painter::Painter;

use anyhow::Context;
use lifelib::{Document, FormatChoice, formats::Format};
use patharg::{InputArg, OutputArg};
use std::io::Write;

pub trait DocumentExt: Sized {
    fn load_from_input(infile: InputArg) -> anyhow::Result<Self>;
    fn dump_to_output(&self, outfile: OutputArg) -> anyhow::Result<()>;
}

impl DocumentExt for Document {
    fn load_from_input(infile: InputArg) -> anyhow::Result<Self> {
        match infile {
            stdin @ InputArg::Stdin => {
                let docstr = stdin
                    .read_to_string()
                    .context("failed to read pattern from standard input")?;
                Document::load_from_str(&docstr, FormatChoice::Autodetect)
                    .context("failed to parse input pattern")
            }
            InputArg::Path(p) => Document::load_from_file(&p, FormatChoice::Autodetect)
                .with_context(|| format!("failed to read pattern from {}", p.display())),
        }
    }

    fn dump_to_output(&self, outfile: OutputArg) -> anyhow::Result<()> {
        let format = match outfile {
            OutputArg::Stdout => Format::Plaintext,
            OutputArg::Path(ref p) => Format::identify(p).ok_or_else(|| {
                anyhow::Error::msg("output path does not have a supported file extension")
            })?,
        };
        let mut fp = outfile.create().context("failed to open output file")?;
        write!(&mut fp, "{}", self.display(format)).context("failed to write to output file")?;
        fp.flush().context("failed to write to output file")?;
        Ok(())
    }
}
