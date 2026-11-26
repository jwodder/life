use clap::Args;
use lifelib::image::ImageBuilder;
use std::num::NonZeroU32;

#[derive(Args, Clone, Debug, PartialEq)]
pub struct Painter {
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
}

impl Painter {
    pub fn build(&self) -> ImageBuilder {
        let [r, g, b, _] = self.live_color.to_rgba8();
        let [dr, dg, db, _] = self.dead_color.to_rgba8();
        let mut builder = ImageBuilder::new()
            .cell_size(self.cell_size)
            .live_color([r, g, b].into())
            .dead_color([dr, dg, db].into())
            .gutter(self.gutter)
            .margin(self.margin);
        if let Some(c) = self.gutter_color {
            let [r, g, b, _] = c.to_rgba8();
            builder = builder.gutter_color([r, g, b].into());
        }
        if let Some(c) = self.margin_color {
            let [r, g, b, _] = c.to_rgba8();
            builder = builder.margin_color([r, g, b].into());
        }
        builder
    }
}
