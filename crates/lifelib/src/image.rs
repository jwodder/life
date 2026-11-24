#![cfg(feature = "image")]
#![cfg_attr(docsrs, doc(cfg(feature = "image")))]
use crate::Pattern;
pub use image;
use image::{Rgb, RgbImage};
use std::num::NonZeroU32;
use thiserror::Error;

const WHITE: Rgb<u8> = Rgb([0xFF, 0xFF, 0xFF]);
const BLACK: Rgb<u8> = Rgb([0, 0, 0]);

#[derive(Copy, Clone, Debug, Eq, PartialEq)]
pub struct ImageBuilder {
    cell_size: NonZeroU32,
    live_color: Rgb<u8>,
    dead_color: Rgb<u8>,
    gutter: u32,
    gutter_color: Rgb<u8>,
    margin: u32,
    margin_color: Rgb<u8>,
}

impl ImageBuilder {
    pub fn new() -> ImageBuilder {
        let Some(cell_size) = NonZeroU32::new(1) else {
            unreachable!("1 should not be 0");
        };
        ImageBuilder {
            cell_size,
            live_color: BLACK,
            dead_color: WHITE,
            gutter: 0,
            gutter_color: WHITE,
            margin: 0,
            margin_color: WHITE,
        }
    }

    pub fn cell_size(mut self, size: NonZeroU32) -> Self {
        self.cell_size = size;
        self
    }

    pub fn live_color(mut self, color: Rgb<u8>) -> Self {
        self.live_color = color;
        self
    }

    pub fn dead_color(mut self, color: Rgb<u8>) -> Self {
        self.dead_color = color;
        self
    }

    pub fn gutter(mut self, gutter: u32) -> Self {
        self.gutter = gutter;
        self
    }

    pub fn gutter_color(mut self, color: Rgb<u8>) -> Self {
        self.gutter_color = color;
        self
    }

    pub fn margin(mut self, margin: u32) -> Self {
        self.margin = margin;
        self
    }

    pub fn margin_color(mut self, color: Rgb<u8>) -> Self {
        self.margin_color = color;
        self
    }

    /// # Errors
    ///
    /// Returns `Err(RenderError::TooLarge)` if the width or height of the
    /// image would exceed `u32::MAX`
    ///
    /// # Panics
    ///
    /// Panics when [`image::ImageBuffer::new()`] panics
    pub fn render(&self, life: &Pattern) -> Result<RgbImage, RenderError> {
        let cell_size = self.cell_size.get();
        let Ok(pat_width) = u32::try_from(life.width()) else {
            return Err(RenderError::TooLarge);
        };
        let Ok(pat_height) = u32::try_from(life.height()) else {
            return Err(RenderError::TooLarge);
        };
        let guttered_size = cell_size
            .checked_add(self.gutter)
            .ok_or(RenderError::TooLarge)?;
        let inner_width = guttered_size
            .checked_mul(pat_width)
            .and_then(|w| w.checked_sub(self.gutter))
            .ok_or(RenderError::TooLarge)?;
        let inner_height = guttered_size
            .checked_mul(pat_height)
            .and_then(|h| h.checked_sub(self.gutter))
            .ok_or(RenderError::TooLarge)?;
        let img_width = self
            .margin
            .checked_mul(2)
            .and_then(|m| m.checked_add(inner_width))
            .ok_or(RenderError::TooLarge)?;
        let img_height = self
            .margin
            .checked_mul(2)
            .and_then(|m| m.checked_add(inner_height))
            .ok_or(RenderError::TooLarge)?;
        let mut img = RgbImage::from_fn(img_width, img_height, |_, _| self.dead_color);
        let ul = life.upper_left();
        for c in life.iter_live() {
            let xstart = match u32::try_from(c.x.abs_diff(ul.x)) {
                Ok(x) => x * guttered_size + self.margin,
                _ => unreachable!("width fit in a u32, so x should too"),
            };
            let ystart = match u32::try_from(c.y.abs_diff(ul.y)) {
                Ok(y) => y * guttered_size + self.margin,
                _ => unreachable!("height fit in a u32, so y should too"),
            };
            for i in 0..cell_size {
                for j in 0..cell_size {
                    img.put_pixel(xstart + i, ystart + j, self.live_color);
                }
            }
        }
        if self.gutter > 0 && self.gutter_color != self.dead_color {
            for row in 1..pat_height {
                let offset = row * guttered_size - self.gutter;
                for y in offset..offset.saturating_add(self.gutter) {
                    for x in 0..inner_width {
                        img.put_pixel(x + self.margin, y + self.margin, self.gutter_color);
                    }
                }
            }
            for column in 1..pat_width {
                let offset = column * guttered_size - self.gutter;
                for x in offset..offset.saturating_add(self.gutter) {
                    for y in 0..inner_height {
                        img.put_pixel(x + self.margin, y + self.margin, self.gutter_color);
                    }
                }
            }
        }
        if self.margin > 0 && self.margin_color != self.dead_color {
            for y in 0..self.margin {
                for x in 0..img_width {
                    img.put_pixel(x, y, self.margin_color);
                    img.put_pixel(x, y + inner_height + self.margin, self.margin_color);
                }
            }
            for x in 0..self.margin {
                for y in 0..img_height {
                    img.put_pixel(x, y, self.margin_color);
                    img.put_pixel(x + inner_width + self.margin, y, self.margin_color);
                }
            }
        }
        Ok(img)
    }
}

impl Default for ImageBuilder {
    fn default() -> ImageBuilder {
        ImageBuilder::new()
    }
}

#[derive(Clone, Copy, Debug, Eq, Error, PartialEq)]
pub enum RenderError {
    #[error("image dimensions too large")]
    TooLarge,
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::PatternParser;
    use image::codecs::pnm::{PnmEncoder, PnmSubtype, SampleEncoding};
    use pretty_assertions::assert_eq;

    fn img2ppm(img: RgbImage) -> String {
        let mut buf = Vec::<u8>::new();
        let enc = PnmEncoder::new(&mut buf).with_subtype(PnmSubtype::Pixmap(SampleEncoding::Ascii));
        img.write_with_encoder(enc).unwrap();
        String::from_utf8(buf).unwrap()
    }

    #[test]
    fn size5() {
        let life = PatternParser::dead_chars(" .")
            .parse(".#.\n..#\n###\n")
            .unwrap();
        let painter = ImageBuilder::new().cell_size(NonZeroU32::new(5).unwrap());
        let img = painter.render(&life).unwrap();
        let imgdata = img2ppm(img);
        assert_eq!(
            imgdata,
            include_str!("testdata/size5.ppm").trim_end_matches('\n')
        );
    }

    #[test]
    fn live_color() {
        let life = PatternParser::dead_chars(" .")
            .parse(".#.\n..#\n###\n")
            .unwrap();
        let painter = ImageBuilder::new()
            .cell_size(NonZeroU32::new(5).unwrap())
            .live_color([0xFF, 0, 0].into());
        let img = painter.render(&life).unwrap();
        let imgdata = img2ppm(img);
        assert_eq!(
            imgdata,
            include_str!("testdata/live_color.ppm").trim_end_matches('\n')
        );
    }

    #[test]
    fn gutter() {
        let life = PatternParser::dead_chars(" .")
            .parse(".#.\n..#\n###\n")
            .unwrap();
        let painter = ImageBuilder::new()
            .cell_size(NonZeroU32::new(5).unwrap())
            .gutter(1);
        let img = painter.render(&life).unwrap();
        let imgdata = img2ppm(img);
        assert_eq!(
            imgdata,
            include_str!("testdata/gutter.ppm").trim_end_matches('\n')
        );
    }

    #[test]
    fn gutter_color() {
        let life = PatternParser::dead_chars(" .")
            .parse(".#.\n..#\n###\n")
            .unwrap();
        let painter = ImageBuilder::new()
            .cell_size(NonZeroU32::new(5).unwrap())
            .gutter(1)
            .gutter_color(Rgb([0xCC, 0xCC, 0xCC]));
        let img = painter.render(&life).unwrap();
        let imgdata = img2ppm(img);
        assert_eq!(
            imgdata,
            include_str!("testdata/gutter_color.ppm").trim_end_matches('\n')
        );
    }

    #[test]
    fn size25_gutter5() {
        let life = PatternParser::dead_chars(" .")
            .parse(".#.\n..#\n###\n")
            .unwrap();
        let painter = ImageBuilder::new()
            .cell_size(NonZeroU32::new(25).unwrap())
            .live_color(Rgb([0xFF, 0, 0]))
            .gutter(5)
            .gutter_color(Rgb([0xCC, 0xCC, 0xCC]));
        let img = painter.render(&life).unwrap();
        let imgdata = img2ppm(img);
        assert_eq!(
            imgdata,
            include_str!("testdata/size25_gutter5.ppm").trim_end_matches('\n')
        );
    }

    #[test]
    fn margin() {
        let life = PatternParser::dead_chars(" .")
            .parse(".#.\n..#\n###\n")
            .unwrap();
        let painter = ImageBuilder::new()
            .cell_size(NonZeroU32::new(5).unwrap())
            .margin(2)
            .margin_color(Rgb([0x60, 0xFF, 0x60]));
        let img = painter.render(&life).unwrap();
        let imgdata = img2ppm(img);
        assert_eq!(
            imgdata,
            include_str!("testdata/margin.ppm").trim_end_matches('\n')
        );
    }

    #[test]
    fn margin_gutter() {
        let life = PatternParser::dead_chars(" .")
            .parse(".#.\n..#\n###\n")
            .unwrap();
        let painter = ImageBuilder::new()
            .cell_size(NonZeroU32::new(5).unwrap())
            .margin(2)
            .margin_color(Rgb([0x60, 0xFF, 0x60]))
            .gutter(1)
            .gutter_color(Rgb([0xCC, 0xCC, 0xCC]));
        let img = painter.render(&life).unwrap();
        let imgdata = img2ppm(img);
        assert_eq!(
            imgdata,
            include_str!("testdata/margin_gutter.ppm").trim_end_matches('\n')
        );
    }

    #[test]
    fn dead_margin_gutter() {
        let life = PatternParser::dead_chars(" .")
            .parse(".#.\n..#\n###\n")
            .unwrap();
        let painter = ImageBuilder::new()
            .cell_size(NonZeroU32::new(5).unwrap())
            .dead_color(Rgb([0, 0xFF, 0xFF]))
            .margin(2)
            .gutter(1);
        let img = painter.render(&life).unwrap();
        let imgdata = img2ppm(img);
        assert_eq!(
            imgdata,
            include_str!("testdata/dead_margin_gutter.ppm").trim_end_matches('\n')
        );
    }
}
