#![cfg(feature = "image")]
#![cfg_attr(docsrs, doc(cfg(feature = "image")))]
use crate::Pattern;
use crate::errors::RenderError;
pub use image;
use image::{Rgb, RgbImage};
use std::num::NonZeroU32;

#[derive(Copy, Clone, Debug, Eq, PartialEq)]
pub struct ImageBuilder {
    cell_size: NonZeroU32,
    live_color: Rgb<u8>,
    gutter: u32,
}

impl ImageBuilder {
    pub fn new() -> ImageBuilder {
        let Some(cell_size) = NonZeroU32::new(1) else {
            unreachable!("1 should not be 0");
        };
        ImageBuilder {
            cell_size,
            live_color: [0, 0, 0].into(),
            gutter: 0,
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

    pub fn gutter(mut self, gutter: u32) -> Self {
        self.gutter = gutter;
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
        let img_width = guttered_size
            .checked_mul(pat_width)
            .and_then(|w| w.checked_sub(self.gutter))
            .ok_or(RenderError::TooLarge)?;
        let img_height = guttered_size
            .checked_mul(pat_height)
            .and_then(|h| h.checked_sub(self.gutter))
            .ok_or(RenderError::TooLarge)?;
        let mut img = RgbImage::from_fn(img_width, img_height, |_, _| [0xFF, 0xFF, 0xFF].into());
        let ul = life.upper_left();
        for c in life.iter_live() {
            let xstart = match u32::try_from(c.x.abs_diff(ul.x)) {
                Ok(x) => x * guttered_size,
                _ => unreachable!("width fit in a u32, so x should too"),
            };
            let ystart = match u32::try_from(c.y.abs_diff(ul.y)) {
                Ok(y) => y * guttered_size,
                _ => unreachable!("height fit in a u32, so y should too"),
            };
            for i in 0..cell_size {
                for j in 0..cell_size {
                    img.put_pixel(xstart + i, ystart + j, self.live_color);
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
    fn test_image1() {
        let life = PatternParser::dead_chars(" .").parse(".#.\n..#\n###\n");
        let painter = ImageBuilder::new().cell_size(NonZeroU32::new(5).unwrap());
        let img = painter.render(&life).unwrap();
        let imgdata = img2ppm(img);
        assert_eq!(
            imgdata,
            include_str!("testdata/test_image1.ppm").trim_end_matches('\n')
        );
    }

    #[test]
    fn test_image_color() {
        let life = PatternParser::dead_chars(" .").parse(".#.\n..#\n###\n");
        let painter = ImageBuilder::new()
            .cell_size(NonZeroU32::new(5).unwrap())
            .live_color([0xFF, 0, 0].into());
        let img = painter.render(&life).unwrap();
        let imgdata = img2ppm(img);
        assert_eq!(
            imgdata,
            include_str!("testdata/test_image_color.ppm").trim_end_matches('\n')
        );
    }

    #[test]
    fn test_image_gutter() {
        let life = PatternParser::dead_chars(" .").parse(".#.\n..#\n###\n");
        let painter = ImageBuilder::new()
            .cell_size(NonZeroU32::new(5).unwrap())
            .gutter(1);
        let img = painter.render(&life).unwrap();
        let imgdata = img2ppm(img);
        assert_eq!(
            imgdata,
            include_str!("testdata/test_image_gutter.ppm").trim_end_matches('\n')
        );
    }
}
