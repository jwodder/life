#![cfg(feature = "image")]
#![cfg_attr(docsrs, doc(cfg(feature = "image")))]
use super::Pattern;
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
    pub fn new(cell_size: NonZeroU32) -> ImageBuilder {
        ImageBuilder {
            cell_size,
            live_color: [0, 0, 0].into(),
            gutter: 0,
        }
    }

    pub fn live_color(mut self, color: Rgb<u8>) -> Self {
        self.live_color = color;
        self
    }

    pub fn gutter(mut self, gutter: u32) -> Self {
        self.gutter = gutter;
        self
    }

    /// # Panics
    ///
    /// Panics if the image width or image height does not fit in a `u32`, or
    /// when [`image::ImageBuffer::new()`] panics.
    pub fn render(&self, life: &Pattern) -> RgbImage {
        let cell_size = self.cell_size.get();
        let pat_width = u32::try_from(life.width()).expect("Pattern width should fit in a u32");
        let pat_height = u32::try_from(life.height()).expect("Pattern height should fit in a u32");
        let guttered_size = cell_size
            .checked_add(self.gutter)
            .expect("cell_size + gutter should not overflow");
        let img_width = guttered_size
            .checked_mul(pat_width)
            .and_then(|w| w.checked_sub(self.gutter))
            .expect("image size should not overflow u32");
        let img_height = guttered_size
            .checked_mul(pat_height)
            .and_then(|h| h.checked_sub(self.gutter))
            .expect("image size should not overflow u32");
        let mut img = RgbImage::from_fn(img_width, img_height, |_, _| [0xFF, 0xFF, 0xFF].into());
        for (y, x) in life.iter_live() {
            let xstart = match u32::try_from(x) {
                Ok(x) => x * guttered_size,
                _ => unreachable!("width fit in a u32, so x should too"),
            };
            let ystart = match u32::try_from(y) {
                Ok(y) => y * guttered_size,
                _ => unreachable!("height fit in a u32, so y should too"),
            };
            for i in 0..cell_size {
                for j in 0..cell_size {
                    img.put_pixel(xstart + i, ystart + j, self.live_color);
                }
            }
        }
        img
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
        let painter = ImageBuilder::new(NonZeroU32::new(5).unwrap());
        let img = painter.render(&life);
        let imgdata = img2ppm(img);
        assert_eq!(
            imgdata,
            include_str!("testdata/test_image1.ppm").trim_end_matches('\n')
        );
    }

    #[test]
    fn test_image_color() {
        let life = PatternParser::dead_chars(" .").parse(".#.\n..#\n###\n");
        let painter =
            ImageBuilder::new(NonZeroU32::new(5).unwrap()).live_color([0xFF, 0, 0].into());
        let img = painter.render(&life);
        let imgdata = img2ppm(img);
        assert_eq!(
            imgdata,
            include_str!("testdata/test_image_color.ppm").trim_end_matches('\n')
        );
    }

    #[test]
    fn test_image_gutter() {
        let life = PatternParser::dead_chars(" .").parse(".#.\n..#\n###\n");
        let painter = ImageBuilder::new(NonZeroU32::new(5).unwrap()).gutter(1);
        let img = painter.render(&life);
        let imgdata = img2ppm(img);
        assert_eq!(
            imgdata,
            include_str!("testdata/test_image_gutter.ppm").trim_end_matches('\n')
        );
    }
}
