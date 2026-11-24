#![cfg(test)]
use assert_cmd::cargo::cargo_bin_cmd;
use assert_fs::NamedTempFile;
use lifelib::image::image::{ImageFormat, ImageReader};
use std::fs::File;
use std::io::BufReader;
use std::path::Path;

static DATA_DIR: &str = concat!(env!("CARGO_MANIFEST_DIR"), "/tests/data");

fn assert_png_files_eq(file1: &Path, file2: &Path) {
    let img1 =
        ImageReader::with_format(BufReader::new(File::open(file1).unwrap()), ImageFormat::Png)
            .decode()
            .unwrap();
    let img2 =
        ImageReader::with_format(BufReader::new(File::open(file2).unwrap()), ImageFormat::Png)
            .decode()
            .unwrap();
    assert_eq!(img1, img2);
}

#[test]
fn defaults() {
    let outfile = NamedTempFile::new("glider.png").unwrap();
    cargo_bin_cmd!("pat2img")
        .arg(Path::new(DATA_DIR).join("glider.cells"))
        .arg(outfile.path())
        .assert()
        .success();
    assert_png_files_eq(&Path::new(DATA_DIR).join("defaults.png"), &outfile);
}

#[test]
fn live_color() {
    let outfile = NamedTempFile::new("glider.png").unwrap();
    cargo_bin_cmd!("pat2img")
        .arg("--live-color")
        .arg("red")
        .arg(Path::new(DATA_DIR).join("glider.cells"))
        .arg(outfile.path())
        .assert()
        .success();
    assert_png_files_eq(&Path::new(DATA_DIR).join("live_color.png"), &outfile);
}

#[test]
fn gutter() {
    let outfile = NamedTempFile::new("glider.png").unwrap();
    cargo_bin_cmd!("pat2img")
        .arg("--gutter")
        .arg("1")
        .arg(Path::new(DATA_DIR).join("glider.cells"))
        .arg(outfile.path())
        .assert()
        .success();
    assert_png_files_eq(&Path::new(DATA_DIR).join("gutter.png"), &outfile);
}

#[test]
fn gutter_color() {
    let outfile = NamedTempFile::new("glider.png").unwrap();
    cargo_bin_cmd!("pat2img")
        .arg("--gutter")
        .arg("1")
        .arg("--gutter-color=CCCCCC")
        .arg(Path::new(DATA_DIR).join("glider.cells"))
        .arg(outfile.path())
        .assert()
        .success();
    assert_png_files_eq(&Path::new(DATA_DIR).join("gutter_color.png"), &outfile);
}

#[test]
fn size10() {
    let outfile = NamedTempFile::new("glider.png").unwrap();
    cargo_bin_cmd!("pat2img")
        .arg("--cell-size")
        .arg("10")
        .arg(Path::new(DATA_DIR).join("glider.cells"))
        .arg(outfile.path())
        .assert()
        .success();
    assert_png_files_eq(&Path::new(DATA_DIR).join("size10.png"), &outfile);
}

#[test]
fn size10_gutter2() {
    let outfile = NamedTempFile::new("glider.png").unwrap();
    cargo_bin_cmd!("pat2img")
        .arg("--cell-size")
        .arg("10")
        .arg("--gutter")
        .arg("2")
        .arg(Path::new(DATA_DIR).join("glider.cells"))
        .arg(outfile.path())
        .assert()
        .success();
    assert_png_files_eq(&Path::new(DATA_DIR).join("size10_gutter2.png"), &outfile);
}

#[test]
fn margin() {
    let outfile = NamedTempFile::new("glider.png").unwrap();
    cargo_bin_cmd!("pat2img")
        .arg("--margin")
        .arg("2")
        .arg("--margin-color=60FF60")
        .arg(Path::new(DATA_DIR).join("glider.cells"))
        .arg(outfile.path())
        .assert()
        .success();
    assert_png_files_eq(&Path::new(DATA_DIR).join("margin.png"), &outfile);
}
