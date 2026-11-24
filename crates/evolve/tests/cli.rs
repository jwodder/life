#![cfg(test)]
use assert_cmd::cargo::cargo_bin_cmd;
use assert_fs::NamedTempFile;
use itertools::{EitherOrBoth, Itertools};
use lifelib::image::image::{AnimationDecoder, codecs::gif::GifDecoder, metadata::LoopCount};
use std::fs::File;
use std::io::BufReader;
use std::path::Path;

static DATA_DIR: &str = concat!(env!("CARGO_MANIFEST_DIR"), "/tests/data");

fn assert_gif_files_eq(file1: &Path, file2: &Path) {
    let fp1 = BufReader::new(File::open(file1).unwrap());
    let dec1 = GifDecoder::new(fp1).unwrap();
    let fp2 = BufReader::new(File::open(file2).unwrap());
    let dec2 = GifDecoder::new(fp2).unwrap();
    match (dec1.loop_count(), dec2.loop_count()) {
        (LoopCount::Infinite, LoopCount::Infinite) => (),
        (LoopCount::Finite(n1), LoopCount::Finite(n2)) => assert_eq!(n1, n2),
        (LoopCount::Finite(_), LoopCount::Infinite) => {
            panic!("file1 doesn't loop infinitely but file2 does")
        }
        (LoopCount::Infinite, LoopCount::Finite(_)) => {
            panic!("file2 doesn't loop infinitely but file1 does")
        }
    }
    for item in dec1.into_frames().zip_longest(dec2.into_frames()) {
        match item {
            EitherOrBoth::Both(f1, f2) => {
                let f1 = f1.unwrap();
                let f2 = f2.unwrap();
                assert_eq!(f1.buffer(), f2.buffer());
                assert_eq!(f1.delay(), f2.delay());
            }
            EitherOrBoth::Left(_) => panic!("file1 has more frames than file2"),
            EitherOrBoth::Right(_) => panic!("file2 has more frames than file1"),
        }
    }
}

#[test]
fn defaults15() {
    let outfile = NamedTempFile::new("glider.gif").unwrap();
    cargo_bin_cmd!("evolve")
        .arg("15")
        .arg(Path::new(DATA_DIR).join("glider.cells"))
        .arg(outfile.path())
        .assert()
        .success();
    assert_gif_files_eq(&Path::new(DATA_DIR).join("glider-15.gif"), &outfile);
}

#[test]
fn wrap30() {
    let outfile = NamedTempFile::new("glider.gif").unwrap();
    cargo_bin_cmd!("evolve")
        .arg("--edges=wrapxy")
        .arg("30")
        .arg(Path::new(DATA_DIR).join("glider.cells"))
        .arg(outfile.path())
        .assert()
        .success();
    assert_gif_files_eq(&Path::new(DATA_DIR).join("glider-30-wrapxy.gif"), &outfile);
}

#[test]
fn grow30() {
    let outfile = NamedTempFile::new("glider.gif").unwrap();
    cargo_bin_cmd!("evolve")
        .arg("--edges=growxy")
        .arg("30")
        .arg(Path::new(DATA_DIR).join("glider.cells"))
        .arg(outfile.path())
        .assert()
        .success();
    assert_gif_files_eq(&Path::new(DATA_DIR).join("glider-30-growxy.gif"), &outfile);
}

#[test]
fn grow30_styled() {
    let outfile = NamedTempFile::new("glider.gif").unwrap();
    cargo_bin_cmd!("evolve")
        .arg("--edges=growxy")
        .arg("-s10")
        .arg("--gutter=2")
        .arg("--gutter-color=CCCCCC")
        .arg("-C")
        .arg("red")
        .arg("30")
        .arg(Path::new(DATA_DIR).join("glider.cells"))
        .arg(outfile.path())
        .assert()
        .success();
    assert_gif_files_eq(
        &Path::new(DATA_DIR).join("glider-30-growxy-styled.gif"),
        &outfile,
    );
}

#[test]
fn margin() {
    let outfile = NamedTempFile::new("glider.gif").unwrap();
    cargo_bin_cmd!("evolve")
        .arg("--edges=wrapxy")
        .arg("-m2")
        .arg("-M60FF60")
        .arg("28")
        .arg(Path::new(DATA_DIR).join("glider.cells"))
        .arg(outfile.path())
        .assert()
        .success();
    assert_gif_files_eq(&Path::new(DATA_DIR).join("margin.gif"), &outfile);
}

#[test]
fn all_colors() {
    let outfile = NamedTempFile::new("glider.gif").unwrap();
    cargo_bin_cmd!("evolve")
        .arg("--edges=wrapxy")
        .arg("-m2")
        .arg("-M60FF60")
        .arg("-g1")
        .arg("-Gcccccc")
        .arg("-Cred")
        .arg("-D00FFFF")
        .arg("28")
        .arg(Path::new(DATA_DIR).join("glider.cells"))
        .arg(outfile.path())
        .assert()
        .success();
    assert_gif_files_eq(&Path::new(DATA_DIR).join("all_colors.gif"), &outfile);
}
