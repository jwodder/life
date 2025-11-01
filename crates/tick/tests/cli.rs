#![cfg(test)]
use assert_cmd::cargo::cargo_bin_cmd;
use assert_fs::{NamedTempFile, TempDir};
use lifelib::image::image::{ImageFormat, ImageReader};
use rstest::rstest;
use std::fs::{read_dir, read_to_string, File};
use std::io::BufReader;
use std::path::Path;

static DATA_DIR: &str = concat!(env!("CARGO_MANIFEST_DIR"), "/tests/data");

fn assert_str_files_eq(file1: &Path, file2: &Path) {
    let str1 = read_to_string(file1).unwrap();
    let str2 = read_to_string(file2).unwrap();
    pretty_assertions::assert_eq!(str1, str2);
}

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

fn listdir(dirpath: &Path) -> Vec<String> {
    let mut filenames = Vec::new();
    let diriter = read_dir(dirpath).unwrap();
    for entry in diriter {
        let entry = entry.unwrap();
        filenames.push(entry.file_name().into_string().unwrap());
    }
    filenames.sort_unstable();
    filenames
}

mod default_number {
    use super::*;

    #[test]
    fn cells() {
        let outfile = NamedTempFile::new("glider1.cells").unwrap();
        cargo_bin_cmd!("tick")
            .arg(Path::new(DATA_DIR).join("glider.cells"))
            .arg(outfile.path())
            .assert()
            .success();
        assert_str_files_eq(&Path::new(DATA_DIR).join("glider1.cells"), &outfile);
    }

    #[test]
    fn rle() {
        let outfile = NamedTempFile::new("glider1.rle").unwrap();
        cargo_bin_cmd!("tick")
            .arg(Path::new(DATA_DIR).join("glider.cells"))
            .arg(outfile.path())
            .assert()
            .success();
        assert_str_files_eq(&Path::new(DATA_DIR).join("glider1.rle"), &outfile);
    }

    #[test]
    fn png() {
        let outfile = NamedTempFile::new("glider1.png").unwrap();
        cargo_bin_cmd!("tick")
            .arg(Path::new(DATA_DIR).join("glider.cells"))
            .arg(outfile.path())
            .assert()
            .success();
        assert_png_files_eq(&Path::new(DATA_DIR).join("glider1.png"), &outfile);
    }
}

#[rstest]
#[case(0, "glider.cells")]
#[case(0, "glider.rle")]
#[case(1, "glider1.cells")]
#[case(1, "glider1.rle")]
#[case(2, "glider2.cells")]
#[case(2, "glider2.rle")]
#[case(3, "glider3.cells")]
#[case(3, "glider3.rle")]
#[case(4, "glider4.cells")]
#[case(4, "glider4.rle")]
#[case(11, "glider11.cells")]
#[case(11, "glider11.rle")]
fn numbers(#[case] number: usize, #[case] filename: &str) {
    let outfile = NamedTempFile::new(filename).unwrap();
    cargo_bin_cmd!("tick")
        .arg(format!("-n{number}"))
        .arg(Path::new(DATA_DIR).join("glider.cells"))
        .arg(outfile.path())
        .assert()
        .success();
    assert_str_files_eq(&Path::new(DATA_DIR).join(filename), &outfile);
}

#[test]
fn number0_png() {
    let outfile = NamedTempFile::new("glider.png").unwrap();
    cargo_bin_cmd!("tick")
        .arg("-n0")
        .arg(Path::new(DATA_DIR).join("glider.cells"))
        .arg(outfile.path())
        .assert()
        .success();
    assert_png_files_eq(&Path::new(DATA_DIR).join("glider.png"), &outfile);
}

#[test]
fn rle2plaintext() {
    let outfile = NamedTempFile::new("glider.cells").unwrap();
    cargo_bin_cmd!("tick")
        .arg("-n0")
        .arg(Path::new(DATA_DIR).join("glider.rle"))
        .arg(outfile.path())
        .assert()
        .success();
    assert_str_files_eq(&Path::new(DATA_DIR).join("glider.cells"), &outfile);
}

mod imgopts {
    use super::*;

    #[test]
    fn live_color() {
        let outfile = NamedTempFile::new("glider.png").unwrap();
        cargo_bin_cmd!("tick")
            .arg("--live-color")
            .arg("red")
            .arg(Path::new(DATA_DIR).join("glider.cells"))
            .arg(outfile.path())
            .assert()
            .success();
        assert_png_files_eq(&Path::new(DATA_DIR).join("glider1-red.png"), &outfile);
    }

    #[test]
    fn gutter() {
        let outfile = NamedTempFile::new("glider.png").unwrap();
        cargo_bin_cmd!("tick")
            .arg("--gutter")
            .arg("1")
            .arg(Path::new(DATA_DIR).join("glider.cells"))
            .arg(outfile.path())
            .assert()
            .success();
        assert_png_files_eq(&Path::new(DATA_DIR).join("glider1-g1.png"), &outfile);
    }

    #[test]
    fn cell_size() {
        let outfile = NamedTempFile::new("glider.png").unwrap();
        cargo_bin_cmd!("tick")
            .arg("--cell-size")
            .arg("10")
            .arg(Path::new(DATA_DIR).join("glider.cells"))
            .arg(outfile.path())
            .assert()
            .success();
        assert_png_files_eq(&Path::new(DATA_DIR).join("glider1-s10.png"), &outfile);
    }

    #[test]
    fn cell_size_gutter() {
        let outfile = NamedTempFile::new("glider.png").unwrap();
        cargo_bin_cmd!("tick")
            .arg("--cell-size")
            .arg("10")
            .arg("--gutter")
            .arg("2")
            .arg(Path::new(DATA_DIR).join("glider.cells"))
            .arg(outfile.path())
            .assert()
            .success();
        assert_png_files_eq(&Path::new(DATA_DIR).join("glider1-s10-g2.png"), &outfile);
    }
}

mod name {
    use super::*;

    #[test]
    fn cells() {
        let outfile = NamedTempFile::new("glider1.cells").unwrap();
        cargo_bin_cmd!("tick")
            .arg("--name")
            .arg("Glider + 1")
            .arg(Path::new(DATA_DIR).join("glider.cells"))
            .arg(outfile.path())
            .assert()
            .success();
        assert_str_files_eq(&Path::new(DATA_DIR).join("glider1-named.cells"), &outfile);
    }

    #[test]
    fn rle() {
        let outfile = NamedTempFile::new("glider1.rle").unwrap();
        cargo_bin_cmd!("tick")
            .arg("--name")
            .arg("Glider + 1")
            .arg(Path::new(DATA_DIR).join("glider.cells"))
            .arg(outfile.path())
            .assert()
            .success();
        assert_str_files_eq(&Path::new(DATA_DIR).join("glider1-named.rle"), &outfile);
    }
}

#[rstest]
#[case(10, "dead", "glider10.rle")]
#[case(11, "dead", "glider11.rle")]
#[case(12, "dead", "glider11.rle")]
#[case(28, "dead", "glider11.rle")]
#[case(10, "wrapx", "glider10.rle")]
#[case(11, "wrapx", "glider11.rle")]
#[case(12, "wrapx", "glider11.rle")]
#[case(28, "wrapx", "glider11.rle")]
#[case(12, "wrapy", "glider12-wrapy.rle")]
#[case(13, "wrapy", "glider13-wrapy.rle")]
#[case(14, "wrapy", "glider13-wrapy.rle")]
#[case(28, "wrapy", "glider13-wrapy.rle")]
#[case(10, "wrapxy", "glider10-wrapxy.rle")]
#[case(11, "wrapxy", "glider11-wrapxy.rle")]
#[case(12, "wrapxy", "glider12-wrapxy.rle")]
#[case(13, "wrapxy", "glider13-wrapxy.rle")]
#[case(14, "wrapxy", "glider14-wrapxy.rle")]
#[case(28, "wrapxy", "glider.rle")]
fn edges_opt(#[case] number: usize, #[case] edges: &str, #[case] filename: &str) {
    let outfile = NamedTempFile::new("outfile.rle").unwrap();
    cargo_bin_cmd!("tick")
        .arg(format!("-n{number}"))
        .arg("--edges")
        .arg(edges)
        .arg(Path::new(DATA_DIR).join("glider.cells"))
        .arg(outfile.path())
        .assert()
        .success();
    assert_str_files_eq(&Path::new(DATA_DIR).join(filename), &outfile);
}

#[test]
fn multiticks() {
    let tmpdir = TempDir::new().unwrap();
    cargo_bin_cmd!("tick")
        .arg("-n")
        .arg("2-4")
        .arg("--name=Glider + %d")
        .arg(Path::new(DATA_DIR).join("glider.cells"))
        .arg(tmpdir.path().join("glider-%d-named.cells"))
        .assert()
        .success();
    let filenames = listdir(tmpdir.path());
    assert_eq!(
        filenames,
        [
            "glider-2-named.cells",
            "glider-3-named.cells",
            "glider-4-named.cells"
        ]
    );
    for fname in filenames {
        assert_str_files_eq(
            &Path::new(DATA_DIR).join(&fname),
            &tmpdir.path().join(fname),
        );
    }
}

#[test]
fn multiticks_no_output_placeholder() {
    let tmpdir = TempDir::new().unwrap();
    cargo_bin_cmd!("tick")
        .arg("-n")
        .arg("2-4")
        .arg("--name=Glider + %d")
        .arg(Path::new(DATA_DIR).join("glider.cells"))
        .arg(tmpdir.path().join("glider.cells"))
        .assert()
        .success()
        .stderr("tick: warning: multiple tick numbers selected but no placeholders included in output path\n");
    let filenames = listdir(tmpdir.path());
    assert_eq!(filenames, ["glider.cells"]);
    assert_str_files_eq(
        &Path::new(DATA_DIR).join("glider-4-named.cells"),
        &tmpdir.path().join("glider.cells"),
    );
}

#[test]
fn create_dir() {
    let tmpdir = TempDir::new().unwrap();
    cargo_bin_cmd!("tick")
        .arg("--name")
        .arg("Glider + 1")
        .arg(Path::new(DATA_DIR).join("glider.cells"))
        .arg(tmpdir.path().join("glider").join("%d.cells"))
        .assert()
        .success();
    let filenames = listdir(tmpdir.path());
    assert_eq!(filenames, ["glider"]);
    let gliders = listdir(&tmpdir.path().join("glider"));
    assert_eq!(gliders, ["1.cells"]);
    assert_str_files_eq(
        &Path::new(DATA_DIR).join("glider1-named.cells"),
        &tmpdir.path().join("glider").join("1.cells"),
    );
}

#[test]
fn create_dirs() {
    let tmpdir = TempDir::new().unwrap();
    cargo_bin_cmd!("tick")
        .arg("--name")
        .arg("Glider + 1")
        .arg(Path::new(DATA_DIR).join("glider.cells"))
        .arg(
            tmpdir
                .path()
                .join("glider")
                .join("plaintext")
                .join("%d.cells"),
        )
        .assert()
        .success();
    assert_eq!(listdir(tmpdir.path()), ["glider"]);
    assert_eq!(listdir(&tmpdir.path().join("glider")), ["plaintext"]);
    assert_eq!(
        listdir(&tmpdir.path().join("glider").join("plaintext")),
        ["1.cells"]
    );
    assert_str_files_eq(
        &Path::new(DATA_DIR).join("glider1-named.cells"),
        &tmpdir
            .path()
            .join("glider")
            .join("plaintext")
            .join("1.cells"),
    );
}
