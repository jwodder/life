#![cfg(test)]
use assert_cmd::Command;
use assert_fs::{assert::PathAssert, NamedTempFile, TempDir};
use predicates::path::eq_file;
use rstest::rstest;
use std::fs::{read_dir, read_to_string};
use std::path::Path;

static DATA_DIR: &str = concat!(env!("CARGO_MANIFEST_DIR"), "/tests/data");

fn assert_str_files_eq(file1: &Path, file2: &Path) {
    let str1 = read_to_string(file1).unwrap();
    let str2 = read_to_string(file2).unwrap();
    pretty_assertions::assert_eq!(str1, str2);
}

mod default_number {
    use super::*;

    #[test]
    fn cells() {
        let outfile = NamedTempFile::new("glider1.cells").unwrap();
        Command::cargo_bin("tick")
            .unwrap()
            .arg(Path::new(DATA_DIR).join("glider.cells"))
            .arg(outfile.path())
            .assert()
            .success();
        assert_str_files_eq(&Path::new(DATA_DIR).join("glider1.cells"), &outfile);
    }

    #[test]
    fn rle() {
        let outfile = NamedTempFile::new("glider1.rle").unwrap();
        Command::cargo_bin("tick")
            .unwrap()
            .arg(Path::new(DATA_DIR).join("glider.cells"))
            .arg(outfile.path())
            .assert()
            .success();
        assert_str_files_eq(&Path::new(DATA_DIR).join("glider1.rle"), &outfile);
    }

    #[test]
    fn png() {
        let outfile = NamedTempFile::new("glider1.png").unwrap();
        Command::cargo_bin("tick")
            .unwrap()
            .arg(Path::new(DATA_DIR).join("glider.cells"))
            .arg(outfile.path())
            .assert()
            .success();
        outfile.assert(eq_file(Path::new(DATA_DIR).join("glider1.png")));
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
    Command::cargo_bin("tick")
        .unwrap()
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
    Command::cargo_bin("tick")
        .unwrap()
        .arg("-n0")
        .arg(Path::new(DATA_DIR).join("glider.cells"))
        .arg(outfile.path())
        .assert()
        .success();
    outfile.assert(eq_file(Path::new(DATA_DIR).join("glider.png")));
}

#[test]
fn rle2plaintext() {
    let outfile = NamedTempFile::new("glider.cells").unwrap();
    Command::cargo_bin("tick")
        .unwrap()
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
        Command::cargo_bin("tick")
            .unwrap()
            .arg("--live-color")
            .arg("red")
            .arg(Path::new(DATA_DIR).join("glider.cells"))
            .arg(outfile.path())
            .assert()
            .success();
        outfile.assert(eq_file(Path::new(DATA_DIR).join("glider1-red.png")));
    }

    #[test]
    fn gutter() {
        let outfile = NamedTempFile::new("glider.png").unwrap();
        Command::cargo_bin("tick")
            .unwrap()
            .arg("--gutter")
            .arg("1")
            .arg(Path::new(DATA_DIR).join("glider.cells"))
            .arg(outfile.path())
            .assert()
            .success();
        outfile.assert(eq_file(Path::new(DATA_DIR).join("glider1-g1.png")));
    }

    #[test]
    fn cell_size() {
        let outfile = NamedTempFile::new("glider.png").unwrap();
        Command::cargo_bin("tick")
            .unwrap()
            .arg("--cell-size")
            .arg("10")
            .arg(Path::new(DATA_DIR).join("glider.cells"))
            .arg(outfile.path())
            .assert()
            .success();
        outfile.assert(eq_file(Path::new(DATA_DIR).join("glider1-s10.png")));
    }

    #[test]
    fn cell_size_gutter() {
        let outfile = NamedTempFile::new("glider.png").unwrap();
        Command::cargo_bin("tick")
            .unwrap()
            .arg("--cell-size")
            .arg("10")
            .arg("--gutter")
            .arg("2")
            .arg(Path::new(DATA_DIR).join("glider.cells"))
            .arg(outfile.path())
            .assert()
            .success();
        outfile.assert(eq_file(Path::new(DATA_DIR).join("glider1-s10-g2.png")));
    }
}

mod name {
    use super::*;

    #[test]
    fn cells() {
        let outfile = NamedTempFile::new("glider1.cells").unwrap();
        Command::cargo_bin("tick")
            .unwrap()
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
        Command::cargo_bin("tick")
            .unwrap()
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
    Command::cargo_bin("tick")
        .unwrap()
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
    Command::cargo_bin("tick")
        .unwrap()
        .arg("-n")
        .arg("2-4")
        .arg("--name=Glider + %d")
        .arg(Path::new(DATA_DIR).join("glider.cells"))
        .arg(tmpdir.path().join("glider-%d-named.cells"))
        .assert()
        .success();
    let mut filenames = Vec::new();
    let diriter = read_dir(tmpdir.path()).unwrap();
    for entry in diriter {
        let entry = entry.unwrap();
        filenames.push(entry.file_name().into_string().unwrap());
    }
    filenames.sort_unstable();
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
