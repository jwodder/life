#![cfg(test)]
use assert_cmd::cargo::cargo_bin_cmd;
use assert_fs::NamedTempFile;
use std::fs::read_to_string;
use std::path::Path;

static DATA_DIR: &str = concat!(env!("CARGO_MANIFEST_DIR"), "/tests/data");

fn assert_str_files_eq(file1: &Path, file2: &Path) {
    let str1 = read_to_string(file1).unwrap();
    let str2 = read_to_string(file2).unwrap();
    pretty_assertions::assert_eq!(str1, str2);
}

#[test]
fn cells_to_rle() {
    let outfile = NamedTempFile::new("glider.rle").unwrap();
    cargo_bin_cmd!("patformat")
        .arg(Path::new(DATA_DIR).join("glider.cells"))
        .arg(outfile.path())
        .assert()
        .success();
    assert_str_files_eq(&Path::new(DATA_DIR).join("glider.rle"), &outfile);
}

#[test]
fn rle_to_cells() {
    let outfile = NamedTempFile::new("glider.cells").unwrap();
    cargo_bin_cmd!("patformat")
        .arg(Path::new(DATA_DIR).join("glider.rle"))
        .arg(outfile.path())
        .assert()
        .success();
    assert_str_files_eq(&Path::new(DATA_DIR).join("glider.cells"), &outfile);
}

#[test]
fn unragged_cells() {
    let outfile = NamedTempFile::new("acorn.cells").unwrap();
    cargo_bin_cmd!("patformat")
        .arg(Path::new(DATA_DIR).join("acorn-ragged.cells"))
        .arg(outfile.path())
        .assert()
        .success();
    assert_str_files_eq(&Path::new(DATA_DIR).join("acorn-canon.cells"), &outfile);
}

#[test]
fn cells_with_rle_ext() {
    let outfile = NamedTempFile::new("glider.rle").unwrap();
    cargo_bin_cmd!("patformat")
        .arg("-f")
        .arg("Plaintext")
        .arg(Path::new(DATA_DIR).join("glider.cells"))
        .arg(outfile.path())
        .assert()
        .success();
    assert_str_files_eq(&Path::new(DATA_DIR).join("glider.cells"), &outfile);
}

#[test]
fn clear_comments_cells() {
    let outfile = NamedTempFile::new("glider.cells").unwrap();
    cargo_bin_cmd!("patformat")
        .arg("--clear-comments")
        .arg(Path::new(DATA_DIR).join("glider.cells"))
        .arg(outfile.path())
        .assert()
        .success();
    assert_str_files_eq(&Path::new(DATA_DIR).join("glider-clear.cells"), &outfile);
}

#[test]
fn clear_comments_rle() {
    let outfile = NamedTempFile::new("glider.rle").unwrap();
    cargo_bin_cmd!("patformat")
        .arg("--clear-comments")
        .arg(Path::new(DATA_DIR).join("glider-owner.rle"))
        .arg(outfile.path())
        .assert()
        .success();
    assert_str_files_eq(&Path::new(DATA_DIR).join("glider-clear.rle"), &outfile);
}

#[test]
fn rle_to_cells_lossy() {
    let outfile = NamedTempFile::new("glider.cells").unwrap();
    cargo_bin_cmd!("patformat")
        .arg(Path::new(DATA_DIR).join("glider-owner.rle"))
        .arg(outfile.path())
        .assert()
        .success();
    assert_str_files_eq(&Path::new(DATA_DIR).join("glider.cells"), &outfile);
}

#[test]
fn bad_ext_override() {
    let outfile = NamedTempFile::new("glider.other").unwrap();
    cargo_bin_cmd!("patformat")
        .arg("-f")
        .arg("cells")
        .arg(Path::new(DATA_DIR).join("glider.cells"))
        .arg(outfile.path())
        .assert()
        .success();
    assert_str_files_eq(&Path::new(DATA_DIR).join("glider.cells"), &outfile);
}

#[test]
fn no_ext_override() {
    let outfile = NamedTempFile::new("glider").unwrap();
    cargo_bin_cmd!("patformat")
        .arg("-f")
        .arg("rle")
        .arg(Path::new(DATA_DIR).join("glider.cells"))
        .arg(outfile.path())
        .assert()
        .success();
    assert_str_files_eq(&Path::new(DATA_DIR).join("glider.rle"), &outfile);
}

#[test]
fn add_comment_cells() {
    let outfile = NamedTempFile::new("glider.cells").unwrap();
    cargo_bin_cmd!("patformat")
        .arg("--comment=Goes nyoooom.")
        .arg(Path::new(DATA_DIR).join("glider.cells"))
        .arg(outfile.path())
        .assert()
        .success();
    assert_str_files_eq(&Path::new(DATA_DIR).join("glider-comment.cells"), &outfile);
}

#[test]
fn add_two_comments_cells() {
    let outfile = NamedTempFile::new("glider.cells").unwrap();
    cargo_bin_cmd!("patformat")
        .arg("--comment=Goes nyoooom.")
        .arg("--comment=(But only at one fourth the speed of light)")
        .arg(Path::new(DATA_DIR).join("glider.cells"))
        .arg(outfile.path())
        .assert()
        .success();
    assert_str_files_eq(&Path::new(DATA_DIR).join("glider-comment2.cells"), &outfile);
}

#[test]
fn add_comment_rle() {
    let outfile = NamedTempFile::new("glider.rle").unwrap();
    cargo_bin_cmd!("patformat")
        .arg("--comment=Goes nyoooom.")
        .arg(Path::new(DATA_DIR).join("glider-owner.rle"))
        .arg(outfile.path())
        .assert()
        .success();
    assert_str_files_eq(&Path::new(DATA_DIR).join("glider-comment.rle"), &outfile);
}

#[test]
fn add_two_comments_rle() {
    let outfile = NamedTempFile::new("glider.rle").unwrap();
    cargo_bin_cmd!("patformat")
        .arg("--comment=Goes nyoooom.")
        .arg("--comment=(But only at one fourth the speed of light)")
        .arg(Path::new(DATA_DIR).join("glider-owner.rle"))
        .arg(outfile.path())
        .assert()
        .success();
    assert_str_files_eq(&Path::new(DATA_DIR).join("glider-comment2.rle"), &outfile);
}

#[test]
fn add_rle_comment() {
    let outfile = NamedTempFile::new("glider.rle").unwrap();
    cargo_bin_cmd!("patformat")
        .arg("--rle-comment")
        .arg("#O Richard K. Guy, 1969")
        .arg(Path::new(DATA_DIR).join("glider.rle"))
        .arg(outfile.path())
        .assert()
        .success();
    assert_str_files_eq(
        &Path::new(DATA_DIR).join("glider-owner-canon.rle"),
        &outfile,
    );
}

#[test]
fn add_two_rle_comments() {
    let outfile = NamedTempFile::new("glider.rle").unwrap();
    cargo_bin_cmd!("patformat")
        .arg("--rle-comment")
        .arg("#O Richard K. Guy, 1969")
        .arg("--rle-comment")
        .arg("#A What's this line for?")
        .arg(Path::new(DATA_DIR).join("glider.rle"))
        .arg(outfile.path())
        .assert()
        .success();
    assert_str_files_eq(&Path::new(DATA_DIR).join("glider-oa.rle"), &outfile);
}

#[test]
fn add_rle_comment_to_cells() {
    let outfile = NamedTempFile::new("glider.cells").unwrap();
    cargo_bin_cmd!("patformat")
        .arg("--rle-comment")
        .arg("#O Richard K. Guy, 1969")
        .arg(Path::new(DATA_DIR).join("glider.rle"))
        .arg(outfile.path())
        .assert()
        .success();
    assert_str_files_eq(&Path::new(DATA_DIR).join("glider.cells"), &outfile);
}

#[test]
fn add_comment_and_rle_comment() {
    let outfile = NamedTempFile::new("glider.rle").unwrap();
    cargo_bin_cmd!("patformat")
        .arg("--rle-comment")
        .arg("#O Richard K. Guy, 1969")
        .arg("-cGoes nyoooom.")
        .arg(Path::new(DATA_DIR).join("glider.rle"))
        .arg(outfile.path())
        .assert()
        .success();
    assert_str_files_eq(&Path::new(DATA_DIR).join("glider-comment.rle"), &outfile);
}

#[test]
fn stdout() {
    cargo_bin_cmd!("patformat")
        .arg(Path::new(DATA_DIR).join("glider.rle"))
        .assert()
        .success()
        .stdout(include_str!("data/glider.cells"));
}

#[test]
fn stdout_rle() {
    cargo_bin_cmd!("patformat")
        .arg("-frle")
        .arg(Path::new(DATA_DIR).join("glider.rle"))
        .assert()
        .success()
        .stdout(include_str!("data/glider.rle"));
}

#[test]
fn set_name_cells() {
    let outfile = NamedTempFile::new("glider.cells").unwrap();
    cargo_bin_cmd!("patformat")
        .arg("-NFeatherweight spaceship")
        .arg(Path::new(DATA_DIR).join("glider.cells"))
        .arg(outfile.path())
        .assert()
        .success();
    assert_str_files_eq(&Path::new(DATA_DIR).join("glider-altname.cells"), &outfile);
}

#[test]
fn set_name_rle() {
    let outfile = NamedTempFile::new("glider.rle").unwrap();
    cargo_bin_cmd!("patformat")
        .arg("-NFeatherweight spaceship")
        .arg(Path::new(DATA_DIR).join("glider.rle"))
        .arg(outfile.path())
        .assert()
        .success();
    assert_str_files_eq(&Path::new(DATA_DIR).join("glider-altname.rle"), &outfile);
}

#[test]
fn clear_set_name_cells() {
    let outfile = NamedTempFile::new("glider.cells").unwrap();
    cargo_bin_cmd!("patformat")
        .arg("--clear-comments")
        .arg("-NFeatherweight spaceship")
        .arg(Path::new(DATA_DIR).join("glider.cells"))
        .arg(outfile.path())
        .assert()
        .success();
    assert_str_files_eq(
        &Path::new(DATA_DIR).join("glider-just-altname.cells"),
        &outfile,
    );
}

#[test]
fn clear_set_name_rle() {
    let outfile = NamedTempFile::new("glider.rle").unwrap();
    cargo_bin_cmd!("patformat")
        .arg("--clear-comments")
        .arg("-NFeatherweight spaceship")
        .arg(Path::new(DATA_DIR).join("glider.rle"))
        .arg(outfile.path())
        .assert()
        .success();
    assert_str_files_eq(
        &Path::new(DATA_DIR).join("glider-just-altname.rle"),
        &outfile,
    );
}

#[test]
fn replace_metadata_cells() {
    let outfile = NamedTempFile::new("glider.cells").unwrap();
    cargo_bin_cmd!("patformat")
        .arg("--clear-comments")
        .arg("-NFeatherweight spaceship")
        .arg("--comment=Moves diagonally at speed c/4")
        .arg("-RO Not John Conway")
        .arg(Path::new(DATA_DIR).join("glider.cells"))
        .arg(outfile.path())
        .assert()
        .success();
    assert_str_files_eq(&Path::new(DATA_DIR).join("glider-altdata.cells"), &outfile);
}

#[test]
fn replace_metadata_rle() {
    let outfile = NamedTempFile::new("glider.rle").unwrap();
    cargo_bin_cmd!("patformat")
        .arg("--clear-comments")
        .arg("-NFeatherweight spaceship")
        .arg("--comment=Moves diagonally at speed c/4")
        .arg("-RO Not John Conway")
        .arg(Path::new(DATA_DIR).join("glider.rle"))
        .arg(outfile.path())
        .assert()
        .success();
    assert_str_files_eq(&Path::new(DATA_DIR).join("glider-altdata.rle"), &outfile);
}

#[test]
fn create_metadata_cells() {
    let outfile = NamedTempFile::new("glider.cells").unwrap();
    cargo_bin_cmd!("patformat")
        .arg("-NFeatherweight spaceship")
        .arg("--comment=Moves diagonally at speed c/4")
        .arg("-RO Not John Conway")
        .arg(Path::new(DATA_DIR).join("glider-clear.cells"))
        .arg(outfile.path())
        .assert()
        .success();
    assert_str_files_eq(&Path::new(DATA_DIR).join("glider-altdata.cells"), &outfile);
}

#[test]
fn create_metadata_rle() {
    let outfile = NamedTempFile::new("glider.rle").unwrap();
    cargo_bin_cmd!("patformat")
        .arg("-NFeatherweight spaceship")
        .arg("--comment=Moves diagonally at speed c/4")
        .arg("-RO Not John Conway")
        .arg(Path::new(DATA_DIR).join("glider-clear.rle"))
        .arg(outfile.path())
        .assert()
        .success();
    assert_str_files_eq(&Path::new(DATA_DIR).join("glider-altdata.rle"), &outfile);
}

#[test]
fn unset_name_cells() {
    let outfile = NamedTempFile::new("glider.cells").unwrap();
    cargo_bin_cmd!("patformat")
        .arg("--clear-comments")
        .arg("--comment=Moves diagonally at speed c/4")
        .arg(Path::new(DATA_DIR).join("glider.cells"))
        .arg(outfile.path())
        .assert()
        .success();
    assert_str_files_eq(&Path::new(DATA_DIR).join("glider-noname.cells"), &outfile);
}

#[test]
fn unset_name_rle() {
    let outfile = NamedTempFile::new("glider.rle").unwrap();
    cargo_bin_cmd!("patformat")
        .arg("--clear-comments")
        .arg("--comment=Moves diagonally at speed c/4")
        .arg(Path::new(DATA_DIR).join("glider-owner.rle"))
        .arg(outfile.path())
        .assert()
        .success();
    assert_str_files_eq(&Path::new(DATA_DIR).join("glider-noname.rle"), &outfile);
}
