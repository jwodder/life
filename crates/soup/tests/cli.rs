use assert_cmd::cargo::cargo_bin_cmd;
use assert_fs::NamedTempFile;
use lifelib::formats::{Letter, Plaintext, Rle};

#[test]
fn five_by_seven_stdout() {
    let out = String::from_utf8(cargo_bin_cmd!("soup").arg("5x7").ok().unwrap().stdout).unwrap();
    let pt = out.parse::<Plaintext>().unwrap();
    assert!(pt.name.is_none());
    assert!(pt.comments.is_empty());
    assert_eq!(pt.pattern.width(), 5);
    assert_eq!(pt.pattern.height(), 7);
}

#[test]
fn five_by_seven_cells() {
    let outfile = NamedTempFile::new("broth.cells").unwrap();
    cargo_bin_cmd!("soup")
        .arg("5x7")
        .arg(outfile.path())
        .assert()
        .success()
        .stdout("");
    let pt = std::fs::read_to_string(outfile)
        .unwrap()
        .parse::<Plaintext>()
        .unwrap();
    assert!(pt.name.is_none());
    assert!(pt.comments.is_empty());
    assert_eq!(pt.pattern.width(), 5);
    assert_eq!(pt.pattern.height(), 7);
}

#[test]
fn five_by_seven_rle() {
    let outfile = NamedTempFile::new("broth.rle").unwrap();
    cargo_bin_cmd!("soup")
        .arg("5x7")
        .arg(outfile.path())
        .assert()
        .success()
        .stdout("");
    let rle = std::fs::read_to_string(outfile)
        .unwrap()
        .parse::<Rle>()
        .unwrap();
    assert!(rle.comments.is_empty());
    assert_eq!(rle.pattern.width(), 5);
    assert_eq!(rle.pattern.height(), 7);
}

#[test]
fn named_commented_cells() {
    let outfile = NamedTempFile::new("broth.cells").unwrap();
    cargo_bin_cmd!("soup")
        .arg("-NBroth")
        .arg("-c")
        .arg("%d does nothing!")
        .arg("5x7")
        .arg(outfile.path())
        .assert()
        .success()
        .stdout("");
    let pt = std::fs::read_to_string(outfile)
        .unwrap()
        .parse::<Plaintext>()
        .unwrap();
    assert_eq!(pt.name.as_deref(), Some("Broth"));
    assert_eq!(pt.comments, ["%d does nothing!"]);
    assert_eq!(pt.pattern.width(), 5);
    assert_eq!(pt.pattern.height(), 7);
}

#[test]
fn named_commented_rle() {
    let outfile = NamedTempFile::new("broth.rle").unwrap();
    cargo_bin_cmd!("soup")
        .arg("-NBroth")
        .arg("-R")
        .arg("#O soup")
        .arg("-c")
        .arg("%d does nothing!")
        .arg("5x7")
        .arg(outfile.path())
        .assert()
        .success()
        .stdout("");
    let pt = std::fs::read_to_string(outfile)
        .unwrap()
        .parse::<Rle>()
        .unwrap();
    assert_eq!(
        pt.comments
            .iter()
            .map(|(ty, text)| (*ty, text.as_ref()))
            .collect::<Vec<(Letter, &str)>>(),
        [
            (Letter::NAME_TYPE, "Broth"),
            (Letter::COMMENT_TYPE, "%d does nothing!"),
            (Letter::OWNER_TYPE, "soup"),
        ]
    );
    assert_eq!(pt.pattern.width(), 5);
    assert_eq!(pt.pattern.height(), 7);
}
