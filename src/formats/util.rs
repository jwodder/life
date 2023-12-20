use std::iter::FusedIterator;

/// Divides a string in two before the first character that does not satisfy
/// the given predicate.  If the first part is nonempty, the parts are
/// returned.  Otherwise, `None` is returned.
///
/// Note that the first part is the maximal leading substring of `s` whose
/// characters all satisfy `predicate`.
pub(super) fn scan_some<P: FnMut(char) -> bool>(s: &str, mut predicate: P) -> Option<(&str, &str)> {
    let boundary = s
        .char_indices()
        .find(move |&(_, ch)| !predicate(ch))
        .map_or(s.len(), |(i, _)| i);
    (boundary > 0).then(|| s.split_at(boundary))
}

/// If `s` contains a LF, CR, or CR LF sequence, return the portion of `s`
/// before the first such sequence and the remainder after the sequence.
pub(super) fn split_at_newline(s: &str) -> Option<(&str, &str)> {
    let start = s.find(['\n', '\r'])?;
    let end = {
        if s.get(start..(start + 2)) == Some("\r\n") {
            start + 2
        } else {
            start + 1
        }
    };
    Some((&s[..start], &s[end..]))
}

/// Like [`str::lines()`], except that a lone CR is also recognized as a line
/// ending and the empty string is broken into one empty line.
pub(super) fn ascii_lines(s: &str) -> AsciiLines<'_> {
    AsciiLines::new(s)
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(super) struct AsciiLines<'a> {
    s: &'a str,
    first: bool,
}

impl<'a> AsciiLines<'a> {
    fn new(s: &'a str) -> AsciiLines<'a> {
        AsciiLines { s, first: true }
    }
}

impl<'a> Iterator for AsciiLines<'a> {
    type Item = &'a str;

    fn next(&mut self) -> Option<&'a str> {
        if let Some((line, s)) = split_at_newline(self.s) {
            self.s = s;
            self.first = false;
            Some(line)
        } else if !self.s.is_empty() || self.first {
            self.first = false;
            Some(std::mem::take(&mut self.s))
        } else {
            None
        }
    }
}

impl FusedIterator for AsciiLines<'_> {}

#[cfg(test)]
mod tests {
    use super::*;

    mod scan_some {
        use super::*;

        #[test]
        fn half() {
            assert_eq!(
                scan_some("123abc", |c| c.is_ascii_digit()),
                Some(("123", "abc"))
            );
        }

        #[test]
        fn all() {
            assert_eq!(
                scan_some("123456", |c| c.is_ascii_digit()),
                Some(("123456", ""))
            );
        }

        #[test]
        fn none() {
            assert_eq!(scan_some("abc123", |c| c.is_ascii_digit()), None);
        }
    }

    mod ascii_lines {
        use super::*;
        use rstest::rstest;

        #[test]
        fn empty() {
            let mut iter = ascii_lines("");
            assert_eq!(iter.next(), Some(""));
            assert_eq!(iter.next(), None);
            assert_eq!(iter.next(), None);
        }

        #[test]
        fn no_newline() {
            let mut iter = ascii_lines("foobar");
            assert_eq!(iter.next(), Some("foobar"));
            assert_eq!(iter.next(), None);
            assert_eq!(iter.next(), None);
        }

        #[rstest]
        #[case("\n")]
        #[case("\r")]
        #[case("\r\n")]
        fn newline_only(#[case] s: &str) {
            let mut iter = ascii_lines(s);
            assert_eq!(iter.next(), Some(""));
            assert_eq!(iter.next(), None);
            assert_eq!(iter.next(), None);
        }

        #[rstest]
        #[case("foo\n")]
        #[case("foo\r")]
        #[case("foo\r\n")]
        fn text_newline(#[case] s: &str) {
            let mut iter = ascii_lines(s);
            assert_eq!(iter.next(), Some("foo"));
            assert_eq!(iter.next(), None);
            assert_eq!(iter.next(), None);
        }

        #[rstest]
        #[case("\nfoo")]
        #[case("\rfoo")]
        #[case("\r\nfoo")]
        fn newline_text(#[case] s: &str) {
            let mut iter = ascii_lines(s);
            assert_eq!(iter.next(), Some(""));
            assert_eq!(iter.next(), Some("foo"));
            assert_eq!(iter.next(), None);
            assert_eq!(iter.next(), None);
        }

        #[rstest]
        #[case("foo\nbar")]
        #[case("foo\rbar")]
        #[case("foo\r\nbar")]
        fn text_newline_text(#[case] s: &str) {
            let mut iter = ascii_lines(s);
            assert_eq!(iter.next(), Some("foo"));
            assert_eq!(iter.next(), Some("bar"));
            assert_eq!(iter.next(), None);
            assert_eq!(iter.next(), None);
        }

        #[rstest]
        #[case("foo“\n”bar")]
        #[case("foo“\r”bar")]
        #[case("foo“\r\n”bar")]
        fn unicode_newline_unicode(#[case] s: &str) {
            let mut iter = ascii_lines(s);
            assert_eq!(iter.next(), Some("foo“"));
            assert_eq!(iter.next(), Some("”bar"));
            assert_eq!(iter.next(), None);
            assert_eq!(iter.next(), None);
        }

        #[rstest]
        #[case("\n\n")]
        #[case("\r\r")]
        #[case("\r\n\r\n")]
        #[case("\n\r")]
        fn two_newlines(#[case] s: &str) {
            let mut iter = ascii_lines(s);
            assert_eq!(iter.next(), Some(""));
            assert_eq!(iter.next(), Some(""));
            assert_eq!(iter.next(), None);
            assert_eq!(iter.next(), None);
        }

        #[rstest]
        #[case("foo\n\nbar")]
        #[case("foo\r\rbar")]
        #[case("foo\r\n\r\nbar")]
        #[case("foo\n\rbar")]
        fn text_two_newlines_text(#[case] s: &str) {
            let mut iter = ascii_lines(s);
            assert_eq!(iter.next(), Some("foo"));
            assert_eq!(iter.next(), Some(""));
            assert_eq!(iter.next(), Some("bar"));
            assert_eq!(iter.next(), None);
            assert_eq!(iter.next(), None);
        }

        #[rstest]
        #[case("foo\nbar\n")]
        #[case("foo\rbar\r")]
        #[case("foo\r\nbar\r\n")]
        fn text_two_newline_text_newline(#[case] s: &str) {
            let mut iter = ascii_lines(s);
            assert_eq!(iter.next(), Some("foo"));
            assert_eq!(iter.next(), Some("bar"));
            assert_eq!(iter.next(), None);
            assert_eq!(iter.next(), None);
        }
    }
}
