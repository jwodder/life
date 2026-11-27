[![Minimum Supported Rust Version](https://img.shields.io/badge/MSRV-1.91-orange)](https://www.rust-lang.org)
[![MIT License](https://img.shields.io/github/license/jwodder/life.svg)](https://opensource.org/licenses/MIT)

`patformat` is a program for converting [Conway's Game of Life][] pattern files
between file formats and/or adding & removing comments from such files.  It can
also be used to "canonicalize" a file (e.g., making all lines in a plaintext
drawing the same length) by "converting" a file in one format to the same
format.

[Conway's Game of Life]: https://en.wikipedia.org/wiki/Conway%27s_Game_of_Life
[plaintext]: https://conwaylife.com/wiki/Plaintext
[Run Length Encoded]: https://conwaylife.com/wiki/Run_Length_Encoded

Usage
=====

    patformat [<options>] [<infile> [<outfile>]]

`patformat` reads a Game of Life pattern from `<infile>`, which must either be a
[plaintext][] file with a "`.cells`" file extension or a [Run Length Encoded][]
file with an "`.rle`" file extension.  Alternatively, `<infile>` can be `-` or
omitted in order to read from standard input, in which case the format will be
guessed based on initial content.

If `--clear-comments` is specified, any & all comments (for plaintext files) or
hash lines (for RLE files) are removed from the document.

If `--name` is specified, the pattern name recorded in an initial `!Name:`
comment (for plaintext files) or `#N` hash line (for RLE files) is set to the
given value.

If `--comment` and/or `--rle-comment` is specified, comment lines or (for RLE
output files only) arbitrary hash lines are added to the comments or hash lines
still in the document.

The resulting comments/hash lines and pattern are written to `<outfile>`.  If
`--format` is specified, the output will be in the given format, regardless of
`<outfile>`'s file extension.  If it is not specified, then `<outfile>`'s file
extension must be `.cells` (to produce a plaintext file) or `.rle` (to produce
an RLE file).  If `<outfile>` is `-` or omitted, the output is written to
standard output (as plaintext if `--format` is not specified).

Options
-------

- `-C`, `--clear-comments` — Remove all comments and hash lines from the input file

- `-c TEXT`, `--comment TEXT` — Add the comment `TEXT` to the output file.
  `TEXT` may not contain newlines.  This option may be specified multiple
  times.

- `-f FORMAT`, `--format FORMAT` — Set the output file format.  `FORMAT` must
  be "`plaintext`", "`cells`" (an alias of "`plaintext`"), or "`rle`", all
  case-insensitive.  If `--format` is not specified, the output format will be
  determined from the output path's file extension, or plaintext when writing
  to stdout.

- `-N TEXT`, `--name TEXT` — Set the pattern name to embed in the output file.
  `TEXT` may not contain newlines.

- `-R "LETTER TEXT"`, `--rle-comment "LETTER TEXT"` — Add the hash line with
  the given type letter and text to an RLE output file.  The argument must
  consist of an optional '#', an ASCII letter, a space, and then text; you will
  likely have to quote the entire string to protect it from your shell.  `TEXT`
  may not contain newlines.  This option may be specified multiple times.
