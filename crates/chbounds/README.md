[![Minimum Supported Rust Version](https://img.shields.io/badge/MSRV-1.91-orange)](https://www.rust-lang.org)
[![MIT License](https://img.shields.io/github/license/jwodder/life.svg)](https://opensource.org/licenses/MIT)

`chbounds` is a program for adjusting the dimensions of [Conway's Game of
Life][] patterns by adding (*padding*) and/or removing (*cropping*) rows &
columns along the edges.

[Conway's Game of Life]: https://en.wikipedia.org/wiki/Conway%27s_Game_of_Life
[plaintext]: https://conwaylife.com/wiki/Plaintext
[Run Length Encoded]: https://conwaylife.com/wiki/Run_Length_Encoded
[bounding box]: https://conwaylife.com/wiki/Bounding_box

Usage
=====

    chbounds [<options>] [<infile> [<outfile>]]

`chbounds` reads a Game of Life pattern from `<infile>`, which must either be a
[plaintext][] file with a "`.cells`" file extension or a [Run Length Encoded][]
file with an "`.rle`" file extension.  Alternatively, `<infile>` can be `-` or
omitted in order to read from standard input, in which case the format will be
guessed based on initial content.

The input pattern is then cropped and/or padded as described by the options
passed to the command.  If `--minimize` was specified, the pattern is first
cropped down to its [bounding box][].  Then, if any other options were
specified, edges are added and/or removed accordingly.  Passing a positive
number as an option argument causes that many rows or columns of dead cells to
be added to the pattern, while a negative number causes the number's absolute
value of rows or columns to be removed from the edges of the pattern.

The resulting pattern is written to `<outfile>`, the file extension of which
must be either "`.cells`" (to produce a plaintext file) or "`.rle`" (to
produce a Run Length Encoded file).  Alternatively, `<outfile>` may be `-`
or omitted to write plaintext to standard output.

Options
-------

- `--bottom INT` — Add/remove `INT` rows to/from the bottom of the pattern.
  This overrides any bottom padding amounts set by `--uniform` or `--vertical`.

- `--horizontal INT` — Add/remove `INT` columns to/from the left and right
  sides of the pattern.  This overrides any horizontal padding amounts set by
  `--uniform`.

- `--left INT` — Add/remove `INT` columns to/from the left side of the pattern.
  This overrides any left padding amounts set by `--uniform` or `--horizontal`.

- `--minimize` — Crop the pattern to its bounding box.  This effect is applied
  before all other options.

- `--right INT` — Add/remove `INT` columns to/from the right side of the
  pattern.  This overrides any right padding amounts set by `--uniform` or
  `--horizontal`.

- `--top INT` — Add/remove `INT` rows to/from the top of the pattern.  This
  overrides any top padding amounts set by `--uniform` or `--vertical`.

- `--uniform INT` — Add/remove `INT` cells on all fours sides of the pattern

- `--vertical INT` — Add/remove `INT` columns to/from the top and bottom of the
  pattern This overrides any vertical padding amounts set by `--uniform`.
