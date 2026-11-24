[![Minimum Supported Rust Version](https://img.shields.io/badge/MSRV-1.91-orange)](https://www.rust-lang.org)
[![MIT License](https://img.shields.io/github/license/jwodder/life.svg)](https://opensource.org/licenses/MIT)

`pat2img` is a program for rendering a [Conway's Game of Life][] pattern as an
image.  Input patterns can be supplied in [plaintext][] or [Run Length
Encoded][] format.

[Conway's Game of Life]: https://en.wikipedia.org/wiki/Conway%27s_Game_of_Life
[plaintext]: https://conwaylife.com/wiki/Plaintext
[Run Length Encoded]: https://conwaylife.com/wiki/Run_Length_Encoded
[`image`]: https://github.com/image-rs/image

Usage
=====

    pat2img [<options>] <infile> <outfile>

`pat2img` reads a Game of Life pattern from `<infile>`, which must either be a
plaintext file with a "`.cells`" file extension or a Run Length Encoded file
with an "`.rle`" file extension.  Alternatively, `<infile>` can be `-` in order
to read from standard input, in which case the format will be guessed based on
initial content.

The image format of the output file is determined automatically based on
`<outfile>`'s file extension, which must be recognized & supported by Rust's
[`image`][] crate.

Options
-------

`COLOR` arguments can be specified as "`#rrggbb`" hex RGB strings (with or
without leading `#`) or as [CSS color names][].

- `-s INT`, `--cell-size INT` — Set the height & width of the cell squares to
  the given number of pixels [default: 5]

- `-g INT`, `--gutter INT` — Insert the given number of pixels as padding
  between adjacent cell squares [default: 0]

- `-G COLOR`, `--gutter-color COLOR` — Set the color of the gutter [default:
  `#FFFFFF`]

- `-C COLOR`, `--live-color COLOR` — Set the color of live cells [default:
  `#000000`]

- `-m INT`, `--margin INT` — Add a margin `INT` pixels thick around the image
  [default: 0]

- `-M COLOR`, `--margin-color COLOR` — Set the color of the margin [default:
  `#FFFFFF`]

[CSS color names]: https://www.w3.org/TR/css-color-4/#named-colors
