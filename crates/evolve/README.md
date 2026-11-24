[![Minimum Supported Rust Version](https://img.shields.io/badge/MSRV-1.91-orange)](https://www.rust-lang.org)
[![MIT License](https://img.shields.io/github/license/jwodder/life.svg)](https://opensource.org/licenses/MIT)

`evolve` is a program for generating an animated GIF of a pattern and its
succeeding generations in [Conway's Game of Life][].

[Conway's Game of Life]: https://en.wikipedia.org/wiki/Conway%27s_Game_of_Life
[plaintext]: https://conwaylife.com/wiki/Plaintext
[Run Length Encoded]: https://conwaylife.com/wiki/Run_Length_Encoded

Usage
=====

    evolve [<options>] <generations> <infile> <outfile>

`evolve` reads a Game of Life pattern from `<infile>`, which must either be a
[plaintext][] file with a "`.cells`" file extension or a [Run Length Encoded][]
file with an "`.rle`" file extension.  Alternatively, `<infile>` can be `-` in
order to read from standard input, in which case the format will be guessed
based on initial content.  The input pattern is then advanced by
`<generations>` minus 1 ticks, and all computed generations, preceded by the
initial pattern, are rendered as frames of an animated GIF that is written to
`<outfile>`.

Patterns are placed on a [bounded grid][] with the same dimensions as the
pattern read from `<infile>`.  By default, a [finite plane][] (in which all
cells outside the grid are dead and cannot come to life) is used, but the
`-E`/`--edges` option can be used to either wrap or automatically grow the grid
along the x- and/or y-axis instead.

[bounded grid]: https://conwaylife.com/wiki/Bounded_grids
[finite plane]: https://conwaylife.com/wiki/Finite_plane

Options
-------

`COLOR` arguments can be specified as "`#rrggbb`" hex RGB strings (with or
without leading `#`) or as [CSS color names][].

- `-s INT`, `--cell-size INT` — Set the height & width of the cell squares to
  the given number of pixels [default: 5]

- `-D COLOR`, `--dead-color COLOR` — Set the color of dead cells [default:
  `#FFFFFF`]

- `-d MS`, `--delay MS` — Set the time between each frame transition as an
  integer number of milliseconds

- `-E VALUE`, `--edges VALUE` — Configure the behavior of the edges of the
  pattern's universe.  The allowed values (case insensitive) are:

    - `dead` *(default)*: Cells beyond the universe's bounds are dead and
      cannot come to life

    - `wrapx`: The universe's x-axis wraps around so that the left edge is
      connected to the right edge

    - `wrapy`: The universe's y-axis wraps around so that the top edge is
      connected to the bottom edge

    - `wrapxy`: The universe's x- and y-axes both wrap around

    - `growx`: The universe's x-axis will be extended to the left or right as
      necessary in order to accomodate new live cells

    - `growy`: The universe's y-axis will be extended to the top or bottom as
      necessary in order to accomodate new live cells

    - `growxy`: The universe's x- and y-axes will both be extended as necessary

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
