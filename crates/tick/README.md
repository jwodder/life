[![Minimum Supported Rust Version](https://img.shields.io/badge/MSRV-1.81-orange)](https://www.rust-lang.org)
[![MIT License](https://img.shields.io/github/license/jwodder/life.svg)](https://opensource.org/licenses/MIT)

`tick` is a program for advancing a pattern in [Conway's Game of Life][].  An
input pattern is read from a [plaintext][] or [Run Length Encoded][] file, and
the resulting pattern after some number of ticks is written out in plaintext or
RLE or as an image.

[Conway's Game of Life]: https://en.wikipedia.org/wiki/Conway%27s_Game_of_Life
[plaintext]: https://conwaylife.com/wiki/Plaintext
[Run Length Encoded]: https://conwaylife.com/wiki/Run_Length_Encoded
[`image`]: https://github.com/image-rs/image

Usage
=====

    tick [<options>] <infile> <outfile>

`tick` reads a Game of Life pattern from `<infile>`, which must either be a
plaintext file with a "`.cells`" file extension or a Run Length Encoded file
with an "`.rle`" file extension.  The pattern is advanced by a number of ticks
given by the `-n`/`--number` option [default: 1], and the result is written to
`<outfile>`.  The file extension of the output path must be "`.cells`" (to
produce a plaintext file), "`.rle`" (to produce a Run Length Encoded file), or
an image file extension supported by the [`image`][] crate (to produce an
image).

Patterns are placed on a [bounded grid][] with the same dimensions as the
pattern read from `<infile>`.  By default, a [finite plane][] (in which all
cells outside the grid are dead and cannot come to life) is used, but the
`-E`/`--edges` option can be used to wrap the grid along the x- and/or y-axis
instead.

[bounded grid]: https://conwaylife.com/wiki/Bounded_grids
[finite plane]: https://conwaylife.com/wiki/Finite_plane

Multiple steps of the input pattern can be produced at once by passing the
`-n`/`--number` option comma-separated tick numbers and/or number ranges.  For
example:

- `-n 1,5,10` — Output the input pattern after 1, 5, and 10 ticks
- `-n 0-4` — Output the input pattern after 0, 1, 2, 3, and 4 ticks
- `-n 1-3,5` — Output the input pattern after 1, 2, 3, and 5 ticks (skipping 4)

When outputting multiple steps, a [tick placeholder](#tick-placeholders) should
be included in the output path in order to write the steps to separate files;
otherwise, the outputs will overwrite each other, and only the last step will
be saved at the end.

Options
-------

- `-E <VALUE>`, `--edges <VALUE>` — Configure the behavior of the edges of the
  pattern's universe.  The allowed values (case insensitive) are:

    - `dead` *(default)*: Cells beyond the universe's bounds are dead and
      cannot come to life

    - `wrapx`: The universe's x-axis wraps around so that the left edge is
      connected to the right edge

    - `wrapy`: The universe's y-axis wraps around so that the top edge is
      connected to the bottom edge

    - `wrapxy`: The universe's x- and y-axes both wrap around

- `-n <NUMBERS>`, `--number <NUMBERS>` — Specify the number(s) of ticks to
  advance the input pattern by in order to produce the output.  `<NUMBERS>`
  consists of one or more nonnegative integers and/or hyphenated inclusive
  ranges of nonnegative integers, all separated by commas.  If multiple tick
  numbers are specified, multiple outputs are produced, one for each specified
  tick number in the input pattern's history.  [default: 1]

The following option only has an effect when outputting to a plaintext or RLE
file:

- `-N <TEXT>`, `--name <TEXT>` — Set the pattern name to embed in the output
  file.  `<TEXT>` may contain [tick placeholders](#tick-placeholders) but may
  not contain newlines.

The following options only have an effect when outputting to an image file:

- `-s <INT>`, `--cell-size <INT>` — Set the height & width of the cell squares
  to the given number of pixels [default: 5]

- `-g <INT>`, `--gutter <INT>` — Insert the given number of pixels as padding
  between adjacent cell squares [default: 0]

- `-C <COLOR>`, `--live-color <COLOR>` — Set the color of live cells.
  `<COLOR>` can be a hex RGB string "`#rrggbb`" (with or without leading `#`)
  or a [CSS color name][].  [default: `#000000`]

[CSS color name]: https://www.w3.org/TR/css-color-4/#named-colors

Tick Placeholders
-----------------

Output paths and `--name` arguments can contain any number of printf-style `%d`
placeholders that will be replaced by the tick number when generating an output
file.  The format of such placeholders is:

```text
%[<flag>][<width>][.<precision>]d
```

where:

- `<flag>` may be:
    - `0` to pad the number on the left with zeroes
    - `-` to left-adjust the number
    - omitted to pad the number on the left with spaces

- `<width>` is a nonnegative integer specifying the minimum field width
  [default: 0].  If the tick number is displayed with fewer than `<width>`
  digits, the number will be padded according to `<flag>`.

- `<precision>` is a nonnegative integer (preceded by a period) specifying the
  minimum number of digits to output [default: 0].  If a precision is given, a
  flag of `0` is ignored.

To include a literal `%` in an output path or `--name` argument, write `%%`.
