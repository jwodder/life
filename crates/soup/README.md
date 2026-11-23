[![Minimum Supported Rust Version](https://img.shields.io/badge/MSRV-1.91-orange)](https://www.rust-lang.org)
[![MIT License](https://img.shields.io/github/license/jwodder/life.svg)](https://opensource.org/licenses/MIT)

`soup` is a program for generating a random pattern (called a *[soup][]*) for
[Conway's Game of Life][].

[soup]: https://conwaylife.com/wiki/Soup
[Conway's Game of Life]: https://en.wikipedia.org/wiki/Conway%27s_Game_of_Life
[plaintext]: https://conwaylife.com/wiki/Plaintext
[Run Length Encoded]: https://conwaylife.com/wiki/Run_Length_Encoded

Usage
=====

    soup [<options>] <size> [<outfile>]

`soup` takes a size in the form `WIDTHxHEIGHT` (e.g., `6x12`) and generates a
random pattern of that size in which each cell has an independent probability
`p` of being alive; `p` is given by the `-p`/`--probability` option and
defaults to 10%.

The resulting pattern is written to `<outfile>`, the file extension of which
must be either "`.cells`" (to produce a [plaintext][] file) or "`.rle`" (to
produce a [Run Length Encoded][] file).  Alternatively, `<outfile>` may be `-`
or omitted to write plaintext to standard output.

Options
-------

- `-c TEXT`, `--comment TEXT` — Embed the comment `TEXT` in the output file.
  `TEXT` may not contain newlines.  This option may be specified multiple
  times.

- `-N TEXT`, `--name TEXT` — Set the pattern name to embed in the output file.
  `TEXT` may not contain newlines.

- `-p PERCENTAGE`, `--probability PERCENTAGE` — Set the probability of a given
  cell being alive.  `PERCENTAGE` must be a floating-point percentage value
  from 0 to 100. [default: 10]
