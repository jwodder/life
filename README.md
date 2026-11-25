[![Project Status: Concept – Minimal or no implementation has been done yet, or the repository is only intended to be a limited example, demo, or proof-of-concept.](https://www.repostatus.org/badges/latest/concept.svg)](https://www.repostatus.org/#concept)
[![CI Status](https://github.com/jwodder/life/actions/workflows/test.yml/badge.svg)](https://github.com/jwodder/life/actions/workflows/test.yml)
[![codecov.io](https://codecov.io/gh/jwodder/life/branch/master/graph/badge.svg)](https://codecov.io/gh/jwodder/life)
[![Minimum Supported Rust Version](https://img.shields.io/badge/MSRV-1.91-orange)](https://www.rust-lang.org)
[![MIT License](https://img.shields.io/github/license/jwodder/life.svg)](https://opensource.org/licenses/MIT)

This is a Rust [workspace][] containing various packages for doing things with
[Conway's Game of Life][].

The packages are:

- Libraries:

    - [`lifelib`][] — Core library implementing the Game of Life and related
      functionality

    - [`life-utils`][] — Internal utilities used by multiple packages

- Programs:

    - [`chbounds`][] — Pad & crop Game of Life patterns

    - [`evolve`][] — Create GIFs of pattern generations

    - [`tick`][] — Advance Game of Life patterns

    - [`parse-check`][] — Check whether pattern files can be parsed by
      `lifelib`

    - [`pat2img`][] — Render patterns as images

    - [`soup`][] — Generate a random pattern

This workspace as a whole is a hobby project for personal experimentation &
edification and is not intended to be generally/widely used by others.  Use
anything here at your own risk.

[workspace]: https://doc.rust-lang.org/cargo/reference/workspaces.html
[Conway's Game of Life]: https://en.wikipedia.org/wiki/Conway%27s_Game_of_Life
[`chbounds`]: https://github.com/jwodder/life/tree/master/crates/chbounds
[`evolve`]: https://github.com/jwodder/life/tree/master/crates/evolve
[`life-utils`]: https://github.com/jwodder/life/tree/master/crates/life-utils
[`lifelib`]: https://github.com/jwodder/life/tree/master/crates/lifelib
[`parse-check`]: https://github.com/jwodder/life/tree/master/crates/parse-check
[`pat2img`]: https://github.com/jwodder/life/tree/master/crates/pat2img
[`soup`]: https://github.com/jwodder/life/tree/master/crates/soup
[`tick`]: https://github.com/jwodder/life/tree/master/crates/tick
