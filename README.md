[![Project Status: Concept – Minimal or no implementation has been done yet, or the repository is only intended to be a limited example, demo, or proof-of-concept.](https://www.repostatus.org/badges/latest/concept.svg)](https://www.repostatus.org/#concept)
[![CI Status](https://github.com/jwodder/life/actions/workflows/test.yml/badge.svg)](https://github.com/jwodder/life/actions/workflows/test.yml)
[![codecov.io](https://codecov.io/gh/jwodder/life/branch/master/graph/badge.svg)](https://codecov.io/gh/jwodder/life)
[![Minimum Supported Rust Version](https://img.shields.io/badge/MSRV-1.81-orange)](https://www.rust-lang.org)
[![MIT License](https://img.shields.io/github/license/jwodder/life.svg)](https://opensource.org/licenses/MIT)

This is a Rust [workspace][] containing various packages for doing things with
[Conway's Game of Life][].

The packages are:

- [`lifelib`][] — Core library implementing the Game of Life and related
  functionality

- [`tick`][] — Program for advancing Game of Life patterns

- [`life-utils`][] — Internal utilities used by multiple packages

[workspace]: https://doc.rust-lang.org/cargo/reference/workspaces.html
[Conway's Game of Life]: https://en.wikipedia.org/wiki/Conway%27s_Game_of_Life
[`lifelib`]: https://github.com/jwodder/life/tree/master/lifelib
[`tick`]: https://github.com/jwodder/life/tree/master/tick
[`life-utils`]: https://github.com/jwodder/life/tree/master/life-utils
