[![Minimum Supported Rust Version](https://img.shields.io/badge/MSRV-1.91-orange)](https://www.rust-lang.org)
[![MIT License](https://img.shields.io/github/license/jwodder/life.svg)](https://opensource.org/licenses/MIT)

`parse-check` is a program for checking whether Game of Life pattern files (in
particular, those distributed by conwaylife.com at
<http://conwaylife.com/patterns/all.zip>) can be parsed by `lifelib`.  It takes
one or more filepaths as arguments and attempts to parse each one in turn,
using each path's file extension to identify the proper file format.  For each
file that cannot be parsed, a message is printed to stderr giving the file path
and an error traceback.  If the `-J`/`--json` option is supplied, errors will
instead be reported as JSON Lines objects written to standard output.
`parse-check` exits successfully iff all files parsed successfully.
