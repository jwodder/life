The following is an exact specification of the [plaintext file format][] for
[Conway's Game of Life][] patterns as recognized by `lifelib`.

[plaintext file format]: https://conwaylife.com/wiki/Plaintext
[Conway's Game of Life]: https://en.wikipedia.org/wiki/Conway%27s_Game_of_Life

- A plaintext document must be encoded in UTF-8 and may not begin with a
  byte-order marker.

- Each line of a plaintext document is terminated by LF, CR, or CR LF.
  Different lines in the same document may use different line terminators, but
  this is discouraged.  The line terminator may be omitted from the last line
  of a plaintext document, but this is discouraged.

- The following "exotic" line endings may not occur anywhere in a plaintext
  document:
    - U+000B LINE TABULATION (a.k.a. "vertical tab," "VTAB," or "VT")
    - U+000C FORM FEED (FF)
    - U+0085 NEXT LINE (NEL)
    - U+2028 LINE SEPARATOR
    - U+2029 PARAGRAPH SEPARATOR

- A plaintext document consists of zero or more *comment lines* followed by a
  *pattern drawing*.

- A *comment line* is a line whose first character is `!`.  The remainder of
  the line is a human-readable comment.

- If the first comment line in a plaintext document begins with `!Name:`
  followed a space (U+0020) character, then the remainder of the line (not
  including the line terminator) specifies the name of the pattern.  Names may
  begin with one or more space characters, and they may be empty.

- A *pattern drawing* is an ASCII drawing of the Game of Life pattern described
  by the document.  The drawing consists of zero or more lines that specify
  each row of the pattern from top to bottom.  Each line consists of zero or
  more `.` and/or `O` characters that specify the cells of the row from left to
  right, with `.` denoting a dead cell and `O` denoting a live cell.

- It is permitted but discouraged for the lines of a pattern drawing to be of
  unequal length.  Such drawings are parsed as though the shorter lines were
  padded with dead cells on the end/right to match the length of the longest
  line in the drawing.

    - Blank lines in a pattern drawing (denoting rows composed entirely of dead
      cells) are accepted but discouraged.

- Empty pattern drawings are accepted.

- A pattern drawing may not contain any characters other than `.`, `O`, and
  line terminators.  In particular, comment lines are not allowed in the middle
  of a pattern drawing.

Example
-------

A plaintext document representing the [glider](https://conwaylife.com/wiki/Glider):

```text
!Name: Glider
!Very famous.
.O.
..O
OOO
```

Implementation Limits
---------------------

`lifelib` only accepts patterns where the width & height are each no larger
than Rust's [`isize::MAX`][] and where the product of the width & height is no
larger than Rust's [`usize::MAX`][].  On most modern computers, these values
are $2^{63} - 1$ (approx. 9 quintillion) and $2^{64} - 1$ (approx. 18
quintillion), respectively.  Providing a too-large pattern will result in an
error, not necessarily a graceful one (assuming you don't eat up all of your
system's RAM first).

[`isize::MAX`]: https://doc.rust-lang.org/std/primitive.isize.html#associatedconstant.MAX
[`usize::MAX`]: https://doc.rust-lang.org/std/primitive.usize.html#associatedconstant.MAX

"Canonical" Output Profile
--------------------------

Plaintext documents emitted by `lifelib` adhere to the following additional
constraints:

- Lines are terminated by LF, including the last line.

- All lines of the pattern drawing are the same length.

- There are no empty lines; the empty pattern is represented by an empty
  pattern drawing.
