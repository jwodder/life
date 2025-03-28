The following is an exact specification of the [plaintext file format][] for
[Conway's Game of Life][] patterns as recognized by `lifelib`.

[plaintext file format]: https://conwaylife.com/wiki/Plaintext
[Conway's Game of Life]: https://en.wikipedia.org/wiki/Conway%27s_Game_of_Life

- A plaintext document must be encoded in UTF-8 and may not begin with a
  byte-order marker.

- Lines in a plaintext document are terminated by LF, CR, and/or CR LF.  The
  line terminator may be omitted from the last line of a plaintext document,
  but this is discouraged.

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
  followed by one or more space (U+0020) characters, then the remainder of the
  line (not including the line terminator) specifies the name of the pattern.
  Names may be empty.

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
