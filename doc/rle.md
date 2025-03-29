The following is an exact specification of the [run length encoded (RLE) file
format][RLE] for [Conway's Game of Life][] patterns as recognized by `lifelib`.

- An RLE document must be encoded in UTF-8 and may not begin with a byte-order
  marker.

- Each line of an RLE document is terminated by LF, CR, or CR LF.  Different
  lines in the same document may use different line terminators, but this is
  discouraged.  The line terminator may be omitted from the last line of an RLE
  document, but this is discouraged.

- The following "exotic" line endings may not occur anywhere in an RLE
  document:
    - U+000B LINE TABULATION (a.k.a. "vertical tab," "VTAB," or "VT")
    - U+000C FORM FEED (FF)
    - U+0085 NEXT LINE (NEL)
    - U+2028 LINE SEPARATOR
    - U+2029 PARAGRAPH SEPARATOR

- The following is a grammar for RLE documents defined using Augmented BNF as
  described in [RFC 5234][] and updated by [RFC 7405][]:

    ```text
    rle-document  =  *(hash-line / blank-line) header pattern

    hash-line     =  "#" LETTER 1*SP text NL
                        ; a "# line"

    text          =  *char-no-nl

    blank-line    =  *WSP NL
                        ; line containing only whitespace

    header        =  *WSP width *WSP "," *WSP height *WSP ["," *WSP rule *WSP] NL
                        ; header line

    width         =  %s"x" *WSP "=" *WSP integer
                        ; width of the pattern

    height        =  %s"y" *WSP "=" *WSP integer
                        ; height of the pattern

    rule          =  %s"rule" *WSP = *WSP ( %s"B3/S23" / "23/3" )
                        ; cellular automaton rule for the pattern
                        ; Only the standard Game of Life is allowed.

    pattern       =  *(*LWSP run) *LWSP "!"

    run           =  [integer] ( %s"b" / %s"o" / "$" )

    char-no-nl    =  <any single Unicode character other than U+000A, U+000B,
                      U+000C, U+000D, U+0085, U+2028, and U+2029>

    integer       =  1*DIGIT
                        ; a nonnegative decimal integer
                        ; The maximum permitted value for an integer production
                        ;     is the platform's `usize::MAX` value.

    LETTER        =  %x41-5A / %x61-7A
                        ; A-Z / a-z

    DIGIT         =  %x30-39
                        ; 0-9

    WSP           =  SP / HTAB
                        ; ASCII horizontal white space

    LWSP          =  WSP / NL

    NL            =  LF / CR LF / CR
                        ; line terminator

    HTAB          =  %x09
                        ; horizontal tab

    LF            =  %x0A
                        ; linefeed character

    CR            =  %x0D
                        ; carriage return

    SP            =  %x20
                        ; space character
    ```

- The `#` lines in an RLE document (defined by the `<hash-line>` rule in the
  ABNF) contain metadata about the pattern.  The `<LETTER>` element of a `#`
  line specifies the type of metadata described by the line, and the `<text>`
  element is the value of the metadata.  `lifelib` only assigns meanings to the
  following `<LETTER>` values:
    - `N` — The `<text>` element specifies the name of the pattern.  If an RLE
      document contains multiple `#` lines of type `N`, `lifelib` only uses the
      first one as the name, and the others are effectively ignored.
    - `C` — The `<text>` element is a comment.
    - `c` — Same as `C`, but not recommended.

- The header line in an RLE document (defined by the `<header>` rule in the
  ABNF) specifies the width and height of the pattern described by the
  document.  The width is the value of the `<integer>` element within the
  `<width>` element, and the height is the value of the `<integer>` element
  within the `<height>` element.

- The header line may optionally contain a cellular automaton rule, but the
  value must be the [rulestring][] for the standard version of Conway's Game of
  Life, i.e., `B3/S23` or `23/3`.

- The `<pattern>` element of an RLE document describes a Conway's Game of Life
  pattern.  It consists of zero or more `<run>` items, each of which is a pair
  of an optional integer (the *run count*, defaulting to 1 if omitted) and a
  *tag* (`b`, `o`, or `$`).

  - The `<run>` items specify the cells of the pattern from top to bottom and
    left to right.  A single item with a `b` or `o` tag denotes a run of
    consecutive cells in the same row that are all dead or alive, respectively,
    with the number of cells being equal to the item's run count.  An item with
    a `$` tag denotes the end of a row.

  - Dead cells at the end of a row do not need to be encoded, and so one or
    more rows of all-dead cells can be encoded as an item with a `$` tag and a
    run count equal to the number of all-dead rows.  (If the all-dead rows are
    preceded by another row, the preceding `$` item may be merged with the `$`
    item for the all-dead rows, transforming, e.g., `$2$` to `3$`.)

  - The end of the last row of the pattern does not need to be encoded.

  - Run counts of zero are accepted but do not add anything to the resulting
    pattern.

  - If the `<run>` items specify any cells outside the dimensions given in the
    header line, those cells are ignored.

- The final `<run>` item in a `<pattern>` is followed by a `!`.  Any text in
  the document after this terminating `!` is ignored.

[RLE]: https://conwaylife.com/wiki/Run_Length_Encoded
[Conway's Game of Life]: https://en.wikipedia.org/wiki/Conway%27s_Game_of_Life
[rulestring]: https://conwaylife.com/wiki/Rulestring
[RFC 5234]: https://www.rfc-editor.org/info/rfc5234
[RFC 7405]: https://www.rfc-editor.org/info/rfc7405

Example
-------

An RLE document representing the [glider](https://conwaylife.com/wiki/Glider):

```text
#N Glider
#C Very famous.
x = 3, y = 3
bo$2bo$3o!
```
