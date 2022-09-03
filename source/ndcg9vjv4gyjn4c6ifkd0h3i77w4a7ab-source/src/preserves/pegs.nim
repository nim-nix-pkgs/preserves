# SPDX-FileCopyrightText: 2021 ☭ Emery Hemingway
# SPDX-License-Identifier: Unlicense

## NPEG rules for Preserves.

import npeg, npeg/lib/utf8

when defined(nimHasUsed): {.used.}

grammar "Preserves":

  Document <- Value * ws * !1

  Value <-
      (ws * (Record | Collection | Atom | Embedded | Compact)) |
      (ws * '@' * Value * Value) |
      (ws * ';' * @'\n' * Value)

  Collection <- Sequence | Dictionary | Set

  Atom <- Boolean | Float | Double | SignedInteger | String | ByteString | Symbol

  Record <- '<' * Value * *Value * ws * '>'

  Sequence <- '[' * ws * *(Value * ws) * ']'

  Dictionary <- '{' * ws * *(Value * ws * ':' * ws * Value * ws) * '}'

  Set <- "#{" * ws * *(Value * ws) * '}'

  Boolean <- "#f" | "#t"

  Float <- >flt * 'f'
  Double <- flt
  SignedInteger <- int

  nat <- '0' | (Digit-'0') * *Digit
  int <- ?'-' * nat
  frac <- '.' * +Digit
  exp <- 'e' * ?('-'|'+') * +Digit
  flt <- int * ((frac * exp) | frac | exp)

  String <- '"' * *(escaped | (utf8.any - '"')) * '"'

  ByteString <- charByteString | hexByteString | b64ByteString
  charByteString <- '#' * >('"' * >(*binchar) * '"')
  hexByteString <- "#x\"" * ws * >(*(Xdigit[2] * ws)) * '"'
  b64ByteString <- "#[" * ws * >(*(base64char * ws)) * ']'

  binchar <- binunescaped | (escape * (escaped | '"' | ('x' * Xdigit[2])))
  binunescaped <- {'\20'..'\21', '#'..'[', ']'..'~'}
  base64char <- {'A'..'Z', 'a'..'z', '0'..'9', '+', '/', '-', '_', '='}

  Symbol <- (symstart * *symcont) | ('|' * *symchar * '|')

  symstart <- Alpha | sympunct | symustart
  symcont <- Alpha | sympunct | symustart | symucont | Digit | '-'
  sympunct <- {'~', '!', '$', '%', '^', '&', '*', '?', '_', '=', '+', '/', '.'}
  symchar <- unescaped | '"' | (escape * (escaped | '|' | ('u' * Xdigit)))
  symustart <- utf8.any - {0..127}
  symucont <- utf8.any - {0..127}
    # TODO: exclude some unicode ranges

  Embedded <- "#!" * Value

  Compact <- "#=" * ws * ByteString

  unescaped <- utf8.any - escaped
  unicodeEscaped <- 'u' * Xdigit[4]
  escaped <- '\\' * ({'{', '"', '|', '\\', 'b', 'f', 'n', 'r', 't'} | unicodeEscaped)
  escape <- '\\'

  ws <- *(' ' | '\t' | '\r' | '\n' | ',')
