# SPDX-FileCopyrightText: 2021 ☭ Emery Hemingway
# SPDX-License-Identifier: Unlicense

import std/[strutils, unittest]
import preserves

const examples = [
("""<capture <discard>>""", "\xB4\xB3\x07capture\xB4\xB3\x07discard\x84\x84"),
("""[1 2 3 4]""", "\xB5\x91\x92\x93\x94\x84"),
("""[-2 -1 0 1]""", "\xB5\x9E\x9F\x90\x91\x84"),
(""""hello"""", "\xB1\x05hello"),
("""" \"hello\" """", "\xB1\x09 \"hello\" "),
("""["a" b #"c" [] #{} #t #f]""", "\xB5\xB1\x01a\xB3\x01b\xB2\x01c\xB5\x84\xB6\x84\x81\x80\x84"),
("""-257""", "\xA1\xFE\xFF"),
("""-1""", "\x9F"),
("""0""", "\x90"),
("""1""", "\x91"),
("""255""", "\xA1\x00\xFF"),
("""1.0f""", "\x82\x3F\x80\x00\x00"),
("""1.0""", "\x83\x3F\xF0\x00\x00\x00\x00\x00\x00"),
("""-1.202e300""", "\x83\xFE\x3C\xB7\xB7\x59\xBF\x04\x26"),
("""#=#x"B4B30763617074757265B4B307646973636172648484"""", "\xB4\xB3\x07capture\xB4\xB3\x07discard\x84\x84"),
("""#f""", "\x80")
]

suite "parse":
  for (txt, bin) in examples:
    test txt:
      checkpoint(txt)
      let test = parsePreserves(txt, int)
      checkpoint($test)
      block:
        let
          a = test
          b = decodePreserves(bin, int)
        check(a == b)
      block:
        let
          a = encode test
          b = bin
        check(cast[string](a).toHex == b.toHex)
