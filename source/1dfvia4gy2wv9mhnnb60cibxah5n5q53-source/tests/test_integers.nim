# SPDX-FileCopyrightText: 2021 ☭ Emery Hemingway
# SPDX-License-Identifier: Unlicense

import streams, strutils, unittest
import bigints, preserves

suite "native":
  let testVectors = @[
  (-257, "A1FEFF"),
  (-256, "A1FF00"),
  (-255, "A1FF01"),
  (-254, "A1FF02"),
  (-129, "A1FF7F"),
  (-128, "A080"),
  (-127, "A081"),
  (-4, "A0FC"),
  (-3, "9D"),
  (-2, "9E"),
  (-1, "9F"),
  (0, "90"),
  (1, "91"),
  (12, "9C"),
  (13, "A00D"),
  (127, "A07F"),
  (128, "A10080"),
  (255, "A100FF"),
  (256, "A10100"),
  (131072, "A2020000"),
  (32767, "A17FFF"),
  (32768, "A2008000"),
  (65535, "A200FFFF"),
  (65536, "A2010000"),
  ]

  for (num, txt) in testVectors:
    test $num:
      let x = num.toPreserve
      var stream = newStringStream()
      stream.write(x)
      block:
        stream.setPosition(0)
        let a = txt
        let b = stream.readAll.toHex
        check(b == a)
      block:
        stream.setPosition(0)
        let y = stream.decodePreserves()
        let a = num
        let b = y.int
        check(b == a)

suite "big":
  let testVectors = @[
  ("87112285931760246646623899502532662132736",
      "B012010000000000000000000000000000000000"),
  ]

  for (decimals, hex) in testVectors:
    test decimals:
      let big = initBigInt(decimals)
      let x = big.toPreserve
      var stream = newStringStream()
      stream.write(x)
      block:
        stream.setPosition(0)
        let a = hex
        let b = stream.readAll.toHex
        check(b == a)
      block:
        stream.setPosition(0)
        let y = stream.decodePreserves()
        let a = big
        let b = y.bigint
        check(b == a)
