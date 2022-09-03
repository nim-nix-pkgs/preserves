# SPDX-FileCopyrightText: 2021 ☭ Emery Hemingway
# SPDX-License-Identifier: Unlicense

import std/[options, tables, unittest]
import bigints, preserves

suite "conversions":
  test "dictionary":
    type Bar = object
      s: string
    type Foobar = tuple
      a, b: int
      c: Bar
    let
      c: Foobar = (a: 1, b: 2, c: Bar(s: "ku", ))
      b = toPreserve(c)
      a = preserveTo(b, Foobar)
    check(a.isSome and (get(a) == c))
    check(b.kind == pkDictionary)

  test "records":
    type Bar {.record: "bar".} = object
      s: string
    type Foobar {.record: "foo".} = tuple
      a, b: int
      c: Bar
    let
      tup: Foobar = (a: 1, b: 2, c: Bar(s: "ku", ))
      prs = toPreserve(tup)
    check(prs.kind == pkRecord)
    check($prs == """<foo 1 2 <bar "ku">>""")
    check(preserveTo(prs, Foobar) == some(tup))

  test "tables":
    var a: Table[int, string]
    for i, s in ["a", "b", "c"]: a[i] = s
    let b = toPreserve(a)
    check($b == """{0: "a" 1: "b" 2: "c"}""")
    var c: Table[int, string]
    check(fromPreserve(c, b))
    check(a == c)

suite "%":
  template check(p: Preserve; s: string) =
    test s: check($p == s)
  check false.toPreserve, "#f"
  check [0, 1, 2, 3].toPreserve, "[0 1 2 3]"
