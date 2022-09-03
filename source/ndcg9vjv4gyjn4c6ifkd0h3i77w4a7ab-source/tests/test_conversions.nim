# SPDX-FileCopyrightText: 2021 ☭ Emery Hemingway
# SPDX-License-Identifier: Unlicense

import std/[options, tables, unittest, xmlparser, xmltree]
import preserves, preserves/xmlhooks

suite "conversions":
  test "dictionary":
    type Bar = tuple
      s: string
    type Foobar {.preservesDictionary.} = object
      a, b: int
      c: Bar
    let
      c = Foobar(a: 1, b: 2, c: ("ku", ))
      b = toPreserve(c)
      a = preserveTo(b, Foobar)
    check(a.isSome and (get(a) == c))
    check(b.kind == pkDictionary)

  test "records":
    type Bar {.preservesRecord: "bar".} = object
      s: string
    type Foobar {.preservesRecord: "foo".} = object
      a, b: int
      c: Bar
    let
      tup = Foobar(a: 1, b: 2, c: Bar(s: "ku", ))
      prs = toPreserve(tup)
    check(prs.kind == pkRecord)
    check($prs == """<foo 1 2 <bar "ku">>""")
    check(preserveTo(prs, Foobar) == some(tup))

  test "tables":
    var a: Table[int, string]
    for i, s in ["a", "b", "c"]: a[i] = s
    let b = toPreserve(a)
    check($b == """{0: "a", 1: "b", 2: "c"}""")
    var c: Table[int, string]
    check(fromPreserve(c, b))
    check(a == c)

  test "XML":
    var a: XmlNode
    var b = parseXML """
      <?xml version="1.0" standalone="no"?>
      <!DOCTYPE svg PUBLIC "-//W3C//DTD SVG 1.1//EN" "http://www.w3.org/Graphics/SVG/1.1/DTD/svg11.dtd">
      <?xml version="1.0"?>
      <svg xmlns="http://www.w3.org/2000/svg" width="10cm" height="3cm" viewBox="0 0 1000 300" version="1.1">
        <desc>Example text01 - 'Hello, out there' in blue</desc>
        <text x="250" y="150" font-family="Verdana" font-size="55" fill="blue">
      Hello, out there
      </text>
        <!-- Show outline of canvas using 'rect' element -->
        <rect x="1" y="1" width="998" height="298" fill="none" stroke="blue" stroke-width="2"/>
      </svg>
    """
    var pr = toPreserve(b, void)
    checkpoint $pr
    check fromPreserve(a, pr)

suite "toPreserve":
  template check(p: Preserve; s: string) =
    test s: check($p == s)
  check false.toPreserve, "#f"
  check [0, 1, 2, 3].toPreserve, "[0 1 2 3]"
