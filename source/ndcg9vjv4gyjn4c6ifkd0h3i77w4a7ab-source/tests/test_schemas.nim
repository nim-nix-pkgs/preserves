# SPDX-FileCopyrightText: 2021 ☭ Emery Hemingway
# SPDX-License-Identifier: Unlicense

import std/[tables, options, os, unittest]
import preserves, preserves/schema, preserves/schemaparse

if dirExists "tests": setCurrentDir "tests"
  # nimble runs tests in the directory above

suite "schema":

  const
    binPath = "../schema.bin"
    textPath = "../schema.prs"

  test "convertability":
    if not fileExists(binPath): skip()
    else:
      var
        b = decodePreserves readFile(binPath)
        scm = preserveTo(b, Schema[void])
      check scm.isSome
      if scm.isSome:
        var a = toPreserve(get scm)
        check(a == b)

  test "parser":
    if not fileExists(binPath): skip()
    else:
      var
        b = decodePreserves readFile(binPath)
        scm = preserveTo(b, Schema[void])
      check scm.isSome
      if scm.isSome:
        var a = toPreserve parsePreservesSchema(readFile textPath, textPath)
        let aDefs = a[0][toSymbol "definitions"]
        let bDefs = b[0][toSymbol "definitions"]
        for (key, val) in aDefs.pairs:
          check(bDefs[key] == val)
        check(a == b)
