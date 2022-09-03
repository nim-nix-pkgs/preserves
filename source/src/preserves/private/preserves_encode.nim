# SPDX-FileCopyrightText: 2021 ☭ Emery Hemingway
# SPDX-License-Identifier: Unlicense

import std/[json, options, streams]
from std/os import extractFilename, paramStr

import ../../preserves, ../../preserves/jsonhooks, ../../preserves/parse

when isMainModule:
  let command = extractFilename(paramStr 0)
  try:
    case command:
    of "preserves_encode":
      let pr = stdin.readAll.parsePreserves
      stdout.newFileStream.write(pr)
    of "preserves_decode":
      let pr = stdin.readAll.decodePreserves
      stdout.writeLine($pr)
    of "preserves_from_json":
      let
        js = stdin.newFileStream.parseJson
        pr = js.toPreserve
      stdout.newFileStream.write(pr)
    of "preserves_to_json":
      let
        pr = stdin.readAll.decodePreserves
        js = preserveTo(pr, JsonNode)
      if js.isSome:
        stdout.writeLine(get js)
      else:
        quit("Preserves not convertable to JSON")
    else:
      quit("no behavior defined for " & command)
  except:
    let msg = getCurrentExceptionMsg()
    quit(msg)
