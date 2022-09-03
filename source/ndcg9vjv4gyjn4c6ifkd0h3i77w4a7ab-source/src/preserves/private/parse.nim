# SPDX-FileCopyrightText: 2021 ☭ Emery Hemingway
# SPDX-License-Identifier: Unlicense

# this module is included in ../../preserves.nim

import std/[parseutils, strutils]
import npeg
import ../pegs

type
  Value = Preserve[void]
  Frame = tuple[value: Value, pos: int]
  Stack = seq[Frame]

proc shrink(stack: var Stack; n: int) = stack.setLen(stack.len - n)

template pushStack(v: Value) = stack.add((v, capture[0].si))

proc parsePreserves*(text: string): Preserve[void] {.gcsafe.} =
  ## Parse a text-encoded Preserves `string` to a `Preserve` value.
  runnableExamples:
    assert parsePreserves"[ 1 2 3 ]" == [ 1, 2, 3 ].toPreserve
  const pegParser = peg("Document", stack: Stack):
    # Override rules from pegs.nim

    Document <- Preserves.Document

    Preserves.Record <- Preserves.Record:
      var
        record: seq[Value]
        labelOff: int
      while stack[labelOff].pos < capture[0].si:
        inc labelOff
      for i in labelOff.succ..stack.high:
        record.add(move stack[i].value)
      record.add(move stack[labelOff].value)
      stack.shrink record.len
      pushStack Value(kind: pkRecord, record: move record)

    Preserves.Sequence <- Preserves.Sequence:
      var sequence: seq[Value]
      for frame in stack.mitems:
        if frame.pos > capture[0].si:
          sequence.add(move frame.value)
      stack.shrink sequence.len
      pushStack Value(kind: pkSequence, sequence: move sequence)

    Preserves.Dictionary <- Preserves.Dictionary:
      var prs = Value(kind: pkDictionary)
      for i in countDown(stack.high.pred, 0, 2):
        if stack[i].pos < capture[0].si: break
        prs[move stack[i].value] = stack[i.succ].value
      stack.shrink prs.dict.len*2
      pushStack prs

    Preserves.Set <- Preserves.Set:
      var prs = Value(kind: pkSet)
      for frame in stack.mitems:
        if frame.pos > capture[0].si:
          prs.incl(move frame.value)
      stack.shrink prs.set.len
      pushStack prs

    Preserves.Boolean <- Preserves.Boolean:
      case $0
      of "#f": pushStack Value(kind: pkBoolean)
      of "#t": pushStack Value(kind: pkBoolean, bool: true)
      else: discard

    Preserves.Float <- Preserves.Float:
      pushStack Value(kind: pkFloat, float: parseFloat($1))

    Preserves.Double <- Preserves.Double:
      pushStack Value(kind: pkDouble)
      let i = stack.high
      discard parseBiggestFloat($0, stack[i].value.double)

    Preserves.SignedInteger <- Preserves.SignedInteger:
      pushStack Value(kind: pkSignedInteger, int: parseInt($0))

    Preserves.String <- Preserves.String:
      pushStack Value(kind: pkString, string: unescape($0).replace("\\n", "\n"))

    Preserves.charByteString <- Preserves.charByteString:
      let s = unescape($1)
      pushStack Value(kind: pkByteString, bytes: cast[seq[byte]](s))

    Preserves.hexByteString <- Preserves.hexByteString:
      pushStack Value(kind: pkByteString, bytes: cast[seq[byte]](parseHexStr($1)))

    Preserves.b64ByteString <- Preserves.b64ByteString:
      pushStack Value(kind: pkByteString, bytes: cast[seq[byte]](base64.decode($1)))

    Preserves.Symbol <- Preserves.Symbol:
      pushStack Value(kind: pkSymbol, symbol: Symbol $0)

    Preserves.Embedded <- Preserves.Embedded:
      var v = stack.pop.value
      v.embedded = true
      pushStack v

    Preserves.Compact <- Preserves.Compact:
      pushStack decodePreserves(stack.pop.value.bytes, void)

  var stack: Stack
  let match = pegParser.match(text, stack)
  if not match.ok:
    raise newException(ValueError, "failed to parse Preserves:\n" & text[match.matchMax..text.high])
  assert(stack.len == 1)
  stack.pop.value

proc parsePreserves*(text: string; E: typedesc): Preserve[E] {.gcsafe.} =
  ## Parse a text-encoded Preserves `string` to a `Preserve[E]` value for embedded type `E`.
  when E is void: parsePreserves(text)
  else: mapEmbeds(parsePreserves(text), E)
