# SPDX-FileCopyrightText: 2021 ☭ Emery Hemingway
# SPDX-License-Identifier: Unlicense

import std/[base64, endians, hashes, options, sets, sequtils, streams, tables, typetraits]
import ./preserves/private/macros

from std/json import escapeJson, escapeJsonUnquoted
from std/strutils import parseEnum
import ./preserves/private/dot

when defined(tracePreserves):
  template trace(args: varargs[untyped]) = {.cast(noSideEffect).}: stderr.writeLine(args)
else:
  template trace(args: varargs[untyped]) = discard

type
  PreserveKind* = enum
    pkBoolean, pkFloat, pkDouble, pkSignedInteger, pkString, pkByteString, pkSymbol,
        pkRecord, pkSequence, pkSet, pkDictionary, pkEmbedded

const
  atomKinds* = {pkBoolean, pkFloat, pkDouble, pkSignedInteger, pkString, pkByteString, pkSymbol}
  compoundKinds* = {pkRecord, pkSequence, pkSet, pkDictionary}

type Symbol* = distinct string
proc `$`*(s: Symbol): string {.borrow.}
proc `<`*(x, y: Symbol): bool {.borrow.}
proc `==`*(x, y: Symbol): bool {.borrow.}
proc len*(s: Symbol): int {.borrow.}
proc hash*(s: Symbol): Hash {.borrow.}

type
  Preserve*[E = void] = object
    case kind*: PreserveKind
    of pkBoolean:
      bool*: bool
    of pkFloat:
      float*: float32
    of pkDouble:
      double*: float64
    of pkSignedInteger:
      int*: BiggestInt
    of pkString:
      string*: string
    of pkByteString:
      bytes*: seq[byte]
    of pkSymbol:
      symbol*: Symbol
    of pkRecord:
      record*: seq[Preserve[E]] # label is last
    of pkSequence:
      sequence*: seq[Preserve[E]]
    of pkSet:
      set*: seq[Preserve[E]]
        # TODO: HashSet
    of pkDictionary:
      dict*: seq[DictEntry[E]]
        # TODO: Tables
    of pkEmbedded:
      embed*: E
    embedded*: bool
      ## Flag to mark embedded Preserves

  DictEntry[E] = tuple[key: Preserve[E], val: Preserve[E]]

proc `==`*[A, B](x: Preserve[A]; y: Preserve[B]): bool =
  ## Check `x` and `y` for equivalence.
  if x.kind == y.kind and x.embedded == y.embedded:
    case x.kind
    of pkBoolean:
      result = x.bool == y.bool
    of pkFloat:
      result = x.float == y.float
    of pkDouble:
      result = x.double == y.double
    of pkSignedInteger:
      result = x.int == y.int
    of pkString:
      result = x.string == y.string
    of pkByteString:
      result = x.bytes == y.bytes
    of pkSymbol:
      result = x.symbol == y.symbol
    of pkRecord:
      result = x.record.len == y.record.len
      for i in 0..x.record.high:
        if not result: break
        result = result and (x.record[i] == y.record[i])
    of pkSequence:
      for i, val in x.sequence:
        if y.sequence[i] != val: return false
      result = true
    of pkSet:
      result = x.set.len == y.set.len
      for i in 0..x.set.high:
        if not result: break
        result = result and (x.set[i] == y.set[i])
    of pkDictionary:
      result = x.dict.len == y.dict.len
      for i in 0..x.dict.high:
        if not result: break
        result = result and
          (x.dict[i].key == y.dict[i].key) and
          (x.dict[i].val == y.dict[i].val)
    of pkEmbedded:
      when A is B:
        when A is void:
          result = true
        else:
          result = x.embed == y.embed

proc `<`(x, y: string | seq[byte]): bool =
  for i in 0 .. min(x.high, y.high):
    if x[i] < y[i]: return true
    if x[i] != y[i]: return false
  x.len < y.len

proc `<`*[A, B](x: Preserve[A]; y: Preserve[B]): bool =
  ## Preserves have a total order over values. Check if `x` is ordered before `y`.
  if x.embedded != y.embedded:
    result = y.embedded
  elif x.kind != y.kind:
    result = x.kind < y.kind
  else:
    case x.kind
    of pkBoolean:
      result = (not x.bool) and y.bool
    of pkFloat:
      result = x.float < y.float
    of pkDouble:
      result = x.double < y.double
    of pkSignedInteger:
      result = x.int < y.int
    of pkString:
      result = x.string < y.string
    of pkByteString:
      result = x.bytes < y.bytes
    of pkSymbol:
      result = x.symbol < y.symbol
    of pkRecord:
      if x.record[x.record.high] < y.record[y.record.high]: return true
      for i in 0..<min(x.record.high, y.record.high):
        if x.record[i] < y.record[i]: return true
        if x.record[i] == y.record[i]: return false
      result = x.record.len < y.record.len
    of pkSequence:
      for i in 0..min(x.sequence.high, y.sequence.high):
        if x.sequence[i] < y.sequence[i]: return true
        if x.sequence[i] != y.sequence[i]: return false
      result = x.sequence.len < y.sequence.len
    of pkSet:
      for i in 0..min(x.set.high, y.set.high):
        if x.set[i] < y.set[i]: return true
        if x.set[i] != y.set[i]: return false
      result = x.set.len < y.set.len
    of pkDictionary:
      for i in 0..min(x.dict.high, y.dict.high):
        if x.dict[i].key < y.dict[i].key: return true
        if x.dict[i].key == y.dict[i].key:
          if x.dict[i].val < y.dict[i].val: return true
          if x.dict[i].val != y.dict[i].val: return false
      result = x.dict.len < y.dict.len
    of pkEmbedded:
      when (not A is void) and (A is B):
        result = x.embed < y.embed

proc hash*(pr: Preserve): Hash =
  ## Produce a `Hash` of `pr` for use with a `HashSet` or `Table`.
  var h = hash(pr.kind.int) !& hash(pr.embedded)
  case pr.kind
  of pkBoolean:
    h = h !& hash(pr.bool)
  of pkFloat:
    h = h !& hash(pr.float)
  of pkDouble:
    h = h !& hash(pr.double)
  of pkSignedInteger:
    h = h !& hash(pr.int)
  of pkString:
    h = h !& hash(pr.string)
  of pkByteString:
    h = h !& hash(pr.bytes)
  of pkSymbol:
    h = h !& hash(string pr.symbol)
  of pkRecord:
    for val in pr.record:
      h = h !& hash(val)
  of pkSequence:
    for val in pr.sequence:
      h = h !& hash(val)
  of pkSet:
    for val in pr.set.items:
      h = h !& hash(val)
  of pkDictionary:
    for (key, val) in pr.dict.items:
      h = h !& hash(key) !& hash(val)
  of pkEmbedded:
      h = h !& hash(pr.embed)
  !$h

proc `[]`*(pr: Preserve; i: int): Preserve =
  ## Select an indexed value from ``pr``.
  ## Only valid for records and sequences.
  case pr.kind
  of pkRecord: pr.record[i]
  of pkSequence: pr.sequence[i]
  else:
    raise newException(ValueError, "`Preserves value is not indexable")

proc `[]=`*(pr: var Preserve; i: Natural; val: Preserve) =
  ## Assign an indexed value into ``pr``.
  ## Only valid for records and sequences.
  case pr.kind
  of pkRecord: pr.record[i] = val
  of pkSequence: pr.sequence[i] = val
  else:
    raise newException(ValueError, "`Preserves value is not indexable")

proc getOrDefault(pr: Preserve; key: Preserve): Preserve =
  ## Retrieves the value of `pr[key]` if `pr` is a dictionary containing `key`
  ## or returns the `#f` Preserves value.
  if pr.kind == pkDictionary:
    for (k, v) in pr.dict:
      if key == k:
        result = v
        break

proc incl*(pr: var Preserve; key: Preserve) =
  ## Include `key` in the Preserves set `pr`.
  for i in 0..pr.set.high:
    if key < pr.set[i]:
      insert(pr.set, [key], i)
      return
  pr.set.add(key)

proc excl*(pr: var Preserve; key: Preserve) =
  ## Exclude `key` from the Preserves set `pr`.
  for i in 0..pr.set.high:
    if pr.set[i] == key:
      delete(pr.set, i, i)
      break

proc `[]`*(pr, key: Preserve): Preserve =
  ## Select a value by `key` from `pr`.
  ## Works for sequences, records, and dictionaries.
  if pr.isDictionary:
    for (k, v) in pr.dict.items:
      if k == key: return v
    raise newException(KeyError, "value not in Preserves dictionary")
  elif (pr.isRecord or pr.isSequence) and key.isInteger:
    result = pr[int key.int]
  else:
    raise newException(ValueError, "invalid Preserves indexing")

func step*(pr, idx: Preserve): Option[Preserve] =
  ## Step into `pr` by index `idx`.
  ## Works for sequences, records, and dictionaries.
  runnableExamples:
    import std/options
    assert step(parsePreserves("""<foo 1 2>"""), 1.toPreserve) == some(2.toPreserve)
    assert step(parsePreserves("""{ foo: 1 bar: 2}"""), "foo".toSymbol) == some(1.toPreserve)
    assert step(parsePreserves("""[ ]"""), 1.toPreserve) == none(Preserve[void])
  if pr.isDictionary:
    for (k, v) in pr.dict.items:
      if k == idx:
        result = some(v)
        break
  elif (pr.isRecord or pr.isSequence) and idx.isInteger:
    let i = int idx.int
    if i < pr.len:
      result = some(pr[i])

proc `[]=`*(pr: var Preserve; key, val: Preserve) =
  ## Insert `val` by `key` in the Preserves dictionary `pr`.
  for i in 0..pr.dict.high:
    if key < pr.dict[i].key:
      insert(pr.dict, [(key, val, )], i)
      return
    elif key == pr.dict[i].key:
      pr.dict[i].val = val
      return
  pr.dict.add((key, val, ))

proc mget*(pr: var Preserve; key: Preserve): var Preserve =
  ## Select a value by `key` from the Preserves dictionary `pr`.
  if pr.isDictionary:
    for (k, v) in pr.dict.items:
      if k == key: return v
      raise newException(KeyError, "key not in Preserves dictionary")
  raise newException(ValueError, "not a Preserves dictionary")

proc toSymbol*(s: sink string; E = void): Preserve[E] {.inline.} =
  ## Create a Preserves symbol value.
  Preserve[E](kind: pkSymbol, symbol: Symbol s)

proc initRecord*[E](label: Preserve[E]; arity: Natural = 0): Preserve[E] =
  ## Create a Preserves record value.
  result = Preserve[E](kind: pkRecord, record: newSeq[Preserve[E]](arity.succ))
  result.record[arity] = label

proc initRecord*[E](label: Preserve[E]; args: varargs[Preserve[E]]): Preserve[E] =
  ## Create a Preserves record value.
  result = Preserve[E](kind: pkRecord,
      record: newSeqOfCap[Preserve[E]](1+args.len))
  for arg in args:
    result.record.add(arg)
  result.record.add(label)

proc initRecord*[E](label: string; args: varargs[Preserve[E]]): Preserve[E] {.inline.} =
  ## Create a Preserves record value.
  initRecord(toSymbol(label, E), args)

proc initSequence*[E](len: Natural = 0): Preserve[E] =
  ## Create a Preserves sequence value.
  Preserve[E](kind: pkSequence, sequence: newSeq[Preserve[E]](len))

proc initSet*[E](): Preserve[E] = Preserve[E](kind: pkSet)
  ## Create a Preserves set value.

proc initDictionary*[E](): Preserve[E] = Preserve[E](kind: pkDictionary)
  ## Create a Preserves dictionary value.

proc embed*[E](pr: sink Preserve[E]): Preserve[E] =
  ## Create a Preserves value that embeds ``e``.
  result = pr
  result.embedded = true

proc embed*[E](e: sink E): Preserve[E] =
  ## Create a Preserves value that embeds ``e``.
  Preserve[E](kind: pkEmbedded, embed: e)

proc len*(pr: Preserve): int =
  ## Return the shallow count of values in ``pr``, that is the number of
  ## fields in a record, items in a sequence, items in a set, or key-value pairs
  ## in a dictionary.
  case pr.kind
  of pkRecord: pr.record.len.pred
  of pkSequence: pr.sequence.len
  of pkSet: pr.set.len
  of pkDictionary: pr.dict.len
  else: 0

iterator items*(pr: Preserve): Preserve =
  ## Shallow iterator over `pr`, yield the fields in a record,
  ## the items of a sequence, the items of a set, or the pairs
  ## of a dictionary.
  case pr.kind
  of pkRecord:
    for i in 0..pr.record.high.pred:
      yield pr.record[i]
  of pkSequence:
    for e in pr.sequence.items: yield e
  of pkSet:
    for e in pr.set.items: yield e
  of pkDictionary:
    for (k, v) in pr.dict.items:
      yield k # key can be an arbitrary Preserve
      yield v
  else: discard

iterator pairs*[E](pr: Preserve[E]): DictEntry[E] =
  assert(pr.kind == pkDictionary, "not a dictionary")
  for i in 0..pr.dict.high: yield pr.dict[i]

func isBoolean*(pr: Preserve): bool {.inline.} = pr.kind == pkBoolean
  ## Check if ``pr`` is a Preserve boolean.

func isFalse*(pr: Preserve): bool {.inline.} =
  ## Check if ``pr`` is equivalent to the zero-initialized ``Preserve``.
  pr.kind == pkBoolean and pr.bool == false

func isFloat*(pr: Preserve): bool {.inline.} = pr.kind == pkFloat
  ## Check if ``pr`` is a Preserve float.

func isDouble*(pr: Preserve): bool {.inline.} = pr.kind == pkDouble
  ## Check if ``pr`` is a Preserve double.

func isInteger*(pr: Preserve): bool {.inline.} = pr.kind == pkSignedInteger
  ## Check if ``pr`` is a Preserve double.

func isString*(pr: Preserve): bool {.inline.} = pr.kind == pkString
  ## Check if ``pr`` is a Preserve text string.

func isByteString*(pr: Preserve): bool {.inline.} = pr.kind == pkByteString
  ## Check if ``pr`` is a Preserves byte string.

func isSymbol*(pr: Preserve): bool {.inline.} = pr.kind == pkSymbol
  ## Check if `pr` is a Preserves symbol.

func isSymbol*(pr: Preserve; sym: string|Symbol): bool {.inline.} =
  ## Check if ``pr`` is a Preserves symbol of ``sym``.
  (pr.kind == pkSymbol) and (pr.symbol == Symbol(sym))

func isRecord*(pr: Preserve): bool {.inline.} = (pr.kind == pkRecord) and (pr.record.len > 0)
  ## Check if ``pr`` is a Preserves record.

proc isSequence*(pr: Preserve): bool {.inline.} = pr.kind == pkSequence
  ## Check if ``pr`` is a Preserves sequence.

proc isSet*(pr: Preserve): bool {.inline.} = pr.kind == pkSet
  ## Check if ``pr`` is a Preserves set.

proc isDictionary*(pr: Preserve): bool {.inline.} = pr.kind == pkDictionary
  ## Check if ``pr`` is a Preserves dictionary.

func isEmbedded*[E](pr: Preserve[E]): bool {.inline.} =
  ## Check if ``pr`` is an embedded value.
  when E is void: pr.embedded # embedded Preserves
  else: pr.kind == pkEmbedded # embedded Nim

proc label*(pr: Preserve): Preserve {.inline.} =
  ## Return the label of record value.
  pr.record[pr.record.high]

proc arity*(pr: Preserve): int {.inline.} =
  ## Return the number of fields in record `pr`.
  pred(pr.record.len)

proc fields*(pr: Preserve): seq[Preserve] {.inline.} =
  ## Return the fields of a record value.
  pr.record[0..pr.record.high.pred]

iterator fields*(pr: Preserve): Preserve =
  ## Iterate the fields of a record value.
  for i in 0..<pr.record.high: yield pr.record[i]

proc unembed*[E](pr: Preserve[E]): E =
  ## Unembed an `E` value from a `Preserve[E]` value.
  if pr.kind != pkEmbedded:
    raise newException(ValueError, "not an embedded value")
  pr.embed

proc writeVarint(s: Stream; n: int) =
  var n = n
  while true:
    let c = int8(n and 0x7f)
    n = n shr 7
    if n == 0:
      s.write((char)c.char)
      break
    else:
      s.write((char)c or 0x80)

proc readVarint(s: Stream): int =
  var shift: int
  while shift < (9*8):
    let c = s.readChar.int
    result = result or ((c and 0x7f) shl shift)
    if (c and 0x80) == 0:
      break
    shift.inc 7

proc write*[E](str: Stream; pr: Preserve[E]) =
  ## Write the binary-encoding of a Preserves value to a stream.
  if pr.embedded: str.write(0x86'u8)
  case pr.kind:
  of pkBoolean:
    case pr.bool
    of false: str.write(0x80'u8)
    of true: str.write(0x81'u8)
  of pkFloat:
    str.write(0x82'u8)
    when system.cpuEndian == bigEndian:
      str.write(pr.float)
    else:
      var be: float32
      swapEndian32(be.addr, pr.float.unsafeAddr)
      str.write(be)
  of pkDouble:
    str.write(0x83'u8)
    when system.cpuEndian == bigEndian:
      str.write(pr.double)
    else:
      var be: float64
      swapEndian64(be.addr, pr.double.unsafeAddr)
      str.write(be)
  of pkSignedInteger:
    if (-3 <= pr.int) and (pr.int <= 12):
      str.write(0x90'i8 or int8(if pr.int < 0: pr.int + 16 else: pr.int))
    else:
      var bitCount = 1'u8
      if pr.int < 0:
        while ((not pr.int) shr bitCount) != 0:
          inc(bitCount)
      else:
        while (pr.int shr bitCount) != 0:
          inc(bitCount)
      var byteCount = (bitCount + 8) div 8
      str.write(0xa0'u8 or (byteCount - 1))
      proc write(n: uint8; i: BiggestInt) =
        if n > 0:
          write(n.pred, i shr 8)
          str.write(i.uint8)
      write(byteCount, pr.int)
  of pkString:
    str.write(0xb1'u8)
    str.writeVarint(pr.string.len)
    str.write(pr.string)
  of pkByteString:
    str.write(0xb2'u8)
    str.writeVarint(pr.bytes.len)
    str.write(cast[string](pr.bytes))
  of pkSymbol:
    str.write(0xb3'u8)
    str.writeVarint(pr.symbol.len)
    str.write(string pr.symbol)
  of pkRecord:
    assert(pr.record.len > 0)
    str.write(0xb4'u8)
    str.write(pr.record[pr.record.high])
    for i in 0..<pr.record.high:
      str.write(pr.record[i])
    str.write(0x84'u8)
  of pkSequence:
    str.write(0xb5'u8)
    for e in pr.sequence:
      str.write(e)
    str.write(0x84'u8)
  of pkSet:
    str.write(0xb6'u8)
    for val in pr.set.items:
      str.write(val)
    str.write(0x84'u8)
  of pkDictionary:
    str.write(0xb7'u8)
    for (key, value) in pr.dict.items:
      str.write(key)
      str.write(value)
    str.write(0x84'u8)
  of pkEmbedded:
    when not E is void:
      str.write(0x86'u8)
      str.write(pr.embed.toPreserve)

proc encode*[E](pr: Preserve[E]): seq[byte] =
  ## Return the binary-encoding of a Preserves value.
  let s = newStringStream()
  s.write pr
  s.setPosition 0
  result = cast[seq[byte]](s.readAll)

proc decodePreserves*(s: Stream; E = void): Preserve[E] =
  ## Decode a Preserves value from a binary-encoded stream.
  proc assertStream(check: bool) =
    if not check:
      raise newException(ValueError, "invalid Preserves stream")
  const endMarker = 0x84
  let tag = s.readUint8()
  case tag
  of 0x80: result = Preserve[E](kind: pkBoolean, bool: false)
  of 0x81: result = Preserve[E](kind: pkBoolean, bool: true)
  of 0x82:
    when system.cpuEndian == bigEndian:
      result = Preserve[E](kind: pkFloat, float: s.readFloat32())
    else:
      result = Preserve[E](kind: pkFloat)
      var be = s.readFloat32()
      swapEndian32(result.float.addr, be.addr)
  of 0x83:
    when system.cpuEndian == bigEndian:
      result = Preserve[E](kind: pkDouble, double: s.readFloat64())
    else:
      result = Preserve[E](kind: pkDouble)
      var be = s.readFloat64()
      swapEndian64(result.double.addr, be.addr)
  of 0x86:
    result = decodePreserves(s, E)
    result.embedded = true
  of 0xb1:
    result = Preserve[E](kind: pkString)
    let len = s.readVarint()
    result.string = s.readStr(len)
  of 0xb2:
    result = Preserve[E](kind: pkByteString)
    let len = s.readVarint()
    result.bytes = cast[seq[byte]](s.readStr(len))
  of 0xb3:
    let len = s.readVarint()
    result = Preserve[E](kind: pkSymbol, symbol: Symbol s.readStr(len))
  of 0xb4:
    result = Preserve[E](kind: pkRecord)
    var label = decodePreserves(s, E)
    while s.peekUint8() != endMarker:
      result.record.add decodePreserves(s, E)
    result.record.add(move label)
    discard s.readUint8()
  of 0xb5:
    result = Preserve[E](kind: pkSequence)
    while s.peekUint8() != endMarker:
      result.sequence.add decodePreserves(s, E)
    discard s.readUint8()
  of 0xb6:
    result = Preserve[E](kind: pkSet)
    while s.peekUint8() != endMarker:
      incl(result, decodePreserves(s, E))
    discard s.readUint8()
  of 0xb7:
    result = Preserve[E](kind: pkDictionary)
    while s.peekUint8() != endMarker:
      result[decodePreserves(s, E)] = decodePreserves(s, E)
    discard s.readUint8()
  of 0xb0:
    let len = s.readVarint()
    result = Preserve[E](kind: pkSignedInteger)
    for _ in 1..len:
      result.int = (result.int shl 8) + s.readUint8().BiggestInt
  of endMarker:
    assertStream(false)
  else:
    case 0xf0 and tag
    of 0x90:
      var n = tag.BiggestInt
      result = Preserve[E](kind: pkSignedInteger,
          int: n - (if n > 0x9c: 0xa0 else: 0x90))
    of 0xa0:
      let len = (tag.int and 0x0f) + 1
      if len > 8: raise newException(ValueError,
        "numbers wider than 64-bits not supported by this Preserves implementation")
      result = Preserve[E](kind: pkSignedInteger, int: s.readUint8().BiggestInt)
      if (result.int and 0x80) != 0: result.int.dec(0x100)
      for i in 1..<len:
        result.int = (result.int shl 8) or s.readUint8().BiggestInt
    else:
      assertStream(false)

proc decodePreserves*(s: string; E = void): Preserve[E] =
  ## Decode a string of binary-encoded Preserves.
  decodePreserves(s.newStringStream, E)

proc decodePreserves*(s: seq[byte]; E = void): Preserve[E] =
  ## Decode a byte-string of binary-encoded Preserves.
  decodePreserves(cast[string](s), E)

template preservesRecord*(label: string) {.pragma.}
  ## Serialize this object or tuple as a record.
  ## See ``toPreserve``.

proc hasPreservesRecordPragma*(T: typedesc): bool =
  ## Test if a type has a `{.preservesRecord: "…".}` pragma attached.
  hasCustomPragma(T, preservesRecord)

proc recordLabel*(T: typedesc): string =
  ## Get the record label set by a pragma on a type.
  runnableExamples:
    type Foo {.preservesRecord: "bar".} = object
      n: int
    assert recordLabel(Foo) == "bar"
  T.getCustomPragmaVal(preservesRecord)

template preservesTuple*() {.pragma.}
  ## Serialize this object or tuple as a tuple.
  ## See ``toPreserve``.

template preservesTupleTail*() {.pragma.}
  ## Serialize this object field to the end of its containing tuple.
  ## See ``toPreserve``.

proc hasPreservesTuplePragma*(T: typedesc): bool =
  ## Test if a type has a `preservesTuple` pragma attached.
  hasCustomPragma(T, preservesTuple)

template preservesDictionary*() {.pragma.}
  ## Serialize this object or tuple as a dictionary.
  ## See ``toPreserve``.

proc hasPreservesDictionaryPragma*(T: typedesc): bool =
  ## Test if a type has a `preservesDictionary` pragma attached.
  hasCustomPragma(T, preservesDictionary)

template preservesOr*() {.pragma.}
  ## Serialize this object as an ``or`` alternative.
  ## See ``toPreserve``.

template preservesLiteral*(value: typed) {.pragma.}
  ## Serialize a Preserves literal within this object.
  ## See ``toPreserve``.

template unpreservable*() {.pragma.}
  ## Pragma to forbid a type from being converted by ``toPreserve``.
  ## Useful for preventing an embeded type from being encoded
  ## as its native type.
  ## Unpreservability is asserted at runtime.

proc toPreserve*[T](x: T; E = void): Preserve[E] =
  ## Serializes ``x`` to Preserves. Can be customized by defining
  ## ``toPreserveHook(x: T; E: typedesc)`` in the calling scope.
  ## Any ``toPreserveHook`` that does not compile will be discarded;
  ## *Write tests for your hooks!*
  ##
  ## When `tracePreserves` is defined (`-d:tracePreserves`) a diagnostic
  ## trace is printing during `toPreserve`.
  when (T is Preserve[E]): result = x
  elif T is E: result = embed(x)
  elif compiles(toPreserveHook(x, E)):
    result = toPreserveHook(x, E)
  elif T is enum:
    result = toSymbol($x, E)
  elif T is seq[byte]:
    result = Preserve[E](kind: pkByteString, bytes: x)
  elif T is array | seq:
    result = Preserve[E](kind: pkSequence, sequence: newSeqOfCap[Preserve[E]](x.len))
    for v in x.items: result.sequence.add(toPreserve(v, E))
  elif T is set:
    result = Preserve[E](kind: pkSet, set: newSeqOfCap[Preserve[E]](x.len))
    for v in x.items: result.incl(toPreserve(v, E))
  elif T is bool:
    result = Preserve[E](kind: pkBoolean, bool: x)
  elif T is float32:
    result = Preserve[E](kind: pkFloat, float: x)
  elif T is float64:
    result = Preserve[E](kind: pkDouble, double: x)
  elif T is tuple:
    result = Preserve[E](kind: pkSequence,
      sequence: newSeqOfCap[Preserve[E]](tupleLen(T)))
    for xf in fields(x):
      result.sequence.add(toPreserve(xf, E))
  elif T is Ordinal:
    result = Preserve[E](kind: pkSignedInteger, int: x.ord.BiggestInt)
  elif T is ptr | ref:
    if system.`==`(x, nil): result = toSymbol("null", E)
    else: result = toPreserve(x[], E)
  elif T is string:
    result = Preserve[E](kind: pkString, string: x)
  elif T is SomeInteger:
    result = Preserve[E](kind: pkSignedInteger, int: x.BiggestInt)
  elif T is Symbol:
    result = Preserve[E](kind: pkSymbol, symbol: x)
  elif T is distinct:
    result = toPreserve(x.distinctBase, E)
  elif T is object:
    template fieldToPreserve(key: string; val: typed): Preserve {.used.} =
      when x.dot(key).hasCustomPragma(preservesLiteral):
        const lit = parsePreserves(x.dot(key).getCustomPragmaVal(preservesLiteral))
        cast[Preserve[E]](lit)
      else:
        toPreserve(val, E)
    when T.hasCustomPragma(unpreservable):
      {.error: $T & " is unpreservable".}
    elif T.hasCustomPragma(preservesOr):
      var hasKind, hasVariant: bool
      for k, v in x.fieldPairs:
        if k == "orKind":
          assert(not hasKind)
          hasKind = true
        else:
          assert(hasKind and not hasVariant)
          result = fieldToPreserve(k, v)
          hasVariant = true
    elif T.hasCustomPragma(preservesRecord):
      result = Preserve[E](kind: pkRecord)
      for k, v in x.fieldPairs:
        result.record.add(fieldToPreserve(k, v))
      result.record.add(tosymbol(T.getCustomPragmaVal(preservesRecord), E))
    elif T.hasCustomPragma(preservesTuple):
      result = initSequence[E]()
      for label, field in x.fieldPairs:
        when x.dot(label).hasCustomPragma(preservesTupleTail):
          for y in field.items:
            result.sequence.add(toPreserve(y, E))
          # TODO: what if there are fields after the tail?
        else:
          result.sequence.add(fieldToPreserve(label, field))
    elif T.hasCustomPragma(preservesDictionary):
      result = initDictionary[E]()
      for key, val in x.fieldPairs:
        result[toSymbol(key, E)] = fieldToPreserve(key, val)
    else: result = toPreserveHook(x, E)
  else: result = toPreserveHook(x, E)
    # the hook doesn't compile but produces a useful error
  trace T, " -> ", result

proc toPreserveHook*[T](set: HashSet[T]; E: typedesc): Preserve[E] =
  ## Hook for preserving ``HashSet``.
  result = Preserve[E](kind: pkSet, set: newSeqOfCap[Preserve[E]](set.len))
  for e in set: result.incl toPreserve(e, E)

proc toPreserveHook*[A, B](table: Table[A, B]|TableRef[A, B], E: typedesc): Preserve[E] =
  ## Hook for preserving ``Table``.
  result = initDictionary[E]()
  for k, v in table.pairs:
    result[toPreserve(k, E)] = toPreserve(v, E)

func containsNativeEmbeds[E](pr: Preserve[E]): bool =
  ## Check if a `Preserve[E]` is convertible to `Preserve[void]`.
  when not E is void:
    if pr.kind in compoundKinds:
      for e in pr.items:
        if e.containsNativeEmbeds:
          result = true
          break
    elif pr.kind == pkEmbedded:
      result = true

proc fromPreserve*[T, E](v: var T; pr: Preserve[E]): bool =
  ## Inplace version of `preserveTo`. Returns ``true`` on
  ## a complete match, otherwise returns ``false``.
  ## Can be customized with `fromPreserveHook[E](x: T; var pr: Preserve[E]): bool`.
  ## Any ``fromPreserveHook`` that does not compile will be discarded;
  ## *Write tests for your hooks!*
  ##
  ## When `tracePreserves` is defined (`-d:tracePreserves`) a diagnostic
  ## trace is printing during `fromPreserve`.
  # TODO: {.raises: [].}
  runnableExamples:
    type Foo {.preservesRecord: "foo".} = object
      x, y: int
    var foo: Foo
    assert(fromPreserve(foo, parsePreserves("""<foo 1 2>""")))
    assert(foo.x == 1)
    assert(foo.y == 2)
  when T is E:
    if not pr.embedded and pr.kind == pkEmbedded:
      v = pr.embed
      return true
  when T is Preserve[E]:
    v = pr
    result = true
  elif T is Preserve[void]:
    if pr.containsNativeEmbeds:
      raise newException(ValueError,
        "cannot convert Preserve value with embedded " & $E & " values")
    v = cast[T](pr)
    result = true
  elif T is Preserve:
    {.error: "cannot convert " & $T & " from " & $Preserve[E].}
  elif compiles(fromPreserveHook(v, pr)):
    result = fromPreserveHook(v, pr)
  elif T is enum:
    if pr.isSymbol:
      try:
        v = parseEnum[T](string pr.symbol)
        result = true
      except ValueError: discard
  elif T is bool:
    if pr.kind == pkBoolean:
      v = pr.bool
      result = true
  elif T is SomeInteger:
    if pr.kind == pkSignedInteger:
      v = T(pr.int)
      result = true
  elif T is seq[byte]:
    if pr.kind == pkByteString:
      v = pr.bytes
      result = true
  elif T is seq:
    if pr.kind == pkSequence:
      v.setLen(pr.len)
      result = true
      for i, e in pr.sequence:
        result = result and fromPreserve(v[i], e)
        if not result:
          v.setLen 0
          break
  elif T is float32:
    if pr.kind == pkFloat:
      v = pr.float
      result = true
  elif T is float64:
    case pr.kind
    of pkFloat:
      v = pr.float
      result = true
    of pkDouble:
      v = pr.double
      result = true
    else: discard
  elif T is Ordinal | SomeInteger:
    if pr.kind == pkSignedInteger:
      v = (T)pr.int
      result = true
  elif T is string:
    case pr.kind
    of pkString:
      v = pr.string
      result = true
    of pkSymbol:
      # loose convertability of Preserves symbol to Nim string
      v = string pr.symbol
      result = true
    else: discard
  elif T is Symbol:
    if pr.kind == pkSymbol:
      v = pr.symbol
      result = true
  elif T is distinct:
    result = fromPreserve(v.distinctBase, pr)
  elif T is tuple:
    case pr.kind
    of pkRecord, pkSequence:
      if pr.len <= tupleLen(T):
        result = true
        var i {.used.}: int
        for f in fields(v):
          if result and i < pr.len:
            result = result and fromPreserve(f, pr[i])
          inc i
    of pkDictionary:
      if tupleLen(T) ==  pr.len:
        result = true
        for key, val in fieldPairs(v):
          try: result = fromPreserve(val, pr[toSymbol(key, E)])
          except KeyError: result = false
          if not result: break
    else: discard
  elif T is ref:
    if isNil(v): new(v)
    result = fromPreserve(v[], pr)
  elif T is object:
    template fieldFromPreserve(key: string; val: typed; pr: Preserve[E]): bool {.used.} =
      when v.dot(key).hasCustomPragma(preservesLiteral):
        const lit = parsePreserves(v.dot(key).getCustomPragmaVal(preservesLiteral))
        pr == lit
      else:
        fromPreserve(val, pr)
    when T.hasCustomPragma(unpreservable):
      raiseAssert($T & " is unpreservable")
    elif T.hasCustomPragma(preservesRecord):
      if pr.isRecord and pr.label.isSymbol(T.getCustomPragmaVal(preservesRecord)):
        result = true
        var i: int
        for key, val in fieldPairs(v):
          if result and i <= pr.len:
            result = result and fieldFromPreserve(key, val, pr.record[i])
          inc i
        result = result and (i == pr.len)
    elif T.hasCustomPragma(preservesTuple):
      if pr.isSequence:
        result = true
        var i: int
        for name, field in fieldPairs(v):
          when v.dot(name).hasCustomPragma(preservesTupleTail):
            if pr.len >= i:
              setLen(v.dot(name), pr.len - i)
              var j: int
              while result and i < pr.len:
                result = result and fieldFromPreserve(name, v.dot(name)[j], pr.sequence[i])
                inc i
                inc j
          else:
            if result and i < pr.len:
              result = result and fieldFromPreserve(name, field, pr.sequence[i])
            inc i
        result = result and (i == pr.len)
    elif T.hasCustomPragma(preservesDictionary):
      if pr.isDictionary:
        result = true
        var i: int
        for key, _ in fieldPairs(v):
          let val = pr.getOrDefault(toSymbol(key, E))
          result = result and fieldFromPreserve(
            key, v.dot(key), val)
          if not result: break
          inc i
        result = result and (i == pr.len)
    elif T.hasCustomPragma(preservesOr):
      for kind in typeof(T.orKind):
        v = T(orKind: kind)
        var fieldWasFound = false
        for key, val in fieldPairs(v):
          when key != "orKind": # fieldPairs unwraps early
            result = fieldFromPreserve(key, v.dot(key), pr)
            fieldWasFound = true
            break
        if not fieldWasFound:
          # hopefully a `discard` of-branch, so discard `pr`
          result = true
        if result: break
    else:
      if pr.isDictionary:
        result = true
        var i: int
        for key, _ in fieldPairs(v):
          let val = pr.getOrDefault(toSymbol(key, E))
          result = result and fieldFromPreserve(
            key, v.dot(key), val)
          if not result: break
          inc i
        result = result and (i == pr.len)
  else:
    result = fromPreserveHook(v, pr)
      # a previous branch determined that the hook does not compile but
      # calling it here explicitly produces a reasonable compiler error
  if not result:
    trace T, " !- ", pr
  else:
    trace T, " <- ", pr

proc preserveTo*(pr: Preserve; T: typedesc): Option[T] =
  ## Reverse of `toPreserve`.
  # TODO: {.raises: [].}
  runnableExamples:
    import std/options
    type Foo {.preservesRecord: "foo".} = object
      x, y: int

    assert(parsePreserves("""<foo "abc">""").preserveTo(Foo).isNone)
    assert(parsePreserves("""<bar 1 2>""").preserveTo(Foo).isNone)
    assert(parsePreserves("""<foo 1 2>""").preserveTo(Foo).isSome)
  var v: T
  if fromPreserve(v, pr):
    result = some(move v)

proc fromPreserveHook*[T, E](v: var set[T]; pr: Preserve[E]): bool =
  ## Hook for unpreserving a `set`.
  if pr.kind == pkSet:
    reset v
    result = true
    var vv: T
    for e in pr.set:
      result = fromPreserve(vv, e)
      if result:
        v.incl vv
      else:
        reset v
        break

proc fromPreserveHook*[T, E](set: var HashSet[T]; pr: Preserve[E]): bool =
  ## Hook for preserving ``HashSet``.
  if pr.kind == pkSet:
    result = true
    set.init(pr.set.len)
    var e: T
    for pe in pr.set:
      result = fromPreserve(e, pe)
      if not result: break
      set.incl(move e)

proc fromPreserveHook*[A,B,E](t: var (Table[A,B]|TableRef[A,B]); pr: Preserve[E]): bool =
  if pr.isDictionary:
    result = true
    var a: A
    var b: B
    for (k, v) in pr.dict.items:
      result = fromPreserve(a, k) and fromPreserve(b, v)
      if not result:
        clear t
        break
      t[move a] = move b

when isMainModule:
  var t: Table[int, string]
  var pr = t.toPreserveHook(void)
  assert fromPreserveHook(t, pr)

proc apply*[E](result: var Preserve[E]; op: proc(_: var Preserve[E])) =
  proc recurse(result: var Preserve[E]) = apply(result, op)
  op(result)
  case result.kind
  of pkBoolean, pkFloat, pkDouble, pkSignedInteger, pkString, pkByteString, pkSymbol, pkEmbedded: discard
  of pkRecord:
    apply(result.record, recurse)
  of pkSequence:
    apply(result.sequence, recurse)
  of pkSet:
    apply(result.set, recurse)
  of pkDictionary:
    apply(result.dict) do (e: var DictEntry[E]):
      recurse(e.key)
      recurse(e.val)

proc mapEmbeds*(pr: sink Preserve[void]; E: typedesc): Preserve[E] =
  ## Convert `Preserve[void]` to `Preserve[E]` using `fromPreserve` for `E`.
  when E is void: {.error: "E cannot be void".}
  if pr.embedded:
    pr.embedded = false
    result = Preserve[E](kind: pkEmbedded)
    if not fromPreserve(result.embed, pr):
      raise newException(ValueError, "failed to convert " & $E & " from " & $pr)
  else:
    case pr.kind
    of pkBoolean, pkFloat, pkDouble, pkSignedInteger, pkString, pkByteString, pkSymbol:
      result = cast[Preserve[E]](pr)
    of pkRecord:
      result = Preserve[E](kind: pr.kind)
      result.record = map(pr.record) do (x: Preserve[void]) -> Preserve[E]:
        mapEmbeds(x, E)
    of pkSequence:
      result = Preserve[E](kind: pr.kind)
      result.sequence = map(pr.sequence) do (x: Preserve[void]) -> Preserve[E]:
        mapEmbeds(x, E)
    of pkSet:
      result = Preserve[E](kind: pr.kind)
      result.set = map(pr.set) do (x: Preserve[void]) -> Preserve[E]:
        mapEmbeds(x, E)
    of pkDictionary:
      result = Preserve[E](kind: pr.kind)
      result.dict = map(pr.dict) do (e: DictEntry[void]) -> DictEntry[E]:
        (mapEmbeds(e.key, E), mapEmbeds(e.val, E))
    of pkEmbedded:
      result = Preserve[E](kind: pkEmbedded)
      if not fromPreserve(result.embed, pr):
        raise newException(ValueError, "failed to convert embedded " & $E)

proc mapEmbeds*[A, B](pr: sink Preserve[A]; op: proc (v: A): B): Preserve[B] =
  ## Convert `Preserve[A]` to `Preserve[B]` using an `A → B` procedure.
  runnableExamples:
    import std/tables
    type MacGuffin = ref object
      stuff: void
    var registry = {20: new MacGuffin}.toTable
    let
      a = [ 20.embed ].toPreserve(int)
      b = mapEmbeds(a) do (i: int) -> MacGuffin:
        registry[i]
    assert typeof(b[0].unembed) is MacGuffin
  when A is Preserve: {.error: "cannot mapEmbeds from Preserve[Preserve[…]]".}
  when B is Preserve: {.error: "cannot mapEmbeds to Preserve[Preserve[…]]".}
  if pr.embedded:
    var
      e: A
      pr = pr # TODO: avoid copy
    pr.embedded = false
    if not fromPreserve(e, pr):
      raise newException(ValueError, "failed to map across embedded types")
    result = embed op(e)
  else:
    case pr.kind
    of pkBoolean, pkFloat, pkDouble, pkSignedInteger, pkString, pkByteString, pkSymbol:
      result = cast[Preserve[B]](pr)
    of pkRecord:
      result = Preserve[B](kind: pr.kind)
      result.record = map(pr.record) do (x: Preserve[A]) -> Preserve[B]:
        mapEmbeds(x, op)
    of pkSequence:
      result = Preserve[B](kind: pr.kind)
      result.sequence = map(pr.sequence) do (x: Preserve[A]) -> Preserve[B]:
        mapEmbeds(x, op)
    of pkSet:
      result = Preserve[B](kind: pr.kind)
      result.set = map(pr.set) do (x: Preserve[A]) -> Preserve[B]:
        mapEmbeds(x, op)
    of pkDictionary:
      result = Preserve[B](kind: pr.kind)
      result.dict = map(pr.dict) do (e: DictEntry[A]) -> DictEntry[B]:
        (mapEmbeds(e.key, op), mapEmbeds(e.val, op))
    of pkEmbedded:
      result = embed op(pr.embed)

proc concat[E](result: var string; pr: Preserve[E]) =
  if pr.embedded: result.add("#!")
  case pr.kind:
  of pkBoolean:
    case pr.bool
    of false: result.add "#f"
    of true: result.add "#t"
  of pkFloat:
    result.add($pr.float & "f")
  of pkDouble:
    result.add $pr.double
  of pkSignedInteger:
    result.add $pr.int
  of pkString:
    result.add escapeJson(pr.string)
  of pkByteString:
    if pr.bytes.allIt(char(it) in {' '..'!', '#'..'~'}):
      result.add("#\"")
      result.add(cast[string](pr.bytes))
      result.add('"')
    else:
      if pr.bytes.len > 64:
        result.add("#[") #]#
        result.add(base64.encode(pr.bytes))
        result.add(']')
      else:
        const alphabet = "0123456789abcdef"
        result.add("#x\"")
        for b in pr.bytes:
          result.add(alphabet[int(b shr 4)])
          result.add(alphabet[int(b and 0xf)])
        result.add('"')
  of pkSymbol:
    result.add(escapeJsonUnquoted(string pr.symbol))
  of pkRecord:
    assert(pr.record.len > 0)
    result.add('<')
    result.concat(pr.record[pr.record.high])
    for i in 0..<pr.record.high:
      result.add(' ')
      result.concat(pr.record[i])
    result.add('>')
  of pkSequence:
    result.add('[')
    for i, val in pr.sequence:
      if i > 0: result.add(' ')
      result.concat(val)
    result.add(']')
  of pkSet:
    result.add("#{")
    for val in pr.set.items:
      result.concat(val)
      result.add(' ')
    if pr.set.len > 1:
      result.setLen(result.high)
    result.add('}')
  of pkDictionary:
    result.add('{')
    var i = 0
    for (key, value) in pr.dict.items:
      if i > 0:
        result.add(' ')
      result.concat(key)
      result.add(": ")
      result.concat(value)
      if i < pr.dict.high:
        result.add(',')
      inc i
    result.add('}')
  of pkEmbedded:
    result.add("#!")
    result.add($pr.embed)

proc `$`*(pr: Preserve): string = concat(result, pr)
  ## Generate the textual representation of ``pr``.

include ./preserves/private/parse
