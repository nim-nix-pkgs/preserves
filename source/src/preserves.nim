# SPDX-FileCopyrightText: 2021 ☭ Emery Hemingway
# SPDX-License-Identifier: Unlicense

import bigints
import std/[base64, endians, hashes, options, sets, sequtils, streams, tables, typetraits]

from std/json import escapeJson, escapeJsonUnquoted
from std/macros import hasCustomPragma, getCustomPragmaVal

type
  PreserveKind* = enum
    pkBoolean, pkFloat, pkDouble, pkSignedInteger, pkBigInteger, pkString, pkByteString, pkSymbol,
        pkRecord, pkSequence, pkSet, pkDictionary, pkEmbedded

const
  atomKinds* = {pkBoolean, pkFloat, pkDouble, pkSignedInteger, pkBigInteger, pkString, pkByteString, pkSymbol}
  compoundKinds* = {pkRecord, pkSequence, pkSet, pkDictionary}

type
  Preserve*[E = void] {.acyclic.} = object
    case kind*: PreserveKind
    of pkBoolean:
      bool*: bool
    of pkFloat:
      float*: float32
    of pkDouble:
      double*: float64
    of pkSignedInteger:
      int*: BiggestInt
    of pkBigInteger:
      bigint*: BigInt
    of pkString:
      string*: string
    of pkByteString:
      bytes*: seq[byte]
    of pkSymbol:
      symbol*: string
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
    of pkBigInteger:
      result = x.bigint == y.bigint
    of pkString:
      result = x.string == y.string
    of pkByteString:
      result = x.bytes == y.bytes
    of pkSymbol:
      result = x.symbol == y.symbol
    of pkRecord:
      result = x.record == y.record
    of pkSequence:
      for i, val in x.sequence:
        if y.sequence[i] != val: return false
      result = true
    of pkSet:
      result = x.set == y.set
    of pkDictionary:
      result = x.dict == y.dict
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
  ## Preserves have a total order over Values. Check if `x` is ordered before `y`.
  if x.embedded != y.embedded:
    result = y.embedded
  elif x.kind != y.kind:
    if x.kind == pkSignedInteger and y.kind == pkBigInteger:
      result = x.int.initBigInt < y.bigint
    elif x.kind == pkBigInteger and y.kind == pkSignedInteger:
      result = x.bigint < y.int.initBigInt
    else:
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
    of pkBigInteger:
      result = x.bigint < y.bigint
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
  of pkBigInteger:
    h = h !& hash(pr.bigint.flags)
    h = h !& hash(pr.bigint)
  of pkString:
    h = h !& hash(pr.string)
  of pkByteString:
    h = h !& hash(pr.bytes)
  of pkSymbol:
    h = h !& hash(pr.symbol)
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

proc `[]`*(pr, key: Preserve): Preserve =
  ## Select a dictionary value from ``pr``.
  if pr.kind == pkDictionary:
    for (k, v) in pr.dict:
      if key == k: return v
    raise newException(KeyError, "Key not in Preserves dictionary")
  else:
    raise newException(ValueError, "`[]` is not valid for " & $pr.kind)

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

proc `[]`*(pr: var Preserve; key: Preserve): Preserve =
  ## Select a value by `key` from the Preserves dictionary `pr`.
  for (k, v) in pr.dict.items:
    if k == key: return v
  raise newException(KeyError, "value not in Preserves dictionary")

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

proc symbol*[E](s: string): Preserve[E] {.inline.} =
  ## Create a Preserves symbol value.
  Preserve[E](kind: pkSymbol, symbol: s)

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

proc initSequence*[E](len: Natural = 0): Preserve[E] =
  ## Create a Preserves sequence value.
  Preserve[E](kind: pkSequence, sequence: newSeq[Preserve[E]](len))

proc initSet*[E](): Preserve[E] = Preserve[E](kind: pkSet)
  ## Create a Preserves set value.

proc initDictionary*[E](): Preserve[E] = Preserve[E](kind: pkDictionary)
  ## Create a Preserves dictionary value.

proc embed*[E](e: E): Preserve[E] =
  ## Create a Preserves value that embeds ``e``.
  Preserve[E](kind: pkEmbedded, embed: e)

proc mapEmbeds*[A, B](pr: Preserve[A]; op: proc (v: A): B): Preserve[B] =
  ## Convert `Preserve[A]` to `Preserve[B]` using an `A -> B` procedure.
  if pr.kind in atomKinds: result = cast[Preserve[B]](pr)
  else:
    result = Preserve[B](kind: pr.kind)
    case pr.kind
    of pkRecord:
      result.record = newSeqOfCap[Preserve[B]](pr.record.len)
      for x in pr.record:
        result.record.add mapEmbeds(x, op)
    of pkSequence:
      result.sequence = newSeqOfCap[Preserve[B]](pr.sequence.len)
      for x in pr.sequence:
        result.record.add mapEmbeds(x, op)
    of pkSet:
      for x in pr.set:
        result.set.incl mapEmbeds(x, op)
    pkDictionary:
      for k, v in pr.dict:
        result.dict.add (mapEmbeds(k, op), mapEmbeds(v, op))
    of pkEmbedded:
      result = embed op(pr.embed)
    else:
      discard

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

func isBoolean*(pr: Preserve): bool {.inline.} = pr.kind == pkBoolean
  ## Check if ``pr`` is a Preserve boolean.

func isFalse*(pr: Preserve): bool =
  ## Check if ``pr`` is equivalent to the zero-initialized ``Preserve``.
  pr.kind == pkBoolean and pr.bool == false

func isFloat*(pr: Preserve): bool {.inline.} = pr.kind == pkFloat
  ## Check if ``pr`` is a Preserve float.

func isDouble*(pr: Preserve): bool {.inline.} = pr.kind == pkDouble
  ## Check if ``pr`` is a Preserve double.

func isInteger*(pr: Preserve): bool {.inline.} = pr.kind in {pkSignedInteger, pkBigInteger}
  ## Check if ``pr`` is a Preserve double.

func isString*(pr: Preserve): bool {.inline.} = pr.kind == pkString
  ## Check if ``pr`` is a Preserve text string.

func isByteString*(pr: Preserve): bool {.inline.} = pr.kind == pkByteString
  ## Check if ``pr`` is a Preserves byte string.

func isSymbol*(pr: Preserve): bool {.inline.} = pr.kind == pkSymbol
  ## Check if `pr` is a Preserves symbol.

func isSymbol*(pr: Preserve; sym: string): bool {.inline.} =
  ## Check if ``pr`` is a Preserves symbol of ``sym``.
  (pr.kind == pkSymbol) and (pr.symbol == sym)

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
  of pkBigInteger:
    doAssert(Negative notin pr.bigint.flags, "negative big integers not implemented")
    var bytes = newSeqOfCap[uint8](pr.bigint.limbs.len * 4)
    var begun = false
    for i in countdown(pr.bigint.limbs.high, 0):
      let limb = pr.bigint.limbs[i]
      for j in countdown(24, 0, 8):
        let b = uint8(limb shr j)
        begun = begun or (b != 0)
        if begun:
          bytes.add(b)
    if bytes.len <= 16:
      str.write(0xa0'u8 or bytes.high.uint8)
    else:
      str.write(0xb0'u8)
      str.writeVarint(bytes.len)
    str.write(cast[string](bytes))
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
    str.write(pr.symbol)
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
    result = Preserve[E](kind: pkSymbol, symbol: s.readStr(len))
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
    result = Preserve[E](kind: pkBigInteger, bigint: initBigint 0)
    for _ in 1..len:
      result.bigint = (result.bigint shl 8) + s.readUint8().int32
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
      if len <= 8:
        result = Preserve[E](kind: pkSignedInteger, int: s.readUint8().BiggestInt)
        if (result.int and 0x80) != 0: result.int.dec(0x100)
        for i in 1..<len:
          result.int = (result.int shl 8) or s.readUint8().BiggestInt
      else:
        result = Preserve[E](kind: pkBigInteger)
        for i in 0..<len:
          result.bigint = (result.bigint shl 8) + s.readUint8().int32
    else:
      assertStream(false)

proc decodePreserves*(s: string; E = void): Preserve[E] =
  ## Decode a string of binary-encoded Preserves.
  decodePreserves(s.newStringStream, E)

proc decodePreserves*(s: seq[byte]; E = void): Preserve[E] =
  ## Decode a byte-string of binary-encoded Preserves.
  decodePreserves(cast[string](s), E)

template record*(label: string) {.pragma.}
  ## Serialize this object or tuple as a record. See ``toPreserve``.

template unpreservable*() {.pragma.}
  ## Pragma to forbid a type from being converted by ``toPreserve``.

proc toPreserve*[T](x: T; E = void): Preserve[E] =
  ## Serializes ``x`` to Preserves. Can be customized by defining
  ## ``toPreserveHook(x: T; E: typedesc)`` in the calling scope.
  ## Any ``toPreserveHook`` that does not compile will be discarded;
  ## *Write tests for your hooks!*
  when (T is Preserve[E]): result = x
  elif compiles(toPreserveHook(x, E)):
    result = toPreserveHook(x, E)
  elif T is Bigint:
    result = Preserve[E](kind: pkBigInteger, bigint: x)
  elif T is seq[byte]:
    result = Preserve[E](kind: pkByteString, bytes: x)
  elif T is array | seq:
    result = Preserve[E](kind: pkSequence, sequence: newSeqOfCap[Preserve[E]](x.len))
    for v in x.items: result.sequence.add(toPreserve(v, E))
  elif T is bool:
    result = Preserve[E](kind: pkBoolean, bool: x)
  elif T is distinct:
    result = toPreserve(x.distinctBase, E)
  elif T is float:
    result = Preserve[E](kind: pkFloat, float: x)
  elif T is float64:
    result = Preserve[E](kind: pkDouble, double: x)
  elif T is object | tuple:
    when T.hasCustomPragma(unpreservable): {.fatal: "unpreservable type".}
    elif T.hasCustomPragma(record):
      result = Preserve[E](kind: pkRecord)
      for _, f in x.fieldPairs: result.record.add(toPreserve(f, E))
      result.record.add(symbol[E](T.getCustomPragmaVal(record)))
    else:
      result = Preserve[E](kind: pkDictionary)
      for k, v in x.fieldPairs:
        result[symbol[E](k)] = toPreserve(v, E)
  elif T is Ordinal:
    result = Preserve[E](kind: pkSignedInteger, int: x.ord.BiggestInt)
  elif T is ptr | ref:
    if system.`==`(x, nil): result = symbol[E]("null")
    else: result = toPreserve(x[], E)
  elif T is string:
    result = Preserve[E](kind: pkString, string: x)
  elif T is SomeInteger:
    result = Preserve[E](kind: pkSignedInteger, int: x.BiggestInt)
  else:
    raiseAssert("unpreservable type" & $T)

proc toPreserveHook*[A](pr: Preserve[A]; E: typedesc): Preserve[E] =
  ## Hook for converting ``Preserve`` values with different embedded types.
  if pr.kind == pkEmbedded:
    when E is void:
      result = toPreserve(pr.embed, E)
    else:
      result = Preserve[E](pk: pr.kind, embed: (E)pr.embed)
  else:
    result = cast[Preserve[E]](pr)

proc toPreserveHook*[T](set: HashSet[T]; E: typedesc): Preserve[E] =
  ## Hook for preserving ``HashSet``.
  result = Preserve[E](kind: pkSet, set: newSeqOfCap[Preserve[E]](set.len))
  for e in set: result.incl toPreserve(e, E)

proc toPreserveHook*[A, B](table: Table[A, B]|TableRef[A, B], E: typedesc): Preserve[E] =
  ## Hook for preserving ``Table``.
  result = initDictionary[E]()
  for k, v in table.pairs: result[toPreserve(k, E)] = toPreserve(v, E)

proc fromPreserve*[T, E](v: var T; pr: Preserve[E]): bool =
  ## Inplace version of `preserveTo`. Returns ``true`` on
  ## a complete match, otherwise returns ``false``.
  ## Can be customized with `fromPreserveHook[E](x: T; var pr: Preserve[E]): bool`.
  ## Any ``fromPreserveHook`` that does not compile will be discarded;
  ## *Write tests for your hooks!*
  # TODO: {.raises: [].}
  runnableExamples:
    import preserves, preserves/parse
    type Foo {.record: "foo".} = object
      x, y: int
    var foo: Foo
    assert(fromPreserve(foo, parsePreserves("""<foo 1 2>""")))
    assert(foo.x == 1)
    assert(foo.y == 2)
  type Value = Preserve
  when T is Value:
    v = pr
    result = true
  elif T is E:
    result = pr.embed
  elif compiles(fromPreserveHook(v, pr)):
    result = fromPreserveHook(v, pr)
  elif T is Bigint:
    case pr.kind
    of pkSignedInteger:
      v = initBigint(pr.int)
      result = true
    of pkBigInteger:
      v = pr.bigint
      result = true
    else: disard
  elif T is bool:
    if pr.kind == pkBoolean:
      v = pr.bool
      result = true
  elif T is SomeInteger:
    if pr.kind == pkSignedInteger:
      v = T(pr.int)
      result = true
  elif T is float:
    if pr.kind == pkFloat:
      v = pr.float
      result = true
  elif T is seq:
    if T is seq[byte] and pr.kind == pkByteString:
      v = pr.bytes
      result = true
    elif pr.kind == pkSequence:
      v.setLen(pr.len)
      result = true
      for i, e in pr.sequence:
        result = result and fromPreserve(v[i], e)
  elif T is float64:
    case pr.kind
    of pkFloat:
      v = pr.float
      result = true
    of pkDouble:
      v = pr.double
      result = true
  elif T is object | tuple:
    case pr.kind
    of pkRecord:
      when T.hasCustomPragma(record):
        if pr.record[pr.record.high].isSymbol T.getCustomPragmaVal(record):
          result = true
          var i = 0
          for fname, field in v.fieldPairs:
            if not result or (i == pr.record.high): break
            result = result and fromPreserve(field, pr.record[i])
            inc(i)
          result = result and (i == pr.record.high) # arity equivalence check=
    of pkDictionary:
      result = true
      var fieldCount = 0
      for key, val in v.fieldPairs:
        inc fieldCount
        for (pk, pv) in pr.dict.items:
          var sym = symbol[E](key)
          if sym == pk:
            result = result and fromPreserve(val, pv)
            break
      result = result and pr.dict.len == fieldCount
    else: discard
  elif T is Ordinal | SomeInteger:
    if pr.kind == pkSignedInteger:
      v = (T)pr.int
      result = true
  elif T is ref:
    if pr != symbol[E]("null"):
      new v
      result = fromPreserve(v[], pr)
  elif T is string:
    if pr.kind == pkString:
      v = pr.string
      result = true
  elif T is distinct:
    result = fromPreserve(result.distinctBase, pr)
  else:
    raiseAssert("no conversion of type Preserve to " & $T)
  if not result: reset v

proc preserveTo*(pr: Preserve; T: typedesc): Option[T] =
  ## Reverse of `toPreserve`.
  ##
  # TODO: {.raises: [].}
  runnableExamples:
    import std/options, preserves, preserves/parse
    type Foo {.record: "foo".} = object
      x, y: int

    assert(parsePreserves("""<foo "abc">""").preserveTo(Foo).isNone)
    assert(parsePreserves("""<bar 1 2>""").preserveTo(Foo).isNone)
    assert(parsePreserves("""<foo 1 2>""").preserveTo(Foo).isSome)
  var v: T
  if fromPreserve(v, pr):
    result = some(move v)

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
    for (k, v) in pr.dict:
      result = fromPreserve(a, k) and fromPreserve(b, v)
      if not result: break
      t[move a] = move b

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
  of pkBigInteger:
    result.add $pr.bigint
  of pkString:
    result.add escapeJson(pr.string)
  of pkByteString:
    for b in pr.bytes:
      if b.char notin {'\20'..'\21', '#'..'[', ']'..'~'}:
        result.add("#[") #]#
        result.add(base64.encode(pr.bytes))
        result.add(']')
        return
    result.add("#\"")
    result.add(cast[string](pr.bytes))
    result.add('"')
  of pkSymbol:
    result.add(escapeJsonUnquoted(pr.symbol))
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
      if i > 0:
        result.add(' ')
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
      inc i
    result.add('}')
  of pkEmbedded:
    when not E is void:
      result.add("#!")
      result.add($pr.embed)

proc `$`*(pr: Preserve): string = concat(result, pr)
  ## Generate the textual representation of ``pr``.

when isMainModule:
  block:
    var t: Table[int, string]
    var pr = t.toPreserveHook(void)
    assert fromPreserveHook(t, pr)
  block:
    var h: HashSet[string]
    var pr = h.toPreserveHook(void)
    assert fromPreserveHook(h, pr)
