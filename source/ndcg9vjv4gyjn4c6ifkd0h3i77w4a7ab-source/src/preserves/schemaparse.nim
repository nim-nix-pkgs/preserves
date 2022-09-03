# SPDX-FileCopyrightText: 2021 ☭ Emery Hemingway
# SPDX-License-Identifier: Unlicense

import std/[strutils, tables]
from std/os import absolutePath, isAbsolute, getCurrentDir, parentDir

import npeg

import ../preserves, ./schema, ./pegs

type
  Value = Preserve[void]
  Definition = schema.Definition[void]
  SchemaData = schema.SchemaData[void]
  Schema = schema.Schema[void]
  Stack = seq[tuple[node: Value, pos: int]]
  ParseState = object
    schema: SchemaData
    stack: Stack
    directory: string

template takeStackAt(): seq[Value] =
  var nodes = newSeq[Value]()
  let pos = capture[0].si
  var i: int
  while i < p.stack.len and p.stack[i].pos < pos:
    inc i
  let stop = i
  while i < p.stack.len:
    nodes.add(move p.stack[i].node)
    inc i
  p.stack.setLen(stop)
  nodes

template takeStackAfter(): seq[Value] =
  var nodes = newSeq[Value]()
  let pos = capture[0].si
  var i: int
  while i < p.stack.len and p.stack[i].pos <= pos:
    inc i
  let stop = i
  while i < p.stack.len:
    nodes.add(move p.stack[i].node)
    inc i
  p.stack.setLen(stop)
  nodes

template popStack(): Value =
  assert(p.stack.len > 0, capture[0].s)
  assert(capture[0].si <= p.stack[p.stack.high].pos, capture[0].s)
  p.stack.pop.node

template pushStack(n: Value) =
  let pos = capture[0].si
  var i: int
  while i < p.stack.len and p.stack[i].pos < pos:
    inc i
  p.stack.setLen(i)
  p.stack.add((n, pos))
  assert(p.stack.len > 0, capture[0].s)

proc toSymbolLit(s: string): Value =
  initRecord(toSymbol"lit", toSymbol s)

proc match(text: string; p: var ParseState) {.gcsafe.}

const parser = peg("Schema", p: ParseState):

  Schema <- ?editorCruft * S * +(Clause * S) * !1

  Clause <- (Version | EmbeddedTypeName | Include | Definition) * S * '.'

  Version <- "version" * S * >(*Digit):
    if parseInt($1) != 1: fail()

  EmbeddedTypeName <- "embeddedType" * S * >("#f" | Ref)

  Include <- "include" * S * (>(+Alnum) | ('"' * >(@'"'))):
    let filepath =
      if isAbsolute($1): $1
      else: absolutePath($1, p.directory)
    var ip = ParseState(
      schema: move p.schema,
      directory: parentDir filepath)
    match(readFile filepath, ip)
    p.schema = move ip.schema

  Definition <- >id * S * '=' * S * (OrPattern | AndPattern | Pattern):
    if p.schema.definitions.hasKey(Symbol $1):
      raise newException(ValueError, "duplicate definition of " & $1)
    var
      node = popStack()
      def: Definition
    if not fromPreserve(def, node):
      raise newException(ValueError, $1 & ": " & $node)
    p.schema.definitions[Symbol $1] = def
    p.stack.setLen(0)

  OrPattern <- ?('/' * S) * AltPattern * +(S * '/' * S * AltPattern):
    var node = initRecord(toSymbol("or"), toPreserve takeStackAt())
    pushStack node

  AltPattern <-
      AltNamed |
      AltRecord |
      AltRef |
      AltLiteralPattern

  AltNamed <- '@' * >id * S * Pattern:
    var n = toPreserve @[toPreserve $1] & takeStackAt()
    pushStack n

  AltRecord <- '<' * >id * *(S * NamedPattern) * '>':
    var n = toPreserve @[
      toPreserve $1,
      initRecord(
        toSymbol"rec",
        toSymbolLit $1,
        initRecord(toSymbol"tuple", toPreserve takeStackAt()))]
    pushStack n

  AltRef <- Ref:
    var n = toPreserve @[toPreserve $0] & takeStackAt()
    pushStack n

  AltLiteralPattern <-
      >Preserves.Boolean |
      >Preserves.Float |
      >Preserves.Double |
      >Preserves.SignedInteger |
      >Preserves.String |
      '=' * >Preserves.Symbol:
    var id = case $1
    of "#f": "false"
    of "#t": "true"
    else: $1
    var n = toPreserve @[
      toPreserve id,
      initRecord(toSymbol"lit", parsePreserves $1)]
    pushStack n

  AndPattern <- ?('&' * S) * NamedPattern * +(S * '&' * S * NamedPattern)

  Pattern <- SimplePattern | CompoundPattern

  SimplePattern <-
      AnyPattern |
      AtomKindPattern |
      EmbeddedPattern |
      LiteralPattern |
      SequenceOfPattern |
      SetOfPattern |
      DictOfPattern |
      Ref

  AnyPattern <- "any":
    pushStack toSymbol"any"

  AtomKindPattern <- Boolean | Float | Double | SignedInteger | String | ByteString | Symbol

  Boolean <- "bool":
    pushStack initRecord(toSymbol"atom", toSymbol"Boolean")

  Float <- "float":
    pushStack initRecord(toSymbol"atom", toSymbol"Float")

  Double <- "double":
    pushStack initRecord(toSymbol"atom", toSymbol"Double")

  SignedInteger <- "int":
    pushStack initRecord(toSymbol"atom", toSymbol"SignedInteger")

  String <- "string":
    pushStack initRecord(toSymbol"atom", toSymbol"String")

  ByteString <- "bytes":
    pushStack initRecord(toSymbol"atom", toSymbol"ByteString")

  Symbol <- "symbol":
    pushStack initRecord(toSymbol"atom", toSymbol"Symbol")

  EmbeddedPattern <- "#!" * SimplePattern:
    var n = initRecord(toSymbol"embedded", popStack())
    pushStack n

  LiteralPattern <- ('=' * >symbol) | ("<<lit>" * >Preserves.Value * ">") | >nonSymbolAtom:
    pushStack initRecord(toSymbol"lit", parsePreserves($1))

  SequenceOfPattern <- '[' * S * SimplePattern * S * "..." * S * ']':
    var n = initRecord(toSymbol"seqof", popStack())
    pushStack n

  SetOfPattern <- "#{" * S * SimplePattern * S * '}':
    var n = initRecord(toSymbol"setof", popStack())
    pushStack n

  DictOfPattern <-
      '{' *
          S * SimplePattern * S * ':' * S * SimplePattern * S * "...:..." * S *
      '}':
    var
      val = popStack()
      key = popStack()
    var n = initRecord(toSymbol"dictof", key, val)
    pushStack n

  Ref <- >(Alpha * *Alnum) * *('.' * >(*Alnum)):
    var path: seq[string]
    for i in 1..<capture.len: path.add capture[i].s
    let name = pop path
    var n = initRecord(toSymbol"ref", toPreserve path, toSymbol name)
    pushStack n

  CompoundPattern <-
      RecordPattern |
      TuplePattern |
      VariableTuplePattern |
      DictionaryPattern

  RecordPattern <-
      ("<<rec>" * S * NamedPattern * *(S * NamedPattern) * '>') |
      ('<' * >Value * *(S * NamedPattern) * '>'):
    if capture.len == 2:
      var n = initRecord(toSymbol"rec",
        toSymbolLit $1,
        initRecord(toSymbol"tuple", toPreserve takeStackAfter()))
      pushStack n

  TuplePattern <-
      '[' * S * *(NamedPattern * S) * ']':
    var n = initRecord(toSymbol"tuple", toPreserve takeStackAfter())
    pushStack n

  VariableTuplePattern <-
      '[' * S * *(NamedPattern * S) * ?(Pattern * S) * "..." * S * ']':
    var fields = takeStackAfter()
    var tail = fields.pop
    tail[1] = initRecord(toSymbol"seqof", tail[1])
    var node = initRecord(toSymbol"tuplePrefix", toPreserve fields, tail)
    pushStack node

  DictionaryPattern <- '{' * S * *(>Value * S * ':' * S * NamedSimplePattern * S) * '}':
    var dict = initDictionary[void]()
    for i in countDown(pred capture.len, 1):
      let key = toSymbol capture[i].s
      dict[key] =  initRecord("named", key, popStack())
    var n = initRecord(toSymbol"dict", dict)
    pushStack n

  NamedPattern <- ('@' * >id * S * SimplePattern) | Pattern:
    if capture.len == 2:
      var n = initRecord(toSymbol"named", toSymbol $1, popStack())
      pushStack n

  NamedSimplePattern <- ('@' * >id * S * SimplePattern) | SimplePattern:
    if capture.len == 2:
      var n = initRecord(toSymbol"named", toSymbol $1, popStack())
      pushStack n

  id <- Alpha * *Alnum

  Comment <- ';' * @'\n'

  S <- *(Space | Comment)

  symbol <- Preserves.Symbol

  nonSymbolAtom <-
      Preserves.Boolean |
      Preserves.Float |
      Preserves.Double |
      Preserves.SignedInteger |
      Preserves.String |
      Preserves.ByteString

  Value <- Preserves.Value

  editorCruft <- '@' * @'\n'

proc match(text: string; p: var ParseState) =
  let match = parser.match(text, p)
  if not match.ok:
    raise newException(ValueError, "failed to parse.\n" & text[0..<match.matchMax])

proc parsePreservesSchema*(text: string; directory = getCurrentDir()): Schema =
  ## Parse a Preserves schema.
  ##
  ## Schemas in binary encoding should instead be parsed as Preserves
  ## and converted to `Schema` with `fromPreserve` or `preserveTo`.
  var p = ParseState(schema: SchemaData(), directory: directory)
  match(text, p)
  Schema(data: p.schema)

when isMainModule:
  import std/streams
  let
    scm = parsePreservesSchema(readAll stdin)
    pr = toPreserve scm
  stdout.newFileStream.write pr
