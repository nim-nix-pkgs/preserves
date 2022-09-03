# SPDX-FileCopyrightText: 2021 ☭ Emery Hemingway
# SPDX-License-Identifier: Unlicense

## NPeg parser for Preserves Schemas.
## https://preserves.gitlab.io/preserves/preserves-schema.html

import std/[parseutils, macros, strutils, tables]
from os import absolutePath, isAbsolute, parentDir

import npeg
import ../preserves, ./parse, ./pegs

type
  Value = Preserve[void]

  Stack = seq[tuple[node: SchemaNode, pos: int]]

  SchemaNodeKind* = enum
    # TODO: audit these kinds later
    snkOr,
    snkAnd,
    snkAlt, # same as snkNamed?
    snkAny,
    snkAtom,
    snkEmbedded,
    snkLiteral,
    snkSequenceOf
    snkSetOf,
    snkDictOf,
    snkRecord,
    snkTuple,
    snkVariableTuple,
    snkDictionary,
    snkNamed,
    snkRef

  AtomKind* = enum
    akBool = "bool"
    akFloat = "float"
    akDouble = "double"
    akInt = "int"
    akString = "string"
    akBytes = "bytes"
    akSymbol = "symbol"

  SchemaNode* {.acyclic.} = ref object
    case kind*: SchemaNodeKind
    of snkAlt:
      altLabel*: string
      altBranch*: SchemaNode
    of snkAny: discard
    of snkAtom:
      atom*: AtomKind
    of snkEmbedded:
      embed*: SchemaNode
    of snkLiteral:
      value*: Value
    of snkNamed:
      name*: string
      pattern*: SchemaNode
    of snkRef:
      refPath*: seq[string]
    else:
      nodes*: seq[SchemaNode]

  Schema* = ref object
    version*: int
    embeddedType*: string
    definitions*: OrderedTable[string, SchemaNode]

  ParseState = object
    filepath: string
    stack: Stack
    schema: Schema

proc add(a: SchemaNode; b: SchemaNode|seq[SchemaNode]): SchemaNode {.discardable.} =
  a.nodes.add b
  a

iterator items*(sn: SchemaNode): SchemaNode =
  case sn.kind
  of snkAny, snkAtom, snkLiteral, snkRef: discard
  of snkAlt:
    yield sn.altBranch
  of snkEmbedded:
    yield sn.embed
  of snkNamed:
    yield sn.pattern
  else:
    for i in 0..sn.nodes.high:
      yield sn.nodes[i]

proc `$`*(n: SchemaNode): string =
  case n.kind
  of snkOr:
    result.add "/ "
    result.add join(n.nodes, " / ")
  of snkAnd:
    result.add "& "
    result.add join(n.nodes, " & ")
  of snkAlt:
    case n.altBranch.kind
    of snkRecord, snkRef:
      result.add $n.altBranch
    of snkLiteral:
      result.add '='
      result.add $n.altBranch
    else:
      result.add '@'
      result.add n.altLabel
      result.add ' '
      result.add $n.altBranch
  of snkAny: result.add "any"
  of snkAtom: result.add $n.atom
  of snkEmbedded:
    result.add "#!" & $n.embed
  of snkLiteral:
    case n.value.kind
    of pkBoolean, pkFloat, pkDouble, pkSignedInteger, pkString, pkByteString:
      result.add $n.value
    else:
      result.add "<<lit>" & $n.value & ">"
  of snkSequenceOf:
    result.add "[ "
    result.add $n.nodes[0]
    result.add " ... ]"
  of snkSetOf:
    result.add "#{"
    result.add n.nodes.join(" ")
    result.add '}'
  of snkDictOf:
    result.add '{'
    result.add $n.nodes[0]
    result.add " : "
    result.add $n.nodes[1]
    result.add " ...:...}"
  of snkRecord:
    result.add '<'
    if n.nodes[0].kind == snkLiteral and n.nodes[0].value.kind == pkSymbol:
      result.add n.nodes[0].value.symbol
      for i in 1..n.nodes.high:
        result.add ' '
        result.add $n.nodes[i]
    else:
      result.add join(n.nodes, " ")
    result.add '>'
  of snkTuple:
    result.add '['
    result.add join(n.nodes, " ")
    result.add ']'
  of snkVariableTuple:
    result.add '['
    result.add join(n.nodes, " ")
    result.add " ...]"
  of snkDictionary:
    result.add '{'
    for i in countup(0, n.nodes.high, 2):
      result.add $n.nodes[i]
      result.add ": "
      result.add $n.nodes[i.succ]
      result.add ' '
    result.add '}'
  of snkNamed:
    result.add '@'
    result.add n.name
    result.add ' '
    result.add $n.pattern
  of snkRef:
    result.add join(n.refPath, ".")

proc `$`*(scm: Schema): string =
  result.add("version = $1 .\n" % $scm.version)
  if scm.embeddedType != "":
    result.add("EmbeddedTypeName = $1 .\n" % scm.embeddedType)
  for n, d in scm.definitions.pairs:
    result.add("$1 = $2 .\n" % [n, $d])

proc `$`(stack: Stack): string =
  for f in stack:
    result.add "\n"
    result.add $f.pos
    result.add ": "
    result.add $f.node

proc match(text: string; p: var ParseState) {.gcsafe.}

template newSchemaNode(snk: SchemaNodeKind): SchemaNode =
  SchemaNode(kind: snk)

template takeStackAt(): seq[SchemaNode] =
  var nodes = newSeq[SchemaNode]()
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

template takeStackAfter(): seq[SchemaNode] =
  var nodes = newSeq[SchemaNode]()
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

template popStack(): SchemaNode =
  assert(p.stack.len > 0, capture[0].s)
  assert(capture[0].si <= p.stack[p.stack.high].pos, capture[0].s)
  p.stack.pop.node

template pushStack(n: SchemaNode) =
  let pos = capture[0].si
  var i: int
  while i < p.stack.len and p.stack[i].pos < pos:
    inc i
  p.stack.setLen(i)
  p.stack.add((n, pos))
  assert(p.stack.len > 0, capture[0].s)

const parser = peg("Schema", p: ParseState):

  Schema <- ?editorCruft * S * +(Clause * S) * !1

  Clause <- (Version | EmbeddedTypeName | Include | Definition) * S * '.'

  Version <- "version" * S * >(*Digit):
    discard parseInt($1, p.schema.version)
    if p.schema.version != 1: fail()

  EmbeddedTypeName <- "embeddedType" * S * >("#f" | Ref):
    if p.schema.embeddedType != "": fail()
    if $1 != "#f": p.schema.embeddedType = $1

  Include <- "include" * S * (>(+Alnum) | ('"' * >(@'"'))):
    var ip = ParseState(
      schema: p.schema,
      filepath:
        if isAbsolute($1): $1
        else: absolutePath($1, p.filepath.parentDir))
    ip.filePath.setLen(ip.filePath.high)
    match(readFile ip.filepath, ip)

  Definition <- >id * S * '=' * S * (OrPattern | AndPattern | Pattern):
    if p.schema.definitions.hasKey $1:
      raise newException(ValueError, "duplicate definition of " & $1)
    p.schema.definitions[$1] = popStack()
    p.stack.setLen(0)

  OrPattern <- ?('/' * S) * AltPattern * +(S * '/' * S * AltPattern):
    let n = snkOr.newSchemaNode.add(takeStackAt())
    assert(n.nodes[0].kind == snkAlt, $n.nodes[0])
    pushStack n

  AltPattern <-
      AltNamed |
      AltRecord |
      AltRef |
      AltLiteralPattern

  AltNamed <- '@' * >id * S * Pattern:
    let n = SchemaNode(kind: snkAlt, altLabel: $1, altBranch: popStack())
    pushStack n

  AltRecord <- '<' * >id * *(S * NamedPattern) * '>':
    let
      id = SchemaNode(kind: snkLiteral, value: symbol[void]($1))
      n = SchemaNode(kind: snkAlt,
          altLabel: $1,
          altBranch: snkRecord.newSchemaNode.add(id).add(takeStackAt()))
    pushStack n

  AltRef <- Ref:
    let n = SchemaNode(kind: snkAlt, altLabel: $0, altBranch: popStack())
    pushStack n

  AltLiteralPattern <-
      >Preserves.Boolean |
      >Preserves.Float |
      >Preserves.Double |
      >Preserves.SignedInteger |
      >Preserves.String |
      '=' * >Preserves.Symbol:
    let
      branch = SchemaNode(kind: snkLiteral, value: parsePreserves($1))
      label = case branch.value.kind
        of pkBoolean:
          if branch.value.bool: "true" else: "false"
        else: $branch.value
          # TODO: numbers?
    pushStack SchemaNode(kind: snkAlt, altLabel: label, altBranch: branch)

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
    let n = SchemaNode(kind: snkAny)
    pushStack n

  AtomKindPattern <-
      "bool" |
      "float" |
      "double" |
      "int" |
      "string" |
      "bytes" |
      "symbol":
    let n = SchemaNode(kind: snkAtom)
    case $0
    of "bool": n.atom = akBool
    of "float": n.atom = akFloat
    of "double": n.atom = akDouble
    of "int": n.atom = akInt
    of "string": n.atom = akString
    of "bytes": n.atom = akBytes
    of "symbol": n.atom = akSymbol
    pushStack n

  EmbeddedPattern <- "#!" * SimplePattern:
    let n = SchemaNode(kind: snkEmbedded, embed: popStack())
    pushStack n

  LiteralPattern <- ('=' * >symbol) | ("<<lit>" * >Preserves.Value * ">") | >nonSymbolAtom:
    let n = SchemaNode(
        kind: snkLiteral,
        value: parsePreserves($1))
    pushStack n

  SequenceOfPattern <- '[' * S * SimplePattern * S * "..." * S * ']':
    let n = newSchemaNode(snkSequenceOf).add(takeStackAfter())
    pushStack n

  SetOfPattern <- "#{" * SimplePattern * '}'

  DictOfPattern <-
      '{' *
          S * SimplePattern * S * ':' * S * SimplePattern * S * "...:..." * S *
      '}':
    let n = newSchemaNode(snkDictOf).add(takeStackAfter())
    assert(n.nodes.len == 2, $n.nodes)
    pushStack n

  Ref <- >(Alpha * *Alnum) * *('.' * >(*Alnum)):
    let n = SchemaNode(kind: snkRef)
    for i in 1..<capture.len: n.refPath.add capture[i].s
    pushStack n

  CompoundPattern <-
      RecordPattern |
      TuplePattern |
      VariableTuplePattern |
      DictionaryPattern

  RecordPattern <-
      ("<<rec>" * S * NamedPattern * *(S * NamedPattern) * '>') |
      ('<' * >Value * *(S * NamedPattern) * '>'):
    let n = newSchemaNode(snkRecord).add(takeStackAfter())
    pushStack n

  TuplePattern <-
      '[' * S * *(NamedPattern * S) * ']':
    var n = SchemaNode(kind: snkTuple)
    for frame in p.stack.mitems:
      if frame.pos > capture[0].si:
        n.nodes.add(move frame.node)
    pushStack n

  VariableTuplePattern <-
      '[' * S * *(NamedPattern * S) * ?(Pattern * S) * "..." * S * ']':
    var n = SchemaNode(kind: snkVariableTuple)
    for frame in p.stack.mitems:
      if frame.pos > capture[0].si:
        n.nodes.add(move frame.node)
    pushStack n

  DictionaryPattern <- '{' * S * *(Value * S * ':' * S * NamedSimplePattern * S) * '}':
    var n = SchemaNode(kind: snkDictionary)
    for frame in p.stack.mitems:
      if frame.pos > capture[0].si:
        n.nodes.add(move frame.node)
    pushStack n

  NamedPattern <- ('@' * >id * S * SimplePattern) | Pattern:
    if capture.len == 2:
      var n = SchemaNode(
          kind: snkNamed, name: $1, pattern: popStack())
      pushStack n

  NamedSimplePattern <- ('@' * >id * S * SimplePattern) | SimplePattern:
    if capture.len == 2:
      var n = SchemaNode(
          kind: snkNamed, name: $1, pattern: popStack())
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

  Value <- Preserves.Value:
    pushStack SchemaNode(
        kind: snkLiteral,
        value: parsePreserves($0))

  editorCruft <- '@' * @'\n'

proc match(text: string; p: var ParseState) =
  let match = parser.match(text, p)
  if not match.ok:
    raise newException(ValueError, "failed to parse " & p.filepath & ":\n" & text[0..<match.matchMax])

proc parsePreservesSchema*(text, filepath: string): Schema =
  ## Parse a Preserves schema into an abstract syntax tree represented as a `Preserve`.
  var p = ParseState(filepath: filepath)
  new p.schema
  match(text, p)
  result = p.schema
  if result.version != 1:
    raise newException(ValueError, "missing or invalid Preserves schema version")
