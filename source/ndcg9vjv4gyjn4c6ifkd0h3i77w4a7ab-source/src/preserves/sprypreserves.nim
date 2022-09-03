# SPDX-FileCopyrightText: ☭ 2021 Emery Hemingway
# SPDX-License-Identifier: Unlicense

import std/[sequtils, tables]

import spryvm/spryvm

import preserves

type
  PreservesNode* = ref object of Value
    preserve: Preserve[void]
  EmbeddedNode* = ref object of PreservesNode
  ByteStringNode* = ref object of StringVal
  RecordNode* = ref object of Blok
  SetNode = ref object of PreservesNode

method eval*(self: PreservesNode; spry: Interpreter): Node =
  self

method `$`*(self: PreservesNode): string =
  $self.preserve

method typeName*(self: PreservesNode): string =
  "preserves-value"

method typeName*(self: EmbeddedNode): string =
  "preserves-embedded-value"

method typeName*(self: ByteStringNode): string =
  "preserves-bytestring"

method typeName*(self: RecordNode): string =
  "preserves-record"

method typeName*(self: SetNode): string =
  "preserves-set"

proc toSpry(pr: Preserve[void], spry: Interpreter): Node =
  if pr.embedded:
    result = EmbeddedNode(preserve: pr)
      # TODO: need to be able to manipulate these
  else:
    case pr.kind
    of pkBoolean:
      result = boolVal(pr.bool, spry)
    of pkFloat:
      result = newValue(pr.float)
    of pkDouble:
      result = newValue(pr.double)
    of pkSignedInteger:
      result = newValue(int pr.int)
    of pkString:
      result = newValue(pr.string)
    of pkByteString:
      result = ByteStringNode(value: cast[string](pr.bytes))
    of pkSymbol:
      result =
        if pr.symbol == "null": newNilVal()
        else: newLitWord(spry, pr.symbol)
    of pkRecord:
      var comp = RecordNode()
      proc f(pr: Preserve[void]): Node = toSpry(pr, spry)
      comp.nodes = map(pr.record, f)
      result = comp
    of pkSequence:
      var blk = newBlok()
      for e in pr.sequence: blk.add toSpry(e, spry)
      result = blk
    of pkSet:
      result = SetNode(preserve: pr)
    of pkDictionary:
      var map = newMap()
      for (key, val) in pr.dict.items:
        map[toSpry(key, spry)] = toSpry(val, spry)
      result = map
    of pkEmbedded:
      result = EmbeddedNode(preserve: pr)

proc toPreserveHook*(node: Node; E: typedesc): Preserve[E] =
  if node of PreservesNode:
    result = PreservesNode(node).preserve
  elif node of RecordNode:
    result = Preserve[E](kind: pkRecord)
    var comp = RecordNode(node)
    proc f(child: Node): Preserve[void] = toPreserve(child, void)
    result.record = map(comp.nodes, f)
  elif node of ByteStringNode:
    result = toPreserve(cast[seq[byte]](ByteStringNode(node).value), E)
  elif node of Blok:
    var blk = Blok(node)
    result = initSequence[E](blk.nodes.len)
    for i, child in blk.nodes: result.sequence[i] = toPreserve(child, E)
  elif node of Map:
    result = initDictionary[E]()
    for key, val in Map(node).bindings:
      result[toPreserve(key, E)] = toPreserve(val, E)
  elif node of StringVal:
    result = toPreserve(StringVal(node).value, E)
  elif node of LitWord:
    result = toSymbol(LitWord(node).word, E)
  elif node of IntVal:
    result = toPreserve(IntVal(node).value, E)
  elif node of FloatVal:
    result = toPreserve(FloatVal(node).value, E)
  elif node of BoolVal:
    result = toPreserve(BoolVal(node).value, E)
  else: # node of NilVal:
    result = toSymbol("null", E)

when isMainModule:
  var
    node: Node
    pr = toPreserveHook(node, void)

proc addPreserves*(spry: Interpreter) =
  nimFunc("parsePreserves"):
    let node = evalArg(spry)
    if node of StringVal:
      let str = StringVal(node).value
      result = PreservesNode(preserve: parsePreserves(str))

  nimFunc("decodePreserves"):
    let node = evalArg(spry)
    if node of StringVal:
      let str = StringVal(node).value
      result = PreservesNode(preserve: decodePreserves(cast[seq[byte]](str)))

  nimMeth("encodePreserves"):
    let node = evalArgInfix(spry)
    if node of PreservesNode:
      var bin = encode PreservesNode(node).preserve
      result = newValue(cast[string](bin))

  nimFunc("fromPreserves"):
    let node = evalArg(spry)
    if node of PreservesNode:
      let pr = PreservesNode(node).preserve
      return toSpry(pr, spry)

  nimMeth("toPreserves"):
    let node = evalArgInfix(spry)
    PreservesNode(preserve: node.toPreserve)

  nimMeth("arity"):
    let node = evalArgInfix(spry)
    if node of RecordNode:
      return newValue(pred SeqComposite(node).nodes.len)

  nimMeth("label"):
    let node = evalArgInfix(spry)
    if node of RecordNode:
      let rec = RecordNode(node)
      return rec.nodes[rec.nodes.high]
