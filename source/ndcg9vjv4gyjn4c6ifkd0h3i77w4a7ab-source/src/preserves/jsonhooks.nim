# SPDX-FileCopyrightText: 2021 ☭ Emery Hemingway
# SPDX-License-Identifier: Unlicense

import std/[json, tables]
import ../preserves

proc toPreserveHook*(js: JsonNode; E: typedesc): Preserve[E] =
  case js.kind
  of JString:
    result = Preserve[E](kind: pkString, string: js.str)
  of JInt:
    result = Preserve[E](kind: pkSignedInteger, int: js.num)
  of JFloat:
    result = Preserve[E](kind: pkDouble, double: js.fnum)
  of JBool:
    result = case js.bval
      of false: toSymbol("false", E)
      of true: toSymbol("true", E)
  of JNull:
    result = toSymbol("null", E)
  of JObject:
    result = Preserve[E](kind: pkDictionary)
    for key, val in js.fields.pairs:
      result[Preserve[E](kind: pkString, string: key)] = toPreserveHook(val, E)
  of JArray:
    result = Preserve[E](kind: pkSequence,
        sequence: newSeq[Preserve[E]](js.elems.len))
    for i, e in js.elems:
      result.sequence[i] = toPreserveHook(e, E)

proc fromPreserveHook*[E](js: var JsonNode; prs: Preserve[E]): bool =
  case prs.kind:
  of pkBoolean:
    js = newJBool(prs.bool)
  of pkFloat:
    js = newJFloat(prs.float)
  of pkDouble:
    js = newJFloat(prs.double)
  of pkSignedInteger:
    js = newJInt(prs.int)
  of pkString:
    js = newJString(prs.string)
  of pkSymbol:
    case prs.symbol.string
    of "false":
      js = newJBool(false)
    of "true":
      js = newJBool(true)
    of "null":
      js = newJNull()
    else:
      return false
  of pkSequence:
    js = newJArray()
    js.elems.setLen(prs.sequence.len)
    for i, val in prs.sequence:
      if not fromPreserve(js.elems[i], val):
        return false
  of pkDictionary:
    js = newJObject()
    for (key, val) in prs.dict.items:
      if key.kind != pkString:
        return false
      var jsVal: JsonNode
      if not fromPreserve(jsVal, val): return false
      js[key.string] = jsVal
  else: return false
  true

proc toJsonHook*[E](pr: Preserve[E]): JsonNode =
  if not fromPreserveHook(result, pr):
    raise newException(ValueError, "cannot convert Preserves value to JSON")

proc fromJsonHook*[E](pr: var Preserve[E]; js: JsonNode) =
  pr = toPreserveHook(js, E)

when isMainModule:
  var js = JsonNode()
  var pr = js.toPreserveHook(void)
  assert fromPreserveHook(js, pr)
  fromJsonHook(pr, js)
  js = toJsonHook(pr)
