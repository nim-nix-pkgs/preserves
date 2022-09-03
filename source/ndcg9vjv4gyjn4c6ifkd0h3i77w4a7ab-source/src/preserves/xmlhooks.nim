# SPDX-FileCopyrightText: 2021 ☭ Emery Hemingway
# SPDX-License-Identifier: Unlicense

import std/[xmltree, strtabs, tables]
import ../preserves

proc toPreserveHook*(xn: XmlNode; E: typedesc): Preserve[E] =
  case xn.kind
  of xnElement:
    result = initSequence[E](xn.len + 2)
    result[0] = toSymbol(xn.tag, E)
    var attrs = initDictionary[E]()
    if not xn.attrs.isNil:
      for key, val in xn.attrs.pairs:
        attrs[toPreserve(key, E)] = toPreserve(val, E)
    result[1] = attrs
    var i = 2
    for child in xn.items:
      result[i] = toPreserveHook(child, E)
      inc i
  of xnText:
    result = initSequence[E](1)
    result[0] = toPreserve(xn.text, E)
  of xnVerbatimText:
    result = initRecord[E]("verbatim", xn.text.toPreserve(E))
  of xnComment:
    result = initRecord[E]("comment", xn.text.toPreserve(E))
  of xnCData:
    result = initRecord[E]("cdata", xn.text.toPreserve(E))
  of xnEntity:
    result = initRecord[E]("entity", xn.text.toPreserve(E))

proc fromPreserveHook*[E](xn: var XmlNode; pr: Preserve[E]): bool =
  case pr.kind:
  of pkSequence:
    if pr.len == 1 and pr[0].isString:
      xn = newText(pr[0].string)
      result = true
    elif pr.len >= 2 and pr[0].isSymbol and pr[1].isDictionary:
      result = true
      var children = newSeq[XmlNode](pr.len - 2)
      for i in 2..<pr.len:
        result = fromPreserve(children[i-2], pr[i])
        if not result: break
      var attrs: XmlAttributes
      if pr[1].len > 0:
        attrs = newStringTable()
        for key, val in pr[1].dict.items:
          if key.isString and val.isString:
            attrs[key.string] = val.string
          else:
            result = false
            break
      if result:
        xn = newXmlTree(string pr[0].symbol, children, attrs)
  of pkRecord:
    if pr.len == 1 and pr[0].isString and pr.label.isSymbol:
      result = true
      case pr.label.symbol.string:
      of "verbatim":
        xn = newVerbatimText(pr[0].string)
      of "comment":
        xn = newComment(pr[0].string)
      of "cdata":
        xn = newCData(pr[0].string)
      of "entity":
        xn = newEntity(pr[0].string)
      else:
        result = false
  else: discard

when isMainModule:
  var xn = XmlNode()
  var pr = xn.toPreserveHook(void)
  assert fromPreserveHook(xn, pr)
