# SPDX-FileCopyrightText: 2021 ☭ Emery Hemingway
# SPDX-License-Identifier: Unlicense

import std/[os, strutils, sets, tables]

import compiler/[ast, idents, renderer, lineinfos]

import ../../preserves, ../schemas

type
  Value = Preserve[void]
  TypeSpec = tuple[node: PNode, embeddable: bool]
  TypeTable = OrderedTable[string, TypeSpec]

proc add(parent, child: PNode): PNode {.discardable.} =
  parent.sons.add child
  parent

proc add(parent: PNode; children: varargs[PNode]): PNode {.discardable.} =
  parent.sons.add children
  parent

proc child(sn: SchemaNode): SchemaNode =
  assert(sn.nodes.len == 1)
  sn.nodes[0]

proc nn(kind: TNodeKind; children: varargs[PNode]): PNode =
  result = newNode(kind)
  result.sons.add(children)

proc nn(kind: TNodeKind; child: PNode): PNode =
  result = newNode(kind)
  result.sons.add(child)

proc ident(s: string): PNode =
  newIdentNode(PIdent(s: s), TLineInfo())

proc accQuote(n: PNode): Pnode =
  nkAccQuoted.newNode.add(n)

proc ident(sn: SchemaNode): PNode =
  var s: string
  case sn.kind
  of snkAlt:
    s = sn.altLabel.nimIdentNormalize
    s[0] = s[0].toLowerAscii
  of snkLiteral: s = $sn.value
  of snkRecord:
    s = sn.nodes[0].value.symbol
  of snkNamed:
    s = sn.name
  of snkDictionary, snkVariableTuple:
    s = "data"
  else:
    raiseAssert("no ident for " & $sn.kind & " " & $sn)
  s.ident.accQuote

proc parameterize(node: PNode; embeddable: bool): PNode =
  if embeddable: nn(nkBracketExpr, node, ident"E")
  else: node

proc parameterize(spec: TypeSpec): PNode =
  parameterize(spec.node, spec.embeddable)

proc isPreserve(n: PNode): bool =
  n.kind == nkBracketExpr and
    n.renderTree == "Preserve[E]"

proc preserveIdent(): Pnode =
  nn(nkBracketExpr, ident"Preserve", ident"E")

proc orEmbed(x: var TypeSpec; y: TypeSpec) =
  x.embeddable = x.embeddable or y.embeddable

proc isEmbeddable(scm: Schema; sn: SchemaNode; seen: var HashSet[string]): bool =
  case sn.kind
  of snkAtom, snkLiteral: discard
  of snkAlt:
    result = isEmbeddable(scm, sn.altBranch, seen)
  of snkAny: result = true
  of snkRef:
    if sn.refPath.len == 1:
      let name = sn.refPath[0]
      if name notin seen: # loop detection
        seen.incl name
        result = isEmbeddable(scm, scm.definitions[name], seen)
      else:
        result = false
    # TODO: cross-module types
  of snkEmbedded:
    result = isEmbeddable(scm, sn.embed, seen)
  of snkNamed:
    result = isEmbeddable(scm, sn.pattern, seen)
  else:
    for bn in sn.nodes:
      result = isEmbeddable(scm, bn, seen)
      if result: break

proc isEmbeddable(scm: Schema; sn: SchemaNode): bool =
  var seen: HashSet[string]
  isEmbeddable(scm, sn, seen)

proc isConst(scm: Schema; sn: SchemaNode): bool =
  case sn.kind
  of snkLiteral: result = true
  of snkRef:
    if sn.refPath.len == 1:
      result = isConst(scm, scm.definitions[sn.refPath[0]])
  else: discard

proc isSymbolEnum(scm: Schema; sn: SchemaNode): bool =
  case sn.kind
  of snkRef:
    if sn.refPath.len == 1:
      result = isSymbolEnum(scm, scm.definitions[sn.refPath[0]])
  of snkOr:
    for bn in sn.nodes:
      if bn.altBranch.kind != snkLiteral or
          bn.altBranch.value.kind != pkSymbol:
        return false
    result = true
  else: discard

proc typeIdent(scm: Schema; sn: SchemaNode): TypeSpec =
  case sn.kind
  of snkAtom:
    case sn.atom
    of akBool: (ident"bool", false)
    of akFloat: (ident"float32", false)
    of akDouble: (ident"float64", false)
    of akInt: (ident"BiggestInt", false)
    of akString: (ident"string", false)
    of akBytes: (nn(nkBracketExpr, ident"seq", ident"byte"), false)
    of akSymbol: (ident"string", false) # TODO: distinct string type for symbols?
  of snkNamed:
    typeIdent(scm, sn.pattern)
  of snkRef:
    var id = ident sn.refPath[sn.refPath.high]
    for i in countDown(sn.refPath.high.pred, 0):
      id = nn(nkDotExpr, ident(sn.refPath[i]), id)
    (id, isEmbeddable(scm, sn))
  else:
    (preserveIdent(), true)

proc toExport(n: sink PNode): PNode =
  nkPostFix.newNode.add(ident"*", n)

proc newEmpty(): PNode = newNode(nkEmpty)

proc literal(scm: Schema; sn: SchemaNode): Value =
  case sn.kind
  of snkLiteral: result = sn.value
  of snkRef:
    if sn.refPath.len == 1:
      result = literal(scm, scm.definitions[sn.refPath[0]])
    else:
      raiseAssert("not convertable to a literal: " & $sn)
  else:
    raiseAssert("not convertable to a literal: " & $sn)

proc toEnumTy(sn: SchemaNode): PNode =
  result = nkEnumTy.newNode.add newEmpty()
  for bn in sn.nodes:
    result.add bn.altLabel.nimIdentNormalize.ident.accQuote

proc toEnumDef(name: string; sn: SchemaNode): PNode =
  nkTypeDef.newNode.add(
    nkPragmaExpr.newNode.add(
      name.ident.toExport,
      nkPragma.newNode.add(ident"pure")),
      newEmpty(),
      sn.toEnumTy)

proc embeddingParams(embeddable: bool): PNode =
  if embeddable:
    nn(nkGenericParams, nn(nkIdentDefs, ident"E", newEmpty(), ident"void"))
  else:
    newEmpty()

proc identDef(sn: SchemaNode; a, b: PNode; embeddable: bool): PNode =
  if embeddable and b.kind != nkBracketExpr:
    nn(nkIdentDefs, a, nn(nkBracketExpr, b, ident"E"), newEmpty())
  else:
    nn(nkIdentDefs, a, b, newEmpty())

proc identDef(sn: SchemaNode; l: PNode; ts: TypeSpec): PNode =
  identDef(sn, l, ts.node, ts.embeddable)

proc typeDef(sn: SchemaNode; name: string; ty: PNode; embeddable: bool): PNode =
  case sn.kind
  of snkRecord:
    nn(nkTypeDef,
      nn(nkPragmaExpr,
      name.ident.toExport,
      nn(nkPragma,
        nn(nkExprColonExpr,
          ident"record",
          PNode(kind: nkStrLit, strVal: sn.nodes[0].value.symbol)))),
      embeddingParams(embeddable),
      ty)
  else:
    nn(nkTypeDef, name.ident.toExport, embeddingParams(embeddable), ty)

proc nimTypeOf(scm: Schema; known: var TypeTable; sn: SchemaNode; name = ""):
    TypeSpec =
  if name in known: return known[name]
  case sn.kind
  of snkOr:
    if isSymbolEnum(scm, sn):
      result.node = sn.toEnumTy
    else:
      let
        enumName = name.nimIdentNormalize & "Kind"
        enumIdent = ident(enumName)
      if enumName notin known:
        known[enumName] = (toEnumDef(enumName, sn), false)
      let recCase = nkRecCase.newNode.add(
        nkIdentDefs.newNode.add(
          "kind".ident.toExport,
          enumName.ident,
          newEmpty()))
      for bn in sn.nodes:
        assert(bn.kind == snkAlt, $bn.kind)
        doAssert(name != "", " no name for " & $sn)
        var memberType: TypeSpec
        if bn.altbranch.kind == snkRef:
          memberType = typeIdent(scm, bn.altBranch)
        else:
          let memberTypeName = name & bn.altLabel.nimIdentNormalize
          memberType.node = ident memberTypeName
          let ty = nimTypeOf(scm, known, bn.altBranch, memberTypeName)
          orEmbed memberType, ty
          if memberTypeName notin known:
            known[memberTypeName] = (
              typeDef(bn.altBranch, memberTypeName, ty.node, ty.embeddable),
              ty.embeddable)
        orEmbed result, memberType
        var recList = nkRecList.newNode
        case bn.altBranch.kind
        of snkRecord:
          case bn.altBranch.nodes.len
          of 0, 1: discard
          of 2:
            if not isConst(scm, bn.altBranch.nodes[1]):
              let label = bn.ident
              let branch = typeIdent(scm, bn.altBranch.nodes[1])
              orEmbed result, branch
              recList.add identDef(bn, label.toExport, branch)
          else:
            recList.add identDef(bn, bn.ident.toExport, memberType)
        else:
          if isConst(scm, bn.altBranch):
            recList.add nkDiscardStmt.newNode.add(newEmpty())
          else:
            recList.add identDef(bn, bn.ident.toExport, memberType)
        let disc = nkDotExpr.newNode.add(
          enumIdent, bn.altLabel.nimIdentNormalize.ident.accQuote)
        if recList.len == 0:
          recList.add identDef(bn, bn.ident.toExport, memberType)
        recCase.add nkOfBranch.newNode.add(disc, recList)
      result.node = nn(nkRefTy, nn(nkObjectTy,
        newEmpty(),
        newEmpty(),
        nn(nkRecList, recCase)))
  of snkAny:
    result = (ident"Preserve", true)
  of snkAtom:
    result = typeIdent(scm, sn)
  of snkEmbedded:
    result = nimTypeOf(scm, known, sn.embed)
  of snkLiteral:
    result.node = case sn.value.kind # nearly verbatim from ../../preserves/src/preserves.nim
    of pkBoolean: ident"bool"
    of pkFloat: ident"float32"
    of pkDouble: ident"float64"
    of pkSignedInteger: ident"BiggestInt"
    of pkBigInteger: ident"BigInt"
    of pkString: ident"string"
    of pkByteString: nn(
      nkBracketExpr, ident"seq", ident"byte")
    of pkSymbol: ident"string"
    of pkRecord: preserveIdent()
    of pkSequence: nn(
      nkBracketExpr, ident"seq", preserveIdent())
    of pkSet: nn(
      nkBracketExpr, ident"HashSet", preserveIdent())
    of pkDictionary: nn(
      nkBracketExpr, ident"TableRef", preserveIdent(), preserveIdent())
    of pkEmbedded:
      raiseAssert "this should never happen"
  of snkSequenceOf:
    result = nimTypeOf(scm, known, sn.child)
    result.node = nkBracketExpr.newNode.add(
        ident"seq",
        parameterize(result))
  of snkSetOf:
    result = nimTypeOf(scm, known, sn.child)
    result.node = nkBracketExpr.newNode.add(
        ident"HashedSet",
        parameterize(result))
  of snkDictOf:
    let
      key = nimTypeOf(scm, known, sn.nodes[0])
      val = nimTypeOf(scm, known, sn.nodes[1])
    orEmbed result, key
    orEmbed result, val
    result.node = nkBracketExpr.newNode.add(
      ident"TableRef", parameterize(key), parameterize(val))
  of snkRecord:
    case sn.nodes.len
    of 0, 1:
      result.node = nn(nkObjectTy,
        newEmpty(),
        newEmpty(),
        nn(nkRecList, nn(nkDiscardStmt, newEmpty())))
    else:
      let recList = nkRecList.newNode()
      for i, field in sn.nodes:
        if i > 0:
          let
            id = field.ident
            fieldType = nimTypeOf(scm, known, field, $id)
          orEmbed result, fieldType
          recList.add identDef(sn, id.toExport, fieldType)
      result.node = nn(nkRefTy, nn(nkObjectTy,
        newEmpty(),
        newEmpty(),
        recList))
  of snkTuple:
    result.node = nkTupleTy.newNode
    for tn in sn.nodes:
      if not isConst(scm, sn):
        let fieldType = nimTypeOf(scm, known, tn)
        orEmbed result, fieldType
        result.node.add identDef(sn, tn.ident, fieldType)
  of snkVariableTuple:
    result.node = nkTupleTy.newNode
    for i, tn in sn.nodes:
      if not isConst(scm, sn):
        let fieldType = nimTypeOf(scm, known, tn)
        orEmbed result, fieldType
        if i == sn.nodes.high:
          result.node.add identDef(
            tn,
            tn.ident,
            nn(nkBracketExpr, ident"seq", fieldType.parameterize),
            fieldType.embeddable)
        else:
          result.node.add identDef(tn, tn.ident, fieldType)
  of snkDictionary:
    result.node = nkTupleTy.newNode
    for i in countup(0, sn.nodes.high, 2):
      let id = ident(sn.nodes[i+0])
      let fieldType = nimTypeOf(scm, known, sn.nodes[i+1], $id)
      orEmbed result, fieldType
      result.node.add identDef(sn.nodes[i+1], id, fieldType)
  of snkNamed:
    result = nimTypeOf(scm, known, sn.pattern, name)
  of snkRef:
    result = typeIdent(scm, sn)
  else:
    result.node = nkCommentStmt.newNode
    result.node.comment = result.node.comment &
      "Missing type generator for " & $sn.kind & " " & $sn

proc exportIdent(id: string): PNode = nn(nkPostFix, ident"*", ident(id))

proc generateConstProcs(result: var seq[PNode]; scm: Schema, name: string; def: SchemaNode) =
  case def.kind
  of snkLiteral:
    var stmts = nn(nkStmtList)
    case def.value.kind
    of pkSignedInteger:
      discard stmts.add newIntNode(nkIntLit, def.value.int)
    of pkSymbol:
      discard stmts.add nn(nkCall,
        nn(nkBracketExpr, ident"symbol", ident"E"),
        PNode(kind: nkStrLit, strVal: def.value.symbol))
    else:
      raiseAssert("conversion of " & $def & " to a Nim literal is not implemented")
    var procId = name
    procId[0] = procId[0].toLowerAscii
    let constProc= nn(nkProcDef,
      exportIdent(procId),
      newEmpty(),
      nn(nkGenericParams, nn(nkIdentDefs, ident"E", newEmpty(), ident"void")),
      nn(nkFormalParams, preserveIdent()),
      newEmpty(),
      newEmpty(),
      stmts)
    constProc.comment = "``" & $def & "``"
    result.add constProc
  else: discard

proc nimLit(scm: Schema; sn: SchemaNode): PNode =
  assert(sn.kind == snkLiteral, $sn)
  case sn.value.kind
  of pkSymbol:
    nn(nkCall,
      nn(nkBracketExpr, ident"symbol", ident"E"),
      PNode(kind: nkStrLit, strVal: sn.value.symbol))
  else:
    raiseAssert("no Nim literal for " & $sn)

proc literalToPreserveCall(pr: Preserve): PNode =
  var prConstr = nn(nkObjConstr, preserveIdent())
  proc constr(kind, field: string; lit: PNode) =
    prConstr.add nn(nkExprColonExpr, ident"kind", ident(kind))
    prConstr.add nn(nkExprColonExpr, ident(field), lit)
  case pr.kind
  of pkBoolean:
    constr($pr.kind, "bool", if pr.bool: ident"true" else: ident"false")
  of pkFloat:
    constr($pr.kind, "float", newFloatNode(nkFloat32Lit, pr.float))
  of pkDouble:
    constr($pr.kind, "double", newFloatNode(nkFloat64Lit, pr.double))
  of pkSignedInteger:
    constr($pr.kind, "int", newIntNode(nkInt64Lit, pr.int))
  of pkString:
    constr($pr.kind, "string", newStrNode(nkTripleStrLit, pr.string))
  of pkByteString:
    return nn(nkCall, ident"parsePreserves", newStrNode(nkTripleStrLit, $pr))
  of pkSymbol:
    constr($pr.kind, "symbol", newStrNode(nkStrLit, pr.symbol))
  else:
    raise newException(ValueError, "refusing to convert to a literal: " & $pr)
  prConstr

proc tupleConstructor(scm: Schema; sn: SchemaNode; ident: PNode): Pnode =
  let seqBracket = nn(nkBracket)
  for i, field in sn.nodes:
    if isConst(scm, field):
      seqBracket.add literalToPreserveCall(literal(scm, field))
    elif sn.kind == snkTuple or i < sn.nodes.high:
      seqBracket.add nn(nkCall,
        ident"toPreserve", nn(nkDotExpr, ident, field.ident), ident"E")
  let seqConstr = nn(nkPrefix, ident"@", seqBracket)
  let colonExpr = nn(nkExprColonExpr, ident"sequence")
  if sn.kind == snkTuple:
    colonExpr.add seqConstr
  else:
    colonExpr.add nn(nkInfix,
      ident"&",
      seqConstr,
      nn(nkDotExpr,
        nn(nkCall, ident"toPreserve",
          nn(nkDotExpr,
            ident, sn.nodes[sn.nodes.high].ident),
          ident"E"),
        ident"sequence"))
  nn(nkObjConstr,
    preserveIdent(),
    nn(nkExprColonExpr, ident"kind", ident"pkSequence"),
    colonExpr)

proc generateProcs(result: var seq[PNode]; scm: Schema; name: string; sn: SchemaNode) =
  case sn.kind
  of snkOr:
    var
      enumId = name.ident
      paramId = ident"v"
      orStmts = nn(nkStmtList)
    if isSymbolEnum(scm, sn):
      let caseStmt = nn(nkCaseStmt, paramId)
      for bn in sn.nodes:
        caseStmt.add nn(nkOfBranch,
          nn(nkDotExpr,
            enumId,
            bn.altLabel.nimIdentNormalize.ident.accQuote),
          nn(nkCall,
            nn(nkBracketExpr, ident"symbol", ident"E"),
            PNode(kind: nkStrLit, strVal: $bn.altLabel)))
      orStmts.add caseStmt
    else:
      let caseStmt = nn(nkCaseStmt, nn(nkDotExpr, paramId, ident"kind"))
      proc genStmts(stmts: PNode; fieldId: PNode; sn: SchemaNode) =
        case sn.kind
        of snkLiteral:
           stmts.add literalToPreserveCall(literal(scm, sn))
        of snkOr, snkRecord, snkRef:
          if sn.kind == snkRef and sn.refPath.len == 1:
            let refDef = scm.definitions[sn.refPath[0]]
            genStmts(stmts, fieldId, refDef)
          else:
            stmts.add nn(nkCall,
              ident"toPreserve",
              nn(nkDotExpr, paramId, fieldId), ident"E")
        of snkTuple, snkVariableTuple:
          stmts.add tupleConstructor(scm, sn, nn(nkDotExpr, paramId, fieldId))
        of snkAtom, snkSequenceOf:
          stmts.add nn(nkCall,
            ident"toPreserve",
            nn(nkDotExpr, paramId, fieldId), ident"E")
        else:
          raiseAssert("no case statement for " & $sn.kind & " " & $sn)
      for bn in sn.nodes:
        let stmts = nn(nkStmtList)
        genStmts(stmts, bn.ident, bn.altBranch)
        caseStmt.add nn(nkOfBranch,
          nn(nkDotExpr,
            ident(name & "Kind"),
            bn.altLabel.nimIdentNormalize.ident.accQuote),
          stmts)
      orStmts.add caseStmt
    result.add nn(nkProcDef,
      exportIdent("toPreserveHook"),
      newEmpty(),
      newEmpty(),
      nn(nkFormalParams,
        preserveIdent(),
        nn(nkIdentDefs,
          paramId, ident(name), newEmpty()),
        nn(nkIdentDefs,
          ident"E", ident"typedesc", newEmpty())),
      newEmpty(),
      newEmpty(),
      orStmts)
  of snkRecord:
    var
      params = nn(nkFormalParams, preserveIdent())
      initRecordCall = nn(nkCall,
        nn(nkBracketExpr, ident"initRecord", ident"E"),
        nimLit(scm, sn.nodes[0]))
    for i, field in sn.nodes:
      if i > 0:
        let
          id = field.ident
        var (fieldType, embeddable) = typeIdent(scm, field)
        if not fieldType.isPreserve:
          fieldType =
            nn(nkInfix,
              ident"|",
              fieldType,
              preserveIdent())
        params.add nn(nkIdentDefs,
          id, fieldType, newEmpty())
        initRecordCall.add(
          nn(nkCall, ident"toPreserve", id, ident"E"))
    var procId = name
    procId[0] = procId[0].toLowerAscii
    let cmt = nkCommentStmt.newNode
    cmt.comment = "Preserves constructor for ``" & name & "``."
    result.add nn(nkProcDef,
      procId.ident.accQuote.toExport,
      newEmpty(),
      nn(nkGenericParams, nn(nkIdentDefs, ident"E", newEmpty(), ident"void")),
      params,
      newEmpty(),
      newEmpty(),
      nn(nkStmtList,
        cmt, initRecordCall))
    block:
      let paramId = name.toLowerAscii.ident.accQuote
      initRecordCall = nn(nkCall,
        nn(nkBracketExpr, ident"initRecord", ident"E"),
        nimLit(scm, sn.nodes[0]))
      for i, field in sn.nodes:
        if i > 0:
          initRecordCall.add nn(nkCall,
            ident"toPreserve",
            nn(nkDotExpr, paramId, field.ident),
            ident"E")
      result.add nn(nkProcDef,
        exportIdent("toPreserveHook"),
        newEmpty(),
        newEmpty(),
        nn(nkFormalParams,
          preserveIdent(),
          nn(nkIdentDefs,
            paramId, ident(name), newEmpty()),
          nn(nkIdentDefs,
            ident"E", ident"typedesc", newEmpty())),
        newEmpty(),
        newEmpty(),
        nn(nkStmtList, initRecordCall))
  of snkTuple, snkVariableTuple:
    let paramId = name.toLowerAscii.ident.accQuote
    result.add nn(nkProcDef,
      exportIdent("toPreserveHook"),
      newEmpty(),
      newEmpty(),
      nn(nkFormalParams,
        preserveIdent(),
        nn(nkIdentDefs,
          paramId, ident(name), newEmpty()),
        nn(nkIdentDefs,
          ident"E", ident"typedesc", newEmpty())),
      newEmpty(),
      newEmpty(),
      nn(nkStmtList, tupleConstructor(scm, sn, paramId)))
  else: discard

proc collectRefImports(imports: PNode; sn: SchemaNode) =
  case sn.kind
  of snkLiteral:
    if sn.value.isDictionary:
      imports.add ident"std/tables"
  of snkDictOf:
    imports.add ident"std/tables"
  of snkRef:
    if sn.refPath.len > 1:
      imports.add ident(sn.refPath[0])
  else:
    for child in sn.items:
      collectRefImports(imports, child)

proc collectRefImports(imports: PNode; scm: Schema) =
  for _, def in scm.definitions:
    collectRefImports(imports, def)

proc generateNimFile*(scm: Schema; path: string) =
  var
    knownTypes: TypeTable
    typeSection = newNode nkTypeSection
    procs: seq[PNode]
    megaType: PNode
  for name, def in scm.definitions.pairs:
    if isConst(scm, def):
      generateConstProcs(procs, scm, name, def)
    else:
      var name = name
      name[0] = name[0].toUpperAscii
      var defIdent = parameterize(ident(name), isEmbeddable(scm, def))
      if megaType.isNil:
        megaType = defIdent
      else:
        megaType = nn(nkInfix,
          ident"|", megaType, defIdent)
      let (t, embeddable) =
        if def.kind == snkAny: (preserveIdent(), true)
        else: nimTypeOf(scm, knownTypes, def, name)
      t.comment = "``" & $def & "``"
      case def.kind
      of snkAtom:
        knownTypes[name] = (nkTypeDef.newNode.add(
          name.ident.toExport, embeddingParams(false), nn(nkDistinctTy, t)),
          embeddable)
      else:
        if def.kind == snkRecord:
          knownTypes[name] = (typeDef(def, name, t, embeddable), embeddable)
        else:
          case t.kind
          of nkEnumTy:
            knownTypes[name] = (nn(nkTypeDef,
              nn(nkPragmaExpr,
                name.ident.toExport,
                nn(nkPragma, ident"pure")),
                newEmpty(),
                t), false)
          of nkDistinctTy:
            knownTypes[name] = (nn(nkTypeDef,
              nn(nkPragmaExpr,
                name.ident.toExport,
                nn(nkPragma,
                  nn(nkExprColonExpr,
                    ident"borrow",
                    accQuote(ident".")))),
                newEmpty(),
                t), embeddable)
          else:
            knownTypes[name] = (nn(nkTypeDef,
              name.ident.toExport, embeddingParams(embeddable), t),
              embeddable)
      generateProcs(procs, scm, name, def)
  for (typeDef, _) in knownTypes.values:
    typeSection.add typeDef
  var imports = nkImportStmt.newNode.add(
    ident"std/typetraits",
    ident"preserves")
  collectRefImports(imports, scm)
  procs.add nn(nkProcDef,
      "$".ident.accQuote.toExport,
      newEmpty(),
      nn(nkGenericParams, nn(nkIdentDefs, ident"E", newEmpty(), newEmpty())),
      nn(nkFormalParams,
        ident"string",
        nn(nkIdentDefs,
          ident"x",
          megaType,
          newEmpty())),
      newEmpty(),
      newEmpty(),
      nn(nkStmtList,
        nn(nkCall, ident"$",
          nn(nkCall, ident"toPreserve", ident"x", ident"E"))))
  procs.add nn(nkProcDef,
      "encode".ident.accQuote.toExport,
      newEmpty(),
      nn(nkGenericParams, nn(nkIdentDefs, ident"E", newEmpty(), newEmpty())),
      nn(nkFormalParams,
        nn(nkBracketExpr, ident"seq", ident"byte"),
        nn(nkIdentDefs,
          ident"x",
          megaType,
          newEmpty())),
      newEmpty(),
      newEmpty(),
      nn(nkStmtList,
        nn(nkCall, ident"encode", nn(nkCall,
          ident"toPreserve", ident"x", ident"E"))))
  var module = newNode(nkStmtList).add(
      imports,
      typeSection
    ).add(procs)
  writeFile(path, renderTree(module, {renderNone, renderIr}))

when isMainModule:
  import std/parseopt
  var inputs: seq[string]
  for kind, key, val in getopt():
    case kind
    of cmdLongOption:
      case key
      else: quit("unhandled option " & key)
    of cmdShortOption:
      case key
      else: quit("unhandled option " & key)
    of cmdArgument:
      inputs.add absolutePath(key)
    of cmdEnd: discard
  for filepath in inputs:
    let
      scm = parsePreservesSchema(readFile filepath, filepath)
      (dir, name, _) = splitFile(filepath)
      outputPath = dir / name & ".nim"
    generateNimFile(scm, outputPath)
    stdout.writeLine(outputPath)
