# SPDX-FileCopyrightText: 2021 ☭ Emery Hemingway
# SPDX-License-Identifier: Unlicense

## This module implements Nim code generation from Preserves schemas.
# This module imports code that it generates! After making any changes here
# the schema module must be regenerated!
# nim c -r ./preserves_schema_nim ../../schema.bin

import std/[hashes, sequtils, strutils, sets, tables]

import compiler/[ast, idents, renderer, lineinfos]

import ../preserves, ./schema

type
  Bundle = schema.Bundle[void]
  Modules = schema.Modules[void]
  Schema = schema.Schema[void]
  Definitions = schema.Definitions[void]
  Definition = schema.Definition[void]
  Pattern = schema.Pattern[void]
  SimplePattern = schema.SimplePattern[void]
  CompoundPattern = schema.CompoundPattern[void]
  DictionaryEntries = schema.DictionaryEntries[void]
  NamedAlternative = schema.NamedAlternative[void]
  NamedSimplePattern = schema.NamedSimplePattern[void]
  NamedPattern = schema.NamedPattern[void]
  Binding = schema.Binding[void]

  TypeSpec = tuple[node: PNode, embeddable: bool]
  TypeTable = OrderedTable[string, PNode]

proc add(parent, child: PNode): PNode {.discardable.} =
  parent.sons.add child
  parent

proc add(parent: PNode; children: varargs[PNode]): PNode {.discardable.} =
  parent.sons.add children
  parent

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

proc pattern(np: NamedPattern): Pattern =
  case np.orKind
  of NamedPatternKind.named:
    Pattern(orKind: PatternKind.SimplePattern, simplePattern: np.named.pattern)
  of NamedPatternKind.anonymous:
    np.anonymous

proc pattern(np: NamedSimplePattern): SimplePattern =
  case np.orKind
  of NamedSimplePatternKind.named:
    np.named.pattern
  of NamedSimplePatternKind.anonymous:
    np.anonymous

proc ident(sp: SimplePattern): PNode =
  raiseAssert "need ident from " #& $sp

proc ident(cp: CompoundPattern; fallback: string): PNode =
  case cp.orKind
  of CompoundPatternKind.`rec`:
    ident($cp.rec.label)
  of CompoundPatternKind.`tuple`,
      CompoundPatternKind.`tuplePrefix`,
      CompoundPatternKind.`dict`:
    ident(fallback)

proc ident(pat: Pattern; fallback = string): PNode =
  case pat.orKind
  of PatternKind.simplePattern:
    ident(pat.simplePattern, fallback)
  of PatternKind.compoundPattern:
    ident(pat.compoundPattern, fallback)

proc ident(np: NamedPattern; fallback: string): PNode =
  case np.orKind
  of NamedPatternKind.`named`:
    ident(string np.named.name)
  of NamedPatternKind.`anonymous`:
    ident(fallback)

proc ident(np: NamedSimplePattern; fallback: string): PNode =
  case np.orKind
  of NamedSimplePatternKind.`named`:
    ident(string np.named.name)
  of NamedSimplePatternKind.`anonymous`:
    ident(fallback)

proc parameterize(node: PNode; embeddable: bool): PNode =
  if embeddable and node.kind notin {nkBracketExpr}:
    nn(nkBracketExpr, node, ident"E")
  else: node

proc parameterize(spec: TypeSpec): PNode =
  parameterize(spec.node, spec.embeddable)

proc isPreserve(n: PNode): bool =
  n.kind == nkBracketExpr and
    n.renderTree == "Preserve[E]"

proc orEmbed(x: var TypeSpec; y: TypeSpec) =
  x.embeddable = x.embeddable or y.embeddable

proc dotExtend(result: var PNode; label: string) =
  var id = ident(label)
  if result.isNil: result = id
  else: result = nn(nkDotExpr, result, id)

proc ident(`ref`: Ref): PNode =
  for m in`ref`.module: dotExtend(result, string m)
  dotExtend(result, `ref`.name.string.capitalizeAscii)

proc deref(scm: Schema; r: Ref): Definition =
  assert r.module == @[]
  scm.data.definitions[r.name]

proc preserveIdent(scm: Schema): Pnode =
  nn(nkBracketExpr, ident"Preserve", ident("E"))

proc embeddedIdent(scm: Schema): PNode =
  case scm.data.embeddedType.orKind
  of EmbeddedtypenameKind.`false`: ident"void"
  of EmbeddedtypenameKind.`Ref`: preserveIdent(scm)

proc hash(r: Ref): Hash = r.toPreserve.hash
type RefSet = HashSet[Ref]

proc isEmbeddable(scm: Schema; pat: Pattern; seen: RefSet): bool {.gcsafe.}
proc isEmbeddable(scm: Schema; def: Definition; seen: RefSet): bool {.gcsafe.}

proc isEmbeddable(scm: Schema; sp: SimplePattern; seen: RefSet): bool =
  case sp.orKind
  of SimplepatternKind.`atom`, SimplepatternKind.`lit`: false
  of SimplepatternKind.`any`: true
  of SimplepatternKind.`embedded`: true
  of SimplepatternKind.`seqof`:
    isEmbeddable(scm, sp.seqof.pattern, seen)
  of SimplepatternKind.`setof`:
    isEmbeddable(scm, sp.setof.pattern, seen)
  of SimplepatternKind.`dictof`:
    isEmbeddable(scm, sp.dictof.key, seen) or
      isEmbeddable(scm, sp.dictof.value, seen)
  of SimplepatternKind.`Ref`:
    if sp.ref.module != @[]: true
    else:
      if sp.ref in seen: false
      else:
        var seen = seen
        seen.incl sp.ref
        isEmbeddable(scm, deref(scm, sp.ref), seen)

proc isEmbeddable(scm: Schema; np: NamedSimplePattern; seen: RefSet): bool =
  case np.orKind
  of NamedSimplePatternKind.`named`:
    isEmbeddable(scm, np.named.pattern, seen)
  of NamedSimplePatternKind.`anonymous`:
    isEmbeddable(scm, np.anonymous, seen)

proc isEmbeddable(scm: Schema; cp: CompoundPattern; seen: RefSet): bool =
  case cp.orKind
  of CompoundPatternKind.`rec`:
    isEmbeddable(scm, cp.rec.label.pattern, seen) or
      isEmbeddable(scm, cp.rec.fields.pattern, seen)
  of CompoundPatternKind.`tuple`:
    any(cp.tuple.patterns) do (np: NamedPattern) -> bool:
      isEmbeddable(scm, np.pattern, seen)
  of CompoundPatternKind.`tupleprefix`:
    proc pred(np: NamedPattern): bool =
      isEmbeddable(scm, np.pattern, seen)
    isEmbeddable(scm, cp.tupleprefix.variable, seen) or
      any(cp.tupleprefix.fixed, pred)
  of CompoundPatternKind.`dict`:
    true # the key type is `Preserve`

proc isEmbeddable(scm: Schema; pat: Pattern; seen: RefSet): bool =
  case pat.orKind
  of PatternKind.`SimplePattern`:
    isEmbeddable(scm, pat.simplePattern, seen)
  of PatternKind.`CompoundPattern`:
    isEmbeddable(scm, pat.compoundPattern, seen)

proc isEmbeddable(scm: Schema; orDef: DefinitionOr; seen: RefSet): bool =
  proc isEmbeddable(na: NamedAlternative): bool =
    isEmbeddable(scm, na.pattern, seen)
  isEmbeddable(orDef.data.pattern0) or
    isEmbeddable(orDef.data.pattern1) or
      sequtils.any(orDef.data.patternN, isEmbeddable)

proc isEmbeddable(scm: Schema; def: Definition; seen: RefSet): bool =
  case def.orKind
  of DefinitionKind.`or`: isEmbeddable(scm, def.or, seen)
  of DefinitionKind.`and`:
    proc isEmbeddable(np: NamedPattern): bool =
      isEmbeddable(scm, np.pattern, seen)
    isEmbeddable(def.and.data.pattern0) or
      isEmbeddable(def.and.data.pattern1) or
        any(def.and.data.patternN, isEmbeddable)
  of DefinitionKind.`Pattern`:
    isEmbeddable(scm, def.pattern, seen)

proc isEmbeddable(scm: Schema; p: Definition|DefinitionOr|Pattern|CompoundPattern|SimplePattern): bool =
  var seen: RefSet
  isEmbeddable(scm, p, seen)

proc isLiteral(scm: Schema; def: Definition): bool {.gcsafe.}

proc isLiteral(scm: Schema; sp: SimplePattern): bool =
  case sp.orKind
  of SimplepatternKind.`Ref`:
    if sp.ref.module.len == 0:
      result = isLiteral(scm, deref(scm, sp.ref))
  of SimplepatternKind.lit:
    result = true
  else: discard

proc isLiteral(scm: Schema; pat: Pattern): bool =
  case pat.orKind
  of PatternKind.SimplePattern:
    isLiteral(scm, pat.simplePattern)
  of PatternKind.CompoundPattern:
    false # TODO it could be a compound of all literals

proc isLiteral(scm: Schema; def: Definition): bool =
  if def.orKind == DefinitionKind.Pattern:
    result = isLiteral(scm, def.pattern)

proc isRef(sp: SimplePattern): bool =
  sp.orKind == SimplePatternKind.`Ref`

proc isRef(pat: Pattern): bool =
  pat.orKind == PatternKind.SimplePattern and
    pat.simplePattern.isRef

proc isSimple(pat: Pattern): bool =
  pat.orKind == PatternKind.SimplePattern

proc isSymbolEnum(scm: Schema; orDef: DefinitionOr): bool =
  proc isLiteral(na: NamedAlternative): bool = isLiteral(scm, na.pattern)
  result = isLiteral(orDef.data.pattern0) and isLiteral(orDef.data.pattern1)
  for na in orDef.data.patternN:
    if not result: break
    result = isLiteral(na)

proc isSymbolEnum(scm: Schema; def: Definition): bool =
  case def.orKind
  of DefinitionKind.Pattern:
    if def.pattern.orKind == PatternKind.SimplePattern and
      def.pattern.simplePattern.orKind == SimplepatternKind.`Ref` and
        def.pattern.simplePattern.ref.module.len == 0:
          result = isSymbolEnum(scm, deref(scm, def.pattern.simplePattern.ref))
            # TODO: no need to de-ref this
  of DefinitionKind.or:
    result = isSymbolEnum(scm, def.or)
  else: discard

proc isSymbolEnum(scm: Schema; sp: SimplePattern): bool =
  # HashSet
  if sp.orKind == SimplepatternKind.`Ref` and sp.ref.module.len == 0:
    result = isSymbolEnum(scm, deref(scm, sp.ref))
  else: discard

proc isAny(scm: Schema; def: Definition): bool =
  if def.orKind == DefinitionKind.Pattern:
    if def.pattern.orKind == PatternKind.SimplePattern:
      case def.pattern.simplePattern.orKind
      of SimplePatternKind.Ref:
        result = isAny(scm, deref(scm, def.pattern.simplePattern.`ref`))
      of SimplePatternKind.any:
        result = true
      else: discard

proc typeIdent(atom: AtomKind): PNode =
  case atom
  of AtomKind.`Boolean`: ident"bool"
  of AtomKind.`Float`: ident"float32"
  of AtomKind.`Double`: ident"float64"
  of AtomKind.`Signedinteger`: ident"BiggestInt"
  of AtomKind.`String`: ident"string"
  of AtomKind.`Bytestring`: nn(nkBracketExpr, ident"seq", ident"byte")
  of AtomKind.`Symbol`: ident"Symbol"

proc typeIdent(scm: Schema; sp: SimplePattern): TypeSpec =
  case sp.orKind
  of SimplepatternKind.`atom`:
    result = (typeIdent(sp.atom.atomKind), false)
  of SimplepatternKind.`seqof`:
    result = typeIdent(scm, sp.seqof.pattern)
    result.node = nn(nkBracketExpr, ident"seq", result.node)
  of SimplepatternKind.`setof`:
    result = typeIdent(scm, sp.setof.pattern)
    result.node =
      if isSymbolEnum(scm, sp.setof.pattern):
        nn(nkBracketExpr, ident"set", result.node)
      else:
        nn(nkBracketExpr, ident"HashSet", result.node)
  of SimplepatternKind.`dictof`:
    let
      key = typeIdent(scm, sp.dictof.key)
      val = typeIdent(scm, sp.dictof.value)
    result.node = nn(nkBracketExpr, ident"Table", key.node, val.node)
    result.embeddable = key.embeddable or val.embeddable
  of SimplepatternKind.`Ref`:
    result = (ident(sp.ref), isEmbeddable(scm, sp))
    result.node = parameterize(result)
  else:
    result = (preserveIdent(scm), true)

proc typeIdent(scm: Schema; pat: Pattern): TypeSpec =
  case pat.orKind
  of PatternKind.SimplePattern: typeIdent(scm, pat.simplePattern)
  else: raiseAssert "no typeIdent for " & $pat

proc toExport(n: sink PNode): PNode =
  nkPostFix.newNode.add(ident"*", n)

proc toStrLit(scm: Schema; sp: SimplePattern): PNode =
  case sp.orKind
  of SimplePatternKind.`lit`:
    result = PNode(kind: nkStrLit, strVal: $sp.lit.value)
  of SimplePatternKind.`Ref`:
    let def = deref(scm, sp.ref)
    result = toStrLit(scm, def.pattern.simplePattern)
  else: assert false

proc toFieldIdent(s: string): PNode =
  nn(nkPostFix, ident("*"), nn(nkAccQuoted, ident(s)))

proc toFieldIdent(scm: Schema, label: string; pat: Pattern): PNode =
  result = label.toFieldIdent
  if isLiteral(scm, pat):
    result = nn(nkPragmaExpr,
      result,
      nn(nkPragma,
        nn(nkExprColonExpr,
          ident"preservesLiteral",
          toStrLit(scm, pat.simplePattern))))

proc newEmpty(): PNode = newNode(nkEmpty)

proc embeddingParams(embeddable: bool): PNode =
  if embeddable:
    nn(nkGenericParams, nn(nkIdentDefs, ident"E", newEmpty(), newEmpty()))
  else:
    newEmpty()

proc identDef(a, b: PNode; embeddable: bool): PNode =
  if embeddable and b.kind notin {nkBracketExpr, nkTupleTy}:
    # TODO: probably not a sufficient check
    nn(nkIdentDefs, a, nn(nkBracketExpr, b, ident"E"), newEmpty())
  else:
    nn(nkIdentDefs, a, b, newEmpty())

proc identDef(l: PNode; ts: TypeSpec): PNode =
  identDef(l, ts.node, ts.embeddable)

proc label(pat: Pattern): string =
  raiseAssert "need to derive record label for " & $pat

proc label(na: NamedPattern): string =
  case na.orKind
  of NamedPatternKind.`named`:
    string na.named.name
  of NamedPatternKind.`anonymous`:
    "data" # TODO

proc idStr(sp: SimplePattern): string =
  if sp.orKind == SimplepatternKind.lit:
    case sp.lit.value.kind
    of pkString:
      result = sp.lit.value.string
    of pkSymbol:
      result = string sp.lit.value.symbol
    else: discard
  doAssert(result != "",  "no idStr for " & $sp)

proc idStr(pat: Pattern): string =
  doAssert(pat.orKind == PatternKind.SimplePattern)
  pat.simplePattern.idStr

proc idStr(np: NamedPattern): string =
  case np.orKind
  of NamedPatternKind.`named`:
    string np.named.name
  of NamedPatternKind.`anonymous`:
    np.anonymous.idStr

proc typeDef(scm: Schema; name: string; pat: Pattern; ty: PNode): PNode =
  let
    embedParams = embeddingParams(isEmbeddable(scm, pat))
    id = name.ident.toExport
  if pat.orKind == PatternKind.`CompoundPattern`:
    case pat.compoundPattern.orKind
    of CompoundPatternKind.`rec`:
      nn(nkTypeDef,
        nn(nkPragmaExpr,
        id, nn(nkPragma,
          nn(nkExprColonExpr,
            ident"preservesRecord",
            PNode(kind: nkStrLit, strVal: pat.compoundPattern.rec.label.idStr)))),
        embedParams,
        ty)
    of CompoundPatternKind.`tuple`, CompoundPatternKind.`tuplePrefix`:
      nn(nkTypeDef,
        nn(nkPragmaExpr, id, nn(nkPragma, ident"preservesTuple")),
        embedParams,
        ty)
    of CompoundPatternKind.`dict`:
      nn(nkTypeDef,
        nn(nkPragmaExpr, id, nn(nkPragma, ident"preservesDictionary")),
        embedParams,
        ty)
  else:
    nn(nkTypeDef, name.ident.toExport, embedParams, ty)

proc typeDef(scm: Schema; name: string; def: Definition; ty: PNode): PNode =
  case def.orKind
  of DefinitionKind.or:
    let pragma = nn(nkPragma, ident"preservesOr")
    if isSymbolEnum(scm, def):
      pragma.add ident"pure"
    nn(nkTypeDef,
      nn(nkPragmaExpr,
        name.ident.accQuote.toExport,
        pragma),
      embeddingParams(isEmbeddable(scm, def)),
      ty)
  of DefinitionKind.and:
    raiseAssert "And variants not suported"
  of DefinitionKind.Pattern:
    typeDef(scm, name, def.pattern, ty)

proc nimTypeOf(scm: Schema; known: var TypeTable; nsp: NamedSimplePattern; name = ""): TypeSpec
proc nimTypeOf(scm: Schema; known: var TypeTable; pat: Pattern; name = ""): TypeSpec

proc nimTypeOf(scm: Schema; known: var TypeTable; cp: CompoundPattern; name = ""): TypeSpec
proc nimTypeOf(scm: Schema; known: var TypeTable; sp: SimplePattern; name = ""): TypeSpec =
  typeIdent(scm, sp)

proc addField(recList: PNode; scm: Schema; known: var TypeTable; sp: SimplePattern; label: string): PNode {.discardable.} =
  let id = label.toFieldIdent
  if isLiteral(scm, sp):
    let id = nn(nkPragmaExpr,
      id,
      nn(nkPragma,
        nn(nkExprColonExpr,
          ident"preservesLiteral",
          toStrLit(scm, sp))))
    recList.add identDef(id, (ident"bool", false))
  else:
    recList.add identDef(id, nimTypeOf(scm, known, sp))

proc addFields(recList: PNode; scm: Schema; known: var TypeTable; cp: CompoundPattern; parentName: string): PNode {.discardable.} =
  template addField(np: NamedPattern) =
    let
      label = np.label
      id = label.toFieldIdent
      pattern = np.pattern
    if pattern.isRef or pattern.isSimple:
      addField(recList, scm, known, pattern.simplePattern, label)
    else:
      var
        typeName = parentName & capitalizeAscii(label)
        fieldSpec = nimTypeOf(scm, known, pattern, label)
      known[typeName] = typeDef(scm, typeName, pattern, fieldSpec.node)
      recList.add identDef(id, ident(typeName), isEmbeddable(scm, pattern))
  case cp.orKind
  of CompoundPatternKind.rec:
    # recList.add identDef(ident(label), nimTypeOf(scm, known, cp, ""))
    raiseassert "unexpected record of fields " #& $cp.rec
  of CompoundPatternKind.tuple:
    for np in cp.tuple.patterns: addField(np)
  of CompoundPatternKind.tuplePrefix:
    for np in cp.tuplePrefix.fixed: addField(np)
    let variableType = nimTypeOf(scm, known, cp.tuplePrefix.variable)
    recList.add identDef(
      nn(nkPragmaExpr,
        ident(cp.tuplePrefix.variable, parentName).accQuote.toExport,
        nn(nkPragma, ident"preservesTupleTail")),
      variableType.parameterize,
      variableType.embeddable)
  else: raiseAssert "not adding fields for " #& $cp
  reclist

proc addFields(recList: PNode; scm: Schema; known: var TypeTable; pat: Pattern; parentName: string): PNode {.discardable.} =
  case pat.orKind
  of PatternKind.SimplePattern:
    addField(recList, scm, known, pat.simplePattern, "data")
  of PatternKind.CompoundPattern:
    discard addFields(recList, scm, known, pat.compoundPattern, parentName)
  reclist

proc addFields(recList: PNode; scm: Schema; known: var TypeTable; entries: DictionaryEntries; parentName: string): PNode {.discardable.} =
  for key, val in entries.pairs:
    doAssert(key.isSymbol)
    let label = string key.symbol
    addField(recList, scm, known, val.pattern, label)
  recList

proc nimTypeOf(scm: Schema; known: var TypeTable; nsp: NamedSimplePattern; name: string): TypeSpec =
  case nsp.orKind
  of NamedsimplepatternKind.named:
    nimTypeOf(scm, known, nsp.named.pattern, string nsp.named.name)
  of NamedsimplepatternKind.anonymous:
    nimTypeOf(scm, known, nsp.anonymous, name)

proc nimTypeOf(scm: Schema; known: var TypeTable; cp: CompoundPattern; name: string): TypeSpec =
  case cp.orKind
  of CompoundPatternKind.`rec`:
    result.node = nn(nkObjectTy,
      newEmpty(), newEmpty(),
      nn(nkRecList).addFields(scm, known, cp.rec.fields.pattern, name))
  of CompoundPatternKind.`tuple`, CompoundPatternKind.`tupleprefix`:
    result.node = nn(nkObjectTy,
      newEmpty(), newEmpty(),
      nn(nkRecList).addFields(scm, known, cp, name))
  of CompoundPatternKind.`dict`:
    result.node = nn(nkObjectTy, newEmpty(), newEmpty(),
      nn(nkRecList).addFields(scm, known, cp.dict.entries, name))
  if result.node.kind == nkObjectTy and isEmbeddable(scm, cp):
    result.node = nn(nkRefTy, result.node)

proc nimTypeOf(scm: Schema; known: var TypeTable; pat: Pattern; name: string): TypeSpec =
  case pat.orKind
  of PatternKind.SimplePattern:
    nimTypeOf(scm, known, pat.simplePattern, name)
  of PatternKind.CompoundPattern:
    nimTypeOf(scm, known, pat.compoundPattern, name)

proc nimTypeOf(scm: Schema; known: var TypeTable; orDef: DefinitionOr; name: string): TypeSpec =
  proc toEnumTy(): PNode =
    let ty = nkEnumTy.newNode.add newEmpty()
    proc add (na: NamedAlternative) =
      ty.add na.variantLabel.ident.accQuote
    add(orDef.data.pattern0)
    add(orDef.data.pattern1)
    for na in orDef.data.patternN:
      add(na)
    ty
  if isSymbolEnum(scm, orDef):
    result.node = toEnumTy()
  else:
    let
      enumName = name & "Kind"
      enumIdent = ident(enumName)
    if enumName notin known:
      known[enumName] = nn(nkTypeDef,
        nn(nkPragmaExpr,
          enumName.ident.toExport,
          nn(nkPragma, ident"pure")),
        newEmpty(),
        toEnumTy())
    let recCase = nkRecCase.newNode.add(
      nkIdentDefs.newNode.add(
        "orKind".ident.toExport,
        enumName.ident,
        newEmpty()))
    template addCase(na: NamedAlternative) =
      let branchRecList = nn(nkRecList)
      var memberType: TypeSpec
      if isLiteral(scm, na.pattern):
        memberType.node = ident"bool"
      elif na.pattern.isRef:
        memberType = typeIdent(scm, na.pattern)
      else:
        let memberTypeName = name & na.variantLabel.capitalizeAscii
        memberType.node = ident memberTypeName
        let ty = nimTypeOf(scm, known, na.pattern, memberTypeName)
        orEmbed memberType, ty
        if memberTypeName notin known and not isLiteral(scm, na.pattern):
          known[memberTypeName] =
            typeDef(scm, memberTypeName, na.pattern, ty.node)
      orEmbed result, memberType
      memberType.node = parameterize(
        memberType.node, isEmbeddable(scm, na.pattern))
      branchRecList.add nn(nkIdentDefs,
        toFieldIdent(scm, na.variantLabel.normalize, na.pattern),
        memberType.node, newEmpty())
      recCase.add nn(nkOfBranch,
        nn(nkDotExpr,
          enumIdent, na.variantLabel.ident.accQuote),
        branchRecList)
    addCase(orDef.data.pattern0)
    addCase(orDef.data.pattern1)
    for na in orDef.data.patternN: addCase(na)
    result.node = nn(nkObjectTy,
      newEmpty(),
      newEmpty(),
      nn(nkRecList, recCase))
    if result.node.kind == nkObjectTy and isEmbeddable(scm, orDef):
      result.node = nn(nkRefTy, result.node)

proc nimTypeOf(scm: Schema; known: var TypeTable; def: Definition; name: string): TypeSpec =
  case def.orKind
  of DefinitionKind.or:
    nimTypeOf(scm, known, def.or, name)
  of DefinitionKind.and: raiseAssert "And definitions are unsupported"
  of DefinitionKind.Pattern:
    nimTypeOf(scm, known, def.pattern, name)

proc generateConstProcs(result: var seq[PNode]; scm: Schema, name: string; def: Definition) =
  discard

proc literalToPreserveCall(scm: Schema; pr: Preserve): PNode =
  var prConstr = nn(nkObjConstr, preserveIdent(scm))
  proc constr(kind, field: string; lit: PNode) =
    prConstr.add nn(nkExprColonExpr, ident"kind", ident(kind))
    prConstr.add nn(nkExprColonExpr, ident(field), lit)
  case pr.orKind
  of pkBoolean:
    constr($pr.orKind, "bool", if pr.bool: ident"true" else: ident"false")
  of pkFloat:
    constr($pr.orKind, "float", newFloatNode(nkFloat32Lit, pr.float))
  of pkDouble:
    constr($pr.orKind, "double", newFloatNode(nkFloat64Lit, pr.double))
  of pkSignedInteger:
    constr($pr.orKind, "BiggestInt", newIntNode(nkInt64Lit, pr.int))
  of pkString:
    constr($pr.orKind, "string", newStrNode(nkTripleStrLit, pr.string))
  of pkByteString:
    return nn(nkCall, ident"parsePreserves", newStrNode(nkTripleStrLit, $pr))
  of pkSymbol:
    constr($pr.orKind, "symbol", newStrNode(nkStrLit, string pr.symbol))
  else:
    raise newException(ValueError, "refusing to convert to a literal: " & $pr)
  prConstr

proc generateProcs(result: var seq[PNode]; scm: Schema; name: string; pat: Pattern) =
  discard

proc generateProcs(result: var seq[PNode]; scm: Schema; name: string; def: Definition) =
  discard

proc collectRefImports(imports: PNode; pat: Pattern)

proc collectRefImports(imports: PNode; sp: SimplePattern) =
  case sp.orKind
  of SimplePatternKind.dictof:
    imports.add ident"std/tables"
  of SimplePatternKind.Ref:
    if sp.`ref`.module != @[]:
      imports.add ident(string sp.ref.module[0])
  else: discard

proc collectRefImports(imports: PNode; cp: CompoundPattern) =
  case cp.orKind
  of CompoundPatternKind.`rec`:
    collectRefImports(imports, cp.rec.label.pattern)
    collectRefImports(imports, cp.rec.fields.pattern)
  of CompoundPatternKind.`tuple`:
    for p in cp.tuple.patterns: collectRefImports(imports, p.pattern)
  of CompoundPatternKind.`tupleprefix`:
    for np in cp.tupleprefix.fixed: collectRefImports(imports, np.pattern)
    collectRefImports(imports, cp.tupleprefix.variable.pattern)
  of CompoundPatternKind.`dict`:
    for nsp in cp.dict.entries.values:
      collectRefImports(imports, nsp.pattern)

proc collectRefImports(imports: PNode; pat: Pattern) =
  case pat.orKind
  of PatternKind.SimplePattern:
    collectRefImports(imports, pat.simplePattern)
  of PatternKind.CompoundPattern:
    collectRefImports(imports, pat.compoundPattern)

proc collectRefImports(imports: PNode; def: Definition) =
  case def.orKind
  of DefinitionKind.`or`:
    collectRefImports(imports, def.or.data.pattern0.pattern)
    collectRefImports(imports, def.or.data.pattern1.pattern)
    for na in def.or.data.patternN:
      collectRefImports(imports, na.pattern)
  of DefinitionKind.`and`:
    collectRefImports(imports, def.and.data.pattern0.pattern)
    collectRefImports(imports, def.and.data.pattern1.pattern)
    for np in def.and.data.patternN:
      collectRefImports(imports, np.pattern)
  of DefinitionKind.Pattern:
    collectRefImports(imports, def.pattern)

proc collectRefImports(imports: PNode; scm: Schema) =
  for _, def in scm.data.definitions:
    collectRefImports(imports, def)

proc renderNimModule*(scm: Schema): string =
  ## Construct and render a Nim module from a `Schema`.
  proc mergeType(x: var PNode; y: PNode) =
    if x.isNil: x = y
    else: x = nn(nkInfix, ident"|", x, y)
  var
    typeDefs: TypeTable
    typeSection = newNode nkTypeSection
    procs: seq[PNode]
    unembeddableType, embeddableType: PNode
  for name, def in scm.data.definitions.pairs:
    if isLiteral(scm, def):
      generateConstProcs(procs, scm, string name, def)
    else:
      var name = string name
      name[0] = name[0].toUpperAscii
      var defIdent = parameterize(ident(name), isEmbeddable(scm, def))
      if not isSymbolEnum(scm, def) and not isAny(scm, def):
        if isEmbeddable(scm, def):
          mergeType(embeddableType, defIdent)
        else:
          mergeType(unembeddableType, defIdent)
      let typeSpec = nimTypeOf(scm, typeDefs, def, name)
      typeDefs[name] = typeDef(scm, name, def, typeSpec.node)
      generateProcs(procs, scm, name, def)
  for td in typeDefs.values:
    typeSection.add td
  var imports = nkImportStmt.newNode.add(
    ident"std/typetraits",
    ident"preserves")
  collectRefImports(imports, scm)
  let genericParams =
    nn(nkGenericParams, nn(nkIdentDefs, ident"E", newEmpty(), newEmpty()))
  if not embeddableType.isNil:
    procs.add nn(nkProcDef,
        "$".toFieldIdent,
        newEmpty(),
        genericParams,
        nn(nkFormalParams,
          ident"string",
          nn(nkIdentDefs,
            ident"x",
            embeddableType,
            newEmpty())),
        newEmpty(),
        newEmpty(),
        nn(nkStmtList,
          nn(nkCall, ident"$",
            nn(nkCall, ident"toPreserve", ident"x", ident"E"))))
    procs.add nn(nkProcDef,
        "encode".ident.toExport,
        newEmpty(),
        genericParams,
        nn(nkFormalParams,
          nn(nkBracketExpr, ident"seq", ident"byte"),
          nn(nkIdentDefs,
            ident"x",
            embeddableType,
            newEmpty())),
        newEmpty(),
        newEmpty(),
        nn(nkStmtList,
          nn(nkCall, ident"encode",
            nn(nkCall, ident"toPreserve", ident"x", ident"E"))))
  if not unembeddableType.isNil:
    procs.add nn(nkProcDef,
        "$".toFieldIdent,
        newEmpty(),
        newEmpty(),
        nn(nkFormalParams,
          ident"string",
          nn(nkIdentDefs,
            ident"x",
            unembeddableType,
            newEmpty())),
        newEmpty(),
        newEmpty(),
        nn(nkStmtList,
          nn(nkCall, ident"$",
            nn(nkCall, ident"toPreserve", ident"x"))))
    procs.add nn(nkProcDef,
        "encode".ident.toExport,
        newEmpty(),
        newEmpty(),
        nn(nkFormalParams,
          nn(nkBracketExpr, ident"seq", ident"byte"),
          nn(nkIdentDefs,
            ident"x",
            unembeddableType,
            newEmpty())),
        newEmpty(),
        newEmpty(),
        nn(nkStmtList,
          nn(nkCall, ident"encode", nn(nkCall,
            ident"toPreserve", ident"x"))))
  var module = newNode(nkStmtList).add(
      imports,
      typeSection
    ).add(procs)
  renderTree(module, {renderNone, renderIr})

when isMainModule:
  import ./schemaparse

  proc writeModule(scm: Schema; path: string) =
    let txt = renderNimModule(scm)
    writeFile(path, txt)
    stdout.writeLine(path)

  import std/[options, os, parseopt]
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
    var useful: bool
    let raw = readFile filepath
    if raw[0] == 0xb4.char:
      let pr = decodePreserves raw
      preserveTo(pr, Schema).map do (scm: Schema):
        useful = true
        let
          (_, name, _) = splitFile(filepath)
          outputPath = name & ".nim"
        writeModule(scm, outputPath)
      preserveTo(pr, Bundle).map do (bundle: Bundle):
        useful = true
        for modPath, scm in bundle.modules:
          let path = joinPath(cast[seq[string]](modPath)) & ".nim"
          writeModule(scm, path)
    else:
      let
        (dir, name, _) = splitFile filepath
        scm = parsePreservesSchema(raw, dir)
        modpath = name & ".nim"
      writeModule(scm, modpath)
      useful = true
    if not useful:
      quit "Failed to recognized " & filepath
