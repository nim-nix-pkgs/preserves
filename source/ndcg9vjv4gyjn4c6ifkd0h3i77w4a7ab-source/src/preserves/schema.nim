
import ../preserves, std/typetraits, std/tables

type
  Ref* {.preservesRecord: "ref".} = object
    `module`*: ModulePath
    `name`*: Symbol

  ModulePath* = seq[Symbol]
  Bundle*[E] {.preservesRecord: "bundle".} = ref object
    `modules`*: Modules[E]

  CompoundPatternKind* {.pure.} = enum
    `rec`, `tuple`, `tuplePrefix`, `dict`
  CompoundPatternRec*[E] {.preservesRecord: "rec".} = ref object
    `label`*: NamedPattern[E]
    `fields`*: NamedPattern[E]

  CompoundPatternTuple*[E] {.preservesRecord: "tuple".} = ref object
    `patterns`*: seq[NamedPattern[E]]

  CompoundPatternTuplePrefix*[E] {.preservesRecord: "tuplePrefix".} = ref object
    `fixed`*: seq[NamedPattern[E]]
    `variable`*: NamedSimplePattern[E]

  CompoundPatternDict*[E] {.preservesRecord: "dict".} = ref object
    `entries`*: DictionaryEntries[E]

  `CompoundPattern`*[E] {.preservesOr.} = ref object
    case orKind*: CompoundPatternKind
    of CompoundPatternKind.`rec`:
        `rec`*: CompoundPatternRec[E]

    of CompoundPatternKind.`tuple`:
        `tuple`*: CompoundPatternTuple[E]

    of CompoundPatternKind.`tuplePrefix`:
        `tupleprefix`*: CompoundPatternTuplePrefix[E]

    of CompoundPatternKind.`dict`:
        `dict`*: CompoundPatternDict[E]


  Modules*[E] = Table[ModulePath, Schema[E]]
  EmbeddedTypeNameKind* {.pure.} = enum
     `false`, `Ref`
  `EmbeddedTypeName`* {.preservesOr.} = object
    case orKind*: EmbeddedTypeNameKind
    of EmbeddedTypeNameKind.`false`:
        `false`* {.preservesLiteral: "#f".}: bool
    of EmbeddedTypeNameKind.`Ref`:
        `ref`*: Ref


  `AtomKind`* {.preservesOr, pure.} = enum
    `Boolean`, `Float`, `Double`, `SignedInteger`, `String`, `ByteString`,
    `Symbol`
  Definitions*[E] = Table[Symbol, Definition[E]]
  DictionaryEntries*[E] = Table[Preserve[E], NamedSimplePattern[E]]
  NamedPatternKind* {.pure.} = enum
    `named`, `anonymous`
  `NamedPattern`*[E] {.preservesOr.} = ref object
    case orKind*: NamedPatternKind
    of NamedPatternKind.`named`:
        `named`*: Binding[E]

    of NamedPatternKind.`anonymous`:
        `anonymous`*: Pattern[E]


  SimplePatternKind* {.pure.} = enum
    `any`, `atom`, `embedded`, `lit`, `seqof`, `setof`, `dictof`, `Ref`
  SimplePatternAtom* {.preservesRecord: "atom".} = object
    `atomKind`*: AtomKind

  SimplePatternEmbedded*[E] {.preservesRecord: "embedded".} = ref object
    `interface`*: SimplePattern[E]

  SimplePatternLit*[E] {.preservesRecord: "lit".} = ref object
    `value`*: Preserve[E]

  SimplePatternSeqof*[E] {.preservesRecord: "seqof".} = ref object
    `pattern`*: SimplePattern[E]

  SimplePatternSetof*[E] {.preservesRecord: "setof".} = ref object
    `pattern`*: SimplePattern[E]

  SimplePatternDictof*[E] {.preservesRecord: "dictof".} = ref object
    `key`*: SimplePattern[E]
    `value`*: SimplePattern[E]

  `SimplePattern`*[E] {.preservesOr.} = ref object
    case orKind*: SimplePatternKind
    of SimplePatternKind.`any`:
        `any`* {.preservesLiteral: "any".}: bool

    of SimplePatternKind.`atom`:
        `atom`*: SimplePatternAtom

    of SimplePatternKind.`embedded`:
        `embedded`*: SimplePatternEmbedded[E]

    of SimplePatternKind.`lit`:
        `lit`*: SimplePatternLit[E]

    of SimplePatternKind.`seqof`:
        `seqof`*: SimplePatternSeqof[E]

    of SimplePatternKind.`setof`:
        `setof`*: SimplePatternSetof[E]

    of SimplePatternKind.`dictof`:
        `dictof`*: SimplePatternDictof[E]

    of SimplePatternKind.`Ref`:
        `ref`*: Ref


  NamedSimplePatternKind* {.pure.} = enum
    `named`, `anonymous`
  `NamedSimplePattern`*[E] {.preservesOr.} = ref object
    case orKind*: NamedSimplePatternKind
    of NamedSimplePatternKind.`named`:
        `named`*: Binding[E]

    of NamedSimplePatternKind.`anonymous`:
        `anonymous`*: SimplePattern[E]


  DefinitionKind* {.pure.} = enum
    `or`, `and`, `Pattern`
  DefinitionOrData*[E] {.preservesTuple.} = ref object
    `pattern0`*: NamedAlternative[E]
    `pattern1`*: NamedAlternative[E]
    `patternN`* {.preservesTupleTail.}: seq[NamedAlternative[E]]

  DefinitionOr*[E] {.preservesRecord: "or".} = ref object
    `data`*: DefinitionOrData[E]

  DefinitionAndData*[E] {.preservesTuple.} = ref object
    `pattern0`*: NamedPattern[E]
    `pattern1`*: NamedPattern[E]
    `patternN`* {.preservesTupleTail.}: seq[NamedPattern[E]]

  DefinitionAnd*[E] {.preservesRecord: "and".} = ref object
    `data`*: DefinitionAndData[E]

  `Definition`*[E] {.preservesOr.} = ref object
    case orKind*: DefinitionKind
    of DefinitionKind.`or`:
        `or`*: DefinitionOr[E]

    of DefinitionKind.`and`:
        `and`*: DefinitionAnd[E]

    of DefinitionKind.`Pattern`:
        `pattern`*: Pattern[E]


  NamedAlternative*[E] {.preservesTuple.} = ref object
    `variantLabel`*: string
    `pattern`*: Pattern[E]

  SchemaData*[E] {.preservesDictionary.} = ref object
    `version`* {.preservesLiteral: "1".}: bool
    `embeddedType`*: EmbeddedTypeName
    `definitions`*: Definitions[E]

  Schema*[E] {.preservesRecord: "schema".} = ref object
    `data`*: SchemaData[E]

  PatternKind* {.pure.} = enum
    `SimplePattern`, `CompoundPattern`
  `Pattern`*[E] {.preservesOr.} = ref object
    case orKind*: PatternKind
    of PatternKind.`SimplePattern`:
        `simplepattern`*: SimplePattern[E]

    of PatternKind.`CompoundPattern`:
        `compoundpattern`*: CompoundPattern[E]


  Binding*[E] {.preservesRecord: "named".} = ref object
    `name`*: Symbol
    `pattern`*: SimplePattern[E]

proc `$`*[E](x: Bundle[E] | CompoundPattern[E] | Modules[E] | Definitions[E] |
    DictionaryEntries[E] |
    NamedPattern[E] |
    SimplePattern[E] |
    NamedSimplePattern[E] |
    Definition[E] |
    NamedAlternative[E] |
    Schema[E] |
    Pattern[E] |
    Binding[E]): string =
  `$`(toPreserve(x, E))

proc encode*[E](x: Bundle[E] | CompoundPattern[E] | Modules[E] | Definitions[E] |
    DictionaryEntries[E] |
    NamedPattern[E] |
    SimplePattern[E] |
    NamedSimplePattern[E] |
    Definition[E] |
    NamedAlternative[E] |
    Schema[E] |
    Pattern[E] |
    Binding[E]): seq[byte] =
  encode(toPreserve(x, E))

proc `$`*(x: Ref | ModulePath | EmbeddedTypeName): string =
  `$`(toPreserve(x))

proc encode*(x: Ref | ModulePath | EmbeddedTypeName): seq[byte] =
  encode(toPreserve(x))
