import hmisc/hasts/[xml_ast, xsd_ast]
import hmisc/other/[oswrap, hshell]
import hmisc/algo/[halgorithm, hstring_algo, clformat,
                   hseq_mapping, namegen]
import std/[strutils, strformat, sequtils, with]
import hmisc/hdebug_misc
import hnimast
import hpprint

import fusion/matching

{.experimental: "caseStmtMacros".}

import std/parsexml

proc assertKind*[T, E: enum](node: T, kindPath: openarray[(int, E)]) =
  var next = node
  for (idx, kind) in kindPath:
    assert next[idx] == kind
    next = next[idx]

proc enumerationFields*(xsd: XsdEntry): seq[XsdEntry] =
  xsd.assertKind([(0, xekSimpleType), (0, xekRestriction)])
  # echo treeRepr(xsd, indexed = true)
  return xsd[0].subnodes


proc enumFieldName(str: string, prefix: string): string =
  let parts = @[prefix] & split(str, {'-', '_'})

  result = parts[0].toLowerAscii()
  for part in parts[1 ..^ 1]:
    result &= capitalizeAscii(part)

  var res: string
  for ch in result:
    res &= toLatinAbbrChar(ch)

  result = res



type PNType = NType[PNode]

#*************************************************************************#
#***********  ^^^^ Boilerplate to move into dependencies ^^^^  ***********#
#*************************************************************************#

using xsd: XsdEntry

type
  XsdCache = object
    enumNames: StringNameCache

using cache: var XsdCache


func fixTypeName(str: string): string =
  if str.isReservedNimType():
    return str

  else:
    capitalizeAscii(str.fixIdentName("X"))

proc identName*(xsd): string =
  if xsd.kind == xekExtension:
    "baseExt"

  else:
    xsd.name().fixIdentName("x")

proc typeName*(xsd): string =
  result = xsd.getType().getNimType()

proc kindTypeName*(xsd): string = xsd.typeName() & "Kind"
proc bodyTypeName*(xsd): string = xsd.typeName() & "Body"
proc parserName*(typeName: string): string =
  "parse" & capitalizeAscii(typeName)

proc kindEnumName*(name: string; parent: XsdEntry, cache): string =
  kindEnumName(name, parent.typeName(), cache.enumNames, true)


proc kindFieldName*(name: string; parent: XsdEntry, cache): string =
  "f" & kindEnumName(name, "F" & parent.typeName(), cache.enumNames, false)

proc fieldName*(name: string, cache): string =
  fixIdentName(name, "f", cache.enumNames)

# proc fieldName*(name: string, parent: XsdEntry, cache)

type
  XsdWrapperKind = enum
    xwkScalar
    xwkOption
    xwkSequence

  XsdType = object
    entry: XsdEntry
    ptype: PNType
    parserCall: string
    kind: XsdWrapperKind
    isPrimitive: bool

  XsdElementWrapperKind = enum
    xewkSingleSequence
    xewkUnboundedSequence
    xewkUnboundedChoice
    xewkSingleChoice

  XsdElementWrapper = object
    case kind*: XsdElementWrapperKind
      of xewkSingleSequence, xewkUnboundedSequence:
        xsdEntry: XsdEntry
        elements: seq[XsdType]

      of xewkUnboundedChoice, xewkSingleChoice:
        choiceEntry: XsdEntry
        alternatives: seq[XsdType]
        parent: XsdEntry


  XsdGenKind = enum
    xgkObject
    xgkEnum
    xgkDistinct

  XsdGenBase {.inheritable.} = object
    nimName {.requiresinit.}: string
    entry {.requiresinit.}: XsdEntry
    xsdType: XsdType

  XsdGenAttr = object of XsdGenBase
    xmlValue {.requiresinit.}: string

  XsdGenElement = object of XsdGenBase
    wrapper: XsdWrapperKind
    enumName {.requiresinit.}: string ## Associated enum constant (if field
                                      ## is used in `xsd:choice` or `mixed`
                                      ## objects)
    xmlTag {.requiresinit.}: string

  XsdGenEnum = object of XsdGenBase
    value: string

  XsdGen = object of XsdGenBase
    case kind: XsdGenKind
      of xgkObject:
        enumPrefix {.requiresinit.}: string
        attrs: seq[XsdGenAttr]
        elements: seq[XsdGenElement]
        isMixed: bool
        mixedStrField: Option[XsdGenElement]
        isChoice: bool
        choiceElements: seq[XsdGenElement]
        # kindTypeName: string
        # bodyTypeName: string

      of xgkEnum:
        values: seq[XsdGenEnum]

      of xgkDistinct:
        ## Base type is stored in `xsdType` field
        discard

using gen: XsdGen


proc kindTypeName*(gen): string = gen.nimName & "Kind"
proc bodyTypeName*(gen): string = gen.nimName & "Body"

proc typeForEntry(xsd): XsdType =
  var isPrimitive = xsd.getType().isPrimitiveType()
  var
    ptype: PNType
    parserCall: string

  if isPrimitive:
    let kind = xsd.getType().classifyPrimitiveTypeKind()
    ptype = newPType(kind.getNimName())
    parserCall = kind.getParserName()

  else:
    if xsd.getType().startsWith("xsd:"):
      raiseImplementError(xsd.getType)

    else:
      ptype = newPType(xsd.getType.fixTypeName())
      parserCall = "parse" & fixTypeName(xsd.getType)

  var wrapperKind: XsdWrapperKind
  if xsd.isOptional():
    if xsd.isUnboundedRepeat():
      wrapperKind = xwkSequence

    else:
      wrapperKind = xwkOption

  return XsdType(
    ptype: ptype, parserCall: parserCall,
    kind: wrapperKind, entry: xsd,
    isPrimitive: isPrimitive
  )

proc wrappedType(
    xsdType: XsdType,
    parent: XsdEntry,
    wrapperKind: XsdElementWrapperKind = xewkSingleSequence,
  ): PNtype =

  case wrapperKind:
    of xewkUnboundedSequence:
      newPType("seq", [xsdType.ptype])

    of xewkSingleSequence:
      case xsdType.kind:
        of xwkSequence: newPType("seq", [xsdType.ptype])
        of xwkOption:   newPType("Option", [xsdType.ptype])
        of xwkScalar:   xsdType.ptype

    of xewkUnboundedChoice:
      newPType("seq", [newPType(parent.bodyTypeName())])

    of xewkSingleChoice:
      newPType(parent.bodyTypeName())

proc typeForWrapper(xsd; parent: XsdEntry): XsdElementWrapper =
  var elements: seq[XsdType]

  var xsd = xsd
  if xsd.kind == xekGroupRef:
    xsd = xsd.groupRef[0]

  for element in xsd:
    case element.kind:
      of xekElement:
        if element.hasName():
          elements.add typeForEntry(element)

        else:
          echov "Element without name"

      else:
        # echov element.kind
        discard


  var kind: XsdElementWrapperKind

  if parent.isMixed():
    # `mixed` type might contain any number of string elements interleaved
    # with other elements, even if is defined using `xsd:sequence`.
    return XsdElementWrapper(
      kind: xewkUnboundedChoice,
      parent: parent,
      choiceEntry: xsd,
      alternatives: elements
    )

  case xsd.kind:
    of xekSequence:
      if xsd.isFinite():
        kind = xewkSingleSequence

      else:
        kind = xewkUnboundedSequence

      result = XsdElementWrapper(kind: kind)
      result.xsdEntry = xsd
      result.elements = elements

    of xekChoice:
      if xsd.isFinite():
        kind = xewkSingleChoice

      else:
        kind = xewkUnboundedChoice

      result = XsdElementWrapper(kind: kind)
      result.choiceEntry = xsd
      result.parent = parent
      result.alternatives = elements

    else:
      discard




proc toXsdEnum(xsd, cache): XsdGen =
  result = XsdGen(entry: xsd, nimName: xsd.name, kind: xgkEnum)
  let enumPrefix = enumPrefixForCamel(xsd.name)

  for field in enumerationFields(xsd):
    result.values.add XsdGenEnum(
      nimName: enumFieldName(field.value, enumPrefix),
      entry: xsd,
      value: field.value
    )

proc toXsdDistinct(xsd, cache): XsdGen =
  result = XsdGen(
    entry: xsd,
    nimName: xsd.name().fixTypeName(),
    xsdType: xsd[0].typeForEntry(),
    kind: xgkDistinct
  )

proc toXsdComplex(xsd, cache): XsdGen =
  var fieldCache: XsdCache
  result = XsdGen(
    entry: xsd, kind: xgkObject,
    nimName: xsd.typeName(),
    enumPrefix: enumPrefixForCamel(xsd.typeName()),
  )

  for attr in xsd.getAttributes():
    if attr.hasName():
      result.attrs.add XsdGenAttr(
        entry: xsd,
        nimName: attr.name().fieldName(fieldCache),
        xsdType: attr.typeForEntry(),
        xmlValue: attr.name()
      )

  if isPrimitiveExtension(xsd):
    result.elements.add XsdGenElement(
      nimName: "baseExt",
      xsdType: xsd.getExtensionSection().typeForEntry(),
      entry: nil,
      xmlTag: "",
      enumName: kindFieldName("baseExt", xsd, fieldCache)
    )


  for entry in xsd:
    case entry.kind:
      of xekAttribute:
        discard

      of xekSequence, xekChoice, xekGroupRef:
        let wrapper = typeForWrapper(entry, xsd)
        case wrapper.kind:
          of xewkSingleSequence:
            for element in wrapper.elements:
              result.elements.add XsdGenElement(
                nimName: element.entry.name().fieldName(fieldCache),
                xsdType: element,
                entry: element.entry,
                wrapper: xwkScalar,
                xmlTag: element.entry.name(),
                enumName: kindFieldName(
                  element.entry.identName(), xsd, cache))

          of xewkUnboundedSequence:
            if wrapper.elements.len == 1:
              let element = wrapper.elements[0]
              result.elements.add XsdGenElement(
                nimName: element.entry.name().fieldName(fieldCache),
                xsdType: element,
                entry: element.entry,
                wrapper: xwkSequence,
                xmlTag: element.entry.name(),
                enumName: kindFieldName(
                  element.entry.identName(), xsd, cache))

            else:
              raiseImplementError($wrapper.elements.len)

          of xewkUnboundedChoice:
            result.isChoice = true

            for alt in wrapper.alternatives:
              let id = alt.entry.name().kindEnumName(xsd, cache)
              result.elements.add XsdGenElement(
                nimName: alt.entry.name().fieldName(fieldCache),
                xsdType: alt,
                entry: alt.entry,
                wrapper: xwkScalar,
                enumName: alt.entry.name().kindEnumName(xsd, cache),
                xmlTag: alt.entry.name()
              )

            if xsd.isMixed():
              result.isMixed = true
              result.mixedStrField = some XsdGenElement(
                nimName: "mixedStr",
                entry: xsd,
                xmlTag: "",
                enumName: "mixedStr".kindEnumName(xsd, cache),
                xsdType: XsdType(
                  ptype: newPType("string"),
                  isPrimitive: true,
                  parserCall: xtkString.getParserName()
                )
              )

          else:
            raiseImplementKindError(wrapper)

      else:
        discard

proc toXsdGen(xsd, cache): seq[XsdGen] =
  case xsd.kind:
    of xekSimpleType:
      if isEnumerationType(xsd):
        result.add toXsdEnum(xsd, cache)

      elif isPrimitiveRestriction(xsd):
        result.add toXsdDistinct(xsd, cache)

    of xekComplexType:
      result.add toXsdComplex(xsd, cache)
      # if result.nimName == "":
      #   echov treeRepr(xsd)
      #   raiseImplementError("")

    of xekGroupDeclare:
      discard

    else:
      raiseImplementKindError(xsd)





proc parserForType(
    xsdType: XsdType, eventKinds: set[XmlEventKind],
    inTag: string = "", skipWrapperElement: bool = true,
    isMixed: bool = false
  ): PNode =

  result = newPCall(
    xsdType.parserCall,
    newPDotFieldExpr("target", xsdType.entry.identName()),
    newPIdent("parser"),
    newPLit(inTag)
  )

  if xsdType.isPrimitive:
    if skipWrapperElement:
      if len(eventKinds * {xmlElementStart, xmlElementOpen}) > 0:
        return pquote do:
          skipElementStart(parser, `inTag`)
          `result`
          skipElementEnd(parser, `inTag`)

  else:
    result.add newPLit(isMixed)


  # else:





proc newParseTargetPType(ptype: PNType): PNType =
  result = newPType(ntkGenericSpec)
  result.add newPType("seq", [ptype])
  result.add ptype
  result.add newPType("Option", [ptype])
  result = newPType("var", [result])

  # result.add newPType("var", [])
  # result.add newPType("var", [ptype])
  # result.add newPType("var", [newPType("Option", [ptype])])

proc generateTypeForObject(xsd, cache):
  tuple[main: PObjectDecl, choice: Option[(PObjectDecl, PEnumDecl)]] =

  result.main = newPObjectDecl(xsd.typeName())

  for attr in xsd.getAttributes():
    if attr.hasName():
      result.main.addField(
        attr.identName(),
        attr.typeForEntry().wrappedType(xsd))


  if isPrimitiveExtension(xsd):
    result.main.addField(
      "baseExt",
      xsd.getExtensionSection().typeForEntry().ptype
    )

  for entry in xsd:
    case entry.kind:
      of xekAttribute:
        discard

      of xekSequence, xekChoice, xekGroupRef:
        let wrapper = typeForWrapper(entry, xsd)
        # echov wrapper.kind, treeRepr(wrapper.xsdEntry)
        # raiseImplementError("")
        case wrapper.kind:
          of xewkSingleSequence:
            for element in wrapper.elements:
              result.main.addField(
                element.entry.identName(),
                element.wrappedType(xsd, wrapper.kind))

          of xewkUnboundedSequence:
            if wrapper.elements.len == 1:
              result.main.addField(
                wrapper.elements[0].entry.identName(),
                wrapper.elements[0].wrappedType(xsd, wrapper.kind))

            else:
              raiseImplementError($wrapper.elements.len)

          of xewkUnboundedChoice:
            result.main.addField(
              "xsdChoice",
              XsdType().wrappedType(xsd, wrapper.kind)
            )

            var
              genObject = newPObjectDecl(xsd.bodyTypeName())
              genEnum = newPEnumDecl(xsd.kindTypeName())

            var selector = newObjectCaseField(
              "kind", newPType(xsd.kindTypeName()))

            for alt in wrapper.alternatives:
              let id = alt.entry.name().kindEnumName(xsd, cache)
              selector.addBranch(
                id.newPIdent(),
                newObjectField(
                  alt.entry.name().kindFieldName(xsd, cache),
                  alt.ptype))

              genEnum.addField(id, docComment = alt.entry.name().wrap("``"))

            if xsd.isMixed():
              let id = kindEnumName("mixedStr", xsd, cache)
              genEnum.addField(id, docComment = "`std:mixed` string content")

              selector.addBranch(
                id.newPIdent(),
                newObjectField("mixedStr", newPType("string")))

            genObject.addField(selector)

            result.choice = some((genObject, genEnum))



          else:
            raiseImplementKindError(wrapper)

      else:
        discard
        # echov entry.kind

proc generateParserForObject(xsd, cache): PProcDecl =
  let targetName = xsd.name.fixTypeName()
  result = newPProcDecl("parse" & targetName, iinfo = currIInfo())

  result.addArgument("target", newParseTargetPType(
    newPType(targetName)))

  result.addArgument(
    "parser",
    newPtype("var", ["HXmlParser"])
  )

  result.addArgument("tag", newPType("string"))
  result.addArgument("inMixed", newPType("bool"), value = some newPIdent("false"))


  let
    next = newPDotFieldExpr("parser", newPCall("next"))
    inAttributes = newPident("inAttributes")


  var attrCase = newCaseStmt(newPDotFieldExpr("parser", "attrKey"))
  for attr in xsd.getAttributes():
    if attr.hasName() and attr.hasType():
      attrCase.addBranch(
        newPLit(attr.name),
        # newAsgn(
        #   newPDotFieldExpr("target", attr.name),
        #   newPCall("parse" & attr.xsdType, newPident("parser"))
        # )
        newPCall(
          attr.typeForEntry().parserCall,
          newPDotFieldExpr("target", attr.identName()),
          newPIdent("parser"),
          newPLit(attr.name)
        )
      )

  attrCase.addBranch pquote do:
    @@@<<(posComment())
    if not(startsWith(parser.attrKey(), ["xmlns:", "xsi:", "xml:"])):
      raiseUnexpectedAttribute(parser)

  var mainCase = newCaseStmt(newPDotFieldExpr("parser", "kind"))

  mainCase.addBranch(
    xmlAttribute,
    attrCase,
    next
  )

  var bodyCase = newCaseStmt(newPDotFieldExpr(
    "parser", newPCall("elementName")))

  proc addFieldBranch(
      target: var PNode, field: XsdType,
      wrapper: XsdElementWrapper
    ) =

    if field.entry.hasName() and field.entry.hasType():
      let parseCall = parserForType(
        field,
        {xmlElementStart, xmlElementEnd},
        field.entry.name(),
        isMixed = xsd.isMixed()
      )
        # newPCall(
        # field.parserCall,
        # newPDotFieldExpr("target", field.entry.identName()),
        # newPIdent("parser"),
        # field.entry.name().newPLit()
      # )

      target.addBranch(
        newPLit(field.entry.name()),
        addPositionComment(parseCall))

  var used = {
    xmlError, xmlEof, xmlCharData, xmlWhitespace,
    xmlComment, xmlPI, xmlCData, xmlEntity, xmlSpecial
  }

  let bodyKind = xsd.bodyTypeName().newPIdent()
  for element in xsd:
    if element.kind in {xekSequence, xekChoice}:
      let wrapper = typeForWrapper(element, xsd)
      case wrapper.kind:
        of xewkSingleSequence:
          for field in wrapper.elements:
            addFieldBranch(bodyCase, field, wrapper)

        of xewkUnboundedSequence:
          if len(wrapper.elements) == 1:
            addFieldBranch(bodyCase, wrapper.elements[0], wrapper)

          else:
            raiseImplementError(
              "More than one element in unbounded sequence")

        of xewkUnboundedChoice:
          var parsers: XsdParsers
          if xsd.isMixed() and xsd[0].kind notin {xekSequence}:
            parsers = getFirstParsers(@[xsd])

          else:
            parsers = mapIt(wrapper.alternatives, it.entry).getFirstParsers()

          used.excl xmlCharData

          let token = newPIdent("token")
          var
            expected: set[XsdTokenKind] = getExpectedKinds(parsers)
            tokenCase = newCaseStmt(newPDotFieldExpr(token, "kind"))
            nameCase = newCaseStmt(newPDotFieldExpr(token, "name"))

          let addcall = newPIdent("add")

          for parser in parsers.onKinds & parsers.onNames:
            let
              field = parser.entry.get().name().kindFieldName(xsd, cache).newPIdent()
              targetType = parser.entry.get().typeName().newPType()

            let
              kindName = parser.entry.get().name().kindEnumName(xsd, cache).newPident()
              tag = if parser.onKind: "" else: parser.tag
              inMixed = newPLit(xsd.isMixed())

            var args = @[newPIdent("tmp"), newPIdent("parser"), newPLit(tag)]
            if not parser.entry.get().getType().isPrimitiveType():
              args.add inMixed

            let body = pquote do:
              @@@<<(posComment())
              var tmp: `targetType.toNNode()`
              `newPIdent(parser.parser)`(@@@args)
              var tmp2 = `bodyKind`(kind: `kindName`, `field`: tmp)
              `addCall`(target.xsdChoice, tmp2)

            if parser.onKind:
              tokenCase.addBranch(parser.kind, body)

            else:
              bodyCase.addBranch(parser.tag, body)

          nameCase.addBranch:
            pquote do:
              raiseUnexpectedToken(parser, token)

          tokenCase.addBranch({xtkElementStart, xtkElementOpen}, nameCase)
          let id = kindEnumName("mixedStr", xsd, cache).newPIdent()
          tokenCase.addBranch:
            pquote do:
              @@@<<(posComment())
              var tmp: string
              parseXsdString(tmp, parser)
              var tmp2 = `bodyKind`(kind: `id`, mixedStr: tmp)
              add(target.xsdChoice, tmp2)


          mainCase.addBranch(
            xmlCharData,
            pquote do:
              @@@<<(posComment())
              let `token` = parser.xsdToken(`newPLit(expected)`)
              `tokenCase`
          )

        else:
          discard
          # raiseImplementKindError(wrapper)

  if xmlCharData in used and xsd.isMixed():
    let id = kindEnumName("mixedStr", xsd, cache).newPIdent()
    used.excl xmlCharData
    mainCase.addBranch(
      xmlCharData,
      pquote do:
        @@@<<(posComment())
        var tmp: string
        parseXsdString(tmp, parser)
        var tmp2 = `bodyKind`(kind: `id`, mixedStr: tmp)
        add(target.xsdChoice, tmp2)
    )


  bodyCase.addBranch pquote do:
    @@@<<(posComment())
    if inMixed:
      return

    else:
      raiseUnexpectedElement(parser)

  mainCase.addBranch(
    {xmlElementOpen, xmlElementStart},
    pquote do:
      if parser.kind == xmlElementOpen:
        `inAttributes` = true

      `bodyCase`

      # `next`
  )


  # if xsd.isMixed():
  #   let
  #     id = kindEnumName("mixedStr", xsd).newPIdent()
  #     bodyKind = xsd.bodyTypeName().newPIdent()

  #   used.excl xmlCharData
  #   mainCase.addBranch(
  #     xmlCharData,
  #     pquote do:
  #       @@@<<(posComment())
  #       var tmp: string
  #       parseXsdString(tmp, parser)
  #       var tmp2 = `bodyKind`(kind: `id`, mixedStr: tmp)
  #       add(target.xsdChoice, tmp2)
  #   )


  # if xsd.findIt(it.kind == xekSequence) == 0:
  #   let wrapper = typeForWrapper(xsd[0], xsd)

  #   if wrapper.elements.len > 0:
  #     let
  #       first = wrapper.elements[0]
  #       call = newPIdent(first.parserCall)
  #       name = first.entry.identName().newPIdent()

  #     used.excl xmlCharData
  #     mainCase.addBranch(
  #       xmlCharData,
  #       pquote do:
  #         @@@<<(posComment())
  #         `call`(target.`name`, parser, tag)
  #     )

    # else:
    #   raiseImplementError(xsd.treeRepr())

  if isPrimitiveExtension(xsd):
    let extension = xsd.getExtensionSection()
    let target = extension.typeForEntry().
      parserForType({xmlCharData}, skipWrapperElement = false)

    used.excl xmlCharData
    mainCase.addBranch(xmlCharData, target)

  mainCase.addBranch(
    used,
    pquote do:
      @@@<<(posComment())
      echo parser.displayAt()
      assert false
  )

  mainCase.addBranch(xmlElementClose, next)
  mainCase.addBranch(
    xmlElementEnd,
    pquote do:
      if parser.elementName() == tag:
        `next`
        break

      else:
        raiseUnexpectedElement(parser)
  )

  let parseName = newPIdent(result.name)

  # let alwaysElement = not isPossiblePrimitiveType(xsd)

  # if xsd.hasAttr("mixed"):
  #   echov xsd.treeRepr()
  #   echov alwaysElement

  let first = getFirstSet(xsd)

  result.impl = pquote do:
    @@@<<(posComment())
    when target is seq:
      while parser.elementName == tag:
        var res: typeof(target[0])
        `parsename`(res, parser, tag)
        add(target, res)

    elif target is Option:
      if parser.elementName == tag:
        var res: typeof(target.get())
        `parseName`(res, parser, tag)
        target = some(res)

    else:
      next(parser)
      var `inAttributes` = false
      while true:
        `mainCase`



proc generateForEnum*(xsd): tuple[decl: PEnumDecl, parser: PProcDecl] =
  result.decl = newPEnumDecl(xsd.name)
  let enumPrefix = enumPrefixForCamel(xsd.name)

  var mainCase = newCaseStmt(
    newPDotFieldExpr("parser", "strVal"))


  for field in enumerationFields(xsd):
    let fieldName = enumFieldName(field.value, enumPrefix)
    mainCase.addBranch(
      newPLit(field.value),
      newAsgn(newPident("target"), newPIdent(fieldName))
    )

    result.decl.addField(
      fieldName,
      docComment = &"XSD enumeration: `{field.value}`"
    )

  result.parser = newPProcDecl("parse" & result.decl.name, iinfo = currIInfo())


  result.parser.addArgument(
    "target",
    newParseTargetPType(newPType(result.decl.name)))

  result.parser.addArgument("parser", newPtype("var", ["HXmlParser"]))
  result.parser.addArgument("tag", newPType("string"))

  let parsename = newPIdent(result.parser.name)

  result.parser.impl = pquote do:
    @@@<<(posComment())
    when target is seq:
      var res: typeof(target[0])
      `parsename`(res, parser, tag)
      add(target, res)

    elif target is Option:
      var res: typeof(target.get())
      `parseName`(res, parser, tag)
      target = some(res)

    else:
      `mainCase`

proc generateForXsd(xsd, cache): seq[PNimDecl] =
  case xsd.kind:
    of xekSimpleType:
      if isEnumerationType(xsd):
        let (decl, parser) = generateForEnum(xsd)
        return @[toNimDecl decl, toNimDecl parser]

      elif isPrimitiveRestriction(xsd):
        let xsdType = xsd[0].typeForEntry()
        let targetType = xsd.name().fixTypeName()
        result.add toNimDecl newAliasDecl(targetType.newPType(), xsdType.ptype)

        var parser = newPProcDecl(targetType.parserName(), iinfo = currIInfo())

        parser.addArgument("target", newParseTargetPType(newPType(targetType)))
        parser.addArgument("parser", newPType("var", ["HXmlParser"]))
        parser.addArgument("tag", newPType("string"))

        let
          baseParseCall = newPIdent(xsdType.parserCall)
          parseCall = newPIdent(parser.name)
          baseType = xsdType.ptype.toNNode()
          newType = newPIdent(targetType)


        parser.impl = pquote do:
          @@@<<(posComment())
          when target is seq:
            var res: typeof(target[0])
            `parseCall`(res, parser, tag)
            add(target, res)

          elif target is Option:
            var res: typeof(target.get())
            `parseCall`(res, parser, tag)
            target = some(res)

          else:
            var tmp: `baseType`
            `baseParseCall`(tmp, parser)
            target = `newType`(tmp)

        result.add toNimDecl parser

      else:
        echov treeRepr(xsd)

    of xekComplexType:
      let (decl, wrapped) = generateTypeForObject(xsd, cache)
      result.add decl
      if wrapped.isSome():
        let (objectDecl, enumDecl) = wrapped.get()
        result.add toNimDecl(enumDecl)
        result.add toNimDecl(objectDecl)

      result.add toNimDecl(generateParserForObject(xsd, cache))



    of xekGroupDeclare:
      discard

    else:
      echov treeRepr(xsd)

proc choiceFields(gen): seq[XsdGenElement] =
  result = gen.choiceElements
  if gen.isMixed:
    result.add gen.elements
    result.add gen.mixedStrField.get()

proc generateForObject(gen, cache): seq[PNimDecl] =
  # if gen.nimName == "SpType":
  #   echov gen.entry.treeRepr()
  #   raiseImplementError("")

  # echov gen.nimName
  var parser = newPProcDecl("parse" & gen.nimname, iinfo = currIInfo())
  with parser:
    addArgument("target", gen.nimName.newPType())
    addArgument("parser", newPtype("var", ["HXmlParser"]))
    addArgument("tag", newPType("string"))
    addArgument("inMixed", newPType("bool"),
                value = some newPIdent("false"))

  var
    next = newPDotFieldExpr("parser", newPCall("next"))
    genObject = newPObjectDecl(gen.nimName)

    attrCase = newCaseStmt(newPDotFieldExpr("parser", "attrKey"))
    mainCase = newCaseStmt(newPDotFieldExpr("parser", "kind"))
    bodyCase = newCaseStmt(newPDotFieldExpr("parser", newPCall("elementName")))

  for attr in gen.attrs:
    genObject.addField(attr.nimName, attr.xsdType.ptype)
    attrCase.addBranch(
      newPLit(attr.entry.name),
      newPCall(
        attr.xsdType.parserCall,
        newPDotFieldExpr("target", attr.nimName),
        newPIdent("parser"),
        newPLit(attr.entry.name)))

  attrCase.addBranch pquote do:
    @@@<<(posComment())
    if not(startsWith(parser.attrKey(), ["xmlns:", "xsi:", "xml:"])):
      raiseUnexpectedAttribute(parser)

  mainCase.addBranch(xmlAttribute, attrCase, next)

  if gen.isMixed or gen.choiceElements.len > 0:
    var
      genEnum = newPEnumDecl(gen.kindTypeName())
      selector = newObjectCaseField("kind", newPType(gen.kindTypeName))
      bodyObject = newPObjectDecl(gen.bodyTypeName())

    let
      bodyKind = gen.kindTypeName.newPIdent()


    for alt in gen.choiceFields():
      selector.addBranch(
        newPIdent(alt.enumName),
        newObjectField(alt.nimName, alt.xsdType.ptype,
                       docComment = alt.entry.name()))

      genEnum.addField(alt.enumName)

      var args = @[newPIdent("tmp"), newPIdent("parser"), newPLit(alt.xmlTag)]
      if not gen.xsdType.isPrimitive:
        args.add newPLit(gen.isMixed)

      let body = pquote do:
        @@@<<(posComment())
        var tmp: `alt.xsdType.ptype.toNNode()`
        `newPIdent(alt.xsdType.parserCall)`(@@@args)
        add(
          target.xsdChoice,
          `bodyKind`(
            kind: `newPIdent(alt.enumName)`,
            `newPident(alt.nimName)`: tmp
          )
        )

      if alt.nimName == "mixedStr":
        mainCase.addBranch(xmlCharData, body)

      else:
        bodyCase.addBranch(alt.xmlTag, body)

    bodyObject.addField(selector)

    genObject.addField("body", newPType("seq", [bodyObject.name]))

    result.add toNimDecl(genEnum)
    result.add toNimDecl(bodyObject)
    result.add toNimDecl(genObject)

  else:
    for elem in gen.elements:
      genObject.addField(elem.nimName, elem.xsdType.ptype)
      var parseCall = newPCall(
        elem.xsdType.parserCall,
        newPDotFieldExpr("target", elem.nimName),
        newPIdent("parser"),
        newPLit(elem.xmlTag)
      )

      if elem.xsdType.isPrimitive:
        parseCall = pquote do:
          skipElementStart(parser, `elem.xmlTag`)
          `parseCall`
          skipElementEnd(parser, `elem.xmlTag`)

      else:
        parseCall.add newPLit(gen.isMixed)

      bodyCase.addBranch(
        newPLit(elem.xmlTag), addPositionComment(parseCall))

    result.add toNimDecl(genObject)


  bodyCase.addBranch pquote do:
    @@@<<(posComment())
    if inMixed: return
    else: raiseUnexpectedElement(parser)


  mainCase.addBranch(xmlElementClose, next)
  mainCase.addBranch({xmlElementOpen, xmlElementStart}):
    pquote do:
      `bodyCase`

  mainCase.addBranch(xmlElementEnd):
    pquote do:
      if parser.elementName() == tag:
        `next`
        break

      else:
        raiseUnexpectedElement(parser)


  let parsename = newPIdent("parse" & gen.nimName)
  parser.impl = pquote do:
    @@@<<(posComment())
    when target is seq:
      while parser.elementName == tag:
        var res: typeof(target[0])
        `parsename`(res, parser, tag)
        add(target, res)

    elif target is Option:
      if parser.elementName == tag:
        var res: typeof(target.get())
        `parseName`(res, parser, tag)
        target = some(res)

    else:
      next(parser)
      while true:
        `mainCase`


  result.add toNimDecl parser

proc generateForEnum(gen, cache): tuple[decl: PEnumDecl, parser: PProcDecl] =
  result.decl = newPEnumDecl(gen.nimName)
  result.parser = newPProcDecl("parse" & gen.nimName, iinfo = currIInfo())

  var mainCase = newCaseStmt(newPDotFieldExpr("parser", "strVal"))

  for field in gen.values:
    mainCase.addBranch(
      newPLit(field.value),
      newAsgn(newPident("target"), newPIdent(field.nimName)))

    result.decl.addField(
      field.nimName,
      docComment = &"XSD enumeration: `{field.value}`")

  result.parser.addArgument(
    "target",
    newParseTargetPType(newPType(result.decl.name)))

  result.parser.addArgument("parser", newPtype("var", ["HXmlParser"]))
  result.parser.addArgument("tag", newPType("string"))

  let parsename = newPIdent(result.parser.name)

  result.parser.impl = pquote do:
    @@@<<(posComment())
    when target is seq:
      var res: typeof(target[0])
      `parsename`(res, parser, tag)
      add(target, res)

    elif target is Option:
      var res: typeof(target.get())
      `parseName`(res, parser, tag)
      target = some(res)

    else:
      `mainCase`


proc generateForDistinct(gen, cache):
  tuple[decl: PAliasDecl, parser: PProcDecl] =

  result.decl = newAliasDecl(gen.nimName.newPType(), gen.xsdType.ptype)
  result.parser = newPProcDecl(gen.nimName.parserName(), iinfo = currIInfo())

  with result.parser:
    addArgument("target", result.decl.newType)
    addArgument("parser", newPType("var", ["HXmlParser"]))
    addArgument("tag", newPType("string"))

  let
    baseParseCall = newPIdent(result.parser.name)
    parseCall = newPIdent(result.parser.name)
    baseType = result.decl.oldType.toNNode()
    newType = result.decl.newType.toNNode()

  result.parser.impl = pquote do:
    @@@<<(posComment())
    when target is seq:
      var res: typeof(target[0])
      `parseCall`(res, parser, tag)
      add(target, res)

    elif target is Option:
      var res: typeof(target.get())
      `parseCall`(res, parser, tag)
      target = some(res)

    else:
      var tmp: `baseType`
      `baseParseCall`(tmp, parser)
      target = `newType`(tmp)



proc generateForXsd(gen: XsdGen, cache): seq[PNimDecl] =
  case gen.kind:
    of xgkEnum:
      let (decl, parser) = generateForEnum(gen, cache)
      result.add toNimDecl(decl)
      result.add toNimDecl(parser)

    of xgkObject:
      result.add generateForObject(gen, cache)

    of xgkDistinct:
      let (decl, parser) = generateForDistinct(gen, cache)
      result.add toNimDecl(decl)
      result.add toNimDecl(parser)

proc withoutImpl*[N](decl: ProcDecl[N]): ProcDecl[N] =
  result = decl
  result.impl = nil

proc generateForXsd*(xsd: AbsFile): seq[PNimDecl] =
  let document = parseXsd(xsd)
  var
    procs: seq[PNimDecl]
    types: seq[PNimTypeDecl]
    forward: seq[PNimDecl]
    cache: XsdCache

  for entry in document:
    for tmp in toXsdGen(entry, cache):
      for generated in tmp.generateForXsd(cache):
        if generated.kind in {nekObjectDecl, nekEnumDecl, nekAliasDecl}:
          types.add toNimTypeDecl(generated)

        elif generated.kind in {nekProcDecl}:
          forward.add toNimDecl(generated.procDecl.withoutImpl())
          procs.add generated

        else:
          procs.add generated

  result.add toNimDecl(types)
  result.add forward
  result.add procs

proc writeXsdGenerator*(decls: seq[PNimDecl], target: AbsFile) =
  target.writeFile(
    """
import std/[options]
import hmisc/hasts/[xml_ast]
export options, xml_ast

import hmisc/algo/halgorithm

""" & $decls
  )

when isMainModule:
  startHax()
  let decls = generateForXsd(AbsFile "/tmp/schema.xsd")

  AbsFile("/tmp/res.nim").writeFile(decls)

  execShell shellCmd(nim, check, errorMax = 2, "/tmp/res.nim")

  "/tmp/parse.nim".writeFile(
    """
import res
import hmisc/hexceptions
import hmisc/hdebug_misc

startHax()

var parser = newHXmlParser(AbsFile "/tmp/in.xml")

var doxygen: DoxygenType

try:
  parseDoxygenType(doxygen, parser, "doxygen")

except:
  pprintErr()


echo "Done parsing"

import hpprint

echo doxygen

"""
  )

  execShell shellCmd(nim, r, "/tmp/parse.nim")

  echo "done"
