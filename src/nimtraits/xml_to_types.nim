import hmisc/hasts/[xml_ast, xsd_ast]
import hmisc/other/[oswrap, hshell]
import hmisc/algo/[halgorithm, hstring_algo, clformat,
                   hseq_mapping, namegen]
import std/[strutils, strformat, sequtils]
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

proc addBranch*[N](main: var N, expr: N, body: varargs[N]) =
  case main.kind.toNNK():
    of nnkCaseStmt:
      if body.len == 0:
        main.add newNTree[N](nnkElse, expr)

      else:
        main.add newNTree[N](
          nnkOfBranch, expr,
          newNTree[N](nnkStmtList, newEmptyNNode[N]() & toSeq(body)))

    else:
      raiseImplementKindError(main)

proc newNLit*[N, T](item: T): N =
  when N is NimNode:
    newLit(item)

  else:
    newPLit(item)

proc addBranch*[N](main: var N, expr: enum, body: varargs[N]) =
  addBranch(main, newNIdent[N]($expr), body)

proc addBranch*[N](main: var N, expr: string, body: varargs[N]) =
  addBranch(main, newNLit[N, string]($expr), body)

# proc addBranch*[N](main: var N, body: N) =
#   case main.kind.toNNK():

proc newPLit*(e: enum): PNode =
  proc enumToStr(x: enum): string {.magic: "EnumToStr", noSideEffect.}
  return newPIdent(enumToStr(e))

proc newPLit*[T](s: set[T]): PNode =
  result = nnkCurly.newPTree()
  for value in s:
    result.add newPLit(value)

proc addBranch*[N, E](main: var N, expr: set[E], body: varargs[N]) =
  addBranch(main, newPLit(expr), body)

proc newAsgn*[N](lhs, rhs: N): N = newNTree[N](nnkAsgn, lhs, rhs)
proc toPNode*(node: PNode): PNode = node
proc toPNode*(val: string): PNode = newPLit(val)
proc newCaseStmt*[N](expr: N): N =
  newNTree[N](nnkCaseStmt, expr)

proc newPDotExpr*(lhs, rhs: PNode | string): PNode =
  newPTree(nnkDotExpr, toPNode(lhs), toPNode(rhs))

proc newPDotFieldExpr*(lhs, rhs: PNode | string): PNode =
  result = newPTree(
    nnkDotExpr, (when lhs is PNode: lhs else: newPident(lhs)))

  when rhs is PNode:
    result.add rhs

  else:
    result.add newPIdent(rhs)

proc newPDotCall*(
    main: string | PNode, callName: string,
    args: varargs[PNode]
  ): PNode =

  var call = newPCall(callName, args)
  result = newPTree(nnkDotExpr, toPNode(main), call)




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





proc enumFieldName(str: string, prefix: string): string =
  let parts = @[prefix] & split(str, {'-', '_'})

  result = parts[0].toLowerAscii()
  for part in parts[1 ..^ 1]:
    result &= capitalizeAscii(part)

  var res: string
  for ch in result:
    res &= toLatinAbbrChar(ch)

  result = res

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

  result.main = newPObjectDecl(
    xsd.typeName(),
#     docComment =
#       xsd.treeRepr(colored = false) & &"""

# - is primitive restriction: {xsd.isPrimitiveRestriction()}
# - is primitive extension: {xsd.isPrimitiveExtension()}
# """
  )

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
      # # if `alwaysElement` or parser.kind in {xmlElementStart, xmlElementOpen}:
      #   if parser.elementName() != tag:
      #     raiseUnexpectedElement(parser, tag)

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

  result.parser = newPProcDecl("parse" & result.decl.name)


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

        var parser = newPProcDecl(targetType.parserName())

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
    for generated in generateForXsd(entry, cache):
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
