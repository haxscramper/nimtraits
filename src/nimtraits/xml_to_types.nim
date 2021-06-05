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
  "loadXml"
  # "parse" & capitalizeAscii(typeName)

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
    nimName: string
    entry: XsdEntry
    xsdType: XsdType

  XsdGenAttr = object of XsdGenBase
    xmlName {.requiresinit.}: string

  XsdGenElement = object of XsdGenBase
    wrapper: XsdWrapperKind
    enumName: string ## Associated enum constant (if field
                                      ## is used in `xsd:choice` or `mixed`
                                      ## objects)
    xmlTag: string

  XsdGenEnum = object of XsdGenBase
    value: string

  XsdGenChoice = object
    nimName: string
    xsdType: XsdType
    elements: seq[XsdGenElement]

  XsdGen = object of XsdGenBase
    case kind: XsdGenKind
      of xgkObject:
        enumPrefix {.requiresinit.}: string
        attrs: seq[XsdGenAttr]
        baseExtField: Option[XsdGenElement]
        case isMixed: bool
          of true:
            mixedStrField: XsdGenElement

          of false:
            discard

        case isChoice: bool
          of true:
            choiceElements: seq[XsdGenChoice]

          of false:
            elements: seq[XsdGenElement]

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

  elif xsd.isUnboundedRepeat():
    wrapperKind = xwkSequence

  if xsd.getType() in ["memberdefType"]:
    echov xsd.getType(), wrapperKind
    echov xsd.treeRepr()

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

proc groupElements(xsd: XsdEntry): seq[XsdEntry] =
  if xsd.kind == xekGroupRef:
    for item in xsd.groupRef[0]:
      result.add groupElements(item)

  else:
    result.add xsd


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

      of xekGroupRef:
        for element in element.groupElements():
          if element.hasName():
            elements.add typeForEntry(element)

      else:
        discard
        # echov element.kind
        # echov element.treeRepr()

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

      for element in mitems(result.elements):
        element.ptype = wrappedType(element, xsd, kind)

    of xekChoice:
      if xsd.isFinite():
        kind = xewkSingleChoice

      else:
        kind = xewkUnboundedChoice

      result = XsdElementWrapper(kind: kind)
      result.choiceEntry = xsd
      result.parent = parent
      result.alternatives = elements

      for element in mitems(result.alternatives):
        element.ptype = wrappedType(element, xsd, kind)


    else:
      raise newUnexpectedKindError(xsd)




proc toXsdEnum(xsd, cache): XsdGen =
  result = XsdGen(entry: xsd, nimName: xsd.name, kind: xgkEnum,
                  xsdType: XsdType(isPrimitive: false))

  let enumPrefix = enumPrefixForCamel(xsd.name)

  for field in enumerationFields(xsd):
    result.values.add XsdGenEnum(
      nimName: enumFieldName(field.value, enumPrefix),
      entry: xsd,
      value: field.value,
      xsdType: XsdType(isPrimitive: false)
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
    xsdType: XsdType(isPrimitive: false),
    isChoice: isChoiceType(xsd) or isMixed(xsd),
    isMixed: isMixed(xsd)
  )



  for attr in xsd.getAttributes():
    if attr.hasName():
      var t = attr.typeForEntry()
      if attr.isOptional():
        t.ptype = newPType("Option", [t.ptype])

      result.attrs.add XsdGenAttr(
        entry: xsd,
        nimName: attr.name().fieldName(fieldCache),
        xsdType: t,
        xmlName: attr.name()
      )

  if isPrimitiveExtension(xsd):
    result.baseExtField = some XsdGenElement(
      nimName: "baseExt",
      xsdType: xsd.getExtensionSection().typeForEntry(),
      entry: nil,
      xmlTag: "",
      enumName: kindFieldName("baseExt", xsd, fieldCache)
    )

  if isMixed(xsd):
    result.mixedStrField = XsdGenElement(
      nimName: "mixedStr",
      entry: xsd,
      xmlTag: "",
      enumName: "mixedStr".kindEnumName(xsd, cache),
      xsdType: XsdType(
        ptype: newPType("string"),
        isPrimitive: true,
        parserCall: xtkString.getParserName()))

  for entry in xsd:
    case entry.kind:
      of xekAttribute, xekSimpleContent:
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
            var elements: seq[XsdGenElement]
            for alt in wrapper.alternatives:
              let id = alt.entry.name().kindEnumName(xsd, cache)
              elements.add XsdGenElement(
                nimName: alt.entry.name().fieldName(fieldCache),
                xsdType: alt,
                entry: alt.entry,
                wrapper: xwkScalar,
                enumName: alt.entry.name().kindEnumName(xsd, cache),
                xmlTag: alt.entry.name()
              )

            for group in elements.groupByIt(it.xsdType.ptype):
              result.choiceElements.add XsdGenChoice(
                nimName: group[0].xsdType.ptype.head.fieldName(fieldCache),
                xsdType: group[0].xsdType,
                elements: group
              )


          else:
            raiseImplementKindError(wrapper)

      else:
        raise newUnexpectedKindError(entry, entry.treeRepr())

proc toXsdGen(xsd, cache): seq[XsdGen] =
  case xsd.kind:
    of xekSimpleType:
      if isEnumerationType(xsd):
        result.add toXsdEnum(xsd, cache)

      elif isPrimitiveRestriction(xsd):
        result.add toXsdDistinct(xsd, cache)

    of xekComplexType:
      result.add toXsdComplex(xsd, cache)

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


proc newParseTargetPType(ptype: PNType): PNType =
  result = newPType("var", [ptype])
  # newPType(ntkGenericSpec)
  # result.add newPType("seq", [ptype])
  # result.add ptype
  # result.add newPType("Option", [ptype])
  # result =

proc newMixed(objName, enumName: string): seq[PNode] =
  result.add nnkObjConstr.newPTree(
    newPIdent(objName),
    nnkExprColonExpr.newPTree(
      newPIdent("kind"),
      newPIdent(enumName)
    )
  )

  result.add nnkDotExpr.newPTree(
    newPIdent("next"), newPIdent("mixedStr"))


proc generateForObject(gen, cache): seq[PNimDecl] =
  var parser = newPProcDecl(gen.nimname.parserName(), iinfo = currIInfo())
  with parser:
    addArgument("parser", newPtype("var", ["HXmlParser"]))
    addArgument("target", gen.nimName.newPType().newParseTargetPType())
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
      newPLit(attr.xmlName),
      newPCall(
        "loadXml",
        # attr.xsdType.parserCall,
        newPIdent("parser"),
        newPDotFieldExpr("target", attr.nimName),
        newPLit(attr.xmlName)))

  attrCase.addBranch pquote do:
    @@@<<(posComment())
    if not(startsWith(parser.attrKey(), ["xmlns:", "xsi:", "xml:"])):
      raiseUnexpectedAttribute(parser)

    else:
      parser.next()

  mainCase.addBranch(XmlEventKind.xmlAttribute, attrCase)

  var unused = {
    xmlError, xmlEof, xmlCharData, xmlWhitespace,
    XmlEventKind.xmlComment, xmlPI, XmlEventKind.xmlCData, xmlEntity, xmlSpecial
  }


  if gen.baseExtField.isSome():
    unused.excl xmlCharData
    let field = gen.baseExtField.get()

    genObject.addField(field.nimName, field.xsdType.ptype)

    mainCase.addBranch(xmlCharData):
      pquote do:
        @@@<<(posComment())
        var tmp: `field.xsdType.ptype.toNNode()`
        `newPIdent(field.xsdType.parserCall)`(tmp, parser, "")
        target.`newPIdent(field.nimName)` = tmp


  if gen.isMixed or gen.isChoice:
    if gen.isMixed:
      unused.excl xmlCharData

    var
      genEnum = newPEnumDecl(gen.kindTypeName())
      selector = newObjectCaseField("kind", newPType(gen.kindTypeName))
      bodyObject = newPObjectDecl(gen.bodyTypeName())

    for group in gen.choiceElements:
      selector.addBranch(
        group.elements.mapIt(newPIdent(it.enumName)),
        newObjectField(group.nimName, group.xsdType.ptype))

      var nameMapCase = newCaseStmt(newPDotFieldExpr("parser", newPCall("elementName")))
      var altCount = 0
      for alt in group.elements:
        inc altCount
        genEnum.addField(alt.enumName)
        nameMapCase.addBranch(alt.xmlTag, newPIdent(alt.enumName))

      if altCount <= 1:
        nameMapCase = newPIdent(group.elements[0].enumName)

      else:
        nameMapCase.addBranch(newPIdent(group.elements[0].enumName))

      var args = @[
        newPIdent("parser"),
        newPIdent("tmp"),
        newPDotCall("parser", "elementName")]

      let body =
        if nameMapCase.kind == nkIdent:
          pquote do:
            @@@<<(posComment())
            var tmp: `group.xsdType.ptype.toNNode()`
            loadXml(@@@args)

            add(
              target.xsdChoice,
              `gen.bodyTypeName().newPIdent()`(
                kind: `nameMapCase`, `newPident(group.nimName)`: tmp))

        else:
          pquote do:
            @@@<<(posComment())
            let kind = `nameMapCase`
            var tmp: `group.xsdType.ptype.toNNode()`
            loadXml(@@@args)

            var tmp2 = `gen.bodyTypeName().newPIdent()`(kind: kind)
            tmp2.`newPident(group.nimName)` = tmp

            add(target.xsdChoice, tmp2)

      bodyCase.addBranch(mapIt(group.elements, it.xmlTag), body)

    if gen.isMixed:
      let alt = gen.mixedStrField
      genEnum.addField(alt.enumName)
      selector.addBranch(
        newPIdent(alt.enumName),
        newObjectField(alt.nimName, alt.xsdType.ptype))

      mainCase.addBranch(xmlCharData):
        pquote do:
          @@@<<(posComment())
          var tmp: string
          parseXsdString(tmp, parser, "")
          add(
            target.xsdChoice,
            `gen.bodyTypeName().newPIdent()`(
              kind: `newPIdent(alt.enumName)`, mixedStr: tmp))

      result.add toNimDecl(
        newPProcDecl(
          "len", {"item": genObject.name}, some newPType("int"),
          impl = pquote(item.xsdChoice.len)
      ))

      result.add toNimDecl(
        newPProcDecl(
          "items", {"item": genObject.name},
          some bodyObject.name,
          declType = ptkIterator,
          impl = pquote(
            for it in item.xsdChoice:
              yield it
          )
      ))

      result.add toNimDecl(
        newPProcDecl(
          "[]", {"item": genObject.name, "idx": newPType("int")},
          some bodyObject.name,
          kind = pkOperator,
          impl = pquote(item.xsdChoice[idx])
      ))

    bodyObject.addField(selector)

    genObject.addField("xsdChoice", newPType("seq", [bodyObject.name]))

    result.add toNimDecl(genEnum)
    result.add toNimDecl(bodyObject)
    result.add toNimDecl(genObject)

  else:
    for elem in gen.elements:
      genObject.addField(elem.nimName, elem.xsdType.ptype)
      var parseCall = newPCall(
        "loadXml",
        newPIdent("parser"),
        newPDotFieldExpr("target", elem.nimName),
        newPLit(elem.xmlTag)
      )

      if gen.isMixed:
        parseCall.add newMixed(
          genObject.name.head,
          gen.mixedStrField.enumName
        )

      bodyCase.addBranch(
        newPLit(elem.xmlTag), addPositionComment(parseCall))

    result.add toNimDecl(genObject)

  bodyCase.addBranch pquote do:
    @@@<<(posComment())
    if inMixed: return
    else: raiseUnexpectedElement(parser, tag)

  mainCase.addBranch({xmlElementOpen, xmlElementStart}):
    pquote do:
      `bodyCase`



  mainCase.addBranch(xmlElementClose, next)

  mainCase.addBranch(xmlElementEnd):
    pquote do:
      if parser.elementName() == tag:
        `next`
        break

      else:
        raiseUnexpectedElement(parser, tag)


  mainCase.addBranch(unused):
    pquote do:
      @@@<<(posComment())
      echo parser.displayAt()
      assert false


  let parsename = newPIdent(gen.nimName.parserName())
  parser.impl = pquote do:
    @@@<<(posComment())
    next(parser)
    while true:
      `mainCase`


  result.add toNimDecl parser

proc generateForEnum(gen, cache): tuple[decl: PEnumDecl, parser: PProcDecl] =
  result.decl = newPEnumDecl(gen.nimName)
  result.parser = newPProcDecl(gen.nimName.parserName(), iinfo = currIInfo())

  var mainCase = newCaseStmt(newPDotFieldExpr("parser", "strVal"))

  for field in gen.values:
    mainCase.addBranch(
      newPLit(field.value),
      newAsgn(newPident("target"), newPIdent(field.nimName)))

    result.decl.addField(
      field.nimName,
      docComment = &"XSD enumeration: `{field.value}`")

  result.parser.addArgument("parser", newPtype("var", ["HXmlParser"]))
  result.parser.addArgument(
    "target",
    newParseTargetPType(newPType(result.decl.name)))

  result.parser.addArgument("tag", newPType("string"))

  let parsename = newPIdent(result.parser.name)

  result.parser.impl = pquote do:
    @@@<<(posComment())
    mixin loadXml
    `mainCase`
    parser.next()


proc generateForDistinct(gen, cache):
  tuple[decl: PAliasDecl, parser: PProcDecl] =

  result.decl = newAliasDecl(gen.nimName.newPType(), gen.xsdType.ptype)
  result.parser = newPProcDecl(gen.nimName.parserName(), iinfo = currIInfo())

  with result.parser:
    addArgument("parser", newPType("var", ["HXmlParser"]))
    addArgument("target", result.decl.newType.newParseTargetPType())
    addArgument("tag", newPType("string"))

  let
    baseParseCall = newPIdent(gen.xsdType.parserCall)
    parseCall = newPIdent(result.parser.name)
    baseType = result.decl.oldType.toNNode()
    newType = result.decl.newType.toNNode()

  result.parser.impl = pquote do:
    @@@<<(posComment())
    var tmp: `baseType`
    `baseParseCall`(tmp, parser)
    target = `newType`(tmp)
    parser.next()



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

        elif generated.kind in {nekProcDecl} and
             generated.procDecl.name notin ["len", "items", "[]"]:
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

  # let file = open AbsFile("/tmp/res.nim")
  # for decl in
  AbsFile("/tmp/res.nim").writeFile($decls)

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
