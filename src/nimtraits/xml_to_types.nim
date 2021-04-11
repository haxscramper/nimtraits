import hmisc/hasts/[xml_ast, xsd_ast]
import hmisc/other/[oswrap, hshell]
import hmisc/algo/[halgorithm, hstring_algo, clformat, hseq_mapping]
import std/[strutils, strformat, sequtils]
import hmisc/hdebug_misc
import hnimast

import fusion/matching

{.experimental: "caseStmtMacros".}

import std/parsexml

proc enumPrefixForCamel*(camel: string): string =
  for part in camel.splitCamel():
    result.add toLowerAscii(part[0])

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

proc addBranch*[N](main: var N, expr: enum, body: varargs[N]) =
  addBranch(main, newNIdent[N]($expr), body)

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
proc newCase*[N](expr: N): N =
  newNTree[N](nnkCaseStmt, expr)

proc newPDotExpr*(lhs, rhs: PNode | string): PNode =
  newPTree(nnkDotExpr, toPNode(lhs), toPNode(rhs))

proc newPDotFieldExpr*(lhs: string, rhs: PNode | string): PNode =
  result = newPTree(nnkDotExpr, newPident(lhs))
  when rhs is PNode:
    result.add rhs

  else:
    result.add newPIdent(rhs)


proc fixIdentName*(str: string, prefix: string): string =
  if str in [

    "addr", "and", "as", "asm", "bind", "block", "break", "case", "cast",
    "concept", "const", "continue", "converter", "defer", "discard",
    "distinct", "div", "do", "elif", "else", "end", "enum", "except",
    "export", "finally", "for", "from", "func", "if", "import", "in",
    "include", "interface", "is", "isnot", "iterator", "let", "macro",
    "method", "mixin", "mod", "nil", "not", "notin", "object", "of", "or",
    "out", "proc", "ptr", "raise", "ref", "return", "shl", "shr", "static",
    "template", "try", "tuple", "type", "using", "var", "when", "while",
    "xor", "yield",

  ]:
    assert prefix.len > 0
    result = prefix & capitalizeAscii(str)

  else:
    result = str





type PNType = NType[PNode]

#*************************************************************************#
#***********  ^^^^ Boilerplate to move into dependencies ^^^^  ***********#
#*************************************************************************#

using xsd: XsdEntry


func fixTypeName(str: string): string = capitalizeAscii(str.fixIdentName("X"))
proc identName*(xsd): string =
  if xsd.kind == xekExtension:
    "baseExt"

  else:
    xsd.name().fixIdentName("x")

proc typeName*(xsd): string = xsd.getType().fixTypeName()
proc kindTypeName*(xsd): string = xsd.getType() & "Kind"
proc bodyTypeName*(xsd): string = xsd.getType() & "Body"
proc parserName*(typeName: string): string =
  "parse" & capitalizeAscii(typeName)

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
    xsdEntry: XsdEntry
    elements: seq[XsdType]
    kind: XsdElementWrapperKind


proc typeForEntry(xsd): XsdType =
  var isPrimitive = true
  var (ptype, parserCall) = case xsd.getType:
    of xsd"string":       (newPType ("string"),   "parseXsdString")
    of xsd"boolean":      (newPType ("bool"),     "parseXsdBoolean")
    of xsd"decimal":      (newPType ("float"),    "parseXsdDecimal")
    of xsd"integer":      (newPType ("int"),      "parseXsdInteger")
    of xsd"float":        (newPType ("float"),    "parseXsdFloat")
    of xsd"double":       (newPType ("float"),    "parseXsdDouble")
    of xsd"duration":     (newPType ("Duration"), "parseXsdDuration")
    of xsd"dateTime":     (newPType ("DateTime"), "parseXsdDateTime")
    of xsd"time":         (newPType ("DateTime"), "parseXsdTime")
    of xsd"date":         (newPType ("DateTime"), "parseXsdDate")
    of xsd"gYearMonth":   (newPType ("DateTime"), "parseXsdGYearMonth")
    of xsd"gYear":        (newPType ("DateTime"), "parseXsdGYear")
    of xsd"gMonthDay":    (newPType ("DateTime"), "paresXsdGMonthDay")
    of xsd"gDay":         (newPType ("DateTime"), "parseXsdGDay")
    of xsd"gMonth":       (newPType ("DateTime"), "parseXsdGMonth")
    # QUESTION - not sure what would be the best representation for this
    # type of content.
    of xsd"hexBinary":    (newPType ("string"), "parseXsdHexBinary")
    of xsd"base64Binary": (newPType ("string"), "parseXsdBase64Binary")
    of xsd"anyURI":       (newPType ("URI"), "parseXsdUri")
    of xsd"QName":        (newPType ("???"), "parseXsdQName")
    of xsd"anyType":      (newPType ("XmlNode"), "parseXsdAnyType")
    else:
      isPrimitive = false
      if xsd.getType().startsWith("xsd:"):
        raiseImplementError(xsd.getType)

      else:
        (newPType(xsd.getType.fixTypeName()),
         "parse" & fixTypeName(xsd.getType))

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

proc typeForWrapper(xsd): XsdElementWrapper =
  var elements: seq[XsdType]

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
  case xsd.kind:
    of xekSequence:
      # echov xsd.xsdMaxOccurs.isSome()
      # echov xsd.xsdMaxOccurs.isSome()

      if xsd.isFinite():
        kind = xewkSingleSequence

      else:
        kind = xewkUnboundedSequence

    else:
      discard

  result.kind = kind
  result.elements = elements
  result.xsdEntry = xsd

  # case xsd.kind:
  #   of xekSequence:

proc parserForType(
    xsdType: XsdType, eventKinds: set[XmlEventKind],
    inTag: string = "", skipWrapperElement: bool = true): PNode =

  result = newPCall(
    xsdType.parserCall,
    newPDotFieldExpr("target", xsdType.entry.identName()),
    newPIdent("parser")
  )

  if xsdType.isPrimitive:
    if skipWrapperElement:
      if len(eventKinds * {xmlElementStart, xmlElementOpen}) > 0:
        return pquote do:
          skipElementStart(parser, `inTag`)
          `result`
          skipElementEnd(parser, `inTag`)

  else:
    result.add newPLit(inTag)




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

proc generateTypeForObject(xsd): PObjectDecl =
  result = newPObjectDecl(
    xsd.name.fixTypeName(),
    docComment =
      xsd.treeRepr(colored = false) & &"""

- is primitive restriction: {xsd.isPrimitiveRestriction()}
- is primitive extension: {xsd.isPrimitiveExtension()}
"""
  )

  for attr in xsd.getAttributes():
    if attr.hasName():
      result.addField(
        attr.identName(),
        attr.typeForEntry().wrappedType(xsd))


  if isPrimitiveExtension(xsd):
    result.addField(
      "baseExt",
      xsd.getExtensionSection().typeForEntry().ptype
    )

  for entry in xsd:
    case entry.kind:
      of xekAttribute:
        discard

      of xekSequence:
        let wrapper = typeForWrapper(entry)
        # echov wrapper.kind, treeRepr(wrapper.xsdEntry)
        # raiseImplementError("")
        case wrapper.kind:
          of xewkSingleSequence:
            for element in wrapper.elements:
              result.addField(
                element.entry.identName(),
                element.wrappedType(xsd, wrapper.kind))

          of xewkUnboundedSequence:
            if wrapper.elements.len == 1:
              result.addField(
                wrapper.elements[0].entry.identName(),
                wrapper.elements[0].wrappedType(xsd, wrapper.kind))

            else:
              raiseImplementError($wrapper.elements.len)

          else:
            raiseImplementKindError(wrapper)

      else:
        discard
        # echov entry.kind

proc generateParserForObject(xsd): PProcDecl =
  let targetName = xsd.name.fixTypeName()
  result = newPProcDecl("parse" & targetName, iinfo = currIInfo())
  result.addArgument("target", newParseTargetPType(
    newPType(targetName)))

  result.addArgument(
    "parser",
    newPtype("var", ["HXmlParser"])
  )

  result.addArgument("tag", newPType("string"))


  let
    next = newPDotFieldExpr("parser", newPCall("next"))
    inAttributes = newPident("inAttributes")


  var attrCase = newCase(newPDotFieldExpr("parser", "attrKey"))
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

  var mainCase = newCase(newPDotFieldExpr("parser", "kind"))

  mainCase.addBranch(
    xmlAttribute,
    attrCase,
    next
  )

  var bodyCase = newCase(newPDotFieldExpr(
    "parser", newPCall("elementName")))

  proc addFieldBranch(
      target: var PNode, field: XsdType,
      wrapper: XsdElementWrapper
    ) =

    if field.entry.hasName() and field.entry.hasType():
      let parseCall = parserForType(
        field,
        {xmlElementStart, xmlElementEnd},
        field.entry.name()
      )
        # newPCall(
        # field.parserCall,
        # newPDotFieldExpr("target", field.entry.identName()),
        # newPIdent("parser"),
        # field.entry.name().newPLit()
      # )

      target.addBranch(newPLit(field.entry.name()), addPositionComment(parseCall))


  for element in xsd:
    if element.kind in {xekSequence, xekChoice}:
      let wrapper = typeForWrapper(element)
      case wrapper.kind:
        of xewkSingleSequence:
          for field in wrapper.elements:
            addFieldBranch(bodyCase, field, wrapper)

        of xewkUnboundedSequence:
          if len(wrapper.elements) == 1:
            addFieldBranch(bodyCase, wrapper.elements[0], wrapper)

          else:
            raiseImplementError("")

        else:
          raiseImplementError("")


  bodyCase.addBranch pquote do:
    @@@<<(posComment())
    raiseUnexpectedElement(parser)

  mainCase.addBranch(
    {xmlElementOpen, xmlElementStart},
    pquote do:
      if parser.kind == xmlElementOpen:
        `inAttributes` = true

      `bodyCase`

      # `next`
  )

  var used = {
    xmlError, xmlEof, xmlCharData, xmlWhitespace,
    xmlComment, xmlPI, xmlCData, xmlEntity, xmlSpecial
  }

  if xsd.findIt(it.kind == xekSequence) == 0:
    let wrapper = typeForWrapper(xsd[0])

    if wrapper.elements.len > 0:
      let
        first = wrapper.elements[0]
        call = newPIdent(first.parserCall)
        name = first.entry.identName().newPIdent()

      used.excl xmlCharData
      mainCase.addBranch(
        xmlCharData,
        pquote do:
          @@@<<(posComment())
          `call`(target.`name`, parser, tag)
      )

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
        # IMPLEMENT generate error
        discard
  )

  let parseName = newPIdent(result.name)

  expandMacros:
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
        if parser.elementName() != tag:
          raiseUnexpectedElement(parser, tag)

        next(parser)
        var `inAttributes` = false
        while true:
          `mainCase`



proc generateForEnum*(xsd): tuple[decl: PEnumDecl, parser: PProcDecl] =
  result.decl = newPEnumDecl(xsd.name)
  let enumPrefix = enumPrefixForCamel(xsd.name)

  var mainCase = newCase(
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

proc generateForXsd(xsd): seq[PNimDecl] =
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
      return @[
        toNimDecl generateTypeForObject(xsd),
        toNimDecl generateParserForObject(xsd)
      ]


    of xekGroupDeclare:
      discard

    else:
      echov treeRepr(xsd)

proc withoutImpl*[N](decl: ProcDecl[N]): ProcDecl[N] =
  result = decl
  result.impl = nil

proc generateForXsd*(xsd: AbsFile): seq[PNimDecl] =
  let document = parseXsd(xsd)
  var procs: seq[PNimDecl]
  var types: seq[PNimTypeDecl]
  var forward: seq[PNimDecl]
  for entry in document:
    for generated in generateForXsd(entry):
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

when isMainModule:
  startHax()
  let decls = generateForXsd(AbsFile "/tmp/schema.xsd")

  "/tmp/res.nim".writeFile(
    """
import std/[options]
import hmisc/hasts/[xml_ast]
export options, xml_ast

import hmisc/algo/halgorithm

""" & $decls
  )

  execShell shellCmd(nim, check, errorMax = 2, "/tmp/res.nim")

  "/tmp/parse.nim".writeFile(
    """
import res
import hmisc/hexceptions

var parser = newHXmlParser(AbsFile "/tmp/in.xml")

var doxygen: DoxygenType

try:
  parseDoxygenType(doxygen, parser, "doxygen")

except:
  pprintErr()


"""
  )

  execShell shellCmd(nim, r, "/tmp/parse.nim")

  echo "done"
