import hmisc/hasts/[xml_ast, xsd_ast]
import hmisc/other/oswrap
import hmisc/algo/[halgorithm, hstring_algo, clformat]
import std/[strutils, strformat, sequtils]
import hmisc/hdebug_misc
import hnimast

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
      main.add newNTree[N](
        nnkOfBranch, expr,
        newNTree[N](nnkStmtList, newEmptyNNode[N]() & toSeq(body)))

    else:
      raiseImplementKindError(main)

proc addBranch*[N](main: var N, expr: enum, body: varargs[N]) =
  addBranch(main, newNIdent[N]($expr), body)

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


type PNType = NType[PNode]

#*************************************************************************#
#***********  ^^^^ Boilerplate to move into dependencies ^^^^  ***********#
#*************************************************************************#

using xsd: XsdEntry

func fixTypeName(str: string): string = capitalizeAscii(str)

type
  XsdWrapperKind = enum
    xwkScalar
    xwkOption
    xwkSequence

  XsdType = object
    entry: XsdEntry
    ptype: PNType
    parserCall: string
    wrapperKind: XsdWrapperKind

proc typeForEntry(xsd): XsdType =
  var (ptype, parserCall) = case xsd.xsdType:
    of xsd"string":       (newPType ("string"),   "parseXsdString")
    of xsd"boolean":      (newPType ("bool"),     "parseXsdBoolean")
    of xsd"decimal":      (newPType ("float"),    "parseXsdDecimal")
    of xsd"integer":      (newPType ("int"),      "parseXsdInteger")
    of xsd"float":        (newPType ("float"),    "parseXsdFloat")
    of xsd"double":       (newPType ("double"),   "parseXsdDouble")
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
    of xsd"hexBinary":    (newPType ("string"), "")
    of xsd"base64Binary": (newPType ("string"), "parseXsdBase64Binary")
    of xsd"anyURI":       (newPType ("URI"), "parseXsdUri")
    of xsd"QName":        (newPType ("???"), "parseXsdQName")
    of xsd"anyType":      (newPType ("XmlNode"), "parseXsdAnyType")
    else:
      if xsd.xsdType.startsWith("xsd:"):
        raiseImplementError(xsd.xsdType)

      else:
        (newPType(xsd.xsdType.fixTypeName()),
         "parse" & fixTypeName(xsd.xsdType))

  var wrapperKind: XsdWrapperKind
  if xsd.isOptional():
    if xsd.isUnboundedRepeat():
      wrapperKind = xwkSequence

    else:
      wrapperKind = xwkOption

  return XsdType(
    ptype: ptype, parserCall: parserCall,
    wrapperKind: wrapperKind, entry: xsd
  )

proc wrappedType(xsdType: XsdType): PNtype =
  case xsdType.wrapperKind:
    of xwkSequence:
      newPType("seq", [xsdType.ptype])

    of xwkOption:
      newPType("Option", [xsdType.ptype])

    of xwkScalar:
      xsdType.ptype

type
  XsdElementWrapperKind = enum
    xewkSingleSequence
    xewkUnboundedSequence

  XsdElementWrapper = object
    xsdEntry: XsdEntry
    elements: seq[XsdType]
    kind: XsdElementWrapperKind

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
        echov treeRepr(element)



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



proc enumFieldName(str: string, prefix: string): string =
  let parts = @[prefix] & split(str, {'-', '_'})

  result = parts[0].toLowerAscii()
  for part in parts[1 ..^ 1]:
    result &= capitalizeAscii(part)

  var res: string
  for ch in result:
    res &= toLatinAbbrChar(ch)

  result = res



proc generateForObject(xsd): tuple[decl: PObjectDecl, parser: PProcDecl] =
  result.decl = newPObjectDecl(xsd.name.fixTypeName())
  echo treeRepr(xsd)
  for entry in xsd:
    case entry.kind:
      of xekAttribute:
        if entry.hasName():
          result.decl.addField(entry.name, typeForEntry(entry).wrappedType())

        else:
          echov treeRepr(entry)

      of xekSequence:
        let wrapper = typeForWrapper(entry)
        # echov wrapper.kind, treeRepr(wrapper.xsdEntry)
        # raiseImplementError("")
        case wrapper.kind:
          of xewkSingleSequence:
            for element in wrapper.elements:
              result.decl.addField(element.entry.name(), element.wrappedType())

          of xewkUnboundedSequence:
            if wrapper.elements.len == 1:
              result.decl.addField(
                wrapper.elements[0].entry.name(),
                newPType("seq", [wrapper.elements[0].wrappedType()]))

            else:
              raiseImplementError($wrapper.elements.len)

          else:
            raiseImplementKindError(wrapper)



      else:
        echov treeRepr(entry)


  result.parser = newPProcDecl("parse" & result.decl.name.head)
  result.parser.addArgument("parser", newPtype("var", ["XmlParser"]))

  let
    next = newPDotFieldExpr("parser", newPCall("next"))
    inAttributes = newPident("inAttributes")


  var attrCase = newCase(newPDotFieldExpr("parser", "attrKey"))
  for attr in xsd.getAttributes():
    if attr.hasName() and attr.hasType():
      attrCase.addBranch(
        newPLit(attr.name),
        newAsgn(
          newPDotFieldExpr("result", attr.name),
          newPCall("parse" & attr.xsdType, newPident("parser"))
        )
      )

  var mainCase = newCase(newPDotFieldExpr("parser", "kind"))

  mainCase.addBranch(
    xmlAttribute,
    attrCase,
    next
  )

  mainCase.addBranch(xmlElementOpen, newAsgn(inAttributes, newPLit(true)))

  result.parser.impl = pquote do:
    assert parser.elementName == `newPLit(xsd.name)`
    var `inAttributes` = false
    while true:
      `mainCase`


proc generateForEnum*(xsd): tuple[decl: PEnumDecl, parser: PProcDecl] =
  result.decl = newPEnumDecl(xsd.name)
  let enumPrefix = enumPrefixForCamel(xsd.name)

  for field in enumerationFields(xsd):
    result.decl.addField(
      enumFieldName(field.value, enumPrefix),
      docComment = &"XSD enumeration: `{field.value}`"
    )

  result.parser = newPProcDecl("parse" & result.decl.name)

  result.parser.addArgument("parser", newPtype("var", ["XmlParser"]))

proc generateForXsd(xsd): seq[PNimDecl] =
  case xsd.kind:
    of xekSimpleType:
      if isEnumerationType(xsd):
        let (decl, parser) = generateForEnum(xsd)
        return @[toNimDecl decl, toNimDecl parser]

      else:
        echo treeRepr(xsd)

    of xekComplexType:
      let (decl, parser) = generateForObject(xsd)
      return @[toNimDecl decl, toNimDecl parser]


    of xekGroupDeclare:
      discard

    else:
      echov treeRepr(xsd)

proc generateForXsd*(xsd: AbsFile): seq[PNimDecl] =
  let document = parseXsd(xsd)
  for entry in document.entry:
    result.add generateForXsd(entry)

when isMainModule:
  startHax()
  let decls = generateForXsd(AbsFile "/tmp/schema.xsd")

  "/tmp/res.nim".writeFile($decls)

  # echo $decls
