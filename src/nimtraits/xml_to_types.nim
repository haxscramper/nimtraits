import hmisc/hasts/[xml_ast, xsd_ast]
import hmisc/other/oswrap
import hmisc/algo/[halgorithm, hstring_algo, clformat]
import std/[strutils, strformat]
import hmisc/hdebug_misc
import hnimast

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

type PNType = NType[PNode]

#*************************************************************************#
#***********  ^^^^ Boilerplate to move into dependencies ^^^^  ***********#
#*************************************************************************#

using xsd: XsdEntry

func fixTypeName(str: string): string = capitalizeAscii(str)

proc typeForEntry(xsd): tuple[ptype: PNType, parserCall: string] =
  case xsd.xsdType:
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



proc enumFieldName(str: string, prefix: string): string =
  let parts = @[prefix] & split(str, {'-', '_'})

  result = parts[0].toLowerAscii()
  for part in parts[1 ..^ 1]:
    result &= capitalizeAscii(part)

  var res: string
  for ch in result:
    res &= toLatinAbbrChar(ch)

  result = res



proc generateForObject(xsd): PObjectDecl =
  result = newPObjectDecl(xsd.name.fixTypeName())
  for entry in xsd:
    case entry.kind:
      of xekAttribute:
        if entry.hasName():
          result.addField(entry.name, typeForEntry(entry).ptype)

        else:
          echo treeRepr(entry)

      of xekSequence:
        for element in entry:
          case element.kind:
            of xekElement:
              if element.hasName():
                result.addField(element.name, typeForEntry(element).ptype)

              else:
                echov "Element without name"

            else:
              echo treeRepr(entry)

      else:
        echo treeRepr(entry)


proc generateForEnum(xsd): PEnumDecl =
  result = newPEnumDecl(xsd.name)
  let enumPrefix = enumPrefixForCamel(xsd.name)

  for field in enumerationFields(xsd):
    result.addField(
      enumFieldName(field.value, enumPrefix),
      docComment = &"XSD enumeration: `{field.value}`"
    )

proc generateForXsd(xsd): PNimDecl =
  case xsd.kind:
    of xekSimpleType:
      if isEnumerationType(xsd):
        return toNimDecl generateForEnum(xsd)

      else:
        echo treeRepr(xsd)

    of xekComplexType:
      return toNimDecl generateForObject(xsd)

    else:
      echo treeRepr(xsd)

proc generateForXsd*(xsd: AbsFile): seq[PNimDecl] =
  let document = parseXsd(xsd)
  for entry in document.entry:
    result.add generateForXsd(entry)

when isMainModule:
  startHax()
  let decls = generateForXsd(AbsFile "/tmp/schema.xsd")

  "/tmp/res.nim".writeFile($decls)

  # echo $decls
