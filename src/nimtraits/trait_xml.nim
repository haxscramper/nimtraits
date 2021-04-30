import ../nimtraits
import hnimast
import hmisc/helpers
import std/[tables, xmltree]
import hmisc/hdebug_misc

import hpprint

macro genNewObject*(obj: typedesc) =
  let impl = getObjectStructure(obj)

  result = newStmtList()

  let newObj = impl.mapItPath(newIdent(path[^1].name)):
    if path.len == 2 and path[^1].kindField.isFinalBranch():
      var res = newCaseStmt(newIdent(path[0].kindField.name))
      for v1 in path[0].ofValue:
        var newCall = nnkObjConstr.newTree(newIdent(impl.name.head))
        newCall.add newExprColon(newIdent(path[0].kindField.name), v1)
        newCall.add newExprColon(newIdent(path[1].kindField.name),
                                 newIdent(path[^1].kindField.name))

        res.addBranch(v1, newAsgn(newIdent("result"), newCall))

      res.addBranch(newDiscardStmt())

      return res

  result.add newObj

  let init = impl.mapItGroups("result".newDot(path[^1])):
    var res = newStmtList()
    for field in group:
      if field.value.isSome():
        res.add newAsgn(newIdent("result").newDot(field), field.value.get())

    res

  result.add init

import std/streams

type
  XmlWriter* = object
    stream: Stream
    indentBuf: string
    ignoreIndent: int

using writer: var XmlWriter

proc newXmlWriter*(stream: Stream): XmlWriter =
  XmlWriter(stream: stream)


proc space*(writer) = writer.stream.write(" ")
proc line*(writer) = writer.stream.write("\n")
proc indent*(writer) = writer.indentBuf.add "  "
proc dedent*(writer) =
  writer.indentBuf.setLen(max(writer.indentBuf.len - 2, 0))

proc writeInd*(writer) =
  if writer.ignoreIndent > 0:
    dec writer.ignoreIndent

  else:
    writer.stream.write(writer.indentBuf)

proc ignoreNextIndent*(writer) = inc writer.ignoreIndent

proc xmlCData*(writer; text: string) =
  writer.stream.write("<![CDATA[")
  writer.stream.write(text)
  writer.stream.write("]]>")

proc xmlStart*(writer; elem: string, indent: bool = true) =
  if indent: writer.writeInd()
  writer.stream.write("<", elem, ">")
  if indent: writer.line()

proc xmlEnd*(writer; elem: string, indent: bool = true) =
  if indent: writer.writeInd()
  writer.stream.write("</", elem, ">")
  if indent: writer.line()

proc xmlOpen*(writer; elem: string, indent: bool = true) =
  if indent: writer.writeInd()
  writer.stream.write("<", elem)

proc xmlClose*(writer) = writer.stream.write(">")

proc xmlCloseEnd*(writer) =
  writer.stream.write("/>")
  writer.line()


proc xmlWrappedCdata*(writer; tag, text: string) =
  writer.writeInd()
  writer.xmlStart(tag, false)
  writer.xmlCData(text)
  writer.xmlEnd(tag, false)
  writer.line()

proc toXmlString*[T](item: Option[T]): string =
  mixin toXmlString
  if item.isSome():
    return toXmlString(item.get())

proc toXmlString*(item: string): string = item
proc toXmlString*(item: enum | bool | float): string = $item
proc toXmlString*(item: SomeInteger): string = $item
proc writeRaw*(writer; text: string) =
  writer.stream.write(xmltree.escape text)

proc xmlAttribute*(
    writer; key: string, value: SomeInteger | bool | float | enum | string) =
  writer.stream.write(
    " ", key, "=\"", xmltree.escape(toXmlString(value)), "\"")

proc xmlAttribute*[T](writer; key: string, value: Option[T]) =
  if value.isSome():
    xmlAttribute(writer, key, value.get())

proc writeXml*(
  writer; value: string | SomeInteger | bool | SomeFloat | enum, tag: string) =
  writer.writeInd()
  writer.xmlStart(tag, false)
  writer.stream.write(xmltree.escape $value)
  writer.xmlEnd(tag, false)
  writer.line()


proc writeXml*[T](writer; values: seq[T], tag: string) =
  mixin writeXml
  for it in values:
    writer.writeXml(it, tag)

proc writeXml*[K, V](writer; table: Table[K, V], tag: string) =
  mixin writeXml
  for key, value in pairs(table):
    writer.xmlStart(tag)
    writer.writeXml(key, "key")
    writer.writeXml(value, "value")
    writer.xmlEnd(tag)

proc writeXml*[T](writer; opt: Option[T], tag: string) =
  if opt.isSome():
    writeXml(writer, opt.get(), tag)

# proc writeXml*[E: enum](writer; value: E, tag: string) =
  # writer.xmlAttribute(tag, $value)

proc writeXml*(writer; value: Slice[int], tag: string) =
  writer.xmlOpen(tag)
  writer.xmlAttribute("a", $value.a)
  writer.xmlAttribute("b", $value.b)
  writer.xmlCloseEnd()

proc writeXml*[E: enum](writer; values: set[E], tag: string) =
  writer.xmlStart(tag)
  writer.indent()
  writer.writeInd()
  for item in values:
    writer.xmlOpen("item")
    writer.xmlAttribute("val", $item)
    writer.xmlCloseEnd()

  writer.dedent()
  writer.xmlEnd(tag)

macro genXmlWriter*(
    obj: typedesc, input, stream, tag: untyped,
    ignoredNames: openarray[string] = [""],
    addClose: static[bool] = true,
    extraAttrWrite: untyped = false,
    addStartIndent: untyped = true,
    addEndIndent: untyped = true
  ) =

  var ignored: seq[string]
  for item in ignoredNames:
    ignored.add item.strVal()

  let
    input = input.copyNimNode()
    stream = stream.copyNimNode()
    impl = getObjectStructure(obj)

  result = newStmtList()

  let attrWrite = impl.mapItGroups(input.newDot(path[^1].name)):
    var res = newStmtList()
    for field in group:
      if (field.isKind or field.isMarkedWith("Attr")) and
         not field.isMarkedWithArg("Skip", "IO"):
        res.add newCall(
          "xmlAttribute", stream, newLit(field.name),
          input.newDot(field))

    res


  var hasFields = false
  let fieldWrite = impl.mapItGroups(input.newDot(path[^1].name)):
    var res = newStmtList()
    for field in group:
      if not (field.isKind or field.isMarkedWith("Attr")) and
         not (field.isMarkedWithArg("Skip", "IO")) and
         field.isExported and
         field.name notin ignored:
        hasFields = true
        res.add newCall(
          "writeXml", stream, input.newDot(field), newLit(field.name))

    res

  result.add newCall("xmlOpen", stream, tag, addStartIndent)
  result.add attrWrite
  # echo extraAttrWrite.treeRepr1()
  if not (extraAttrWrite.kind in {nnkIdent, nnkSym} and
          extraAttrWrite.eqIdent("false")):
    result.add extraAttrWrite

  if hasFields:
    result.add newCall("indent", stream)
    result.add newCall("xmlClose", stream)
    result.add newCall("line", stream)

    result.add fieldWrite
    result.add newCall("dedent", stream)
    if addClose:
      result.add newCall("xmlEnd", stream, tag, addEndIndent)
  else:
    if addClose:
      result.add newCall("xmlCloseEnd", stream)

  echov result
