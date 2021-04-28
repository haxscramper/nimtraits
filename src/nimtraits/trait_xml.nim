import ../nimtraits
import hnimast
import hmisc/helpers

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

using writer: var XmlWriter

proc newXmlWriter*(stream: Stream): XmlWriter =
  XmlWriter(stream: stream)


proc space*(writer) = writer.stream.write(" ")
proc line*(writer) = writer.stream.write("\n")
proc indent*(writer) = writer.indentBuf.add "  "
proc dedent*(writer) =
  writer.indentBuf.setLen(max(writer.indentBuf.len - 2, 0))
proc writeInd*(writer) = writer.stream.write(writer.indentBuf)

proc xmlStart*(writer; elem: string, indent: bool = true) =
  if indent: writer.writeInd()
  writer.stream.write("<", elem, ">")
  if indent: writer.line()

proc xmlEnd*(writer; elem: string, indent: bool = true) =
  if indent: writer.writeInd()
  writer.stream.write("</", elem, ">")
  if indent: writer.line()

proc xmlOpen*(writer; elem: string) = writer.writeInd(); writer.stream.write("<", elem)
proc xmlClose*(writer) = writer.stream.write(">")
proc xmlCloseEnd*(writer) =
  writer.stream.write("/>")
  writer.line()

proc xmlAttribute*(writer; key, value: string) =
  writer.stream.write(key, "=\"", value, "\"")

proc toXmlString*[T](item: T): string =
  discard


proc writeXml*(writer; value: string | int | bool, tag: string) =
  writer.writeInd()
  writer.xmlStart(tag, false)
  writer.stream.write($value)
  writer.xmlEnd(tag, false)
  writer.line()

proc writeXml*[T](writer; values: seq[T], tag: string) =
  mixin writeXml
  for it in values:
    writer.writeXml(it, tag)

proc writeXml*[T](writer; opt: Option[T], tag: string) =
  if opt.isSome():
    writeXml(writer, opt.get(), tag)

proc writeXml*[E: enum](writer; value: E, tag: string) =
  writer.xmlAttribute(tag, $value)

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


macro genXmlWriter*(obj: typedesc, input, stream, tag: untyped) =

  let
    input = input.copyNimNode()
    stream = stream.copyNimNode()
    impl = getObjectStructure(obj)

  result = newStmtList()
  result.add newCall("xmlOpen", stream, tag)

  let attrWrite = impl.mapItGroups(input.newDot(path[^1].name)):
    var res = newStmtList()
    for field in group:
      if field.isKind or field.isMarkedWith("Attr"):
        res.add newCall("space", stream)
        res.add newCall(
          "xmlAttribute", stream, newLit(field.name),
          newCall("toXmlString", input.newDot(field)))

    res

  result.add attrWrite
  result.add newCall("xmlClose", stream)
  result.add newCall("line", stream)

  let fieldWrite = impl.mapItGroups(input.newDot(path[^1].name)):
    var res = newStmtList()
    res.add newCall("indent", stream)
    for field in group:
      if not (field.isKind or field.isMarkedWith("Attr")) and field.isExported:
        res.add newCall(
          "writeXml", stream, input.newDot(field), newLit(field.name))
    res.add newCall("dedent", stream)

    res

  result.add fieldWrite
  result.add newCall("xmlEnd", stream, tag)


  # echo result
