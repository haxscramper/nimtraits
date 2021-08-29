import ../nimtraits

import hnimast
import std/[xmltree, sequtils]

import hmisc/core/all
import hmisc/hasts/[xml_ast, xsd_ast]
import hmisc/core/all
export xml_ast, xsd_ast

type
  XsdWriter* = object
    types: Table[string, XsdEntry]

func newXsdComplexType*(): XsdEntry =
  newTree(xekComplexComplexType)

func newXsdAttr*(useInfo: XsdEntry, name: string): XsdEntry =
  discard

func newXsdElement*(useInfo: XsdEntry, name: string): XsdEntry =
  discard

func getXsdEntryUse*(xw: var XsdWriter, s: typedesc[string]): XsdEntry =
  discard

func getXsdEntryUse*[E: enum](xw: var XsdWriter, s: typedesc[E]): XsdEntry =
  if $s notin xw.types:
    debugecho "Register enum"

func getXsdEntryUse*[T](xw: var XsdWriter, s: typedesc[seq[T]]): XsdEntry =
  let item = getXsdEntryUse(xw, T)

func getXsdEntryUse*[T](xw: var XsdWriter, s: typedesc[Option[T]]): XsdEntry =
  let item = getXsdEntryUse(xw, T)

func getXsdEntryUse*[A, B](xw: var XsdWriter, t: typedesc[Table[A, B]]): XsdEntry =
  let key = getXsdEntryUse(xw, A)
  let val = getXsdEntryUse(xw, B)

macro genXsdWriterUse*(obj: typedesc, writer: untyped): untyped =
  let impl = getObjectStructure(obj)

  result = newStmtList()
  let tmp = newIdent("tmp")
  result.add newVar(tmp, obj)
  result.add newAsgn(
    newIdent("result"),
    newCall("newXsdComplexType"))

  var
    attrWrite = newStmtList()
    fieldWrite = newStmtList()

  for field in iterateFields(impl):
    if not field.isExported or field.isMarkedWith("Skip", "IO"):
      discard

    elif field.isKind or field.isMarkedWith("Attr"):
      result.add newCall(
        "add",
        newIdent("result"),
        newCall("getXsdEntryUse", writer,
          newCall("typeof", tmp.newDot(field.name))).
          newCall("newXsdAttr", newLit(field.name))
      )

    else:
      result.add newCall(
        "add",
        newIdent("result"),
        newCall("getXsdEntryUse", writer,
          newCall("typeof", tmp.newDot(field.name))).
          newCall("newXsdElement", newLit(field.name))
      )





macro genXmlLoader*(
    obj: typedesc, target, stream, tag: untyped,
    newObjExpr: untyped = nil,
    loadHeader: static[bool] = true,
    extraFieldLoad: untyped = nil,
    skipFieldLoad: untyped = [""],
    extraAttrLoad: untyped = nil
  ): untyped =

  ##[

- @arg{loadHeader} :: Generate code to load object start (`<tag`), kind
  fields and fields marked with `.Attr.`. Can be turned off to manually
  process input attributes and then generate remaining boilerplate. NOTE:
  setting to `true` implies that @arg{target} object would be created
  externally, and @arg{newObjExpr} is ignored in that case.
- @arg{extraFieldLoad} :: Additional field handlers for object. Passed
  AST must be either `nil`, or follow pattern
  @patt{Curly[all ExprColonExpr[@name, @loader]]}
- @inject{} :: Identifiers for all kind fields - they can be used in
  @arg{newObjExpr}

]##

  result = newStmtList()

  var ignored: seq[string] = mapIt(skipFieldLoad, it.strVal())

  if loadHeader:
    result.add stream.newCall("skipElementStart", tag)

  let
    target = target.copyNimNode()
    stream = stream.copyNimNode()
    impl = getObjectStructure(obj)

  var
    declareKind = newStmtList()
    loadKind = newCaseStmt(stream.newCall("attrKey"))
    newObject = impl.newCall()
    loadAttr = newCaseStmt(stream.newCall("attrKey"))
    loadFields = newCaseStmt(stream.newCall("elementName"))

  for field in iterateFields(impl):
    if not(field.isExported) or
       field.isMarkedWith("Skip", "IO") or
       field.name in ignored:
      discard

    elif field.isKind:
      declareKind.add newVar(field.name, field.fldType)
      newObject.addArgument(field.name, newIdent(field.name))

      loadKind.addBranch(
        field.name,
        stream.newCall("loadXml", newIdent(field.name), newLit(field.name)))

    elif field.isMarkedWith("Attr"):
      loadAttr.addBranch(
        field.name,
        stream.newCall("loadXml", target.newDot(field), newLit(field.name)))

    else:
      loadFields.addBranch(
        field.name,
        stream.newCall("loadXml", target.newDot(field), newLit(field.name)))

  if declareKind.len > 0 and loadHeader:
    result.add declareKind

    let done = newIdent("kindParse")
    result.add newVar(done, newNType("bool"), newLit(false))

    loadKind.addBranch(newAsgn(done, newLit(true)))

    result.add newWhile(
      newAnd(newNot(done), stream.newCall("kind").newIn({
        XmlEventKind.xmlAttribute})),
      loadKind)

  if loadHeader:
    if newObjExpr.kind != nnkNilLit:
      result.add newAsgn(target, newObjExpr)

    else:
      result.add newAsgn(target, newObject)

  var main = newCaseStmt(stream.newDot("kind"))

  if extraAttrLoad.kind != nnkNilLit:
    for attr in extraAttrLoad:
      loadAttr.addBranch(attr[0], attr[1])

  loadAttr.addBranch(stream.newCall("raiseUnexpectedAttribute"))

  if extraFieldLoad.kind != nnkNilLit:
    for field in extraFieldLoad:
      loadFields.addBranch(field[0], field[1])

  loadFields.addBranch(stream.newCall(
    "raiseUnknownElement",
    newLit("While parsing fields for " & impl.name.head)))

  if loadAttr.len > 1 and loadHeader:
    main.addBranch({XmlEventKind.xmlAttribute}, loadAttr)

  if loadFields.len > 1:
    main.addBranch({xmlElementStart, xmlElementOpen}, loadFields)

  main.addBranch({xmlElementClose}, stream.newCall("next"))
  main.addBranch({xmlElementEnd},
                 stream.newCall("skipElementEnd", tag), newBreak())
  main.addBranch(stream.newCall(
    "raiseUnknownElement", newLit("While parsing " & impl.name.head)))

  result.add newWhile(newLit(true), main)


macro genXmlWriter*(
    obj: typedesc, input, stream, tag: untyped,
    skipFieldWrite: openarray[string] = [""],
    addClose: static[bool] = true,
    extraAttrWrite: untyped = false,
    addStartIndent: untyped = true,
    addEndIndent: untyped = true,
    hasFieldsExpr: untyped = true
  ): untyped =
  let obj = if hasObjectStructure(obj): obj else: baseImplSym(obj)

  var ignored: seq[string]
  for item in skipFieldWrite:
    ignored.add item.strVal()

  let
    input = input.copyNimNode()
    stream = stream.copyNimNode()
    impl = getObjectStructure(obj)

  result = newStmtList()

  let kindWrite = impl.mapItGroups(input.newDot(path[^1].name)):
    var res = newStmtList()
    for field in group:
      if field.isKind:
        res.add newCall(
          "xmlAttribute", stream, newLit(field.name),
          input.newDot(field))

    res

  let attrWrite = impl.mapItGroups(input.newDot(path[^1].name)):
    var res = newStmtList()
    for field in group:
      if field.isMarkedWith("Attr") and
         not field.isMarkedWith("Skip", "IO"):
        res.add newCall(
          "xmlAttribute", stream, newLit(field.name),
          input.newDot(field))

    res


  var hasFields = false
  let fieldWrite = impl.mapItGroups(input.newDot(path[^1].name)):
    var res = newStmtList()
    for field in group:
      if not (field.isKind or field.isMarkedWith("Attr")) and
         not (field.isMarkedWith("Skip", "IO")) and
         field.isExported and
         field.name notin ignored:
        hasFields = true
        res.add newCall(
          "writeXml", stream, input.newDot(field), newLit(field.name))

    res

  result.add newCall("xmlOpen", stream, tag, addStartIndent)
  result.add kindWrite
  result.add attrWrite
  if not (extraAttrWrite.kind in {nnkIdent, nnkSym} and
          extraAttrWrite.eqIdent("false")):
    result.add extraAttrWrite

  var writeFields = nnkIfStmt.newTree()

  block:
    var stmt = newStmtList()
    stmt.add newCall("indent", stream)
    stmt.add newCall("xmlClose", stream)
    stmt.add newCall("line", stream)

    stmt.add fieldWrite
    stmt.add newCall("dedent", stream)
    if addClose:
      stmt.add newCall("xmlEnd", stream, tag, addEndIndent)

    writeFields.addBranch(
      newCall("and", newLit(hasFields), hasFieldsExpr),
      stmt)

  block:
    if addClose:
      writeFields.addBranch(newCall("xmlCloseEnd", stream))

  result.add writeFields

proc writeXml*[T: not enum](writer: var XmlWriter, obj: T, tag: string) =
  mixin writeXml
  genXmlWriter(T, obj, writer, tag)


proc loadXml*[T: not enum](reader: var HXmlParser, obj: var T, tag: string) =
  mixin loadXml
  genXmlLoader(T, obj, reader, tag)
