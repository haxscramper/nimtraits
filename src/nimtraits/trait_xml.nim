import ../nimtraits

import hnimast
import std/[xmltree]

import hmisc/helpers
import hmisc/hasts/xml_ast
import hmisc/hdebug_misc
export xml_ast

macro genXmlLoader*(
    obj: typedesc, target, stream, tag: untyped,
    newObjExpr: untyped = nil,
    loadHeader: static[bool] = true,
    extraFieldLoader: untyped = nil
  ): untyped =

  ##[

- @arg{loadHeader} :: Generate code to load object start (`<tag`), kind
  fields and fields marked with `.Attr.`. Can be turned off to manually
  process input attributes and then generate remaining boilerplate. NOTE:
  setting to `true` implies that @arg{target} object would be created
  externally, and @arg{newObjExpr} is ignored in that case.
- @arg{extraFieldLoader} :: Additional field handlers for object. Passed
  AST must be either `nil`, or follow pattern
  @patt{Curly[all ExprColonExpr[@name, @loader]]}

]##

  result = newStmtList()

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
    if not field.isExported or field.isMarkedWith("Skip", "IO"):
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

  loadAttr.addBranch(stream.newCall("raiseUnexpectedAttribute"))

  if extraFieldLoader.kind != nnkNilLit:
    for field in extraFieldLoader:
      loadFields.addBranch(field[0], field[1])

  loadFields.addBranch(stream.newCall("raiseUnexpectedElement"))

  if loadAttr.len > 1 and loadHeader:
    main.addBranch({XmlEventKind.xmlAttribute}, loadAttr)

  if loadFields.len > 1:
    main.addBranch({xmlElementStart, xmlElementOpen}, loadFields)

  main.addBranch({xmlElementClose}, stream.newCall("next"))
  main.addBranch({xmlElementEnd}, stream.newCall("next"), newBreak())
  main.addBranch(stream.newCall("raiseUnexpectedElement"))

  result.add newWhile(newLit(true), main)

  echov result

macro genXmlWriter*(
    obj: typedesc, input, stream, tag: untyped,
    ignoredNames: openarray[string] = [""],
    addClose: static[bool] = true,
    extraAttrWrite: untyped = false,
    addStartIndent: untyped = true,
    addEndIndent: untyped = true,
    hasFieldsExpr: untyped = true
  ): untyped =

  var ignored: seq[string]
  for item in ignoredNames:
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
