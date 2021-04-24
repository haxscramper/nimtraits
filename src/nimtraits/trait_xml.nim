import ../nimtraits
import hnimast
import hmisc/helpers

import hpprint

proc isFinalBranch*[N](field: ObjectField[N]): bool =
  if not field.isKind:
    return true

  else:
    result = true
    for branch in items(field.branches):
      for field in branch.flds:
        if field.isKind:
          return false


proc newIdent*(str: string): NimNode = newIdentNode(str)
proc newVar*[N](name: string, varType: NType[N], default: N = nil): N =
  newNTree[N](nnkVarSection, newNTree[N](
    nnkIdentDefs,
    newNIdent[N](name),
    toNNode[N](varType),
    (if isNil(default): newEmptyNNode[N]() else: default)
  ))

proc dotField*[N](self: N, field: ObjectField[N]): N =
  newNTree[N](nnkDotExpr, self, newNIdent[N](field.name))

proc newObjectPathElem*[N](
    field: ObjectField[N], branch: OBjectBranch[N]): ObjectPathElem[N] =

  if branch.isElse:
    NObjectPathElem(
      isElse: true, kindField: field,
      notOfValue: branch.notOfValue)

  else:
    NObjectPathElem(
      isElse: false, kindField: field,
      ofValue: normalizeSet(branch.ofValue))

type
  KindFields[N] = seq[ObjectField[N]] # Using this typedef makes semcheck fail. 10/10
  NKindFields = KindFields[NimNode]

proc mapBranches*(
    field: NObjectField, parent: seq[ObjectField[NimNode]],
    caseExpr: proc(path: seq[ObjectField[NimNode]]): NimNode,
    mapBranch: proc(path: seq[ObjectField[NimNode]], branch: NObjectBranch): NimNode
  ): NimNode =

  if field.isKind:
    result = nnkCaseStmt.newTree(caseExpr(parent))
    for branch in field.branches:
      let thisPath = parent & field # newObjectPathElem(field, branch)
      let cbRes = mapBranch(thisPath, branch).nilToDiscard()

      var branchBody = newStmtList()
      for field in branch.flds:
        if field.isKind:
          branchBody.add field.mapBranches(
            thisPath, caseExpr, mapBranch)

      if branch.isElse:
        result.add nnkElse.newTree(newStmtList(cbRes, branchBody))

      else:
        result.add nnkOfBranch.newTree(
          normalizeSet(branch.ofValue), newStmtList(cbRes, branchBody))


proc mapBranches*(
    obj: NObjectDecl,
    caseExpr: proc(path: seq[ObjectField[NimNode]]): NimNode,
    mapBranch: proc(path: seq[ObjectField[NimNode]], branch: NObjectBranch): NimNode
  ): NimNode =
  result = newStmtList()
  for field in items(obj.fields):
    if field.isKind:
      result.add field.mapBranches(@[field], caseExpr, mapBranch)

template mapSelfBranches*(obj: NObjectDecl, expr, body: untyped): untyped =
  mapBranches(
    obj,
    proc(path {.inject.}: seq[ObjectField[NimNode]]): NimNode = expr,
    proc(path {.inject.}: seq[ObjectField[NimNode]],
         branch {.inject.}: NObjectBranch): NimNode = body
  )

proc fixEmptyStmt*(node: NimNode): NimNode =
  if isEmptyNode(node):
    newDiscardStmt()

  else:
    node


proc mapCase*(
    field: NObjectField,
    parent: seq[NObjectField],
    caseExpr: proc(field: NObjectField, path: seq[NObjectField]): NimNode,
    cb: proc(field: NObjectField, path: seq[NObjectField]): NimNode
  ): NimNode =

  if field.isKind:
    result = nnkCaseStmt.newTree(caseExpr(field, parent))
    for branch in field.branches:
      if branch.isElse:
        var body = nnkElse.newTree()
        for field in branch.flds:
          if field.isKind:
            body.add mapCase(field, parent & field, caseExpr, cb)

          else:
            body.add mapCase(field, parent, caseExpr, cb)

        result.add fixEmptyStmt(body)

      else:
        var body = newStmtList()
        for field in branch.flds:
          if field.isKind:
            body.add mapCase(field, parent & field, caseExpr, cb)

          else:
            body.add mapCase(field, parent, caseExpr, cb)


        result.add nnkOfBranch.newTree(
          normalizeSet(branch.ofValue),
          fixEmptyStmt(body))


    let cbRes = cb(field, parent)
    if cbRes != nil:
      result = newStmtList(cbRes, result)

  else:
    result = newStmtList(cb(field, parent))

proc mapCase*(
    objectDecl: NObjectDecl,
    caseExpr: proc(field: NObjectField, path: seq[NObjectField]): NimNode,
    cb: proc(field: NObjectField, path: seq[NObjectField]): NimNode
  ): NimNode =

  result = newStmtList()
  for field in objectDecl.flds:
    result.add field.mapCase(@[field], caseExpr, cb)

template mapSelfCase*(objectDecl: NObjectDecl, expr, body: untyped): untyped =
  mapCase(
    objectDecl,
    proc(field {.inject.}: NObjectField, path {.inject.}: seq[NObjectField]): NimNode = expr,
    proc(field {.inject.}: NObjectField, path {.inject.}: seq[NObjectField]): NimNode = body
  )

macro genXmlWriter*(obj: typedesc, stream, target: untyped) =
  let
    stream = stream.copyNimNode()
    impl = getObjectStructure(obj)
    kinds = impl.getKindFields()
    self = ident("self")

  # let writeKind = self.eachCase(impl) do(field: TraitField) -> NimNode:
  #   if field.isKind:
  #     result = newCall(
  #       "writeAttr", stream, self.dotField(field),
  #       newCall("$", self.dotField(field)))


  # echo writeKind.toStrLit()

  # let writeAttrs = eachCase(self, impl) do(field: TraitField) -> NimNode:
  #   if field.isTaggedWith("Attr"):
  #     result = newCall(
  #       "writeAttr", stream, self.dotField(field),
  #       newCall("$", self.dotField(field)))

  # echo writeAttrs.toStrLit()

  # let writeBody = eachCase(self, impl) do(field: TraitField) -> NimNode:
  #   if not field.isTaggedWith("Attr"):
  #     result = newcall("writeXml", stream, self.dotField(field))

  # echo writeBody.toStrLit()

  let branches2 = impl.mapSelfCase(newIdent(field.name)):
    var res = newStmtList()
    if field.isKind:
      res.add newVar(field.name, field.fldType)
      res.add newCall("load", newIdent(field.name))

    if field.isFinalBranch():
      var call = newCall("new" & impl.name.head)
      for kind in path:
        call.add newIdent(kind.name)

      res.add call

    res

  echo branches2.toStrLit()
