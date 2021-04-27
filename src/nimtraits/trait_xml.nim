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

proc fixEmptyStmt*(node: NimNode): NimNode =
  if isEmptyNode(node):
    newDiscardStmt()

  else:
    node



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

proc dotField*[N](self: N, name: string): N =
  newNTree[N](nnkDotExpr, self, newNIdent[N](name))

proc newSet*[N](elements: varargs[N]): N =
  newNTree[N](nnkCurly, elements)

proc newExprColon*[N](lhs, rhs: N): N =
  newNTree[N](nnkExprColonExpr, lhs, rhs)

proc addBranchBody*[N](main: var N, branch: ObjectBranch[N], body: N) =
  let branchBody = fixEmptyStmt(body)

  if branch.isElse:
    main.add nnkElse.newTree(branchBody)

  else:
    main.add nnkOfBranch.newTree(
      newSet(branch.ofValue), branchBody)


template mapItKindFields*(branch: NObjectBranch, body: untyped): untyped =
  var branchBody = newStmtList()
  for field {.inject.} in branch.flds:
    if field.isKind:
      branchBody.add body

  branchBody




proc newObjectPathElem*[N](
    field: ObjectField[N], branch: OBjectBranch[N]): ObjectPathElem[N] =

  if branch.isElse:
    NObjectPathElem(
      isElse: true, kindField: field,
      notOfValue: branch.notOfValue)

  else:
    NObjectPathElem(
      isElse: false, kindField: field,
      ofValue: branch.ofValue)

type
  KindFields[N] = seq[ObjectField[N]] # Using this typedef makes semcheck fail. 10/10
  NKindFields = KindFields[NimNode]

proc mapBranches*(
    field: NObjectField,
    parent: seq[ObjectField[NimNode]],
    caseExpr: proc(path: seq[ObjectField[NimNode]]): NimNode,
    mapBranch: proc(path: seq[ObjectField[NimNode]],
                    branch: NObjectBranch): NimNode
  ): NimNode =

  if field.isKind:
    result = nnkCaseStmt.newTree(caseExpr(parent))
    for branch in field.branches:
      let thisPath = parent & field # newObjectPathElem(field, branch)
      result.addBranchBody(
        branch,
        newStmtList(
          mapBranch(thisPath, branch).fixEmptyStmt(),
          branch.mapItKindFields(field.mapBranches(
            thisPath, caseExpr, mapBranch))))


proc mapBranches*(
    obj: NObjectDecl,
    caseExpr: proc(path: seq[ObjectField[NimNode]]): NimNode,
    mapBranch: proc(path: seq[ObjectField[NimNode]],
                    branch: NObjectBranch): NimNode
  ): NimNode =
  result = newStmtList()
  for field in items(obj.flds):
    if field.isKind:
      result.add field.mapBranches(@[field], caseExpr, mapBranch)

template mapItBranches*(obj: NObjectDecl, expr, body: untyped): untyped =
  mapBranches(
    obj,
    proc(path {.inject.}: seq[ObjectField[NimNode]]): NimNode = expr,
    proc(path {.inject.}: seq[ObjectField[NimNode]],
         branch {.inject.}: NObjectBranch): NimNode = body
  )


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
          newSet(branch.ofValue),
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

template mapItCase*(objectDecl: NObjectDecl, expr, body: untyped): untyped =
  mapCase(
    objectDecl,
    proc(field {.inject.}: NObjectField,
         path {.inject.}: seq[NObjectField]): NimNode = expr,
    proc(field {.inject.}: NObjectField,
         path {.inject.}: seq[NObjectField]): NimNode = body
  )


proc mapGroups*(
    field: NObjectField,
    parent: seq[ObjectField[NimNode]],
    caseExpr: proc(path: seq[ObjectField[NimNode]]): NimNode,
    mapGroup: proc(path: seq[ObjectField[NimNode]], group: seq[NObjectField]): NimNode
  ): NimNode =

  if field.isKind:
    let thisPath = parent & field
    result = nnkCaseStmt.newTree(caseExpr(thisPath))
    for branch in field.branches:
      result.addBranchBody(
        branch,
        newStmtList(
          mapGroup(thisPath, branch.flds).fixEmptyStmt(),
          mapItKindFields(branch, field.mapGroups(
            thisPath, caseExpr, mapGroup))))


proc mapGroups*(
    obj: NObjectDecl,
    caseExpr: proc(path: seq[ObjectField[NimNode]]): NimNode,
    mapGroup: proc(path: seq[ObjectField[NimNode]], group: seq[NObjectField]): NimNode
  ): NimNode =

  result = newStmtList mapGroup(@[], obj.flds)
  for fld in items(obj.flds):
    if fld.isKind:
      result.add fld.mapGroups(@[], caseExpr, mapGroup)

template mapItGroups*(objectDecl: NObjectDecl, expr, body: untyped): untyped =
  mapGroups(
    objectDecl,
    proc(path {.inject.}: seq[NObjectField]): NimNode = expr,

    proc(path {.inject.}: seq[NObjectField],
         group {.inject.}: seq[NObjectField]): NimNode = body
  )


proc mapPath*(
    fld: NObjectField,
    parentField: seq[NObjectField],
    parentPath: NObjectPath,
    caseExpr: proc(path: seq[NObjectField]): NimNode,
    cb: proc(path: NObjectPath, fields: seq[NObjectField]): NimNode
  ): NimNode =

  if fld.isKind:
    result = nnkCaseStmt.newTree(caseExpr(parentField))
    for branch in fld.branches:
      let thisPath = parentPath & newObjectPathElem(fld, branch)
      result.addBranchBody(
        branch,
        newStmtList(
          cb(thisPath, branch.flds).fixEmptyStmt(),
          branch.mapItKindFields(field.mapPath(
            parentField & field, thisPath, caseExpr, cb))))

proc mapPath*(
    obj: NObjectDecl,
    caseExpr: proc(path: seq[NObjectField]): NimNode,
    cb: proc(path: NObjectPath, fields: seq[NObjectField]): NimNode
  ): NimNode =
  result = newStmtList cb(@[], obj.flds)
  for fld in items(obj.flds):
    if fld.isKind:
      result.add fld.mapPath(@[fld], @[], caseExpr, cb)


template mapItPath*(objectDecl: NObjectDecl, expr, body: untyped): untyped =
  mapPath(
    objectDecl,
    proc(path {.inject.}: seq[NObjectField]): NimNode = expr,

    proc(path {.inject.}: NObjectPath,
         group {.inject.}: seq[NObjectField]): NimNode = body
  )


proc getFlatFieldsPath*[N](decl: ObjectDecl[N]):
    seq[tuple[field: ObjectField[N], path: ObjectPath[N]]] =

  proc aux(
      parent: ObjectPath[N], field: ObjectField[N]
    ): seq[(ObjectField[N], ObjectPath[N])] =

    result.add (field, parent)
    if field.isKind:
      for branch in field.branches:
        for field in branch.flds:
          result.add aux(parent & newObjectPathElem(field, branch), field)

  for field in decl.flds:
    result.add aux(@[], field)


macro genXmlWriter*(obj: typedesc, stream, target: untyped) =
  let
    stream = stream.copyNimNode()
    impl = getObjectStructure(obj)
    kinds = impl.getKindFields()


  let branches2 = impl.mapItGroups(newIdent(path[^1].name)):
    var res = newStmtList()
    if path.len > 0 and path[^1].isFinalBranch():
      var call = newCall("new" & impl.name.head)
      for field in path:
        call.add newIdent(field.name)

      res.add newAsgn(newIdent("target"), call)

    res

  echo branches2.toStrLit()

  var loader = newCaseStmt(newCall("name", stream))
  for (field, path) in impl.getFlatFieldsPath():
    if not field.isKind:
      loader.addBranch(
        field.name,
        newStmtList(
          onPath(target, path),
          newCall("load", dotField(target, field))))

  # echo loader.toStrLit()

  let newObj = impl.mapItPath(newIdent(path[^1].name)):
    if path.len == 2 and path[^1].kindField.isFinalBranch():
      var res = newStmtList()
      for v1 in path[0].ofValue:
        for v2 in path[1].ofValue:
          var newCall = nnkObjConstr.newTree(newIdent(impl.name.head))
          newCall.add newExprColon(newIdent(path[0].kindField.name), v1)
          newCall.add newExprColon(newIdent(path[1].kindField.name), v2)

          res.add newAsgn(newIdent("result"), newCall)

      return res

  echo newObj
