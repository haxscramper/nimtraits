import ../nimtraits
import hnimast
import hmisc/helpers

import hpprint

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
  KindFields[N] = seq[ObjectField[N]]
  NKindFields* = KindFields[NimNode]

proc mapBranches*(
    field: NObjectField, parent: NKindFields,
    caseExpr: proc(kinds: NKindFields): NimNode,
    mapBranch: proc(kinds: NKindFields, branch: NObjectBranch): NimNode
  ): NimNode =

  if field.isKind:
    result = nnkCaseStmt.newTree(caseExpr(parent))
    for branch in field.branches:
      let thisPath = parent & field
      let cbRes = mapBranch(thisPath, branch).nilToDiscard()

      var branchBody = newStmtList()
      for field in branch.flds:
        if field.isKind:
          branchBody.add mapBranches(
            field, thisPath, caseExpr, mapBranch)

      if branch.isElse:
        result.add nnkElse.newTree(newStmtList(cbRes, branchBody))

      else:
        result.add nnkOfBranch.newTree(
          normalizeSet(branch.ofValue), newStmtList(cbRes, branchBody))


proc mapBranches*(
    obj: NObjectDecl,
    caseExpr: proc(kinds: NKindFields): NimNode,
    mapBranch: proc(kinds: NKindFields, branch: NObjectBranch): NimNode
  ): NimNode =
  result = newStmtList()
  for field in items(obj.fields):
    if field.isKind:
      result.add field.mapBranches(@[field], caseExpr, mapBranch)

template mapSelfBranches*(obj: NObjectDecl, expr, body: untyped): untyped =
  mapBranches(
    ident "self", obj,
    proc(path {.inject.}: NKindFields): NimNode = expr,
    proc(path {.inject.}: NKindFields,
         branch {.inject.}: NObjectBranch): NimNode = body
  )

proc newIdent*(str: string): NimNode = newIdentNode(str)

macro genXmlWriter*(obj: typedesc, stream, target: untyped) =
  let
    stream = stream.copyNimNode()
    impl = getObjectStructure(obj)
    kinds = impl.getKindFields()
    self = ident("self")

  let writeKind = self.eachCase(impl) do(field: TraitField) -> NimNode:
    if field.isKind:
      result = newCall(
        "writeAttr", stream, self.dotField(field),
        newCall("$", self.dotField(field)))


  echo writeKind.toStrLit()

  let writeAttrs = eachCase(self, impl) do(field: TraitField) -> NimNode:
    if field.isTaggedWith("Attr"):
      result = newCall(
        "writeAttr", stream, self.dotField(field),
        newCall("$", self.dotField(field)))

  echo writeAttrs.toStrLit()

  let writeBody = eachCase(self, impl) do(field: TraitField) -> NimNode:
    if not field.isTaggedWith("Attr"):
      result = newcall("writeXml", stream, self.dotField(field))

  echo writeBody.toStrLit()
# newDotExpr(self, ident field.name)

  let branches = impl.mapSelfBranches(
    tern(path.len == 0,
         newIdent("k1"),
         newIdent(path[^1].kindField.name))
  ):
    newCall("load", newIdent(path[^1].kindField.name))

  echo branches.toStrLit()
