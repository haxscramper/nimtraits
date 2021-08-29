import ../nimtraits

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
