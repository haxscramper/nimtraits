import hnimast
import hnimast/store_decl
export hnimast
import hmisc/core/all
export store_decl

template defaultImpl*(arg: untyped) {.pragma.}

macro Default*(obj: untyped): untyped =
  var defaulted = nnkBracket.newTree()
  proc aux(node: NimNode) =
    case node.kind:
      of nnkIdentDefs:
        if node[2].kind != nnkEmpty:
          let name = node.parseIdentName().name
          defaulted.add nnkTupleConstr.newTree(
            newLit(name.strVal()), node[2])

          node[2] = newEmptyNode()

      of nnkTokenKinds:
        discard

      else:
        for subnode in node:
          aux(subnode)


  aux(obj)

  if obj[0].kind == nnkPragmaExpr:
    obj[0][1].add newCall("defaultImpl", defaulted)

  else:
    raise newImplementKindError(obj[0])

  return obj

template Attr*() {.pragma.}
template Skip*(contexts: varargs[untyped]) {.pragma.}
