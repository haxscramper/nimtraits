import hnimast
import hmisc/hexceptions
import hmisc/algo/halgorithm
import hmisc/macros/iflet
import hmisc/hdebug_misc
export hnimast

{.push warning[UnusedImport]:off.}

import hpprint
import std/[macros, strformat, options, sequtils, sugar, strutils, tables]

type
  TraitObject* = ObjectDecl[NimNode]
  TraitField* = ObjectField[NimNode]
  TraitPath* = ObjectPath[NimNode]

  DeriveParams* = object
    exported*: bool

  DeriveConf* = object
    traits*: seq[TraitConf]
    params*: DeriveParams

  TraitConf* = object
    name*: string
    triggers*: seq[string]
    implCb*: (var TraitObject, DeriveParams) ~> NimNode
    overrides*: seq[string]

var objectImplMap {.compiletime.}: Table[string, TraitObject]
var enumImplMap {.compiletime.}: Table[string, NEnumDecl]

proc getObjectStructure*(obj: NimNode): TraitObject =
  let hash = obj.signatureHash()
  if hash in objectImplMap:
    objectImplMap[hash]

  else:
    raiseArgumentError(
      "Cannot get object structure for node " &
      obj.toStrLit().strVal() &
      " - not recorded in object impl map"
    )

proc getEnumStructure*(obj: NimNode): NEnumDecl =
  enumImplMap[obj.signatureHash()]

proc isObject*(node: NimNode): bool =
  case node.kind:
    of nnkObjectTy:
      true

    of nnkEnumTy:
      false

    of nnkRefTy, nnkPtrTy:
      node[0].kind in {nnkObjectTy}

    of nnkTypeDef:
      isObject(node[2])

    else:
      raiseImplementKindError(node)

proc setObjectStructure*(obj: NimNode, consts: seq[NimNode]) =
  let impl = getTypeImplBody(obj, false)
  if impl.isObject():
    if obj.signatureHash() notin objectImplMap:
      var parsed: TraitObject = parseObject(impl, false, consts)
      if parsed.hasPragma("defaultImpl"):
        let pragma = parsed.getPragmaArgs("defaultImpl")
        for field in iterateFields(parsed):
          for arg in pragma[0]:
            if field.name == arg[0].strVal():
              field.value = some arg[1]

      objectImplMap[obj.signatureHash()] = parsed


  else:
    var parsed = parseEnum(impl)
    enumImplMap[obj.signatureHash()] = parsed

macro storeTraitsImpl*(obj: typed, consts: varargs[typed]) =
  setObjectStructure(obj, toSeq(consts))

macro storeTraits*(obj: untyped, consts: varargs[untyped]) =
  # Generate call to store all constants in `(name, node)` plist
  result = newCall("storeTraitsImpl", obj)
  for c in consts:
    result.add nnkPar.newTree(newLit(c.strVal()), c)

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
    raiseImplementKindError(obj[0])

  return obj

macro Derive*(obj: typed): untyped =
  echo obj.treeRepr1()
  result = obj


template Attr*() {.pragma.}
template Skip*(contexts: varargs[untyped]) {.pragma.}
