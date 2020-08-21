import hmisc/types/hnim_ast

type
  TraitObject* = Object[NimNode, NPragma]

  DeriveConf* = object
    traits*: seq[TraitConf]
    commonMarkers*: seq[string]

  TraitConf* = object
    name*: string
    triggers*: seq[string]
    implCb*: proc(obj: TraitObject): NimNode {.noSideEffect.}

macro derive*(
  conf: static[DeriveConf], typesection: untyped): untyped =
  discard


func makeGetSetImpl*(obj: Object): NimNode =
  discard

const deriveGetSetConf* = TraitConf(
  name: "GetSet",
  triggers: @[],
)


const commonDerives* = DeriveConf(
  commonMarkers: @["name"],
  traits: @[deriveGetSetConf]
)
