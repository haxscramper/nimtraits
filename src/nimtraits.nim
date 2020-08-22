import hmisc/types/hnim_ast
import hmisc/hexceptions
import hmisc/macros/[obj_field_macros, iflet]
import hpprint
import macros, strformat, options, sequtils

type
  TraitObject* = Object[NimNode, NPragma]
  TraitField* = ObjectField[NimNode, NPragma]

  DeriveConf* = object
    traits*: seq[TraitConf]
    # commonMarkers*: seq[string]

  TraitConf* = object
    name*: string
    triggers*: seq[string]
    implCb*: TraitObject ~> NimNode

macro derive*(
  conf: static[DeriveConf], typesection: untyped): untyped =
  var traitImpls: seq[NimNode]
  result = newStmtList()
  typesection.expectKind nnkStmtList
  for section in typesection:
    section.expectKind nnkTypeSection
    var restypes: seq[NimNode]
    for obj in section:
      case obj.kind:
        of nnkTypeDef:
          var obj: TraitObject = parseObject(obj, parseNimPragma)
          if obj.annotation.isSome():
            for annot in obj.annotation.get().elements:
              if annot.kind == nnkCall and annot[0] == ident("derive"):
                for trait in annot[1..^1]: # for all traits
                  let name =
                    if trait.kind == nnkIdent:
                      trait.strVal()
                    else: # assuming `nnkCall`
                      trait[0].strVal()

                  for impl in conf.traits:
                    if impl.name == name and (impl.implCb != nil):
                      traitImpls.add impl.implCb(obj)

          let
            fldAnnots = conf.traits.mapIt(it.triggers).concat()

          # Iterate each annotation and filter out ones that were used
          # by `derive`.
          obj.eachAnnotMut do(pr: var Option[NPragma]) -> void:
            if pr.isSome():
              let elems = pr.get().elements
              var pass: seq[NimNode]

              case pr.get().kind:
                of oakObjectToplevel:
                  for elem in elems:
                    if elem.kind == nnkCall and elem[0] == ident("derive"):
                      discard # drop `{.derive(...).}`
                    else:
                      pass.add elem
                else:
                  for elem in elems:
                    let k = elem.kind
                    if k == nnkIdent and elem.strVal() in fldAnnots:
                      discard # drop `{.<trait-name>.}`
                    elif k == nnkCall and elem[0].strVal() in fldAnnots:
                      discard # drop `{.<trait>(.. <args> ..)}`
                    else:
                      pass.add elem

              if pass.len > 0:
                pr.get().elements = pass
              else:
                pr = none(NPragma)

          restypes.add obj.toNimNode()
        else:
          restypes.add obj

    result.add nnkTypeSection.newTree(restypes)
  result.add nnkStmtList.newTree(traitImpls)

  echo result.toStrLit()


func toNimNode(str: string): NimNode = ident(str)

func makeGetSetImpl*(obj: Object): NimNode =
  var setdecl: seq[NimNode]
  obj.eachField do(fld: TraitField):
    if fld.annotation.isSome():
      iflet (prName = fld.annotation.get().getElem("name")):
        assertNodeKind(prName[1], {nnkIdent})
        let fldId = ident fld.name

        # setter proc `field=`
        setdecl.add mkProcDeclNode(
          nnkAccQuoted.newTree(prName[1], ident "="),
            @[
              ("self", obj.name, nvdVar),
              (fld.name, mkNType(fld.fldType), nvdLet)
            ],
          quote do:
            self.`fldId` = `fldId`
        )

        # getter proc `field()`
        setdecl.add mkProcDeclNode(
          prName[1],
          mkNType(fld.fldType), # XXXX
          { "self" : obj.name },
          quote do:
            self.`fldId`
        )

  result = newStmtList(setdecl)


const deriveGetSetConf* = TraitConf(
  name: "GetSet",
  triggers: @["name"],
  implCb: makeGetSetImpl
)


const commonDerives* = DeriveConf(
  # commonMarkers: @["name"],
  traits: @[deriveGetSetConf]
)
