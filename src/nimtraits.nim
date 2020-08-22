import hmisc/types/hnim_ast
import hmisc/hexceptions
import hmisc/macros/[obj_field_macros, iflet]
import hpprint
import macros, strformat, options, sequtils, sugar

# TODO support trait implementation builder debuggging - because callbacks
#      can modifty object definition it is necessary to keep track of all
#      transformations.

type
  TraitObject* = Object[NimNode, NPragma]
  TraitField* = ObjectField[NimNode, NPragma]

  DeriveConf* = object
    traits*: seq[TraitConf]
    # commonMarkers*: seq[string]

  TraitConf* = object
    name*: string
    triggers*: seq[string]
    implCb*: var TraitObject ~> NimNode
    overrides*: seq[string]

func excl*(lhs: var seq[string], rhs: seq[string]) =
  for it in rhs:
    let idx = lhs.find(it)
    if idx >= 0:
      lhs.del idx

#========================  derive implementation  ========================#

macro derive*(
  conf: static[DeriveConf], typesection: untyped): untyped =
  # TODO provide compilation errors on unknown `Derive` annotations
  var traitImpls: seq[NimNode]
  result = newStmtList()
  typesection.assertNodeKind {nnkStmtList}
  for section in typesection:
    section.assertNodeKind {nnkTypeSection}
    var restypes: seq[NimNode]
    for obj in section:
      case obj.kind:
        of nnkTypeDef:
          var obj: TraitObject = parseObject(obj, parseNimPragma)
          if obj.annotation.isSome():
            for annot in obj.annotation.get().elements:
              if annot.kind == nnkCall and annot[0] == ident("derive"):
                var deriveNames = collect(newSeq):
                  for trait in annot[1..^1]: # for all traits
                    if trait.kind == nnkIdent:
                      trait.strVal()
                    else: # assuming `nnkCall`, dropping parameters for now
                      trait[0].strVal()


                for impl in conf.traits:
                  if impl.name in deriveNames:
                    deriveNames.excl impl.overrides # XXXX no test for
                    # mutually excusive traits
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

#========================  GetSet implementation  ========================#

func makeGetSetImpl*(obj: var Object): NimNode =
  var setdecl: seq[NimNode]
  let name = obj.name
  obj.eachField do(fld: TraitField):
    if fld.annotation.isSome():
      iflet (prName = fld.annotation.get().getElem("name")):
        assertNodeKind(prName[1], {nnkIdent})
        let fldId = ident fld.name

        # setter proc `field=`
        setdecl.add mkProcDeclNode(
          nnkAccQuoted.newTree(prName[1], ident "="),
            @[
              ("self", name, nvdVar),
              (fld.name, mkNType(fld.fldType), nvdLet)
            ],
          quote do:
            self.`fldId` = `fldId`
        )

        # getter proc `field()`
        setdecl.add mkProcDeclNode(
          prName[1],
          mkNType(fld.fldType), # XXXX
          { "self" : name },
          quote do:
            self.`fldId`
        )

  result = newStmtList(setdecl)

#==========================  Eq implementation  ==========================#

func makeEqImpl*(obj: var Object): NimNode =
  let impl = (ident "lhs", ident "rhs").eachParallelCase(obj) do(
    objid: LhsRhsNode, fld: TraitField) -> NimNode:

    let
      fld = ident fld.name
      lhs = objid.lhs
      rhs = objid.rhs

    quote do:
        if `lhs`.`fld` != `rhs`.`fld`:
          return false


  result = [ident "=="].mkProcDeclNode(
    mkNType("bool"),
    { "lhs" : obj.name, "rhs" : obj.name },
    pragma = mkNPragma("noSideEffect"),
    impl = (
      quote do:
        `impl`
        return true
    )
  )

#=======================  Validate implementation  =======================#

type
  ValidationError* = ref object of CatchableError

# NOTE this is a really questionable implementation choice - mutate
# all fields and


func makeValidateImpl*(obj: var Object): NimNode =
  ## NOTE all 'validated' fields will be made private and renamed
  ## (prefix `validated` will be added).
  var validators: seq[NimNode]
  let name = obj.name

  func getChecks(check: NimNode, fld: TraitField): NimNode =
    newStmtList: collect(newSeq):
      for ch in check[1..^1]:
        let errStr = &"Error while validating field {fld.name} " &
          &"for type {name}: assertion '" & ch.toStrLit().strVal() & "' failed."

        quote do: # TODO generate static assert for correct return type
          if not `ch`:
            var exc: ValidationError
            new(exc)
            exc.msg = `errStr`
            raise exc
            # raise newException(ValidationError, `errStr`)


  obj.eachFieldMut do(fld: var TraitField):
    iflet (check = fld.annotation.getElem("check")):
      let checks = check.getChecks(fld)
      let fldId = ident("validate_" & fld.name)

      validators.add newAccQuoted(fld.name, "=").mkProcDeclNode(
        [ ("self", name, nvdVar), ("it", mkNType(fld.fldType), nvdLet) ],
        quote do:
          when not defined(release): # XXXX
            `checks`
          self.`fldId` = it
      )


      validators.add mkProcDeclNode(
        ident(fld.name),
        mkNType(fld.fldType), # XXXX
        { "self" : name },
        quote do:
          self.`fldId`
      )

  let self = ident "self"
  let total = self.eachCase(obj) do(objid: NimNode, fld: NField[NPragma]) -> NimNode:
    iflet (check = fld.annotation.getElem("check")):
      let
        checks = check.getChecks(fld)
        fldId = ident fld.name

      return quote do:
        let it {.inject.} = `self`.`fldId`
        `checks`

  validators.add ident("validate").mkProcDeclNode(
    { "self" : obj.name }, total, mkNPragma("noSideEffect"))


  obj.eachFieldMut do(fld: var TraitField):
    fld.name = "validate_" & fld.name

  result = newStmtList(validators)



#=======================  Default implementation  ========================#

func makeDefaultImpl*(obj: var Object): NimNode =
  discard


#=======================  JsonRepr implementation  =======================#

func makeJsonReprImpl*(obj: var Object): NimNode =
  discard


#=======================  XmlRepr implementation  ========================#

func makeXmlReprImpl*(obj: var Object): NimNode =
  discard


#====================  Default set of trait builders  ====================#

const commonDerives* = DeriveConf(
  traits: @[
    TraitConf(
      name: "GetSet",
      triggers: @["name"],
      implCb: makeGetSetImpl,
    ),
    TraitConf(
      name: "Validate",
      triggers: @["check", "name"],
      overrides: @["GetSet", "Default"],
      implCb: makeValidateImpl,
    ),
    TraitConf(
      name: "Eq",
      triggers: @[],
      implCb: makeEqImpl
    ),
    TraitConf(
      name: "Default",
      triggers: @[],
      implCb: makeDefaultImpl
    ),
    TraitConf(
      name: "JsonRepr",
      triggers: @[],
      implCb: makeJsonReprImpl
    ),
    TraitConf(
      name: "XmlRepr",
      triggers: @[],
      implCb: makeXmlReprImpl
    )
  ]
)
