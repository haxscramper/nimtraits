import hmisc/types/hnim_ast
import hmisc/hexceptions
import hmisc/algo/halgorithm
import hmisc/macros/[obj_field_macros, iflet]
import hpprint
import macros, strformat, options, sequtils, sugar, strutils, tables

# TODO support trait implementation builder debuggging - because callbacks
#      can modifty object definition it is necessary to keep track of all
#      transformations.

type
  TraitObject* = Object[NimNode, NPragma]
  TraitField* = ObjectField[NimNode, NPragma]

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

func excl*(lhs: var seq[string], rhs: seq[string]) =
  for it in rhs:
    let idx = lhs.find(it)
    if idx >= 0:
      lhs.del idx

const internalPrefix*: string = "impl_"

func getApiName*(fld: TraitField): string =
  iflet (fname = fld.annotation.getElem("name")):
    fname.expectKind nnkCall
    fname[1].strVal
  else:
    fld.name.dropPrefix(internalPrefix)

func isInternalFld*(fld: TraitField): bool =
  fld.name.startsWith(internalPrefix)

func getInternalName*(fld: TraitField): string =
  fld.name

func renameInternal*(fld: var TraitField): void =
  fld.name.addPrefix(internalPrefix)

func asInternal*(fld: TraitField): string =
  fld.name.addPrefix(internalPrefix)

# func requiresRenaming*(fld: TraitField): bool =
#   fld.markedAs("immut") or
#   fld.markedAs("name") or
#   fld.markedAs("check")

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
                    traitImpls.add impl.implCb(obj, conf.params)

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

          # echo $!obj.toNimNode()
          restypes.add obj.toNimNode()
        else:
          restypes.add obj

    result.add nnkTypeSection.newTree(restypes)
  result.add nnkStmtList.newTree(traitImpls)

  echo result.toStrLit()


func toNimNode(str: string): NimNode = ident(str)

#========================  GetSet implementation  ========================#

func makeGetSetImpl*(obj: var Object, params: DeriveParams): NimNode =
  let objName = obj.name
  var sameNames: Table[string, NType]

  block: # generate list of fields with the same public name; store
         # their types
    obj.eachFieldMut do(fld: var TraitField):
      if fld.markedAs("name"):
        let fname = fld.getApiName()
        if fname notin sameNames:
          sameNames[fname] = fld.fldType
        else:
          # TODO better error message
          assert fld.fldType == sameNames[fname]

        fld.renameInternal()

  let
    self = ident "self"
    it = ident "it"

  result = newStmtList()

  block:
    for apiName, fldType in sameNames:
      # Iterate over all pats; find all that can return result
      var resPaths: seq[tuple[path: NPath[NPragma], fld: TraitField]]
      discard self.eachPath(obj) do(
        path: NPath[NPragma], flds: seq[TraitField]) -> NimNode:
        for fld in flds:
          if fld.getApiName() == apiName:
            resPaths.add (path, fld)

      # for each possible path generate 'isOnPath' predicate
      var resGets: seq[NimNode]
      for (path, fld) in resPaths:
        let
          fldId = ident fld.getInternalName()
          onPath = self.onPath(path)
        resGets.add quote do:
          if `onPath`:
            return `self`.`fldId`

      var getImpl = newStmtList(resGets,)
      getImpl.add quote do: # if all checks failed - object has wrong kind
        raiseAssert("#[ IMPLEMENT:ERRMSG ]#")


      result.add (ident apiName).mkProcDeclNode(
        fldType, { "self" : objName },
        getImpl,
        exported = params.exported
      )

  debugecho $!result




  # block: # getter proc `field()`
  #   for name, fldType in sameNames:
  #     let getImpl = self.eachPath(obj) do(
  #       path: NPath[NPragma], flds: seq[TraitField]) -> NimNode:
  #       var getFld: NimNode
  #       var matches: bool = false
  #       for fld in flds:
  #         debugecho fld.getApiName(), " ", name
  #         if fld.getApiName() == name:
  #           getFld = newReturn(newDotExpr(self, ident fld.getInternalName()))
  #           matches = true

  #       if not matches:
  #         let errLit = newLit("#[ IMPLEMENT:ERRMSG ]#")
  #         getFld = quote do:
  #           if true:
  #             raiseAssert(`errLit`)

  #       getFld

  #     result.add (ident name).mkProcDeclNode(
  #       fldType, { "self" : objName },
  #       getImpl,
  #       exported = params.exported
  #     )

  # block: # setter for proc `field=`
  #   for name, fldType in sameNames:
  #     let setImpl = self.eachPath(obj) do(
  #       path: NPath[NPragma], flds: seq[TraitField]) -> NimNode:
  #       var matches: bool = false
  #       for fld in flds:
  #         if fld.getApiName() == name:
  #           let fldId = ident fld.getInternalName()
  #           matches = true
  #           result = quote do:
  #             debugecho "iii"
  #             # self.`fldId` = `it`

  #       if not matches:
  #         result = newCall(ident "raiseAssert",
  #                          newLit("#[ IMPLEMENT:ERRMSG ]#"))

  #     result.add mkProcDeclNode(
  #       nnkAccQuoted.newTree(ident name, ident "="),
  #         @[
  #           ("self", objName, nvdVar),
  #           ("it", fldType, nvdLet)
  #         ],
  #       impl = setImpl,
  #       exported = params.exported
  #     )



        # if fld.markedAs("immut"):
        #   # setter proc `field=`
        #   setdecl.add mkProcDeclNode(
        #     nnkAccQuoted.newTree(prName[1], ident "="),
        #       @[
        #         ("self", name, nvdVar),
        #         (fld.name, fld.fldType, nvdLet)
        #       ],
        #     newEmptyNode(),
        #     pragma = mkNPragma(
        #       nnkExprColonExpr.newTree(
        #         ident("error"),
        #         newLit(&"Field '{objName}.{prName[1].strVal()}' is marked as " &
        #           "'const' and cannot be assigned to"))),
        #     exported = params.exported
        #   )
        # else:


  # obj.eachCase do(fld: TraitField):
  #   if fld.annotation.isSome():
  #     iflet (prName = fld.annotation.get().getElem("name")):
  #       assertNodeKind(prName[1], {nnkIdent})
  #       let
  #         fldId = ident fld.name
  #         objName = $name

  #       if fld.markedAs("immut"):
  #         # setter proc `field=`
  #         setdecl.add mkProcDeclNode(
  #           nnkAccQuoted.newTree(prName[1], ident "="),
  #             @[
  #               ("self", name, nvdVar),
  #               (fld.name, fld.fldType, nvdLet)
  #             ],
  #           newEmptyNode(),
  #           pragma = mkNPragma(
  #             nnkExprColonExpr.newTree(
  #               ident("error"),
  #               newLit(&"Field '{objName}.{prName[1].strVal()}' is marked as " &
  #                 "'const' and cannot be assigned to"))),
  #           exported = params.exported
  #         )
  #       else:
  #         # setter proc `field=`
  #         setdecl.add mkProcDeclNode(
  #           nnkAccQuoted.newTree(prName[1], ident "="),
  #             @[
  #               ("self", name, nvdVar),
  #               (fld.name, fld.fldType, nvdLet)
  #             ],
  #           quote do:
  #             self.`fldId` = `fldId`
  #           ,
  #           exported = params.exported
  #         )

  #       # getter proc `field()`
  #       setdecl.add prName[1].mkProcDeclNode(
  #         fld.fldType, { "self" : name },
  #         newReturn(newDotExpr(ident "self", fldId)),
  #         exported = params.exported
  #       )


#==========================  Eq implementation  ==========================#

func makeEqImpl*(obj: var Object, params: DeriveParams): NimNode =
  let
    lhs = ident "lhs"
    rhs = ident "rhs"
  let impl = (lhs, rhs).eachParallelCase(obj) do(
    fld: TraitField) -> NimNode:
    let fld = ident fld.name
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
    ),
    exported = params.exported
  )

#=======================  Validate implementation  =======================#

type
  ValidationError* = ref object of CatchableError

# NOTE this is a really questionable implementation choice - mutate
# all fields and


func makeValidateImpl*(obj: var Object, params: DeriveParams): NimNode =
  ## NOTE all 'validated' fields will be made private and renamed
  ## (prefix `validated` will be added).
  var validators: seq[NimNode]
  let name = obj.name

  func getChecks(check: NimNode, fld: TraitField): NimNode =
    newStmtList: collect(newSeq):
      for ch in check[1..^1]:
        let errStr = &"Error while validating field '{name}.{fld.name}'" &
          &": assertion '" & ch.toStrLit().strVal() & "' failed."

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
      fld.renameInternal()
      let fldId = ident fld.getInternalName()

      validators.add newAccQuoted(fld.getAPIname(), "=").mkProcDeclNode(
        [ ("self", name, nvdVar), ("it", fld.fldType, nvdLet) ],
        quote do:
          when not defined(release): # XXXX
            `checks`
          self.`fldId` = it

        ,
        exported = params.exported
      )


      validators.add mkProcDeclNode(
        ident(fld.getAPIname()), fld.fldType,
        { "self" : name },
        newReturn(newDotExpr(ident "self", fldId)),
        exported = params.exported
      )

  let self = ident "self"
  let total = self.eachCase(obj) do(fld: NField[NPragma]) -> NimNode:
    iflet (check = fld.annotation.getElem("check")):
      let
        checks = check.getChecks(fld)
        fldId = ident fld.name

      return quote do:
        let it {.inject.} = `self`.`fldId`
        `checks`

  validators.add ident("validate").mkProcDeclNode(
    { "self" : obj.name }, total,
    pragma = mkNPragma("noSideEffect"),
    exported = params.exported
  )


  result = newStmtList(validators)
  # debugecho $!result


#=========================  Hash implementation  =========================#

func makeHashImpl*(obj: var Object, params: DeriveParams): NimNode =
  let self = ident "self"
  let impl = eachCase(self, obj) do(fld: TraitField) -> NimNode:
    let h = ident "h"
    newAssignment(h,
      newInfix(
        "!&", `h`,
        newCall(
          "hash", newDotExpr(self, ident fld.name))))

  result = (ident "hash").mkProcDeclNode(
    mkNType("Hash"),
    { "self" : obj.name },
    newStmtList(
      newVarStmt("h", mkNtype("Hash"), newLit(0)),
      impl,
      newReturn(newPrefix("!$", ident "h"))
    ),
    mkNPragma("noSideEffect"),
    exported = params.exported
  )

#=======================  Default implementation  ========================#

func makeDefaultImpl*(obj: var Object, params: DeriveParams): NimNode =
  discard


#=======================  JsonRepr implementation  =======================#

func makeJsonReprImpl*(obj: var Object, params: DeriveParams): NimNode =
  discard


#=======================  XmlRepr implementation  ========================#

func makeXmlReprImpl*(obj: var Object, params: DeriveParams): NimNode =
  discard


#====================  Default set of trait builders  ====================#

const commonDerives* = DeriveConf(
  traits: @[
    TraitConf(
      name: "GetSet",
      triggers: @["name", "immut"],
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
      name: "Hash",
      triggers: @[],
      implCb: makeHashImpl
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
