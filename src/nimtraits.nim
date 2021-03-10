import hnimast, hnimast/obj_field_macros
import hmisc/hexceptions
import hmisc/algo/halgorithm
import hmisc/macros/iflet

{.push warning[UnusedImport]:off.}

import hpprint
import macros, strformat, options, sequtils, sugar, strutils, tables

# TODO support trait implementation builder debuggging - because callbacks
#      can modifty object definition it is necessary to keep track of all
#      transformations.

type
  TraitObject* = ObjectDecl[NimNode, NPragma]
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
      assertNodeKind(obj, {nnkTypeDef})
      case obj[2].kind:
        of nnkObjectTy:
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

  # echo result.toStrLit()


func toNimNode(str: string): NimNode = ident(str)

#========================  GetSet implementation  ========================#

func makeGetSetImpl*(obj: var TraitObject, params: DeriveParams): NimNode =
  let objName = obj.name
  var sameNames: Table[string, NType[NimNode]]

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

        fld.exported = false
        fld.renameInternal()

  let
    self = ident "self"
    it = ident "it"

  result = newStmtList()

  block:
    for apiName, fldType in sameNames:
      # Iterate over all pats; find all that can return result
      var resPaths: seq[tuple[
        path: NObjectPath[NPragma],
        fld: TraitField,
        immut: bool]] = @[]

      discard self.eachPath(obj) do(
        path: NObjectPath[NPragma], flds: seq[TraitField]) -> NimNode:
        for fld in flds:
          if fld.getApiName() == apiName:
            # debugecho fld.getInternalName(), " is named as ", fld.getApiName()
            resPaths.add (path, fld, fld.markedAs("immut"))

      # debugecho resPaths.len, " fields have the same api name ", apiName
      block: # getter builder
        # for each possible path generate 'isOnPath' predicate
        var resGets: seq[NimNode]
        for (path, fld, _) in resPaths:
          let
            fldId = ident fld.getInternalName()
            onPath = self.onPath(path)
          resGets.add quote do:
            if `onPath`:
              return `self`.`fldId`

        var getImpl = newStmtList(resGets)
        getImpl.add quote do: # if all checks failed - object has wrong kind
          raiseAssert("#[ IMPLEMENT:ERRMSG ]#")


        result.add toNNode newNProcDecl(apiName).withIt do:
          it.returnType = fldType
          it.addArgument("self", objName)
          it.impl = getImpl
          it.exported = params.exported

      block: # setter builder
        # for each possible path generate 'isOnPath' predicate
        # if fld.markedAs("immut"):
        #   # setter proc `field=`

        if resPaths.allOfIt(it.immut):
          result.add toNNode newNProcDecl(apiName).withIt do:
            it.kind = pkAssgn
            it.exported = params.exported
            it.addARgument({
              "self": newNType("var", [objName]),
              "it": fldType
            })

            it.pragma = newNPragma(
              nnkExprColonExpr.newTree(
                ident("error"),
                newLit(&"Field '{objName}.{apiName}' is marked as " &
                  "'immut' for all paths and cannot be assigned to")))

        else:
          let matched = ident "matched"
          var resGets: seq[NimNode]
          for (path, fld, immut) in resPaths:
            let
              fldId = ident fld.getInternalName()
              onPath = self.onPath(path)

            let immutAssert =
              if immut:
                newCall(
                  "raiseAssert",
                  newLit(
                    &"Field '{objName}.{apiName} is " &
                      "immutable for object kind"))
                    # TODO print current object kind values
              else:
                newEmptyNode()

            resGets.add quote do:
              if `onPath`:
                if true:
                  `immutAssert`
                `matched` = true
                `self`.`fldId` = `it`

          var setImpl = newStmtList(resGets)
          setImpl.add quote do:
            if not `matched`:
              raiseAssert("#[ IMPLEMENT:ERRMSG ]#")

          result.add toNNode newNProcDecl(apiName).withIt do:
            it.kind = pkAssgn
            it.exported = params.exported
            it.addArgument({
              "self": newNType("var", [objName]),
              "it": fldType
            })
            it.impl = quote do:
              var `matched`: bool = false
              `setImpl`

          # result.add newProcDeclNode(
          #   nnkAccQuoted.newTree(ident , ident "="),
          #     @[
          #       ("self", objName, nvdVar),
          #       ("it", fldType, nvdLet)
          #     ],
          #   impl =
          #     (
          #       quote do:
          #     )
          #   ,
          #   exported = params.exported
          # )

  # block:
  #   for apiName, fldType in sameNames:

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

  #     result.add (ident name).newProcDeclNode(
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

  #     result.add newProcDeclNode(
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
        #   setdecl.add newProcDeclNode(
        #     nnkAccQuoted.newTree(prName[1], ident "="),
        #       @[
        #         ("self", name, nvdVar),
        #         (fld.name, fld.fldType, nvdLet)
        #       ],
        #     newEmptyNode(),
        #     pragma = newNPragma(
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
  #         setdecl.add newProcDeclNode(
  #           nnkAccQuoted.newTree(prName[1], ident "="),
  #             @[
  #               ("self", name, nvdVar),
  #               (fld.name, fld.fldType, nvdLet)
  #             ],
  #           newEmptyNode(),
  #           pragma = newNPragma(
  #             nnkExprColonExpr.newTree(
  #               ident("error"),
  #               newLit(&"Field '{objName}.{prName[1].strVal()}' is marked as " &
  #                 "'const' and cannot be assigned to"))),
  #           exported = params.exported
  #         )
  #       else:
  #         # setter proc `field=`
  #         setdecl.add newProcDeclNode(
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
  #       setdecl.add prName[1].newProcDeclNode(
  #         fld.fldType, { "self" : name },
  #         newReturn(newDotExpr(ident "self", fldId)),
  #         exported = params.exported
  #       )


#==========================  Eq implementation  ==========================#

func makeEqImplBody*(obj: TraitObject, params: DeriveParams): NimNode =
  let
    lhs = ident "lhs"
    rhs = ident "rhs"

  let impl = (lhs, rhs).eachParallelCase(obj) do(
    fld: TraitField) -> NimNode:
    let fld = ident fld.name
    quote do:
      if `lhs`.`fld` != `rhs`.`fld`:
        return false

  return impl



func makeEqImpl*(obj: var TraitObject, params: DeriveParams): NimNode =
  let impl = makeEqImplBody(obj, params)

  result = toNNode newNProcDecl("==").withIt do:
    it.returnType = newNType("bool")
    it.addARgument({ "lhs" : obj.name, "rhs" : obj.name })
    it.pragma = newNPragma("noSideEffect")
    it.kind = pkOperator

    it.impl = quote do:
      `impl`
      return true

    it.exported = params.exported

#=======================  Validate implementation  =======================#

type
  ValidationError* = ref object of CatchableError

# NOTE this is a really questionable implementation choice - mutate
# all fields and


func makeValidateImpl*(obj: var TraitObject, params: DeriveParams): NimNode =
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

      validators.add toNNode newNProcDecl(fld.getApiName()).withIt do:
        it.kind = pkAssgn
        it.addArgument({
          "self": newNType("var", [name]),
          "it": fld.fldType
        })

        it.exported = params.exported
        let itName = ident("it")
        it.impl = quote do:
          when not defined(release): # XXXX
            `checks`
          self.`fldId` = `itName`


      # validators.add newAccQuoted(fld.getAPIname(), "=").newProcDeclNode(
      #   [ ("self", name, nvdVar), ("it", fld.fldType, nvdLet) ],
      #   quote do:
      #   ,
      #   exported = params.exported
      # )


      validators.add toNNode newNProcDecl(fld.getApiName()).withIt do:
        it.returnType = fld.fldType
        it.addArgument("self", name)
        it.exported = params.exported
        it.impl = newReturn(newDotExpr(ident "self", fldId))

  let self = ident "self"
  let total = self.eachCase(obj) do(fld: NObjectField[NPragma]) -> NimNode:
    iflet (check = fld.annotation.getElem("check")):
      let
        checks = check.getChecks(fld)
        fldId = ident fld.name

      return quote do:
        let it {.inject.} = `self`.`fldId`
        `checks`

  validators.add toNNode newNProcDecl("validate").withIt do:
    it.addArgument("self", obj.name)
    it.impl = total
    it.pragma = newNPragma("noSideEffect")
    it.exported = params.exported

  result = newStmtList(validators)


#=========================  Hash implementation  =========================#

func makeHashImplBody*(obj: TraitObject, params: DeriveParams): NimNode =
  let self = ident "self"
  let impl = eachCase(self, obj) do(fld: TraitField) -> NimNode:
    let h = ident "h"
    newAssignment(h,
      newInfix(
        "!&", `h`,
        newCall(
          "hash", newDotExpr(self, ident fld.name))))

  return newStmtList(
    newVarStmt("h", newNtype("Hash"), newLit(0)),
    impl,
    newReturn(newPrefix("!$", ident "h"))
  )


func makeHashImpl*(obj: var TraitObject, params: DeriveParams): NimNode =
  result = toNNode newNProcDecl("hash").withIt do:
    it.returnType = newNType("Hash")
    it.addArgument("self", obj.name)
    it.impl = makeHashImplBody(obj, params)
    it.pragma = newNPragma("noSideEffect")
    it.exported = params.exported

#=======================  Default implementation  ========================#

func makeDefaultImpl*(obj: var TraitObject, params: DeriveParams): NimNode =
  discard


#=======================  JsonRepr implementation  =======================#

func makeJsonReprImpl*(obj: var TraitObject, params: DeriveParams): NimNode =
  discard


#=======================  XmlRepr implementation  ========================#

func makeXmlReprImpl*(obj: var TraitObject, params: DeriveParams): NimNode =
  discard


#====================  Default set of trait builders  ====================#

macro initEqImpl*(T: typed): untyped =
  parseObject(T, parseNimPragma).makeEqImplBody(DeriveParams())

macro initHashImpl*(T: typed): untyped =
  parseObject(T, parseNimPragma).makeHashImplBody(DeriveParams())

const commonDerives* = DeriveConf(
  params: DeriveParams(
    exported: true
  ),
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
