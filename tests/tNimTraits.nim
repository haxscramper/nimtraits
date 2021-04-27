{.push warning[UnusedImport]:off.}

import sugar, strutils, sequtils, strformat, hashes, tables, macros
import ../src/nimtraits, ../src/nimtraits/trait_xml
import marshal
import hmisc/helpers
import hnimast

#===========================  implementation  ============================#

#================================  tests  ================================#

import unittest

const conf = commonDerives.withIt do:
  it.params.exported = false # disable export for unit testing


# FIXME fails to compile when I put this in unit test
derive commonDerives:
  type
    Hhhhh {.derive(Hash, Eq).} = object
      f1: float
      f3: int
      case f5: bool
        of false:
          f2: char
        else:
          f4: float

var hh: Table[Hhhhh, int]
hh[Hhhhh(f3: 12)] = 1231

suite "Nim traits":
  test "Positional init":
    type
      HLStackOpKind = enum
        hsoLoad
        hsoCallFunc
        hsoForIter
        hsoJump
        hsoIfNotJump
        hsoPopTop
        hsoGetIter
        hsoStoreName
        hsoLoadName

      HLStackOp {.storeDefaults.} = object
        case kind*: HLStackOpKind
          of hsoLoad:
            value*: string

          of hsoCallFunc:
            argc*: int

          of hsoForIter, hsoJump, hsoIfNotJump:
            jumpOffset*: int

          of hsoStoreName, hsoLoadName:
            varName*: string

          else:
            discard

        annotation*: string

    macro op(kind: static[HLStackOpKind], args: varargs[untyped]):
      untyped =
      result = initPositionalInitImpl(kind, "HLStackOp", toSeq(args))

    doAssert hsoJump.op(10).jumpOffset == 10
    let opImpl = hsoLoadName.op("test")

  test "Store defaults":
    type Def {.storeDefaults.} = object
      fld1: int = 10


    initDefaultInitImpl("Def", false)

    doAssert initDef().fld1 == 10
    doAssert initDef(11).fld1 == 11


  test "{GetSet} Two fields with the same API name":
    derive conf:
      type GetSetSameName {.derive(GetSet).} = object
        case ch: char
          of 'e':
            e {.name(goodName).}: int
          of 'z':
            z {.name(goodName).}: int
          else:
            discard

    var tt = GetSetSameName(ch: 'e')

    tt.goodName = 12
    doAssert tt.goodName == 12

  test "{GetSet}; Getter/setter - change field API name":
    derive conf:
      type
        Type1 {.derive(GetSet).} = object
          f1 {.name(field).}: int

    var tt: Type1
    tt.field = 12
    doAssert tt.field == 12

  test "{GetSet}; fully const field":
    derive conf:
      type Type {.derive(GetSet).} = object
        f2 {.name(field), immut.}: int

    var tt: Type
    when false: # NOTE compilation error test
      tt.field = 12312

  test "{GetSet}; const field with partial immutability":
   derive conf:
     type Type {.derive(GetSet).} = object
       case kind: bool
       of true:
         fld1 {.name(field), immut.}: int
       of false:
         fld2 {.name(field).}: int


   var tt = Type(kind: true)
   expect AssertionError:
     tt.field = 123

  test "{GetSet}; get field from else branch":
    derive conf:
      type Type {.derive(GetSet).} = object
        case kind: bool
        of true:
          fld2 {.name(field).}: int
        else:
          fld1 {.name(field).}: int

    var tt = Type(kind: true)
    doAssert tt.field == 0

  test "{Eq}; Simple use case":
    derive conf:
      type
        Type {.derive(Eq).} = object
          case kind: bool
            of true:
              a: char
            of false:
              b: float

    doAssert Type(kind: false) != Type(kind: true)

    func customEq(lhs, rhs: Type): bool = initEqImpl(Type)

  test "Field validation":
    derive conf:
      type
        Type {.derive(Validate).} = object
          fld {.check(it.startsWith("hhh")).}: string

    var t: Type # no default constrctor, all validations are basically
                # useless

    expect ValidationError:
      t.fld = "####"

  test "Custom trait implementation":
    func makeEchoImpl(obj: var TraitObject, params: DeriveParams): NimNode =
      let
        self = ident "self" # name of the object for case statement.
        impl = self.eachCase(obj) do(fld: TraitField) -> NimNode:
          # Iterate each field in object and execute callbac for it.
          let
            fldName = newLit fld.getApiName()
            # To avoid collision betteen different traits that might
            # modify field names it is necessary to use `getApiName` -
            # to get public field name
            fldId = ident fld.getInternalName()
            # `getInternalName` returns actual name of the field in
            # object
          quote do:
            echo "Field '", `fldName`, "' has value ", `self`.`fldId`

      # Result of trait implementation callback can be anyting - in
      # this case it is a procedure declaration. Helper proc builder
      # from `hmisc/types/hnim_ast` is used.
      result = (ident "echoAll").newProcDeclNode(
        { "self" : obj.name },
        impl,
        exported = false
      )


    const deriveConf = DeriveConf( # Create custom set of trait
                                   # configurations
      traits: @[
        TraitConf(
          name: "EchoFields", # <-----------------+
          implCb: makeEchoImpl)])    #            |
                                     #            |
    derive deriveConf: # Use it in derive macro   |________
      type        #__________ annotate type with `EchoFields`
        A {.derive(EchoFields).} = object
          case bbb: bool
          of true:
            zzz: int
          else:
            qqq: char

    let test = A()
    test.echoAll()

  test "Declare init":
    func makeInitImpl(obj: var TraitObject, params: DeriveParams): NimNode =
      let
        self = ident "self"
        impl = self.eachCase(obj) do(fld: TraitField) -> NimNode:
          if fld.value.isSome():
            let val = fld.value.get()
            let fld = ident fld.getInternalName()
            let res = ident "result"
            return quote do:
              `res`.`fld` = `val`

      let init = ident("init" & obj.name.head)
      let name = ident(obj.name.head)
      result = quote do:
        proc `init`(): `name` =
          `impl`

    const deriveConf = DeriveConf(
      traits: @[TraitConf(name: "Init", implCb: makeInitImpl)])

    derive deriveConf:
      type
        A {.derive(Init).} = object
          hello: int = 12

    let val = initA()
    echo val



suite "Nim traits combinations":
  derive conf:
    type
      Test {.derive(Eq, Validate).} = object
        case str: bool
          of true:
            sfld {.check(it.len < 20).}: string
          of false:
            ifld {.check(it mod 2 == 0).}: int

  var t: Test

  doAssert Test() == Test()

  expect ValidationError:
    t.sfld = "1039285701394875091843750984231570234897"

import std/streams

suite "`trait`":
  test "template annotations":
    template Eq() {.pragma.}
    template XmlIO() {.pragma.}
    template Attr() {.pragma.}

    type
      En1 = enum e1First, e1FirstCopy1, e1FirstCopy2, e1Second
      En2 = enum e2First, e2Second, e2SecondCopy = 5,
        e2SecondCopy2, e2SecondCopy3 = 10
      En3 = enum e3First, e3Second

    const constValue = { e2SecondCopy .. e2SecondCopy2 }
    const constValue2 = e3Second

    type
      Obj {.Default, Eq, XmlIO.} = object
        case k1: En1
          of e1First .. e1FirstCopy2:
             case k2: En2
               of e2First:
                 f12first*: string = "test"

               of e2Second:
                 f12second*: string = "test2"
                 f12secondDouble*: string = "test23"

               of constValue, e2SecondCopy3:
                 discard

          of e1Second:
            case k3: En3
              of e3First:
                f13first* {.Attr.}: string = "test3"

              of constValue2:
                f13second*: string = "testf13"


    storeTraits(Obj, constValue, constValue2)

    # proc newObj(): Obj =
    #   genNewObject(Obj)

    proc writeXml(stream: XmlWriter, target: Obj) =
      genXmlWriter(Obj, target, stream, "item")

    let writer = newXmlWriter(stdout.newFileStream())
    writer.writeXml(Obj())
