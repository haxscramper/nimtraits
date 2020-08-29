import sugar, strutils, sequtils, strformat, hashes, tables, macros
import ../src/nimtraits
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
    assert tt.goodName == 12

  test "{GetSet}; Getter/setter - change field API name":
    derive conf:
      type
        Type1 {.derive(GetSet).} = object
          f1 {.name(field).}: int

    var tt: Type1
    tt.field = 12
    assert tt.field == 12

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
    assert tt.field == 0

  test "{Eq}; Simple use case":
    derive conf:
      type
        Type {.derive(Eq).} = object
          case kind: bool
            of true:
              a: char
            of false:
              b: float

    assert Type(kind: false) != Type(kind: true)

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
    func makeEchoImpl(obj: var Object, params: DeriveParams): NimNode =
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

      debugecho $!result

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

  assert Test() == Test()

  expect ValidationError:
    t.sfld = "1039285701394875091843750984231570234897"
