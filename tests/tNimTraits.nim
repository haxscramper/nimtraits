import sugar, strutils, sequtils, strformat
import ../src/nimtraits
import marshal

#===========================  implementation  ============================#

#================================  tests  ================================#

import unittest

suite "Nim traits":
  test "Derive get/set":
    derive commonDerives:
      type
        Type {.derive(GetSet).} = object
          f1 {.name(field).}: int

    var tt: Type
    tt.field = 12
    echo tt.field

  test "Derive eq":
    derive commonDerives:
      type
        Type {.derive(Eq).} = object
          case kind: bool
            of true:
              a: char
            of false:
              b: float

    echo Type(kind: false) == Type(kind: true)

  test "Field validation":
    derive commonDerives:
      type
        Type {.derive(Validate).} = object
          fld {.check(it.startsWith("hhh")).}: string

  test "Serialization to JSON":
    type
      Test = object
        case kind: bool
          of true:
            a: char
          of false:
            b: float

    let val = Test()
    echo $$val
