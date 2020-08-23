import sugar, strutils, sequtils, strformat, hashes, tables
import ../src/nimtraits
import marshal
import hmisc/helpers

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
  test "Derive get/set":
    derive conf:
      type
        Type {.derive(GetSet).} = object
          f1 {.name(field).}: int

    var tt: Type
    tt.field = 12
    echo tt.field

  test "Derive eq":
    derive conf:
      type
        Type {.derive(Eq).} = object
          case kind: bool
            of true:
              a: char
            of false:
              b: float

    echo Type(kind: false) == Type(kind: true)

  test "Field validation":
    derive conf:
      type
        Type {.derive(Validate).} = object
          fld {.check(it.startsWith("hhh")).}: string

    var t: Type # no default constrctor, all validations are basically
                # useless

    expect ValidationError:
      t.fld = "####"

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
