import std/[strutils, unittest, macros, streams]

import ../src/nimtraits, ../src/nimtraits/[trait_xml, trait_new]
import hmisc/other/oswrap
import hmisc/helpers
import hnimast
import hpprint

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
        case k1*: En1
          of e1First .. e1FirstCopy2:
             case k2*: En2
               of e2First:
                 f12first*: string = "test"

               of e2Second:
                 f12second*: string = "test2"
                 f12secondDouble*: string = "test23"

               of constValue, e2SecondCopy3:
                 discard

          of e1Second:
            case k3*: En3
              of e3First:
                f13first* {.Attr.}: string = "test3"

              of constValue2:
                f13second*: string = "testf13"


    storeTraits(Obj, constValue, constValue2)

    proc newObj(
        k1: En1 = e1First, k2: En2 = e2Second, k3: En3 = e3First
      ): Obj =

      genNewObject(Obj)

    proc writeXml(stream: var XmlWriter, target: Obj, tag: string) =
      genXmlWriter(Obj, target, stream, tag)

    proc loadXml(stream: var HXmlParser, target: var Obj, tag: string) =
      genXmlLoader(Obj, target, stream, tag)

    proc reloadXml[T](obj: T) =
      var
        outStr: string
        writer = newXmlWriter(newOutStringStream(outStr))

      writer.writeXml(obj, "item")
      echo outStr

      var
        reader = newHXmlParser(outStr)
        target: T

      reader.loadXml(target, "item")

      pprint obj
      pprint target

    var obj = newObj(e1Second)
    obj.f13first = "a"

    reloadXml(obj)


