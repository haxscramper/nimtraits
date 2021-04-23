import ../nimtraits
import hnimast

import hpprint

proc dotField*[N](self: N, field: ObjectField[N]): N =
  newNTree[N](nnkDotExpr, self, newNIdent[N](field.name))

macro genXmlWriter*(obj: typedesc, stream, target: untyped) =
  let
    stream = stream.copyNimNode()
    impl = getObjectStructure(obj)
    kinds = impl.getKindFields()
    self = ident("self")

  let writeKind = self.eachCase(impl) do(field: TraitField) -> NimNode:
    if field.isKind:
      result = newCall(
        "writeAttr", stream, self.dotField(field),
        newCall("$", self.dotField(field)))


  echo writeKind.toStrLit()


  var inAttrs = true
  let writeAttrs = eachCase(self, impl) do(field: TraitField) -> NimNode:
    if field.isTaggedWith("Attr"):
      result = newCall(
        "writeAttr", stream, self.dotField(field),
        newCall("$", self.dotField(field)))

  echo writeAttrs.toStrLit()
  let writeBody = eachCase(self, impl) do(field: TraitField) -> NimNode:
    if not field.isTaggedWith("Attr"):
      result = newcall("writeXml", stream, self.dotField(field))

  echo writeBody.toStrLit()
