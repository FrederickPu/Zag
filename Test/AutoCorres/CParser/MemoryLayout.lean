import Lang.AutoCorres.CParser.MemoryLayout
import Lang.AutoCorres.CParser.Frontend
import Test.AutoCorres.CParser.EmbeddedFixtures

/-! # Generated global object layouts -/

namespace Zag.Test.AutoCorres.CParser.MemoryLayout

open Zag.Lang.AutoCorres.CParser
open Zag.Lang.AutoCorres.CParser.ProgramAnalysis
open Zag.Lang.AutoCorres.CParser.MemoryLayout

private def program? (entry : String) : Option Program :=
  (Frontend.preprocessAndAnalyze .arm EmbeddedFixtures.files entry).program

private def namedObjects? (entry : String) : Option (List (String × Nat × Nat × Nat)) := do
  let program ← program? entry
  let layout ← (generate program).toOption
  layout.objects.mapM fun object => do
    let symbol ← program.symbolById? object.symbolId
    return (symbol.sourceName, object.base, object.size, object.alignment)

private def certifies? (entry : String) : Option Bool := do
  let program ← program? entry
  return (certify program).isOk

example : namedObjects? "proof-tests/global_array_update.c" =
    some [("foo", 4096, 4096, 4)] := by
  native_decide

example : namedObjects? "proof-tests/array_indirect_update.c" =
    some [("array", 4096, 40, 4)] := by
  native_decide

example : namedObjects? "parse-tests/heap_lift_array.c" =
    some [("foo", 4096, 40, 4)] := by
  native_decide

example : namedObjects? "parse-tests/signed_ptr_ptr.c" = some [
    ("arr_ptr_1", 4096, 4, 4),
    ("arr_1", 4100, 480, 4)] := by
  native_decide

example : namedObjects? "parse-tests/struct1.c" = some [
    ("g_1", 4096, 4, 4),
    ("k_1", 4100, 4, 4),
    ("cow", 4104, 8, 4)] := by
  native_decide

example : [
    "proof-tests/global_array_update.c",
    "proof-tests/array_indirect_update.c",
    "parse-tests/heap_lift_array.c",
    "parse-tests/signed_ptr_ptr.c",
    "parse-tests/struct1.c"].all (certifies? · == some true) := by
  native_decide

private def arrayLeafFacts? (entry symbolName : String) (count : Nat) : Option Bool := do
  let program ← program? entry
  let certificate ← (certify program).toOption
  let symbol ← program.symbols.find? (·.sourceName = symbolName)
  let object ← certificate.layout.objectBySymbolId? symbol.id
  let first ← (certificate.layout.leafAt? symbol.id object.base (.signed .int)).orElse
    fun _ => certificate.layout.leafAt? symbol.id object.base (.unsigned .int)
  let lastAddress := object.base + (count - 1) * 4
  let last := certificate.layout.leaves.any fun leaf =>
    leaf.objectSymbolId = symbol.id && certificate.layout.leafAddress? leaf = some lastAddress
  return first.offset = 0 && last &&
    (certificate.layout.leaves.filter (·.objectSymbolId = symbol.id)).length = count

example : arrayLeafFacts? "proof-tests/global_array_update.c" "foo" 1024 = some true := by
  native_decide

example : arrayLeafFacts? "proof-tests/array_indirect_update.c" "array" 10 = some true := by
  native_decide

private def structLeafAddresses? : Option (List Nat) := do
  let program ← program? "parse-tests/struct1.c"
  let certificate ← (certify program).toOption
  let symbol ← program.symbols.find? (·.sourceName = "cow")
  certificate.layout.leaves.filter (·.objectSymbolId = symbol.id) |>.mapM
    certificate.layout.leafAddress?

example : structLeafAddresses? = some [4104, 4108] := by native_decide

private def inlineLeafAddresses? (source symbolName : String) : Option (List Nat) := do
  let program ← (Frontend.analyzeSource .arm "aggregate-layout.c" source).program
  let certificate ← (certify program).toOption
  let symbol ← program.symbols.find? (·.sourceName = symbolName)
  certificate.layout.leaves.filter (·.objectSymbolId = symbol.id) |>.mapM
    certificate.layout.leafAddress?

example : inlineLeafAddresses? "
    struct inner { int x; unsigned y; };
    struct outer { struct inner child; int z; };
    struct outer object;
  " "object" = some [4096, 4100, 4104] := by
  native_decide

example : inlineLeafAddresses? "
    struct pair { int x; int y; };
    struct pair values[2];
  " "values" = some [4096, 4100, 4104, 4108] := by
  native_decide

example : inlineLeafAddresses? "
    struct node { int x; };
    struct siblings { struct node left; struct node right; };
    struct siblings value;
  " "value" = some [4096, 4100] := by
  native_decide

private def cyclicStructMetadataRejected? : Option Bool := do
  let program ← (Frontend.analyzeSource .arm "cyclic-layout.c"
    "struct item { int value; }; struct item object;").program
  let info ← program.structs.find? (·.sourceName = "item_C")
  let field ← info.fields.head?
  let recursiveField := { field with type := .structTy info.canonicalName }
  let structs := program.structs.map fun candidate =>
    if candidate.id = info.id then { candidate with fields := [recursiveField] } else candidate
  let cyclic := { program with structs }
  return match generate cyclic with
    | .error .invariantFailure => true
    | _ => false

example : cyclicStructMetadataRejected? = some true := by native_decide

private def pointerLeafExists? : Option Bool := do
  let program ← program? "parse-tests/signed_ptr_ptr.c"
  let certificate ← (certify program).toOption
  let symbol ← program.symbols.find? (·.sourceName = "arr_ptr_1")
  let object ← certificate.layout.objectBySymbolId? symbol.id
  return (certificate.layout.leafAt? symbol.id object.base symbol.type).isSome

example : pointerLeafExists? = some true := by native_decide

private def tinyAddressSpaceRejected : Option Bool := do
  let program ← program? "proof-tests/global_array_update.c"
  let tiny := { program with target := { program.target with pointerWidth := 12 } }
  return !(generate tiny).isOk

example : tinyAddressSpaceRejected = some true := by native_decide

private def corruptedLayoutsRejected : Option Bool := do
  let program ← program? "proof-tests/global_array_update.c"
  let layout ← (generate program).toOption
  let object ← layout.objects.head?
  let wrongWidth := { layout with pointerWidth := layout.pointerWidth - 1 }
  let wrongTypeObject := { object with type := .signed .short }
  let wrongType := { layout with objects := wrongTypeObject :: layout.objects.drop 1 }
  let wrongBaseObject := { object with base := object.base + 1 }
  let wrongBase := { layout with objects := wrongBaseObject :: layout.objects.drop 1 }
  let wrongNext := { layout with nextAddress := layout.nextAddress + 1 }
  return !(check program wrongWidth).all && !(check program wrongType).all &&
    !(check program wrongBase).all && !(check program wrongNext).all

example : corruptedLayoutsRejected = some true := by native_decide

private def resizedGlobalProgram? (count : Int) : Option Program := do
  let program ← program? "proof-tests/global_array_update.c"
  let symbols := program.symbols.map fun symbol =>
    if symbol.kind = .global then
      { symbol with type := .array (.signed .int) (some count) }
    else symbol
  return { program with
    target := { program.target with pointerWidth := 16 }
    symbols }

private def onePastReservationAndOverflow : Option Bool := do
  let exact ← resizedGlobalProgram? 15359
  let onePastUnrepresentable ← resizedGlobalProgram? 15360
  let overflow ← resizedGlobalProgram? 15361
  return (generate exact).isOk && !(generate onePastUnrepresentable).isOk &&
    !(generate overflow).isOk

example : onePastReservationAndOverflow = some true := by native_decide

end Zag.Test.AutoCorres.CParser.MemoryLayout
