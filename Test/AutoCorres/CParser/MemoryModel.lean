import Lang.AutoCorres.CParser.MemoryModel
import Lang.AutoCorres.CParser.Frontend
import Test.AutoCorres.CParser.EmbeddedFixtures

/-! # Bounded ARM memory regressions -/

namespace Zag.Test.AutoCorres.CParser.MemoryModel

open Zag.Lang.AutoCorres.CParser
open Zag.Lang.AutoCorres.CParser.ProgramAnalysis
open Zag.Lang.AutoCorres.CParser.MemoryLayout
open Zag.Lang.AutoCorres.CParser.MemoryModel

private def frontend :=
  Frontend.preprocessAndAnalyze .arm EmbeddedFixtures.files
    "proof-tests/global_array_update.c"

private theorem hasProgram : frontend.program.isSome := by native_decide

private def program : Program := frontend.program.get hasProgram

private def certificate : MemoryLayout.Certificate program :=
  (MemoryLayout.certify program).toOption.get (by native_decide)

private def fooSymbol? := program.symbols.find? (·.sourceName = "foo")

private theorem hasFooSymbol : fooSymbol?.isSome := by native_decide

private def fooId : Nat := (fooSymbol?.get hasFooSymbol).id

private def foo? : Option Pointer := Pointer.ofGlobal? certificate.layout fooId

private theorem hasFoo : foo?.isSome := by native_decide

private def foo : Pointer := foo?.get hasFoo

private def element (index : Int) : Option Pointer :=
  foo.add? certificate.layout 4 index

example : encodeIntegerLE 4 42 = [42, 0, 0, 0] := by native_decide
example : encodeIntegerLE 4 (-1) = [255, 255, 255, 255] := by native_decide
example : decodeUnsignedLE [42, 0, 0, 0] = 42 := by native_decide
example : encodeIntegerLE 4 0x12345678 = [0x78, 0x56, 0x34, 0x12] := by
  native_decide
example : decodeUnsignedLE [0x78, 0x56, 0x34, 0x12] = 0x12345678 := by
  native_decide
example : decodeIntegerLE ⟨.signed, 32⟩ [255, 255, 255, 255] = -1 := by
  native_decide

private def stored42 : Option ByteHeap := do
  let pointer ← element 3
  storeInteger? certificate (.signed .int) pointer 42 zeroHeap

example : stored42.bind (fun heap => readBytes? heap 4108 4) =
    some [42, 0, 0, 0] := by
  native_decide

example : stored42.bind (fun heap =>
    (element 3).bind fun pointer =>
      loadInteger? certificate (.signed .int) pointer heap) = some 42 := by
  native_decide

example : stored42.bind (fun heap =>
    (element 4).bind fun other =>
      loadInteger? certificate (.signed .int) other heap) = some 0 := by
  native_decide

example : (element (-1)).isNone := by native_decide
example : (element 1025).isNone := by native_decide
example : foo.add? certificate.layout 1 1 = none := by native_decide

private def onePast : Option Pointer := element 1024

example : onePast.map (·.address.toNat) = some 8192 := by native_decide
example : onePast.map (authorized certificate (.signed .int)) = some false := by
  native_decide

example : onePast.bind (fun pointer =>
    loadInteger? certificate (.signed .int) pointer zeroHeap) = none := by
  native_decide

example : initializeZero program |>.isOk := by native_decide

private def zeroImage? : Option (Image program) := (initializeZero program).toOption

example : zeroImage?.map (fun image => image.bytes foo.address) = some 0 := by
  native_decide

example : readBytes? zeroHeap (2 ^ 32 - 1) 1 = some [0] := by native_decide
example : readBytes? zeroHeap (2 ^ 32 - 1) 2 = none := by native_decide

private def wrongProvenance : Pointer := { foo with provenance := some (fooId + 1) }

example : authorized certificate (.signed .int) wrongProvenance = false := by
  native_decide

example : authorized certificate (.unsigned .int) foo = false := by
  native_decide

private def explicitProgram? : Option Program :=
  (Frontend.preprocessAndAnalyze .arm EmbeddedFixtures.files
    "parse-tests/read_global_array.c").program

example : explicitProgram?.map (fun explicit => !(initializeZero explicit).isOk) =
    some true := by
  native_decide

private def initializedRegisters? : Option (List Int) := do
  let explicit ← explicitProgram?
  let image ← (initializeImage explicit).toOption
  let symbol ← explicit.symbols.find? (·.sourceName = "msgRegisters")
  let pointer ← Pointer.ofGlobal? image.layout.layout symbol.id
  (List.range 6).mapM fun index => do
    let pointer ← pointer.add? image.layout.layout 4 (Int.ofNat index)
    loadInteger? image.layout (.unsigned .long) pointer image.bytes

example : initializedRegisters? = some [0, 1, 2, 3, 4, 5] := by
  native_decide

private def str2longInitialized? : Option (List Int) := do
  let initialized ← (Frontend.preprocessAndAnalyze .arm EmbeddedFixtures.files
    "examples/str2long.c").program
  let image ← (initializeImage initialized).toOption
  ["LONG_MAX", "LONG_MIN", "error"].mapM fun name => do
    let symbol ← initialized.symbols.find? (·.sourceName = name)
    let pointer ← Pointer.ofGlobal? image.layout.layout symbol.id
    loadInteger? image.layout symbol.type pointer image.bytes

example : str2longInitialized? = some [
    9223372036854775807, -9223372036854775808, 0] := by
  native_decide

private def convertedInitializers? : Option (List Int) := do
  let converted ← (Frontend.analyzeSource .arm "initializer-conversion.c" "
    long long values[] = {
      0xffffffffU + 1,
      ((unsigned int)-1 > 0)
    };
  ").program
  let image ← (initializeImage converted).toOption
  let symbol ← converted.symbols.find? (·.sourceName = "values")
  let pointer ← Pointer.ofGlobal? image.layout.layout symbol.id
  (List.range 2).mapM fun index => do
    let pointer ← pointer.add? image.layout.layout 8 (Int.ofNat index)
    loadInteger? image.layout (.signed .longLong) pointer image.bytes

example : convertedInitializers? = some [0, 1] := by native_decide

private def enumInitializers? : Option (List Int) := do
  let initialized ← (Frontend.analyzeSource .arm "enum-initializer.c" "
    enum { N = 3 };
    int x = N;
    long long y = 0xffffffffU + N;
  ").program
  let image ← (initializeImage initialized).toOption
  ["x", "y"].mapM fun name => do
    let symbol ← initialized.symbols.find? (·.sourceName = name)
    let pointer ← Pointer.ofGlobal? image.layout.layout symbol.id
    loadInteger? image.layout symbol.type pointer image.bytes

example : enumInitializers? = some [3, 2] := by native_decide

private def explicitNullPointerBytes? : Option (List UInt8) := do
  let initialized ← (Frontend.analyzeSource .arm "null-pointer-initializer.c"
    "int *pointer = 0;").program
  let image ← (initializeImage initialized).toOption
  let symbol ← initialized.symbols.find? (·.sourceName = "pointer")
  let pointer ← Pointer.ofGlobal? image.layout.layout symbol.id
  readBytes? image.bytes pointer.address.toNat 4

example : explicitNullPointerBytes? = some [0, 0, 0, 0] := by native_decide

private def partialInitializer? : Option (List Int) := do
  let program ← (Frontend.analyzeSource .arm "partial-initializer.c"
    "int values[3] = {7};").program
  let image ← (initializeImage program).toOption
  let symbol ← program.symbols.find? (·.sourceName = "values")
  let pointer ← Pointer.ofGlobal? image.layout.layout symbol.id
  (List.range 3).mapM fun index => do
    let pointer ← pointer.add? image.layout.layout 4 (Int.ofNat index)
    loadInteger? image.layout (.signed .int) pointer image.bytes

example : partialInitializer? = some [7, 0, 0] := by native_decide

private def nestedInitializerRejected? : Option Bool := do
  let nested ← (Frontend.analyzeSource .arm "nested-initializer.c"
    "int values[2][2] = {{1}, {2}};").program
  return match initializeImage nested with
    | .error (.unsupportedInitializer _) => true
    | _ => false

example : nestedInitializerRejected? = some true := by native_decide

private def aarch64Program : Program := { program with target := .aarch64 }

example : !(initializeZero aarch64Program).isOk := by native_decide

end Zag.Test.AutoCorres.CParser.MemoryModel
