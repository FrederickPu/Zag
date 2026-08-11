import Lang.AutoCorres.CParser.Frontend
import Test.AutoCorres.CParser.EmbeddedFixtures
import Test.AutoCorres.Upstream.Types

/-!
# Complete `struct` proof test

The pinned theory only registers `struct.c` with `external_file` and runs
`install_C_file`.  This certificate therefore stops at exact source
provenance and the substantive metadata produced by parser analysis.
-/

namespace Zag.Test.AutoCorres.Upstream.Struct

open Zag.Lang.AutoCorres.CParser
open Zag.Lang.AutoCorres.CParser.ProgramAnalysis
open Zag.Test.AutoCorres.CParser

def fixturePath : String := "proof-tests/struct.c"

def vendoredSource : String :=
  include_str "../Fixtures/proof-tests/struct.c"

def pinnedSource : String :=
  "/*\n" ++
  " * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)\n" ++
  " *\n" ++
  " * SPDX-License-Identifier: BSD-2-Clause\n" ++
  " */\n" ++
  "\n" ++
  "struct s {\n" ++
  "    unsigned long x;\n" ++
  "};\n" ++
  "\n" ++
  "struct s f(struct s v)\n" ++
  "{\n" ++
  "    return v;\n" ++
  "}\n"

def installationResult : Frontend.Result :=
  Frontend.preprocessAndAnalyze .arm EmbeddedFixtures.files fixturePath

private theorem option_eq_some_get (value : Option α) (isSome : value.isSome) :
    value = some (value.get isSome) := by
  cases value with
  | none => simp at isSome
  | some value => rfl

def installedProgram : Program :=
  installationResult.program.get (by native_decide)

def structType : AnalyzedCType := .structTy "s_C#0"

def functionType : AnalyzedCType := .function structType [structType]

structure FieldMetadata where
  sourceName : String
  type : AnalyzedCType
  offset : Nat
  deriving DecidableEq, Repr

structure StructMetadata where
  id : Nat
  sourceName : String
  canonicalName : String
  fields : List FieldMetadata
  size : Nat
  alignment : Nat
  defined : Bool
  complete : Bool
  deriving DecidableEq, Repr

def structMetadata : List StructMetadata :=
  installedProgram.structs.map fun info =>
    { id := info.id
      sourceName := info.sourceName
      canonicalName := info.canonicalName
      fields := info.fields.map fun field =>
        { sourceName := field.sourceName, type := field.type, offset := field.offset }
      size := info.size
      alignment := info.alignment
      defined := info.defined
      complete := info.complete }

structure SymbolMetadata where
  id : Nat
  sourceName : String
  type : AnalyzedCType
  kind : SymbolKind
  linkage : Option Linkage
  deriving DecidableEq, Repr

def symbolMetadata : List SymbolMetadata :=
  installedProgram.symbols.map fun symbol =>
    { id := symbol.id
      sourceName := symbol.sourceName
      type := symbol.type
      kind := symbol.kind
      linkage := symbol.linkage }

structure FunctionMetadata where
  symbolId : Nat
  returnType : AnalyzedCType
  parameters : List Nat
  locals : List Nat
  deriving DecidableEq, Repr

def functionMetadata : List FunctionMetadata :=
  installedProgram.functions.map fun info =>
    { symbolId := info.symbolId
      returnType := info.returnType
      parameters := info.parameters
      locals := info.locals }

abbrev SourceProvenance : Prop :=
  pinnedCommit = "bc2599a59c43e673dca021b10b9841e9b8da4430" ∧
    vendoredSource = pinnedSource ∧
    EmbeddedFixtures.files.find? (fun file => file.name == fixturePath) =
      some { name := fixturePath, source := pinnedSource } ∧
    installationResult.preprocessedSource = pinnedSource ∧
    installationResult.dependencies = #[]

abbrev InstallationSuccess : Prop :=
  installationResult.program = some installedProgram ∧
    installationResult.isSuccess = true ∧
    installationResult.diagnostics.isEmpty = true ∧
    installationResult.parseFailure.isNone = true ∧
    installationResult.analysisError.isNone = true

abbrev StructDeclaration : Prop :=
  structMetadata = [{
    id := 0
    sourceName := "s_C"
    canonicalName := "s_C#0"
    fields := [{ sourceName := "x_C", type := .unsigned .long, offset := 0 }]
    size := 4
    alignment := 4
    defined := true
    complete := true }]

abbrev ArmLayout : Prop :=
  installedProgram.target = Target.arm ∧
    installedProgram.target.longWidth = 32 ∧
    installedProgram.target.charWidth = 8 ∧
    (CType.sizeof installedProgram.target
      (fun name => if name = "s_C#0" then 4 else -1) structType).toOption = some 4

abbrev ByValueFunctionSignature : Prop :=
  symbolMetadata = [{
      id := 0, sourceName := "f", type := functionType,
      kind := .function, linkage := some .external }, {
      id := 1, sourceName := "v", type := structType,
      kind := .parameter 0, linkage := none }] ∧
    functionMetadata = [{
      symbolId := 0, returnType := structType, parameters := [1], locals := [] }]

abbrev SymbolUniqueness : Prop :=
  (installedProgram.symbols.map (·.id)).Nodup ∧
    (installedProgram.symbolsNamed "f").length = 1 ∧
    (installedProgram.symbolsNamed "v").length = 1

abbrev GeneratedTypeNameStability : Prop :=
  CType.typeName structType = "struct_s_C#0" ∧
    CType.typeName functionType = "[struct_s_C#0]->struct_s_C#0" ∧
    installedProgram.structs.map (·.canonicalName) = ["s_C#0"]

/-- All observations made by the upstream theory's two installation commands. -/
structure InstallationCertificate : Prop where
  sourceProvenance : SourceProvenance
  installationSuccess : InstallationSuccess
  structDeclaration : StructDeclaration
  armLayout : ArmLayout
  byValueFunctionSignature : ByValueFunctionSignature
  symbolUniqueness : SymbolUniqueness
  generatedTypeNameStability : GeneratedTypeNameStability

set_option maxRecDepth 100000 in
set_option maxHeartbeats 500000 in
theorem installationCertificate : InstallationCertificate := by
  constructor
  · native_decide
  · constructor
    · exact option_eq_some_get installationResult.program (by native_decide)
    · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide

theorem exact_source_provenance : SourceProvenance :=
  installationCertificate.sourceProvenance

theorem install_C_file_succeeds : InstallationSuccess :=
  installationCertificate.installationSuccess

theorem struct_tag_fields_are_exact : StructDeclaration :=
  installationCertificate.structDeclaration

theorem arm_size_alignment_layout_are_exact : ArmLayout :=
  installationCertificate.armLayout

theorem by_value_signature_is_exact : ByValueFunctionSignature :=
  installationCertificate.byValueFunctionSignature

theorem installed_symbols_are_unique : SymbolUniqueness :=
  installationCertificate.symbolUniqueness

theorem generated_type_names_are_stable : GeneratedTypeNameStability :=
  installationCertificate.generatedTypeNameStability

theorem install_C_file_certificate : InstallationCertificate := installationCertificate

end Zag.Test.AutoCorres.Upstream.Struct
