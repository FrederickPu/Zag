import Lang.AutoCorres.CParser.Frontend
import Test.AutoCorres.CParser.EmbeddedFixtures
import Test.AutoCorres.Upstream.Types

/-!
# Complete `struct` proof test

The pinned [`struct.thy`](https://github.com/seL4/l4v/blob/bc2599a59c43e673dca021b10b9841e9b8da4430/tools/autocorres/tests/proof-tests/struct.thy)
only registers [`struct.c`](https://github.com/seL4/l4v/blob/bc2599a59c43e673dca021b10b9841e9b8da4430/tools/autocorres/tests/proof-tests/struct.c)
with `external_file` and runs `install_C_file`. This certificate therefore
stops at exact source provenance and the parser metadata that command produces.
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
  installedProgram.structs.map (·.id) = [0] ∧
    installedProgram.structs.map (·.sourceName) = ["s_C"] ∧
    installedProgram.structs.map (·.canonicalName) = ["s_C#0"] ∧
    installedProgram.structs.map (·.fields.map fun field =>
      (field.sourceName, field.type, field.offset)) = [[("x_C", .unsigned .long, 0)]] ∧
    installedProgram.structs.map (·.size) = [4] ∧
    installedProgram.structs.map (·.alignment) = [4] ∧
    installedProgram.structs.map (·.defined) = [true] ∧
    installedProgram.structs.map (·.complete) = [true]

abbrev ArmLayout : Prop :=
  installedProgram.target = Target.arm ∧
    installedProgram.target.longWidth = 32 ∧
    installedProgram.target.charWidth = 8 ∧
    (CType.sizeof installedProgram.target
      (fun name => if name = "s_C#0" then 4 else -1) structType).toOption = some 4

abbrev ByValueFunctionSignature : Prop :=
  installedProgram.symbols.map (·.id) = [0, 1] ∧
    installedProgram.symbols.map (·.sourceName) = ["f", "v"] ∧
    installedProgram.symbols.map (·.type) = [functionType, structType] ∧
    installedProgram.symbols.map (·.kind) = [.function, .parameter 0] ∧
    installedProgram.symbols.map (·.linkage) = [some .external, none] ∧
    installedProgram.functions.map (·.symbolId) = [0] ∧
    installedProgram.functions.map (·.returnType) = [structType] ∧
    installedProgram.functions.map (·.parameters) = [[1]] ∧
    installedProgram.functions.map (·.locals) = [[]]

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
theorem install_C_file_certificate : InstallationCertificate := by
  refine ⟨by native_decide, ?_, by native_decide, by native_decide,
    by native_decide, by native_decide, by native_decide⟩
  exact ⟨option_eq_some_get installationResult.program (by native_decide), by native_decide⟩

theorem exact_source_provenance : SourceProvenance :=
  install_C_file_certificate.sourceProvenance

theorem install_C_file_succeeds : InstallationSuccess :=
  install_C_file_certificate.installationSuccess

theorem struct_tag_fields_are_exact : StructDeclaration :=
  install_C_file_certificate.structDeclaration

theorem arm_size_alignment_layout_are_exact : ArmLayout :=
  install_C_file_certificate.armLayout

theorem by_value_signature_is_exact : ByValueFunctionSignature :=
  install_C_file_certificate.byValueFunctionSignature

theorem installed_symbols_are_unique : SymbolUniqueness :=
  install_C_file_certificate.symbolUniqueness

theorem generated_type_names_are_stable : GeneratedTypeNameStability :=
  install_C_file_certificate.generatedTypeNameStability

end Zag.Test.AutoCorres.Upstream.Struct
