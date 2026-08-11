import Test.AutoCorres.CParser.ScalarSimpl.PlusCertificate

namespace Zag.Test.AutoCorres.CParser.ScalarSimpl

open Zag.Lang.AutoCorres.CParser
open Zag.Lang.AutoCorres.CParser.ScalarSimpl

private def plusProgram : ProgramAnalysis.Program := plusCertificate.program

set_option maxRecDepth 100000 in
set_option maxHeartbeats 500000 in
theorem plus_fixture_resolves : (resolveIR plusProgram "plus").isOk := by native_decide

private def plusErasedTranslationUnit : ProgramAnalysis.Program :=
  { plusProgram with translationUnit := [] }

private def plusErasedSymbols : ProgramAnalysis.Program :=
  { plusProgram with symbols := [] }

private theorem plusTranslationUnitIsNonempty : plusCertificate.program.translationUnit ≠ [] := by
  native_decide

private theorem plusSymbolsAreNonempty : plusCertificate.program.symbols ≠ [] := by
  native_decide

theorem erased_translation_unit_has_no_frontend_provenance :
    ¬CertifiedFrontend.analyze .arm EmbeddedFixtures.files "examples/plus.c" "plus" =
      .ok plusErasedTranslationUnit := by
  intro equality
  rw [plusCertificate.analyzed] at equality
  have same := Except.ok.inj equality
  have observed := congrArg (fun program => program.translationUnit) same
  exact plusTranslationUnitIsNonempty (by simpa [plusErasedTranslationUnit] using observed)

theorem erased_symbol_table_has_no_frontend_provenance :
    ¬CertifiedFrontend.analyze .arm EmbeddedFixtures.files "examples/plus.c" "plus" =
      .ok plusErasedSymbols := by
  intro equality
  rw [plusCertificate.analyzed] at equality
  have same := Except.ok.inj equality
  have observed := congrArg (fun program => program.symbols) same
  exact plusSymbolsAreNonempty (by simpa [plusErasedSymbols] using observed)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 500000 in
theorem plus_exact_resolution : (resolveFunction plusProgram "plus").toOption = some plus :=
  by native_decide

end Zag.Test.AutoCorres.CParser.ScalarSimpl
