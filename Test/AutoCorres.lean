import Lang.AutoCorres.CParser.Frontend
import Lang.AutoCorres.ML.autocorres
import Test.L1
import Test.L2
import Test.AutoCorres.Upstream.Plus
import Test.AutoCorres.Upstream.SkipHeapAbs
import Test.AutoCorres.Kernel.HeapLift
import Test.AutoCorres.Kernel.WordAbstract
import Test.AutoCorres.Kernel.WordAbstractOperations
import Test.AutoCorres.UnsignedPipeline
import Test.AutoCorres.CParser.ScalarSimpl
import Test.AutoCorres.CParser.MemorySimpl
import Test.AutoCorres.CParser.PhasePipeline.Basic

/-!
# Current AutoCorres pipeline integration tests

This root connects the pure C frontend to the proof-producing phase kernels.
The direct scalar slice now has a certified analyzed-C-to-SIMPL edge; broader C
and the remaining phase-local examples are not claimed as adjacent. Every
correspondence asserted below is an actual certificate between its stated
models.
-/

namespace Zag.Test.AutoCorres

open Zag.Lang.AutoCorres
open Zag.Lang.AutoCorres.CParser

private def source : String := "
unsigned plus(unsigned a, unsigned b) { return a + b; }
unsigned plus2(unsigned a, unsigned b) { return plus(a, b); }
"

def frontend := Frontend.analyzeSource .arm "plus.c" source

theorem frontend_succeeds : frontend.isSuccess := by native_decide

theorem frontend_discovers_functions :
    frontend.program.map (fun program =>
      ((program.symbolsNamed "plus").length,
       (program.symbolsNamed "plus2").length)) = some (1, 1) := by
  native_decide

theorem frontend_discovers_direct_call :
    frontend.program.map (fun program => program.calls.length) = some 1 := by
  native_decide

private def isPlusReturn : Statement → Bool
  | .stmt ⟨.returnStmt (some (.e ⟨.binOp .plus
      (.e ⟨.var left _, _⟩) (.e ⟨.var right _, _⟩), _⟩)), _⟩ =>
      left == "a" && right == "b"
  | _ => false

private def isPlus2Return : Statement → Bool
  | .stmt ⟨.returnFnCall (.e ⟨.var function _, _⟩)
      [(.e ⟨.var left _, _⟩), (.e ⟨.var right _, _⟩)], _⟩ =>
      function == "plus" && left == "a" && right == "b"
  | _ => false

private def hasExpectedBody (name : String) (bodyCheck : Statement → Bool) :
    ExternalDeclaration → Bool
  | .functionDefinition (_, function) _ _ _ body =>
      function.value == name &&
        match body.value with
        | [.statement statement] => bodyCheck statement
        | _ => false
  | .declaration _ => false

theorem frontend_preserves_function_bodies :
    frontend.program.map (fun program =>
      program.translationUnit.any (hasExpectedBody "plus" isPlusReturn) &&
      program.translationUnit.any (hasExpectedBody "plus2" isPlus2Return)) = some true := by
  native_decide

/-! ## Certified adjacent phases -/

theorem analyzed_c_to_simpl_certified
    (state : CParser.ScalarSimpl.State)
    (outcome : CParser.ScalarSimpl.Raw.FunctionOutcome) :
    CParser.ScalarSimpl.Raw.FunctionExec
        CParser.ScalarSimpl.plusCertificate.program "plus"
        CParser.ScalarSimpl.plusCertificate.functionInfo
        CParser.ScalarSimpl.plusCertificate.rawBody
        CParser.ScalarSimpl.plus.returnType state outcome ↔
      Simpl.Exec CParser.ScalarSimpl.emptyEnvironment
        CParser.ScalarSimpl.plus.command (.normal state)
        (CParser.ScalarSimpl.Raw.embedOutcome outcome) :=
  CParser.ScalarSimpl.plus_finite_execution_iff state outcome

theorem simpl_to_l1_certified :
    L1.L1Corres false
      Upstream.Plus.SimplConv.env
      Upstream.Plus.SimplConv.certificate.target.denote
      Upstream.Plus.SimplConv.source :=
  Upstream.Plus.SimplConv.manual_source_corres

theorem simpl_target_executes_addition :
    (Except.ok (), Upstream.Plus.SimplConv.update
      Upstream.Plus.SimplConv.initial) ∈
      (Upstream.Plus.SimplConv.certificate.target.denote
        Upstream.Plus.SimplConv.initial).results :=
  Upstream.Plus.SimplConv.target_runs

theorem l1_closed_ssa_is_exact :
    cast (by simp only [SSABridge.outcomeTy_type])
      (Zag.Lang.SSA.SSAExpr.evalM? (L1.toSSA Zag.Test.L1.caughtThrow).ctx []
        SSABridge.outcomeTy (L1.toSSA Zag.Test.L1.caughtThrow).expr) =
      some (SSABridge.suspend Zag.Test.L1.caughtThrow) :=
  Zag.Test.L1.closed_ssa_bridge_eval_exact

theorem l1_to_l2_certified :
    Zag.Lang.AutoCorres.ML.LocalVarExtract.Extracts
      Upstream.Plus.LocalVarExtract.model
      Upstream.Plus.LocalVarExtract.certificate.target
      Upstream.Plus.LocalVarExtract.source :=
  Upstream.Plus.LocalVarExtract.manual_source_extracts

theorem l2_target_executes_local_update :
    (Except.ok
        { Upstream.Plus.LocalVarExtract.initial with
          result := BitVec.ofNat 32 7 }, ()) ∈
      (Upstream.Plus.LocalVarExtract.certificate.target.denote
        Upstream.Plus.LocalVarExtract.initial ()).results :=
  Upstream.Plus.LocalVarExtract.target_returns_updated_locals

theorem l2_closed_ssa_is_exact :
    cast (by simp only [SSABridge.outcomeTy_type])
        (Zag.Lang.SSA.SSAExpr.evalM?
          (L2.toSSA (Zag.Test.L2.catchCertificate.target.denote
            Zag.Test.L2.initialLocals)).ctx []
          SSABridge.outcomeTy
          (L2.toSSA (Zag.Test.L2.catchCertificate.target.denote
            Zag.Test.L2.initialLocals)).expr) =
      some (SSABridge.suspend
        (Zag.Test.L2.catchCertificate.target.denote Zag.Test.L2.initialLocals)) :=
  Zag.Test.L2.l2_closed_ssa_evaluates_exactly

theorem heap_lift_is_certified :
    Zag.Lang.AutoCorres.HeapLift.L2Tcorres
      Kernel.HeapLift.stateMap
      Kernel.HeapLift.certificate.target.denote
      Kernel.HeapLift.source.denote :=
  Kernel.HeapLift.certified

theorem heap_lift_guard_rejects_invalid :
    (Kernel.HeapLift.certificate.target.denote
      { cell := 7, valid := false }).failed :=
  Kernel.HeapLift.target_fails_when_invalid

theorem word_abstract_is_certified (argument : BitVec 32) :
    Zag.Lang.AutoCorres.WordAbstract.corresTA (fun _ => True)
      (Zag.Lang.AutoCorres.WordAbstract.Kernel.typeMap
        Kernel.WordAbstract.Word).abstract
      (Zag.Lang.AutoCorres.WordAbstract.Kernel.typeMap .unit).abstract
      (Kernel.WordAbstract.certificate.target.denote argument.toNat)
      (Kernel.WordAbstract.source.denote argument) :=
  Kernel.WordAbstract.certified argument

theorem word_abstract_overflow_is_guarded :
    (Kernel.WordAbstract.certificate.target.denote 4294967295
      (BitVec.ofNat 32 1)).failed :=
  Kernel.WordAbstract.target_fails_on_overflow

theorem type_strengthen_is_exact (arguments : BitVec 32 × BitVec 32) :
    Upstream.Plus.TypeStrengthen.source.denote arguments =
      Zag.Lang.AutoCorres.TypeStrengthen.embed .pure
        (Upstream.Plus.TypeStrengthen.certificate arguments).target.denote :=
  Upstream.Plus.TypeStrengthen.manual_phase_exact arguments

theorem skip_heap_abs_target_updates_state :
    Zag.Lang.AutoCorres.CParser.MemoryModel.loadExternalInteger?
      [Upstream.SkipHeapAbs.externalObject] Upstream.SkipHeapAbs.intType
      Upstream.SkipHeapAbs.pointer Upstream.SkipHeapAbs.afterBody.heap = some 8 :=
  Upstream.SkipHeapAbs.endpoint_increments_pointed_memory

end Zag.Test.AutoCorres
