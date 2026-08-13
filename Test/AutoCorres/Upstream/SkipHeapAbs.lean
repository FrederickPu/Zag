import Lang.AutoCorres.CParser.PhasePipeline
import Test.AutoCorres.CParser.EmbeddedFixtures

/-!
# Complete pinned `skip_heap_abs` proof test

Sources:

* [`skip_heap_abs.c`](https://github.com/seL4/l4v/blob/bc2599a59c43e673dca021b10b9841e9b8da4430/tools/autocorres/tests/proof-tests/skip_heap_abs.c)
* [`skip_heap_abs.thy`](https://github.com/seL4/l4v/blob/bc2599a59c43e673dca021b10b9841e9b8da4430/tools/autocorres/tests/proof-tests/skip_heap_abs.thy)
-/

namespace Zag.Test.AutoCorres.Upstream.SkipHeapAbs

open Zag.Lang.AutoCorres
open Zag.Lang.AutoCorres.CParser
open Zag.Lang.AutoCorres.CParser.ProgramAnalysis
open Zag.Lang.AutoCorres.CParser.MemoryModel
open Zag.Lang.AutoCorres.CParser.MemorySimpl
open Zag.Lang.AutoCorres.CParser.PhasePipeline
open Zag.Test.AutoCorres.CParser

set_option maxRecDepth 100000
set_option maxHeartbeats 800000

private theorem Option.eq_some_get (value : Option α) (success : value.isSome) :
    value = some (value.get success) := by
  cases value <;> simp_all

abbrev Files := EmbeddedFixtures.files
def entry := "proof-tests/skip_heap_abs.c"
def functionName := "f"
def options : Options := { skipHeapAbs := true }

run_refinement fixture from certifyFrontend .arm Files entry functionName
success_by native_decide

theorem exact_fixture_analyzed :
    (Frontend.preprocessAndAnalyze .arm Files entry).program = some fixture.certificate.program :=
  fixture.certificate.analyzed

theorem exact_fixture_frontend_success :
    (Frontend.preprocessAndAnalyze .arm Files entry).isSuccess = true :=
  fixture.certificate.frontendSuccess

theorem call_graph_certifies :
    (CallGraph.certify fixture.certificate.program).isOk := by native_decide

run_refinement metadata from PhasePipeline.run options .arm Files entry
success_by native_decide

theorem generated_function_metadata_exists :
    (metadata.lookupFunction entry functionName).isSome := by native_decide

/-- The pinned upstream assertion: `skip_heap_abs` omits HeapLift. -/
theorem heap_lift_metadata_absent :
    (metadata.lookupFunction entry functionName).isSome ∧
      metadata.lookup entry functionName .heapLift = none := by
  exact ⟨by native_decide, by native_decide⟩

theorem later_phase_metadata_present :
    (metadata.lookup entry functionName .wordAbstract).isSome &&
      (metadata.lookup entry functionName .typeStrengthen).isSome := by native_decide

def simplCertificate :=
  ML.SimplConv.simplConv false emptyEnvironment fixture.certificate.supported

run_refinement lveSupported from PhasePipeline.recognizeLve simplCertificate.target
success_by native_decide

noncomputable def translation : SkippedHeapTranslation fixture :=
  translateSkippedHeap fixture lveSupported

theorem simpl_corresponds :
    L1.L1Corres false emptyEnvironment translation.simpl.target.denote
      (fixture.function.command fixture.certificate.layout) :=
  translation.simpl.corres

theorem lve_corresponds :
    L2.L2Corres stateModel.projectGlobals stateModel.projectLocals
      stateModel.projectLocals (fun state => stateModel.projectLocals state = ())
      translation.nonLifted translation.simpl.target.denote :=
  translation.lve.corres ()

theorem word_abstract_corresponds :
    WordAbstract.corresTA (fun _ => True) id id
      translation.wordAbstracted translation.nonLifted :=
  translation.wordAbstractCorres

theorem type_strengthen_is_exact :
    L2.call translation.wordAbstracted = translation.strengthened :=
  translation.typeStrengthenExact

def intType : AnalyzedCType := .signed .int
def pointer : Pointer := { address := BitVec.ofNat 32 4096, provenance := some 100 }
def externalObject : ExternalObject :=
  { provenance := 100, base := 4096, size := 4, type := intType }
def initialHeap : ByteHeap :=
  (writeBytes? zeroHeap 4096 (encodeIntegerLE 4 7)).getD zeroHeap
def callerState : State := { heap := initialHeap, external := [externalObject] }

theorem caller_object_authorizes_access :
    externalObject.authorizes intType pointer = true := by native_decide

theorem caller_heap_contains_seven :
    loadExternalInteger? [externalObject] intType pointer initialHeap = some 7 := by
  native_decide

run_refinement entered from fixture.function.enter [.pointer pointer] callerState
success_by native_decide

private def initialized : State :=
  (Stmt.initialize? fixture.certificate.layout 2 intType
    (.load intType (.deref intType (.local (.ptr intType) 1))) entered.resetReturn).get
      (by native_decide)

private def assigned : State :=
  (Stmt.assign? fixture.certificate.layout
    (.deref intType (.local (.ptr intType) 1))
    (.integerBinary intType intType .plus (.local intType 2) (.literal intType 1)) initialized).get
      (by native_decide)

def afterBody : State :=
  (Stmt.return? fixture.certificate.layout intType (some (.local intType 2)) assigned).get
    (by native_decide)

theorem generated_function_executes :
    fixture.function.Exec fixture.certificate.layout entered (.normal afterBody) := by
  apply Function.Exec.returned
  rw [show fixture.function.body =
    .seq
      (.declare 2 intType
        (some (.load intType (.deref intType (.local (.ptr intType) 1)))))
      (.seq
        (.assign (.deref intType (.local (.ptr intType) 1))
          (.integerBinary intType intType .plus (.local intType 2) (.literal intType 1)))
        (.seq (.return intType (some (.local intType 2))) .skip)) by native_decide]
  exact .seqNormal (.initialize (Option.eq_some_get _ (by native_decide)))
    (.seqNormal (.assign (Option.eq_some_get _ (by native_decide)))
      (.seqReturned (.ret (Option.eq_some_get _ (by native_decide)))))

theorem endpoint_returns_old_value : afterBody.result = .integer 7 := by native_decide

theorem endpoint_increments_pointed_memory :
    loadExternalInteger? [externalObject] intType pointer afterBody.heap = some 8 := by
  native_decide

theorem behavioral_endpoint :
    afterBody.result = .integer 7 ∧
      loadExternalInteger? [externalObject] intType pointer afterBody.heap = some 8 :=
  ⟨endpoint_returns_old_value, endpoint_increments_pointed_memory⟩

theorem simpl_endpoint_executes :
    Simpl.Exec emptyEnvironment (fixture.function.command fixture.certificate.layout)
      (.normal entered) (.normal afterBody) :=
  fixture.function.command_correct fixture.certificate.layout generated_function_executes

end Zag.Test.AutoCorres.Upstream.SkipHeapAbs
