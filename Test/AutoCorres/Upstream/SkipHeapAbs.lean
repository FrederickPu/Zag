import Lang.AutoCorres.CParser.PhasePipeline
import Test.AutoCorres.CParser.EmbeddedFixtures

/-!
# Complete `skip_heap_abs` proof test

This runs the exact embedded `skip_heap_abs.c` fixture with the upstream
`skip_heap_abs` option and checks the generated per-file phase table.
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

abbrev Files := EmbeddedFixtures.files

def entry : String := "proof-tests/skip_heap_abs.c"
def functionName : String := "f"
def options : Options := { skipHeapAbs := true }

private theorem except_toOption_isSome_of_isOk (value : Except ε α) (isOk : value.isOk) :
    value.toOption.isSome := by
  cases value with
  | error _ => exact Bool.noConfusion isOk
  | ok _ => rfl

private theorem option_eq_some_get (value : Option α) (isSome : value.isSome) :
    value = some (value.get isSome) := by
  cases value with
  | none => simp at isSome
  | some value => rfl

def frontendResult :=
  certifyFrontend .arm Files entry functionName

theorem fixture_certifies : frontendResult.isOk := by
  native_decide

def fixture : Certified .arm Files entry functionName :=
  frontendResult.toOption.get
    (except_toOption_isSome_of_isOk frontendResult fixture_certifies)

theorem exact_fixture_analyzed :
    (Frontend.preprocessAndAnalyze .arm Files entry).program =
      some fixture.certificate.program :=
  fixture.certificate.analyzed

theorem exact_fixture_frontend_success :
    (Frontend.preprocessAndAnalyze .arm Files entry).isSuccess = true :=
  fixture.certificate.frontendSuccess

def callGraphResult := CallGraph.certify fixture.certificate.program

theorem call_graph_certifies : callGraphResult.isOk := by
  native_decide

def metadataResult := PhasePipeline.run options .arm Files entry

theorem generated_pipeline_succeeds : metadataResult.isOk := by
  native_decide

def metadata : Metadata :=
  metadataResult.toOption.get
    (except_toOption_isSome_of_isOk metadataResult generated_pipeline_succeeds)

theorem generated_function_metadata_exists :
    (metadata.lookupFunction entry functionName).isSome := by
  native_decide

/-- The substantive upstream assertion, observed from the generated phase table. -/
theorem heap_lift_metadata_absent :
    metadata.lookup entry functionName .heapLift = none := by
  native_decide

def heapLiftCertificate : Option PhaseEntry :=
  metadata.lookup entry functionName .heapLift

theorem heap_lift_certificate_absent : heapLiftCertificate = none :=
  heap_lift_metadata_absent

theorem later_phase_metadata_present :
    (metadata.lookup entry functionName .wordAbstract).isSome &&
      (metadata.lookup entry functionName .typeStrengthen).isSome := by
  native_decide

def simplCertificate :=
  ML.SimplConv.simplConv false emptyEnvironment fixture.certificate.supported

def lveResult := PhasePipeline.recognizeLve simplCertificate.target

theorem lve_result_succeeds : lveResult.isOk := by
  native_decide

def lveSupported : LocalVarExtract.Kernel.Supported stateModel simplCertificate.target :=
  lveResult.toOption.get
    (except_toOption_isSome_of_isOk lveResult lve_result_succeeds)

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

def callerState : State :=
  { heap := initialHeap, external := [externalObject] }

theorem caller_object_authorizes_access :
    externalObject.authorizes intType pointer = true := by
  native_decide

theorem caller_heap_contains_seven :
    loadExternalInteger? [externalObject] intType pointer initialHeap = some 7 := by
  native_decide

def enteredResult := fixture.function.enter [.pointer pointer] callerState

theorem entered_result_succeeds : enteredResult.isOk := by
  native_decide

def entered : State :=
  enteredResult.toOption.get
    (except_toOption_isSome_of_isOk enteredResult entered_result_succeeds)

def declaration : Stmt := fixture.function.body

private def initialized? : Option State :=
  Stmt.initialize? fixture.certificate.layout 2 intType
    (.load intType (.deref intType (.local (.ptr intType) 1))) entered.resetReturn

private theorem initialized_exists : initialized?.isSome := by native_decide

private def initialized : State := initialized?.get initialized_exists

private def assigned? : Option State :=
  Stmt.assign? fixture.certificate.layout
    (.deref intType (.local (.ptr intType) 1))
    (.integerBinary intType intType .plus (.local intType 2) (.literal intType 1)) initialized

private theorem assigned_exists : assigned?.isSome := by native_decide

private def assigned : State := assigned?.get assigned_exists

private def returned? : Option State :=
  Stmt.return? fixture.certificate.layout intType (some (.local intType 2)) assigned

private theorem returned_exists : returned?.isSome := by native_decide

def afterBody : State := returned?.get returned_exists

theorem generated_body_shape : fixture.function.body =
    .seq
      (.declare 2 intType
        (some (.load intType (.deref intType (.local (.ptr intType) 1)))))
      (.seq
        (.assign (.deref intType (.local (.ptr intType) 1))
          (.integerBinary intType intType .plus
            (.local intType 2) (.literal intType 1)))
        (.seq (.return intType (some (.local intType 2))) .skip)) := by
  native_decide

private theorem body_executes :
    Stmt.Exec fixture.certificate.layout fixture.function.body entered.resetReturn
      (.returned afterBody) := by
  rw [generated_body_shape]
  exact .seqNormal (.initialize (option_eq_some_get initialized? initialized_exists))
    (.seqNormal (.assign (option_eq_some_get assigned? assigned_exists))
      (.seqReturned (.ret (option_eq_some_get returned? returned_exists))))

theorem generated_function_executes :
    fixture.function.Exec fixture.certificate.layout entered (.normal afterBody) :=
  .returned body_executes

theorem endpoint_returns_old_value : afterBody.result = .integer 7 := by
  native_decide

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
