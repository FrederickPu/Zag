import Lang.AutoCorres.CParser.MemorySimpl
import Test.AutoCorres.CParser.EmbeddedFixtures

/-! # Certified memory lowering of embedded C fixtures -/

namespace Zag.Test.AutoCorres.CParser.MemorySimpl

set_option maxRecDepth 100000
set_option maxHeartbeats 500000

open Zag.Lang.AutoCorres.CParser
open Zag.Lang.AutoCorres.CParser.ProgramAnalysis
open Zag.Lang.AutoCorres.CParser.MemoryLayout
open Zag.Lang.AutoCorres.CParser.MemoryModel
open Zag.Lang.AutoCorres.CParser.MemorySimpl

private abbrev ResolvedError := Zag.Lang.AutoCorres.CParser.MemorySimpl.Error
private abbrev ResolvedExpr := Zag.Lang.AutoCorres.CParser.MemorySimpl.Expr
private abbrev ResolvedFunction := Zag.Lang.AutoCorres.CParser.MemorySimpl.Function

private theorem option_eq_some_get (value : Option α) (isSome : value.isSome) :
    value = some (value.get isSome) := by
  cases value with
  | none => simp at isSome
  | some value => rfl

private theorem except_toOption_isSome_of_isOk (value : Except ε α) (isOk : value.isOk) :
    value.toOption.isSome := by
  cases value with
  | error _ =>
      exact Bool.noConfusion isOk
  | ok _ => rfl

private theorem function_exec_of_eq {program : ProgramAnalysis.Program}
    (layout : MemoryLayout.Certificate program) {actual expected : ResolvedFunction}
    {state : State} {outcome : Zag.Lang.AutoCorres.Simpl.XState State Unit}
    (equality : actual = expected) (execution : expected.Exec layout state outcome) :
    actual.Exec layout state outcome := by
  cases equality
  exact execution

private def globalBarResult :=
  certifyFrontend .arm EmbeddedFixtures.files "proof-tests/global_array_update.c" "bar"

private def globalBar2Result :=
  certifyFrontend .arm EmbeddedFixtures.files "proof-tests/global_array_update.c" "bar2"

private def heapBarResult :=
  certifyFrontend .arm EmbeddedFixtures.files "parse-tests/heap_lift_array.c" "bar"

private def heapBazResult :=
  certifyFrontend .arm EmbeddedFixtures.files "parse-tests/heap_lift_array.c" "baz"

theorem embedded_functions_certify :
    globalBarResult.isOk && globalBar2Result.isOk && heapBarResult.isOk := by
  native_decide

private theorem globalBarResult_isOk : globalBarResult.isOk := by
  have h := embedded_functions_certify
  simp only [Bool.and_eq_true] at h ⊢
  exact h.1.1

private theorem globalBar2Result_isOk : globalBar2Result.isOk := by
  have h := embedded_functions_certify
  simp only [Bool.and_eq_true] at h ⊢
  exact h.1.2

private theorem heapBarResult_isOk : heapBarResult.isOk := by
  have h := embedded_functions_certify
  simp only [Bool.and_eq_true] at h ⊢
  exact h.2

private def globalBar : Certified .arm EmbeddedFixtures.files
    "proof-tests/global_array_update.c" "bar" :=
  globalBarResult.toOption.get
    (except_toOption_isSome_of_isOk globalBarResult globalBarResult_isOk)

private def globalBar2 : Certified .arm EmbeddedFixtures.files
    "proof-tests/global_array_update.c" "bar2" :=
  globalBar2Result.toOption.get
    (except_toOption_isSome_of_isOk globalBar2Result globalBar2Result_isOk)

private def heapBar : Certified .arm EmbeddedFixtures.files
    "parse-tests/heap_lift_array.c" "bar" :=
  heapBarResult.toOption.get
    (except_toOption_isSome_of_isOk heapBarResult heapBarResult_isOk)

def globalBarSupported :
    Zag.Lang.AutoCorres.SimplConv.Kernel.Supported
      (globalBar.function.command globalBar.certificate.layout) :=
  globalBar.certificate.supported

def globalBar2Supported :
    Zag.Lang.AutoCorres.SimplConv.Kernel.Supported
      (globalBar2.function.command globalBar2.certificate.layout) :=
  globalBar2.certificate.supported

def heapBarSupported :
    Zag.Lang.AutoCorres.SimplConv.Kernel.Supported
      (heapBar.function.command heapBar.certificate.layout) :=
  heapBar.certificate.supported

theorem global_bar_finite_iff (state : State) (outcome : Raw.FunctionOutcome) :
    Raw.FunctionExec globalBar.certificate.layout "bar" globalBar.certificate.functionInfo
        globalBar.certificate.rawBody state outcome ↔
      Zag.Lang.AutoCorres.Simpl.Exec emptyEnvironment
        (globalBar.function.command globalBar.certificate.layout) (.normal state)
        (Raw.embedOutcome outcome) :=
  globalBar.certificate.finite_iff state outcome

private def globalFooSymbol :=
  globalBar.certificate.program.symbols.find? (·.sourceName = "foo")

private theorem hasGlobalFoo : globalFooSymbol.isSome := by native_decide

private def globalFooId : Nat := (globalFooSymbol.get hasGlobalFoo).id

private def globalFoo : Pointer :=
  (Pointer.ofGlobal? globalBar.certificate.layout.layout globalFooId).get (by native_decide)

private def globalFoo3 : Pointer :=
  (globalFoo.add? globalBar.certificate.layout.layout 4 3).get (by native_decide)

private def expectedGlobalBar : Function := {
  name := "bar"
  returnType := .void
  parameters := []
  locals := []
  body := .seq
    (.assign
      (.index (.signed .int) (.signed .int)
        (.globalArray (.array (.signed .int) (some 1024)) globalFoo)
        (.literal (.signed .int) 3))
      (.literal (.signed .int) 42))
    .skip }

private def expectedGlobalBar2 : Function := {
  name := "bar2"
  returnType := .ptr (.signed .int)
  parameters := []
  locals := []
  body := .seq
    (.return (.ptr (.signed .int)) (some
      (.address (.ptr (.signed .int))
        (.index (.signed .int) (.signed .int)
          (.globalArray (.array (.signed .int) (some 1024)) globalFoo)
          (.literal (.signed .int) 3)))))
    .skip }

theorem global_bar_is_the_exact_resolved_body :
    globalBar.function = expectedGlobalBar := by native_decide

theorem global_bar2_is_the_exact_resolved_body :
    globalBar2.function = expectedGlobalBar2 := by native_decide

private def globalBarInitial : State := globalBar.certificate.initialState

theorem global_bar_initial_state_is_certified_image :
    globalBarInitial.heap = globalBar.certificate.image.bytes := rfl

private def globalBarLocation : LValue :=
  .index (.signed .int) (.signed .int)
    (.globalArray (.array (.signed .int) (some 1024)) globalFoo)
    (.literal (.signed .int) 3)

private def globalBarValue : ResolvedExpr := .literal (.signed .int) 42

private def globalBarStore? : Option ByteHeap :=
  storeInteger? globalBar.certificate.layout (.signed .int) globalFoo3 42
    globalBarInitial.heap

private theorem globalBarStoreSome : globalBarStore?.isSome := by native_decide

private def globalBarExpectedHeap : ByteHeap := globalBarStore?.get globalBarStoreSome

private theorem globalBarStoreEq : globalBarStore? = some globalBarExpectedHeap :=
  option_eq_some_get globalBarStore? globalBarStoreSome

private def globalBarAfterStore : State :=
  globalBarInitial.withHeap globalBarExpectedHeap

private def globalBarFinal : State :=
  globalBarAfterStore.returnValue Zag.Lang.AutoCorres.CParser.MemorySimpl.Value.void

private theorem globalBarTarget : globalBar.certificate.program.target = .arm := by
  native_decide

private theorem globalBarValueEval :
    globalBarValue.eval globalBar.certificate.layout globalBarInitial =
      some (Zag.Lang.AutoCorres.CParser.MemorySimpl.Value.integer 42) := by
  native_decide

private theorem globalBarLocationEval :
    globalBarLocation.eval globalBar.certificate.layout globalBarInitial =
      some (.memory globalFoo3 (.signed .int)) := by
  native_decide

private theorem globalBarCast42 :
    castValue .arm (.signed .int)
        (Zag.Lang.AutoCorres.CParser.MemorySimpl.Value.integer 42) =
      some (Zag.Lang.AutoCorres.CParser.MemorySimpl.Value.integer 42) := by
  native_decide

private theorem globalBarAssignEq :
    Stmt.assign? globalBar.certificate.layout globalBarLocation globalBarValue globalBarInitial =
      some globalBarAfterStore := by
  have storeEq :
      storeInteger? globalBar.certificate.layout (.signed .int) globalFoo3 42
          globalBarInitial.heap = some globalBarExpectedHeap :=
    globalBarStoreEq
  simp [Stmt.assign?, globalBarValueEval, globalBarLocationEval, writeLocation,
    globalBarTarget, globalBarCast42, storeEq, globalBarAfterStore]

theorem global_bar_resolved_executes_exactly :
    globalBar.function.Exec globalBar.certificate.layout globalBarInitial
      (.normal globalBarFinal) := by
  apply function_exec_of_eq globalBar.certificate.layout
    global_bar_is_the_exact_resolved_body
  apply Function.Exec.fellOffVoid rfl
  apply Stmt.Exec.seqNormal
  · simpa [expectedGlobalBar, globalBarLocation, globalBarValue, globalBarInitial,
      Certificate.initialState, State.resetReturn] using Stmt.Exec.assign globalBarAssignEq
  · exact .skip

theorem global_bar_simpl_executes_exactly :
    Zag.Lang.AutoCorres.Simpl.Exec emptyEnvironment
      (globalBar.function.command globalBar.certificate.layout) (.normal globalBarInitial)
      (.normal globalBarFinal) :=
  globalBar.function.command_correct globalBar.certificate.layout
    global_bar_resolved_executes_exactly

theorem global_bar_raw_executes_exactly :
    Raw.FunctionExec globalBar.certificate.layout "bar" globalBar.certificate.functionInfo
      globalBar.certificate.rawBody globalBarInitial (.success globalBarFinal) :=
  (globalBar.certificate.finite_iff globalBarInitial (.success globalBarFinal)).2 (by
    simpa [Raw.embedOutcome] using global_bar_simpl_executes_exactly)

theorem global_bar_full_final_state :
    globalBarFinal = globalBarAfterStore.returnValue .void ∧
      globalBarFinal.heap = globalBarExpectedHeap ∧
      globalBarFinal.result = .void ∧ globalBarFinal.returned = true ∧
      globalBarFinal.value = globalBarInitial.value ∧
      globalBarFinal.initialized = globalBarInitial.initialized ∧
      loadInteger? globalBar.certificate.layout (.signed .int) globalFoo3
        globalBarFinal.heap = some 42 ∧
      globalBarFinal.heap (BitVec.ofNat 32 4096) =
        globalBarInitial.heap (BitVec.ofNat 32 4096) ∧
      globalBarFinal.heap (BitVec.ofNat 32 4112) =
        globalBarInitial.heap (BitVec.ofNat 32 4112) := by
  constructor
  · rfl
  · simp only [globalBarFinal, globalBarAfterStore, State.returnValue, State.withHeap]
    native_decide

private def globalBar2Initial : State := globalBar2.certificate.initialState

theorem global_bar2_initial_state_is_certified_image :
    globalBar2Initial.heap = globalBar2.certificate.image.bytes := rfl

private def globalBar2ReturnedPointer : Pointer := globalFoo3

private def globalBar2Final : State :=
  globalBar2Initial.returnValue
    (Zag.Lang.AutoCorres.CParser.MemorySimpl.Value.pointer globalBar2ReturnedPointer)

private def globalBar2Expression : ResolvedExpr :=
  .address (.ptr (.signed .int))
    (.index (.signed .int) (.signed .int)
      (.globalArray (.array (.signed .int) (some 1024)) globalFoo)
      (.literal (.signed .int) 3))

private theorem globalBar2ExpressionEval :
    globalBar2Expression.eval globalBar2.certificate.layout globalBar2Initial =
      some (Zag.Lang.AutoCorres.CParser.MemorySimpl.Value.pointer globalBar2ReturnedPointer) := by
  native_decide

private theorem globalBar2ReturnEq :
    Stmt.return? globalBar2.certificate.layout (.ptr (.signed .int))
      (some globalBar2Expression) globalBar2Initial = some globalBar2Final := by
  simp [Stmt.return?, globalBar2ExpressionEval, castValue, CType.ptrType, globalBar2Final]

theorem global_bar2_resolved_executes_exactly :
    globalBar2.function.Exec globalBar2.certificate.layout globalBar2Initial
      (.normal globalBar2Final) := by
  apply function_exec_of_eq globalBar2.certificate.layout
    global_bar2_is_the_exact_resolved_body
  apply Function.Exec.returned
  apply Stmt.Exec.seqReturned
  apply Stmt.Exec.ret
  simpa [expectedGlobalBar2, globalBar2Expression, globalBar2Initial,
    Certificate.initialState, State.resetReturn] using globalBar2ReturnEq

theorem global_bar2_simpl_executes_exactly :
    Zag.Lang.AutoCorres.Simpl.Exec emptyEnvironment
      (globalBar2.function.command globalBar2.certificate.layout) (.normal globalBar2Initial)
      (.normal globalBar2Final) :=
  globalBar2.function.command_correct globalBar2.certificate.layout
    global_bar2_resolved_executes_exactly

theorem global_bar2_raw_executes_exactly :
    Raw.FunctionExec globalBar2.certificate.layout "bar2"
      globalBar2.certificate.functionInfo globalBar2.certificate.rawBody globalBar2Initial
      (.success globalBar2Final) :=
  (globalBar2.certificate.finite_iff globalBar2Initial (.success globalBar2Final)).2 (by
    simpa [Raw.embedOutcome] using global_bar2_simpl_executes_exactly)

theorem global_bar2_full_final_state :
    globalBar2ReturnedPointer =
        { address := BitVec.ofNat 32 4108, provenance := some globalFooId } ∧
      globalBar2Final.heap = globalBar2Initial.heap ∧
      globalBar2Final.result = .pointer globalBar2ReturnedPointer ∧
      globalBar2Final.returned = true ∧
      globalBar2Final.value = globalBar2Initial.value ∧
      globalBar2Final.initialized = globalBar2Initial.initialized ∧
      authorized globalBar2.certificate.layout (.signed .int) globalBar2ReturnedPointer := by
  simp only [globalBar2Final, State.returnValue]
  native_decide

private def heapFooSymbol :=
  heapBar.certificate.program.symbols.find? (·.sourceName = "foo")

private theorem hasHeapFoo : heapFooSymbol.isSome := by native_decide

private def heapFooId : Nat := (heapFooSymbol.get hasHeapFoo).id

private def heapFoo : Pointer :=
  (Pointer.ofGlobal? heapBar.certificate.layout.layout heapFooId).get (by native_decide)

private def heapFoo1 : Pointer :=
  (heapFoo.add? heapBar.certificate.layout.layout 4 1).get (by native_decide)

private def expectedHeapBar : Function := {
  name := "bar"
  returnType := .unsigned .int
  parameters := []
  locals := []
  body := .seq
    (.assign
      (.index (.unsigned .int) (.unsigned .int)
        (.globalArray (.array (.unsigned .int) (some 10)) heapFoo)
        (.literal (.signed .int) 1))
      (.literal (.signed .int) 42))
    (.seq
      (.return (.unsigned .int) (some
        (.load (.unsigned .int)
          (.index (.unsigned .int) (.unsigned .int)
            (.globalArray (.array (.unsigned .int) (some 10)) heapFoo)
            (.literal (.signed .int) 1)))))
      .skip) }

theorem heap_bar_is_the_exact_resolved_body :
    heapBar.function = expectedHeapBar := by native_decide

private def heapBarInitial : State := heapBar.certificate.initialState

theorem heap_bar_initial_state_is_certified_image :
    heapBarInitial.heap = heapBar.certificate.image.bytes := rfl

private def heapBarLocation : LValue :=
  .index (.unsigned .int) (.unsigned .int)
    (.globalArray (.array (.unsigned .int) (some 10)) heapFoo)
    (.literal (.signed .int) 1)

private def heapBarValue : ResolvedExpr := .literal (.signed .int) 42

private def heapBarStore? : Option ByteHeap :=
  storeInteger? heapBar.certificate.layout (.unsigned .int) heapFoo1 42 heapBarInitial.heap

private theorem heapBarStoreSome : heapBarStore?.isSome := by native_decide

private def heapBarExpectedHeap : ByteHeap := heapBarStore?.get heapBarStoreSome

private theorem heapBarStoreEq : heapBarStore? = some heapBarExpectedHeap :=
  option_eq_some_get heapBarStore? heapBarStoreSome

private def heapBarAfterStore : State := heapBarInitial.withHeap heapBarExpectedHeap

private def heapBarFinal : State := heapBarAfterStore.returnValue
  (Zag.Lang.AutoCorres.CParser.MemorySimpl.Value.integer 42)

private theorem heapBarTarget : heapBar.certificate.program.target = .arm := by
  native_decide

private theorem heapBarValueEval :
    heapBarValue.eval heapBar.certificate.layout heapBarInitial =
      some (Zag.Lang.AutoCorres.CParser.MemorySimpl.Value.integer 42) := by
  native_decide

private theorem heapBarLocationEval :
    heapBarLocation.eval heapBar.certificate.layout heapBarInitial =
      some (.memory heapFoo1 (.unsigned .int)) := by
  native_decide

private theorem heapBarCast42 :
    castValue .arm (.unsigned .int)
        (Zag.Lang.AutoCorres.CParser.MemorySimpl.Value.integer 42) =
      some (Zag.Lang.AutoCorres.CParser.MemorySimpl.Value.integer 42) := by
  native_decide

private theorem heapBarAssignEq :
    Stmt.assign? heapBar.certificate.layout heapBarLocation heapBarValue heapBarInitial =
      some heapBarAfterStore := by
  have storeEq :
      storeInteger? heapBar.certificate.layout (.unsigned .int) heapFoo1 42
          heapBarInitial.heap = some heapBarExpectedHeap :=
    heapBarStoreEq
  simp [Stmt.assign?, heapBarValueEval, heapBarLocationEval, writeLocation,
    heapBarTarget, heapBarCast42, storeEq, heapBarAfterStore]

private def heapBarReturnExpression : ResolvedExpr :=
  .load (.unsigned .int) heapBarLocation

private theorem heapBarReturnExpressionEval :
    heapBarReturnExpression.eval heapBar.certificate.layout heapBarAfterStore =
      some (Zag.Lang.AutoCorres.CParser.MemorySimpl.Value.integer 42) := by
  native_decide

private theorem heapBarReturnEq :
    Stmt.return? heapBar.certificate.layout (.unsigned .int)
      (some heapBarReturnExpression) heapBarAfterStore = some heapBarFinal := by
  simp [Stmt.return?, heapBarReturnExpressionEval, heapBarTarget, heapBarCast42, heapBarFinal]

theorem heap_bar_resolved_executes_exactly :
    heapBar.function.Exec heapBar.certificate.layout heapBarInitial (.normal heapBarFinal) := by
  apply function_exec_of_eq heapBar.certificate.layout heap_bar_is_the_exact_resolved_body
  apply Function.Exec.returned
  apply Stmt.Exec.seqNormal
  · simpa [expectedHeapBar, heapBarLocation, heapBarValue, heapBarInitial,
      Certificate.initialState, State.resetReturn] using Stmt.Exec.assign heapBarAssignEq
  · apply Stmt.Exec.seqReturned
    apply Stmt.Exec.ret
    simpa [expectedHeapBar, heapBarReturnExpression, heapBarLocation] using heapBarReturnEq

theorem heap_bar_simpl_executes_exactly :
    Zag.Lang.AutoCorres.Simpl.Exec emptyEnvironment
      (heapBar.function.command heapBar.certificate.layout) (.normal heapBarInitial)
      (.normal heapBarFinal) :=
  heapBar.function.command_correct heapBar.certificate.layout heap_bar_resolved_executes_exactly

theorem heap_bar_raw_executes_exactly :
    Raw.FunctionExec heapBar.certificate.layout "bar" heapBar.certificate.functionInfo
      heapBar.certificate.rawBody heapBarInitial (.success heapBarFinal) :=
  (heapBar.certificate.finite_iff heapBarInitial (.success heapBarFinal)).2 (by
    simpa [Raw.embedOutcome] using heap_bar_simpl_executes_exactly)

theorem heap_bar_full_final_state :
    heapBarFinal = heapBarAfterStore.returnValue (.integer 42) ∧
      heapBarFinal.heap = heapBarExpectedHeap ∧
      heapBarFinal.result = .integer 42 ∧ heapBarFinal.returned = true ∧
      heapBarFinal.value = heapBarInitial.value ∧
      heapBarFinal.initialized = heapBarInitial.initialized ∧
      loadInteger? heapBar.certificate.layout (.unsigned .int) heapFoo1
        heapBarFinal.heap = some 42 ∧
      heapBarFinal.heap (BitVec.ofNat 32 4096) =
        heapBarInitial.heap (BitVec.ofNat 32 4096) ∧
      heapBarFinal.heap (BitVec.ofNat 32 4104) =
        heapBarInitial.heap (BitVec.ofNat 32 4104) := by
  constructor
  · rfl
  · simp only [heapBarFinal, heapBarAfterStore, State.returnValue, State.withHeap]
    native_decide

private def isSubobjectBoundsError : Except ResolvedError α → Bool
  | .error (.unsupportedExpression _ message) =>
      message == "pointer indexing requires certified subobject bounds"
  | _ => false

theorem heap_baz_requires_subobject_bounds : isSubobjectBoundsError heapBazResult := by
  native_decide

private def operatorFiles : Preprocessor.FileMap := [{
  name := "operators.c"
  source := "int bitwise(void) { return 1 | 2; } int logical_and(void) { return 0 && 1; } int logical_or(void) { return 1 || 0; }" }]

private def isIntegerOperatorError : Except ResolvedError α → Bool
  | .error (.unsupportedExpression _ message) =>
      message == "integer operator is not implemented"
  | _ => false

theorem bitwise_and_short_circuit_operators_are_rejected :
    isIntegerOperatorError (certifyFrontend .arm operatorFiles "operators.c" "bitwise") &&
      isIntegerOperatorError
        (certifyFrontend .arm operatorFiles "operators.c" "logical_and") &&
      isIntegerOperatorError
        (certifyFrontend .arm operatorFiles "operators.c" "logical_or") := by
  native_decide

private def representationFiles : Preprocessor.FileMap := [{
  name := "representations.c"
  source := "int *cast_zero(void) { return (int *)0; } int *null_return(void) { return 0; }" }]

private def isCrossRepresentationCast : Except ResolvedError α → Bool
  | .error (.unsupportedExpression _ message) =>
      message == "cross-representation cast is not implemented"
  | _ => false

private def isCrossRepresentationReturn : Except ResolvedError α → Bool
  | .error (.unsupportedExpression _ message) =>
      message == "return crosses value representations"
  | _ => false

theorem cross_representation_cast_and_null_pointer_return_are_rejected :
    isCrossRepresentationCast
        (certifyFrontend .arm representationFiles "representations.c" "cast_zero") &&
      isCrossRepresentationReturn
        (certifyFrontend .arm representationFiles "representations.c" "null_return") := by
  native_decide

private def pointerMemoryFiles : Preprocessor.FileMap := [{
  name := "pointer-memory.c"
  source := "int *stored_pointer; int values[1]; void set_pointer(void) { stored_pointer = values; }" }]

private def isUnsupportedPointerMemory : Except ResolvedError α → Bool
  | .error (.unsupportedType _ (.ptr _)) => true
  | _ => false

theorem pointer_valued_memory_assignment_is_rejected :
    isUnsupportedPointerMemory
      (certifyFrontend .arm pointerMemoryFiles "pointer-memory.c" "set_pointer") := by
  native_decide

private def arbitraryPointerFiles : Preprocessor.FileMap := [{
  name := "arbitrary-pointer.c"
  source := "int arbitrary_index(int *pointer) { return pointer[0]; }" }]

theorem arbitrary_pointer_indexing_is_rejected :
    isSubobjectBoundsError
      (certifyFrontend .arm arbitraryPointerFiles "arbitrary-pointer.c" "arbitrary_index") := by
  native_decide

private def pointerBypassFiles : Preprocessor.FileMap := [{
  name := "pointer-bypass.c"
  source := "int pointer_add(int *pointer) { return *(pointer + 0); } int values[1]; int array_truth(void) { return !values; }" }]

private def isTopLevelBoundsError : Except ResolvedError α → Bool
  | .error (.unsupportedExpression _ message) =>
      message == "pointer arithmetic requires certified top-level array bounds"
  | _ => false

private def isLogicalNotRepresentationError : Except ResolvedError α → Bool
  | .error (.unsupportedExpression _ message) =>
      message == "logical not of non-integer value"
  | _ => false

theorem pointer_arithmetic_bypass_and_array_truth_are_rejected :
    isTopLevelBoundsError
        (certifyFrontend .arm pointerBypassFiles "pointer-bypass.c" "pointer_add") &&
      isLogicalNotRepresentationError
        (certifyFrontend .arm pointerBypassFiles "pointer-bypass.c" "array_truth") := by
  native_decide

private def implicitNullFiles : Preprocessor.FileMap := [{
  name := "implicit-null.c"
  source := "int *global_pointer; void assign_null(void) { global_pointer = 0; } int local_null(void) { int *pointer = 0; return 0; }" }]

private def isAssignmentRepresentationError : Except ResolvedError α → Bool
  | .error (.unsupportedExpression _ message) =>
      message == "assignment crosses value representations"
  | _ => false

private def isInitializerRepresentationError : Except ResolvedError α → Bool
  | .error (.unsupportedExpression _ message) =>
      message == "initializer crosses value representations"
  | _ => false

theorem implicit_null_assignment_and_initialization_are_rejected :
    isAssignmentRepresentationError
        (certifyFrontend .arm implicitNullFiles "implicit-null.c" "assign_null") &&
      isInitializerRepresentationError
        (certifyFrontend .arm implicitNullFiles "implicit-null.c" "local_null") := by
  native_decide

private def callFiles : Preprocessor.FileMap := [{
  name := "call.c"
  source := "int g[2]; int callee(void) { return g[0]; } int caller(void) { return callee(); }" }]

private def isDirectCall : Except ResolvedError α → Bool
  | .error (.directCall _) => true
  | _ => false

theorem direct_call_is_explicitly_rejected :
    isDirectCall (certifyFrontend .arm callFiles "call.c" "caller") := by
  native_decide

private def missingLayoutFiles : Preprocessor.FileMap := [{
  name := "missing-layout.c"
  source := "extern int missing; void set(void) { missing = 1; }" }]

private def isUnallocatedExternal : Except ResolvedError α → Bool
  | .error (.unallocatedExternal _ name) => name == "missing"
  | _ => false

theorem resolved_extern_without_storage_is_explicitly_unsupported :
    isUnallocatedExternal (certifyFrontend .arm missingLayoutFiles "missing-layout.c" "set") := by
  native_decide

private def stackAddressFiles : Preprocessor.FileMap := [{
  name := "stack-address.c"
  source := "int *bad(void) { int local = 3; return &local; }" }]

private def isUnsupportedStackAddress : Except ResolvedError α → Bool
  | .error (.localAddress _) => true
  | _ => false

theorem stack_pointer_without_layout_provenance_is_rejected :
    isUnsupportedStackAddress
      (certifyFrontend .arm stackAddressFiles "stack-address.c" "bad") := by
  native_decide

private def structFiles : Preprocessor.FileMap := [{
  name := "struct-memory.c"
  source := "struct pair { int left; unsigned right; }; struct pair pair; int scalar; int fields(void) { pair.left = 7; scalar = pair.left; return scalar; }" }]

theorem direct_global_scalar_and_struct_field_certify :
    (certifyFrontend .arm structFiles "struct-memory.c" "fields").isOk := by
  native_decide

private def controlFiles : Preprocessor.FileMap := [{
  name := "control-memory.c"
  source := "int values[2]; int flow(int x) { while (x) { if (x <= 1) values[0] = x; x = x - 1; } return values[0]; }" }]

theorem memory_sequence_if_and_while_certify :
    (certifyFrontend .arm controlFiles "control-memory.c" "flow").isOk := by
  native_decide

end Zag.Test.AutoCorres.CParser.MemorySimpl
