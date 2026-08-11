import Test.AutoCorres.CParser.ScalarSimpl.MultByAddInvariant
import Test.AutoCorres.CParser.ScalarSimpl.Plus2Termination

namespace Zag.Test.AutoCorres.CParser.ScalarSimpl

open Zag.Lang.AutoCorres.CParser.ScalarSimpl
open FixtureHelpers

def multByAddInitial (a b : MultByAddWord32) : State :=
  match multByAdd.enter [Int.ofNat a.toNat, Int.ofNat b.toNat] with
  | .ok state => state
  | .error _ => {}

def multByAddResult (a b : MultByAddWord32) : State :=
  let value := multByAddAccumulate b a.toNat 0
  (multByAddState 0 b value).returnValue u32 (u32.cast value)

theorem mult_by_add_local_initializer_state (a b : MultByAddWord32) :
    ((multByAddInitial a b).resetReturn.clear 3).write 3 u32 0 =
      multByAddState a.toNat b 0 := by
  simp [multByAddInitial, mult_by_add_is_resolved_body, expectedMultByAdd,
    Function.enter, multByAddState, State.resetReturn, State.clear, State.write]
  funext key
  by_cases key = 1 <;> by_cases key = 2 <;> by_cases key = 3 <;> simp_all

theorem mult_by_add_resolved_executes (a b : MultByAddWord32) :
    multByAdd.Exec (multByAddInitial a b) (.normal (multByAddResult a b)) := by
  apply Function.Exec.returned
  rw [mult_by_add_is_resolved_body]
  apply Stmt.Exec.seqNormal
  · apply Stmt.Exec.init (result := 0)
    simp [Expr.eval]
  · rw [mult_by_add_local_initializer_state]
    apply Stmt.Exec.seqNormal
    · exact multByAddLoop_exec a.toNat b 0 a.isLt
    · apply Stmt.Exec.seqReturned
      apply Stmt.Exec.ret
      simp [Expr.eval, multByAddState_read_result]

theorem mult_by_add_generated_simpl_executes (a b : MultByAddWord32) :
    Zag.Lang.AutoCorres.Simpl.Exec emptyEnvironment multByAdd.command
      (.normal (multByAddInitial a b)) (.normal (multByAddResult a b)) :=
  multByAdd.command_correct _ _ (mult_by_add_resolved_executes a b)

def multByAddEmitsSupported :
    Zag.Lang.AutoCorres.SimplConv.Kernel.Supported multByAdd.command :=
  multByAddCertificate.supported

theorem mult_by_add_finite_execution_equivalence :
    Raw.Equivalent multByAddCertificate.program "mult_by_add"
      multByAddCertificate.functionInfo multByAddCertificate.rawBody
      multByAdd.returnType multByAdd.command :=
  multByAddCertificate.resolution.compose

theorem mult_by_add_finite_execution_iff (state : State) (outcome : Raw.FunctionOutcome) :
    Raw.FunctionExec multByAddCertificate.program "mult_by_add"
        multByAddCertificate.functionInfo multByAddCertificate.rawBody
        multByAdd.returnType state outcome ↔
      Zag.Lang.AutoCorres.Simpl.Exec emptyEnvironment multByAdd.command (.normal state)
        (Raw.embedOutcome outcome) :=
  multByAddCertificate.finite_iff state outcome

theorem mult_by_add_raw_fixture_executes (a b : MultByAddWord32) :
    Raw.FunctionExec multByAddCertificate.program "mult_by_add"
      multByAddCertificate.functionInfo multByAddCertificate.rawBody multByAdd.returnType
      (multByAddInitial a b) (.success (multByAddResult a b)) :=
  (mult_by_add_finite_execution_iff (multByAddInitial a b)
    (.success (multByAddResult a b))).2 (by
      simpa [Raw.embedOutcome] using mult_by_add_generated_simpl_executes a b)

theorem mult_by_add_success_is_wrapping_product (a b : MultByAddWord32) :
    BitVec.ofInt 32 (multByAddResult a b).result = a * b := by
  simp only [multByAddResult, State.returnValue]
  rw [u32_cast_idempotent, bitvec_of_u32_cast,
    mult_by_add_accumulate_word]
  simp

/-- Upstream's SIMPL partial-correctness theorem at the exact fixture-generated command. -/
theorem mult_by_add_simpl_partial_correctness (a b : MultByAddWord32)
    (post : State)
    (execution : Zag.Lang.AutoCorres.Simpl.Exec emptyEnvironment multByAdd.command
      (.normal (multByAddInitial a b)) (.normal post)) :
    BitVec.ofInt 32 post.result = a * b := by
  have resolved := multByAdd.command_complete execution
  have equality := function_exec_deterministic multByAdd resolved
    (mult_by_add_resolved_executes a b)
  have postEq : post = multByAddResult a b := by simpa using equality
  rw [postEq]
  exact mult_by_add_success_is_wrapping_product a b

theorem mult_by_add_any_success_is_wrapping_product (a b : MultByAddWord32) (post : State)
    (execution : Raw.FunctionExec multByAddCertificate.program "mult_by_add"
      multByAddCertificate.functionInfo multByAddCertificate.rawBody multByAdd.returnType
      (multByAddInitial a b) (.success post)) :
    BitVec.ofInt 32 post.result = a * b := by
  apply mult_by_add_simpl_partial_correctness a b post
  exact (mult_by_add_finite_execution_iff (multByAddInitial a b) (.success post)).1
    execution

end Zag.Test.AutoCorres.CParser.ScalarSimpl
