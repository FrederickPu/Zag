import Test.AutoCorres.CParser.ScalarSimpl.PlusResolution

namespace Zag.Test.AutoCorres.CParser.ScalarSimpl

open Zag.Lang.AutoCorres.CParser
open Zag.Lang.AutoCorres.CParser.ScalarSimpl
open FixtureHelpers

private def expectedPlus : Function :=
  { name := "plus"
    returnType := u32
    parameters := [(1, u32), (2, u32)]
    locals := []
    body := .seq
      (.return u32 (.binary u32 u32 .add (.variable u32 1) (.variable u32 2)))
      .skip }

set_option maxRecDepth 100000 in
set_option maxHeartbeats 500000 in
theorem plus_is_resolved_by_symbol_id : plus = expectedPlus := by
  native_decide

def plusInitial (a b : Int) : State :=
  match plus.enter [a, b] with
  | .ok state => state
  | .error _ => {}

def plusResult (a b : Int) : State :=
  (plusInitial a b).resetReturn.returnValue u32
    (u32.cast (u32.cast a + u32.cast b))

private theorem plus_read_one (a b : Int) :
    (plusInitial a b).resetReturn.read? 1 = some (u32.cast a) := by
  simp [plusInitial, plus_is_resolved_by_symbol_id, expectedPlus, Function.enter,
    State.resetReturn, State.read?, State.write]

private theorem plus_read_two (a b : Int) :
    (plusInitial a b).resetReturn.read? 2 = some (u32.cast b) := by
  simp [plusInitial, plus_is_resolved_by_symbol_id, expectedPlus, Function.enter,
    State.resetReturn, State.read?, State.write]

theorem plus_enter_eq (a b : Int) :
    plus.enter [a, b] = .ok (plusInitial a b) := by
  unfold plusInitial
  rw [plus_is_resolved_by_symbol_id]
  simp [expectedPlus, Function.enter]

private theorem plus_initial_read_one (a b : Int) :
    (plusInitial a b).read? 1 = some (u32.cast a) := by
  simp [plusInitial, plus_is_resolved_by_symbol_id, expectedPlus, Function.enter,
    State.read?, State.write]

private theorem plus_initial_read_two (a b : Int) :
    (plusInitial a b).read? 2 = some (u32.cast b) := by
  simp [plusInitial, plus_is_resolved_by_symbol_id, expectedPlus, Function.enter,
    State.read?, State.write]

theorem plus_add_expression_eval (a b : Int) :
    (Expr.binary u32 u32 .add (.variable u32 1) (.variable u32 2)).eval
        (plusInitial a b) =
      some (u32.cast (u32.cast a + u32.cast b)) := by
  simp only [Expr.eval]
  rw [plus_initial_read_one, plus_initial_read_two]
  simp [u32_checked, u32_cast_idempotent]

theorem plus_resolved_executes (a b : Int) :
    plus.Exec (plusInitial a b) (.normal (plusResult a b)) := by
  apply Function.Exec.returned
  rw [plus_is_resolved_by_symbol_id]
  apply Stmt.Exec.seqReturned
  apply Stmt.Exec.ret (result := u32.cast (u32.cast a + u32.cast b))
  simp [Expr.eval, plus_read_one, plus_read_two, u32_checked, u32_cast_idempotent]

theorem plus_generated_simpl_executes (a b : Int) :
    Zag.Lang.AutoCorres.Simpl.Exec emptyEnvironment plus.command
      (.normal (plusInitial a b)) (.normal (plusResult a b)) :=
  plus.command_correct _ _ (plus_resolved_executes a b)

def plusEmitsSupported :
    Zag.Lang.AutoCorres.SimplConv.Kernel.Supported plus.command :=
  plusCertificate.supported

theorem plus_finite_execution_equivalence :
    Raw.Equivalent plusCertificate.program "plus" plusCertificate.functionInfo
      plusCertificate.rawBody plus.returnType plus.command :=
  plusCertificate.resolution.compose

theorem plus_finite_execution_iff (state : State) (outcome : Raw.FunctionOutcome) :
    Raw.FunctionExec plusCertificate.program "plus" plusCertificate.functionInfo
        plusCertificate.rawBody plus.returnType state outcome ↔
      Zag.Lang.AutoCorres.Simpl.Exec emptyEnvironment plus.command (.normal state)
        (Raw.embedOutcome outcome) :=
  plusCertificate.finite_iff state outcome

theorem plus_raw_fixture_executes :
    Raw.FunctionExec plusCertificate.program "plus" plusCertificate.functionInfo
      plusCertificate.rawBody plus.returnType (plusInitial 4 5) (.success (plusResult 4 5)) :=
  (plus_finite_execution_iff (plusInitial 4 5) (.success (plusResult 4 5))).2 (by
    simpa [Raw.embedOutcome] using plus_generated_simpl_executes 4 5)

theorem plus_raw_fixture_executes_in_simpl :
    Zag.Lang.AutoCorres.Simpl.Exec emptyEnvironment plus.command
      (.normal (plusInitial 4 5)) (.normal (plusResult 4 5)) := by
  simpa [Raw.embedOutcome] using
    (plus_finite_execution_iff (plusInitial 4 5) (.success (plusResult 4 5))).1
      plus_raw_fixture_executes

private def isArityError (expected actual : Nat) :
    Except Zag.Lang.AutoCorres.CParser.ScalarSimpl.Error State → Bool
  | .error (.argumentCountMismatch "plus" foundExpected foundActual) =>
      foundExpected = expected && foundActual = actual
  | _ => false

example : isArityError 2 1 (plus.enter [1]) := by native_decide

example : isArityError 2 3 (plus.enter [1, 2, 3]) := by native_decide

example : (plus.enter [4, 5] (State.write {} 1 u32 99)).toOption.map (·.read? 1) =
    some (some 4) := by
  native_decide

end Zag.Test.AutoCorres.CParser.ScalarSimpl
