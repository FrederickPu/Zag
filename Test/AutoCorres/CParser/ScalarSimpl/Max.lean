import Test.AutoCorres.CParser.ScalarSimpl.MaxResolution

namespace Zag.Test.AutoCorres.CParser.ScalarSimpl

open Zag.Lang.AutoCorres.CParser
open Zag.Lang.AutoCorres.CParser.ScalarSimpl
open FixtureHelpers

private def expectedMax : Function :=
  { name := "max"
    returnType := u32
    parameters := [(1, u32), (2, u32)]
    locals := []
    body := .seq
      (.cond (.binary s32 u32 .lessEqual (.variable u32 1) (.variable u32 2))
        (.seq (.seq (.return u32 (.variable u32 2)) .skip) .skip) .skip)
      (.seq (.return u32 (.variable u32 1)) .skip) }

set_option maxRecDepth 100000 in
set_option maxHeartbeats 500000 in
theorem max_is_resolved_by_symbol_id : maxFunction = expectedMax := by
  native_decide

private def maxInitial (a b : Int) : State :=
  match maxFunction.enter [a, b] with
  | .ok state => state
  | .error _ => {}

private def maxResult (a b : Int) : State :=
  (maxInitial a b).resetReturn.returnValue u32
    (if u32.cast a ≤ u32.cast b then u32.cast b else u32.cast a)

private theorem max_read_one (a b : Int) :
    (maxInitial a b).resetReturn.read? 1 = some (u32.cast a) := by
  simp [maxInitial, max_is_resolved_by_symbol_id, expectedMax, Function.enter,
    State.resetReturn, State.read?, State.write]

private theorem max_read_two (a b : Int) :
    (maxInitial a b).resetReturn.read? 2 = some (u32.cast b) := by
  simp [maxInitial, max_is_resolved_by_symbol_id, expectedMax, Function.enter,
    State.resetReturn, State.read?, State.write]

theorem max_resolved_executes (a b : Int) :
    maxFunction.Exec (maxInitial a b) (.normal (maxResult a b)) := by
  apply Function.Exec.returned
  rw [max_is_resolved_by_symbol_id]
  by_cases ordered : u32.cast a ≤ u32.cast b
  · apply Stmt.Exec.seqReturned
    apply Stmt.Exec.condTrue (value := 1)
    · simp [Expr.eval, max_read_one, max_read_two, u32_cast_idempotent, ordered]
    · decide
    · apply Stmt.Exec.seqReturned
      apply Stmt.Exec.seqReturned
      apply Stmt.Exec.ret
      simpa [Expr.eval, maxResult, ordered] using max_read_two a b
  · apply Stmt.Exec.seqNormal
    · apply Stmt.Exec.condFalse
      · simp [Expr.eval, max_read_one, max_read_two, u32_cast_idempotent, ordered]
      · exact .skip
    · apply Stmt.Exec.seqReturned
      apply Stmt.Exec.ret
      simpa [Expr.eval, maxResult, ordered] using max_read_one a b

theorem max_generated_simpl_executes (a b : Int) :
    Zag.Lang.AutoCorres.Simpl.Exec emptyEnvironment maxFunction.command
      (.normal (maxInitial a b)) (.normal (maxResult a b)) :=
  maxFunction.command_correct _ _ (max_resolved_executes a b)

def maxEmitsSupported :
    Zag.Lang.AutoCorres.SimplConv.Kernel.Supported maxFunction.command :=
  maxCertificate.supported

theorem max_finite_execution_equivalence :
    Raw.Equivalent maxCertificate.program "max" maxCertificate.functionInfo
      maxCertificate.rawBody maxFunction.returnType maxFunction.command :=
  maxCertificate.resolution.compose

theorem max_finite_execution_iff (state : State) (outcome : Raw.FunctionOutcome) :
    Raw.FunctionExec maxCertificate.program "max" maxCertificate.functionInfo
        maxCertificate.rawBody maxFunction.returnType state outcome ↔
      Zag.Lang.AutoCorres.Simpl.Exec emptyEnvironment maxFunction.command (.normal state)
        (Raw.embedOutcome outcome) :=
  maxCertificate.finite_iff state outcome

theorem max_raw_fixture_executes_then_branch :
    Raw.FunctionExec maxCertificate.program "max" maxCertificate.functionInfo
      maxCertificate.rawBody maxFunction.returnType (maxInitial 4 9)
        (.success (maxResult 4 9)) :=
  (max_finite_execution_iff (maxInitial 4 9) (.success (maxResult 4 9))).2 (by
    simpa [Raw.embedOutcome] using max_generated_simpl_executes 4 9)

theorem max_raw_then_branch_executes_in_simpl :
    Zag.Lang.AutoCorres.Simpl.Exec emptyEnvironment maxFunction.command
      (.normal (maxInitial 4 9)) (.normal (maxResult 4 9)) := by
  simpa [Raw.embedOutcome] using
    (max_finite_execution_iff (maxInitial 4 9) (.success (maxResult 4 9))).1
      max_raw_fixture_executes_then_branch

theorem max_raw_fixture_executes_else_branch :
    Raw.FunctionExec maxCertificate.program "max" maxCertificate.functionInfo
      maxCertificate.rawBody maxFunction.returnType (maxInitial 9 4)
        (.success (maxResult 9 4)) :=
  (max_finite_execution_iff (maxInitial 9 4) (.success (maxResult 9 4))).2 (by
    simpa [Raw.embedOutcome] using max_generated_simpl_executes 9 4)

theorem max_raw_else_branch_executes_in_simpl :
    Zag.Lang.AutoCorres.Simpl.Exec emptyEnvironment maxFunction.command
      (.normal (maxInitial 9 4)) (.normal (maxResult 9 4)) := by
  simpa [Raw.embedOutcome] using
    (max_finite_execution_iff (maxInitial 9 4) (.success (maxResult 9 4))).1
      max_raw_fixture_executes_else_branch

end Zag.Test.AutoCorres.CParser.ScalarSimpl
