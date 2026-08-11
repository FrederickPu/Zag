import Test.AutoCorres.CParser.ScalarSimpl.Plus2Correctness

namespace Zag.Test.AutoCorres.CParser.ScalarSimpl

open Zag.Lang.AutoCorres.CParser.ScalarSimpl
open FixtureHelpers

theorem stmt_exec_deterministic
    (first : Stmt.Exec statement state firstOutcome)
    (second : Stmt.Exec statement state secondOutcome) :
    firstOutcome = secondOutcome := by
  induction first generalizing secondOutcome with
  | skip => cases second; rfl
  | seqNormal first rest firstIH restIH =>
      cases second with
      | seqNormal otherFirst otherRest =>
          have sameMiddle := firstIH otherFirst
          cases sameMiddle
          exact restIH otherRest
      | seqReturned otherFirst => cases firstIH otherFirst
      | seqFault otherFirst => cases firstIH otherFirst
  | seqReturned first firstIH =>
      cases second with
      | seqNormal otherFirst _ => cases firstIH otherFirst
      | seqReturned otherFirst => cases firstIH otherFirst; rfl
      | seqFault otherFirst => cases firstIH otherFirst
  | seqFault first firstIH =>
      cases second with
      | seqNormal otherFirst _ => cases firstIH otherFirst
      | seqReturned otherFirst => cases firstIH otherFirst
      | seqFault otherFirst => cases firstIH otherFirst; rfl
  | assign id type value evaluation =>
      cases second with
      | assign _ _ _ other => rw [evaluation] at other; cases other; rfl
      | assignFault _ _ _ other => rw [evaluation] at other; cases other
  | assignFault id type value evaluation =>
      cases second with
      | assign _ _ _ other => rw [evaluation] at other; cases other
      | assignFault => rfl
  | declare => cases second; rfl
  | init id type value evaluation =>
      cases second with
      | init _ _ _ other => rw [evaluation] at other; cases other; rfl
      | initFault _ _ _ other => rw [evaluation] at other; cases other
  | initFault id type value evaluation =>
      cases second with
      | init _ _ _ other => rw [evaluation] at other; cases other
      | initFault => rfl
  | ret evaluation =>
      cases second with
      | ret other => rw [evaluation] at other; cases other; rfl
      | retFault other => rw [evaluation] at other; cases other
  | retFault evaluation =>
      cases second with
      | ret other => rw [evaluation] at other; cases other
      | retFault => rfl
  | condTrue evaluation nonzero branch branchIH =>
      cases second with
      | condTrue otherEvaluation _ otherBranch =>
          rw [evaluation] at otherEvaluation
          cases otherEvaluation
          exact branchIH otherBranch
      | condFalse otherEvaluation _ => rw [evaluation] at otherEvaluation; cases otherEvaluation; exact (nonzero rfl).elim
      | condFault otherEvaluation => rw [evaluation] at otherEvaluation; cases otherEvaluation
  | condFalse evaluation branch branchIH =>
      cases second with
      | condTrue otherEvaluation otherNonzero _ => rw [evaluation] at otherEvaluation; cases otherEvaluation; exact (otherNonzero rfl).elim
      | condFalse otherEvaluation otherBranch => rw [evaluation] at otherEvaluation; exact branchIH otherBranch
      | condFault otherEvaluation => rw [evaluation] at otherEvaluation; cases otherEvaluation
  | condFault evaluation =>
      cases second with
      | condTrue otherEvaluation _ _ => rw [evaluation] at otherEvaluation; cases otherEvaluation
      | condFalse otherEvaluation _ => rw [evaluation] at otherEvaluation; cases otherEvaluation
      | condFault => rfl
  | whileFalse evaluation =>
      cases second with
      | whileFalse => rfl
      | whileTrue otherEvaluation otherNonzero _ _ => rw [evaluation] at otherEvaluation; cases otherEvaluation; exact (otherNonzero rfl).elim
      | whileRet otherEvaluation otherNonzero _ => rw [evaluation] at otherEvaluation; cases otherEvaluation; exact (otherNonzero rfl).elim
      | whileBodyFault otherEvaluation otherNonzero _ => rw [evaluation] at otherEvaluation; cases otherEvaluation; exact (otherNonzero rfl).elim
      | whileGuardFault otherEvaluation => rw [evaluation] at otherEvaluation; cases otherEvaluation
  | whileTrue evaluation nonzero iteration rest iterationIH restIH =>
      cases second with
      | whileFalse otherEvaluation => rw [evaluation] at otherEvaluation; cases otherEvaluation; exact (nonzero rfl).elim
      | whileTrue otherEvaluation _ otherIteration otherRest =>
          rw [evaluation] at otherEvaluation
          cases otherEvaluation
          have sameMiddle := iterationIH otherIteration
          cases sameMiddle
          exact restIH otherRest
      | whileRet otherEvaluation _ otherIteration => cases iterationIH otherIteration
      | whileBodyFault otherEvaluation _ otherIteration => cases iterationIH otherIteration
      | whileGuardFault otherEvaluation => rw [evaluation] at otherEvaluation; cases otherEvaluation
  | whileRet evaluation nonzero iteration iterationIH =>
      cases second with
      | whileFalse otherEvaluation => rw [evaluation] at otherEvaluation; cases otherEvaluation; exact (nonzero rfl).elim
      | whileTrue otherEvaluation _ otherIteration _ => cases iterationIH otherIteration
      | whileRet otherEvaluation _ otherIteration => exact iterationIH otherIteration
      | whileBodyFault otherEvaluation _ otherIteration => exact iterationIH otherIteration
      | whileGuardFault otherEvaluation => rw [evaluation] at otherEvaluation; cases otherEvaluation
  | whileBodyFault evaluation nonzero iteration iterationIH =>
      cases second with
      | whileFalse otherEvaluation => rw [evaluation] at otherEvaluation; cases otherEvaluation; exact (nonzero rfl).elim
      | whileTrue otherEvaluation _ otherIteration _ => cases iterationIH otherIteration
      | whileRet otherEvaluation _ otherIteration => cases iterationIH otherIteration
      | whileBodyFault otherEvaluation _ otherIteration => exact iterationIH otherIteration
      | whileGuardFault otherEvaluation => rw [evaluation] at otherEvaluation
  | whileGuardFault evaluation =>
      cases second with
      | whileFalse otherEvaluation => rw [evaluation] at otherEvaluation; cases otherEvaluation
      | whileTrue otherEvaluation _ _ _ => rw [evaluation] at otherEvaluation; cases otherEvaluation
      | whileRet otherEvaluation _ _ => rw [evaluation] at otherEvaluation; cases otherEvaluation
      | whileBodyFault otherEvaluation _ _ => rw [evaluation] at otherEvaluation
      | whileGuardFault => rfl

theorem function_exec_deterministic (function : Function)
    (first : function.Exec state firstOutcome)
    (second : function.Exec state secondOutcome) : firstOutcome = secondOutcome := by
  cases first with
  | returned firstBody =>
      cases second with
      | returned secondBody => cases stmt_exec_deterministic firstBody secondBody; rfl
      | fault secondBody => cases stmt_exec_deterministic firstBody secondBody
      | fellOff secondBody => cases stmt_exec_deterministic firstBody secondBody
  | fault firstBody =>
      cases second with
      | returned secondBody => cases stmt_exec_deterministic firstBody secondBody
      | fault secondBody => cases stmt_exec_deterministic firstBody secondBody; rfl
      | fellOff secondBody => cases stmt_exec_deterministic firstBody secondBody
  | fellOff firstBody =>
      cases second with
      | returned secondBody => cases stmt_exec_deterministic firstBody secondBody
      | fault secondBody => cases stmt_exec_deterministic firstBody secondBody
      | fellOff secondBody => cases stmt_exec_deterministic firstBody secondBody; rfl

theorem plus2_any_success_is_wrapping_add (a b : Word32) (post : State)
    (execution : Raw.FunctionExec plus2Certificate.program "plus2"
      plus2Certificate.functionInfo plus2Certificate.rawBody plus2.returnType
      (plus2Initial a b) (.success post)) :
    BitVec.ofInt 32 post.result = a + b := by
  have resolved := plus2Certificate.resolution.rawToResolved
    (plus2Initial a b) (.success post) execution
  have equality := function_exec_deterministic plus2 resolved (plus2_resolved_executes a b)
  have stateEquality : post = plus2Result a b := by
    simpa [Raw.embedOutcome] using equality
  rw [stateEquality]
  exact plus2_success_is_wrapping_add a b

theorem plus2_no_failure (a b : Word32) :
    ¬Raw.FunctionExec plus2Certificate.program "plus2" plus2Certificate.functionInfo
      plus2Certificate.rawBody plus2.returnType (plus2Initial a b) .undefinedBehavior := by
  intro failed
  have resolvedFailure := plus2Certificate.resolution.rawToResolved
    (plus2Initial a b) .undefinedBehavior failed
  have equality := function_exec_deterministic plus2 (plus2_resolved_executes a b) resolvedFailure
  cases equality

/-- Total validity: every u32 input has a finite success, and no finite C failure exists. -/
theorem plus2_total_no_failure (a b : Word32) :
    Raw.FunctionExec plus2Certificate.program "plus2" plus2Certificate.functionInfo
        plus2Certificate.rawBody plus2.returnType (plus2Initial a b)
          (.success (plus2Result a b)) ∧
      ¬Raw.FunctionExec plus2Certificate.program "plus2" plus2Certificate.functionInfo
        plus2Certificate.rawBody plus2.returnType (plus2Initial a b) .undefinedBehavior :=
  ⟨plus2_raw_fixture_executes a b, plus2_no_failure a b⟩

end Zag.Test.AutoCorres.CParser.ScalarSimpl
