import Lang.AutoCorres.SimplConvRecursion

/-! # Object-level recursive SimplConv regression -/

namespace Zag.Test.AutoCorres.Kernel.SimplConvRecursion

open Zag.Lang.AutoCorres
open Zag.Lang.AutoCorres.SimplConv.Recursive

inductive Procedure where
  | countdown
deriving DecidableEq

private def sourceBody : Simpl.Com Nat Procedure Unit :=
  .Cond (· = 0) .Skip (.Seq (.Basic (· - 1)) (.Call .countdown))

private def environment : Simpl.Body Nat Procedure Unit
  | .countdown => some sourceBody

private def targetBody : Syntax Procedure Nat :=
  .condition (· = 0) .skip (.seq (.modify (· - 1)) (.internalCall .countdown))

private def bodySupported : Supported id environment sourceBody targetBody :=
  .cond (· = 0) .skip (.seq (.basic (· - 1)) (.internalCall Procedure.countdown))

private def family : Family id environment where
  sourceBody := fun | .countdown => sourceBody
  targetBody := fun | .countdown => targetBody
  defined := by intro procedure; cases procedure; rfl
  supported := by intro procedure; cases procedure; exact bodySupported

theorem countdown_exec : ∀ value,
    Simpl.Exec environment (.Call .countdown) (.normal value) (.normal 0)
  | 0 => .call rfl (.condTrue rfl .skip)
  | value + 1 => by
      apply Simpl.Exec.call rfl
      apply Simpl.Exec.condFalse (by simp)
      apply Simpl.Exec.seq
      · exact .basic
      · simpa using countdown_exec value

theorem countdown_corres (measure : Nat) :
    L1.L1Corres false environment (family.atMeasure measure .countdown)
      (.Call .countdown) :=
  family.atMeasure_call_corres measure .countdown

@[simp] private theorem pure_not_failed (value : α) (state : σ) :
    ¬(Zag.Lang.AutoCorres.pure value state).failed := by
  simp [Zag.Lang.AutoCorres.pure]

local macro "simp_countdown" : tactic => `(tactic|
  simp [family, Family.atMeasure, Family.atMeasureSyntax, targetBody,
    Syntax.instantiate, L1.Syntax.denote, L1.condition, L1.seq,
    L1.skip, L1.modify, L1.fail, Zag.Lang.AutoCorres.liftE,
    Zag.Lang.AutoCorres.bindE, Zag.Lang.AutoCorres.bind,
    Zag.Lang.AutoCorres.modify,
    Zag.Lang.AutoCorres.throw, returnOk, Zag.Lang.AutoCorres.pure])

theorem countdown_no_fail : ∀ value,
    ¬(family.atMeasure (value + 1) .countdown value).failed := by
  intro value
  induction value with
  | zero => simp_countdown
  | succ value inductionHypothesis =>
      simp [family, Family.atMeasure, targetBody] at inductionHypothesis
      simp_countdown
      rintro result post ⟨modified, middle, modifiedResult, liftedResult⟩
      change (modified, middle) = ((), value) at modifiedResult
      cases modifiedResult
      change (result, post) = (Except.ok (), value) at liftedResult
      cases liftedResult
      exact inductionHypothesis

theorem countdown_insufficient : ∀ value,
    (family.atMeasure value .countdown value).failed := by
  intro value
  induction value with
  | zero => simp_countdown
  | succ value inductionHypothesis =>
      simp [family, Family.atMeasure, targetBody] at inductionHypothesis
      simp_countdown
      refine ⟨Except.ok (), value, ?_, inductionHypothesis⟩
      exact ⟨(), value, rfl, rfl⟩

theorem countdown_result (value : Nat) :
    (Except.ok (), 0) ∈
      (family.atMeasure (value + 1) .countdown value).results := by
  have correspondence := countdown_corres (value + 1)
  exact (correspondence value (countdown_no_fail value)).1 _ (countdown_exec value)

theorem countdown_three_no_fail :
    ¬(family.atMeasure 4 .countdown 3).failed :=
  countdown_no_fail 3

theorem countdown_three_result :
    (Except.ok (), 0) ∈ (family.atMeasure 4 .countdown 3).results :=
  countdown_result 3

inductive MixedProcedure where
  | recursive
  | dependency
deriving DecidableEq

inductive MixedMember where
  | recursive

private def embedMixed : MixedMember → MixedProcedure
  | .recursive => .recursive

private def mixedEnvironment : Simpl.Body Nat MixedProcedure Unit
  | .recursive => some (.Call .dependency)
  | .dependency => some .Skip

private def mixedSupported : Supported embedMixed mixedEnvironment
    (.Call .dependency) (.externalCall .skip) :=
  .externalCall .dependency .Skip .skip rfl (L1.L1Corres_skip false mixedEnvironment)

private def mixedFamily : Family embedMixed mixedEnvironment where
  sourceBody := fun | .recursive => .Call .dependency
  targetBody := fun | .recursive => .externalCall .skip
  defined := by intro member; cases member; rfl
  supported := by intro member; cases member; exact mixedSupported

/-- An already-certified dependency does not consume the current SCC measure. -/
theorem external_call_succeeds_at_first_measure :
    ¬(mixedFamily.atMeasure 1 .recursive 7).failed := by
  simp [mixedFamily, Family.atMeasure, Family.atMeasureSyntax, Syntax.instantiate,
    L1.Syntax.denote, L1.skip, returnOk, Zag.Lang.AutoCorres.pure]

end Zag.Test.AutoCorres.Kernel.SimplConvRecursion
