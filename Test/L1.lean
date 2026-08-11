import Lang.AutoCorres.ML.simpl_conv

/-!
# AutoCorres L1 semantic tests

These tests exercise the current shallow L1 semantics, the SIMPL language and
proof-producing conversion, and the exact closed SSA bridge.
-/

namespace Zag.Test.L1

open Zag.Lang.AutoCorres

structure State where
  x : Nat
  y : Nat
  deriving DecidableEq, Repr

def initial : State := ⟨3, 4⟩
def reversed : State := ⟨5, 2⟩

def bumpX (state : State) : State :=
  { state with x := state.x + 1 }

def bumpY (state : State) : State :=
  { state with y := state.y + 1 }

def xLtY (state : State) : Prop :=
  state.x < state.y

def yLtX (state : State) : Prop :=
  state.y < state.x

def never (_ : State) : Prop := False
def always (_ : State) : Prop := True

abbrev Program := L1.L1Program State
abbrev Command := Simpl.Com State Empty Unit

def env : Simpl.Body State Empty Unit :=
  fun proc => nomatch proc

/-! ## L1 outcomes and control flow -/

theorem skip_normal :
    (Except.ok (), initial) ∈ ((L1.skip : Program) initial).results := by
  simp [L1.skip]

theorem throw_abrupt :
    (Except.error (), initial) ∈ ((L1.throw : Program) initial).results := by
  simp [L1.throw]

def caughtThrow : Program :=
  L1.catch L1.throw (L1.modify bumpX)

theorem catch_handles_throw :
    (Except.ok (), bumpX initial) ∈ (caughtThrow initial).results := by
  unfold caughtThrow L1.catch handle
  rw [mem_bind]
  refine ⟨Except.error (), initial, ?_, ?_⟩
  · exact throw_abrupt
  · simp [L1.modify]

def shortCircuit : Program :=
  L1.seq L1.throw (L1.modify bumpX)

theorem seq_short_circuits_after_throw :
    (Except.error (), initial) ∈ (shortCircuit initial).results := by
  unfold shortCircuit L1.seq bindE
  rw [mem_bind]
  refine ⟨Except.error (), initial, throw_abrupt, ?_⟩
  exact (mem_throw).2 ⟨rfl, rfl⟩

theorem seq_does_not_run_after_throw :
    ¬ (Except.error (), bumpX initial) ∈ (shortCircuit initial).results := by
  intro member
  unfold shortCircuit L1.seq bindE at member
  rw [mem_bind] at member
  rcases member with ⟨result, middle, first, second⟩
  change (result, middle) = (Except.error (), initial) at first
  cases first
  change (Except.error (), bumpX initial) = (Except.error (), initial) at second
  have stateEq : bumpX initial = initial := by injection second
  simp [bumpX, initial] at stateEq

theorem guard_true_succeeds :
    (Except.ok (), initial) ∈ ((L1.guard xLtY : Program) initial).results := by
  change (Except.ok (), initial) ∈
    (liftE (Zag.Lang.AutoCorres.guard xLtY) initial).results
  rw [mem_liftE, mem_guard]
  simp [xLtY, initial]

theorem guard_false_fails :
    ((L1.guard yLtX : Program) initial).failed := by
  change (liftE (Zag.Lang.AutoCorres.guard yLtX) initial).failed
  unfold liftE
  rw [failed_bind]
  exact Or.inl ((failed_guard).2 (by simp [yLtX, initial]))

noncomputable def chooseByOrder : Program :=
  L1.condition xLtY (L1.modify bumpX) (L1.modify bumpY)

theorem condition_true_branch :
    (Except.ok (), bumpX initial) ∈ (chooseByOrder initial).results := by
  simp [chooseByOrder, L1.condition, xLtY, initial, L1.modify, bumpX]

theorem condition_false_branch :
    (Except.ok (), bumpY reversed) ∈ (chooseByOrder reversed).results := by
  simp [chooseByOrder, L1.condition, xLtY, reversed, L1.modify, bumpY]

def falseLoop : Program :=
  L1.while never (L1.modify bumpX)

theorem while_false_preserves_state :
    (Except.ok (), initial) ∈ (falseLoop initial).results := by
  change WhileResult _ _ (some (Except.ok (), initial))
    (some (Except.ok (), initial))
  exact .stop (by simp [never])

def throwingLoop : Program :=
  L1.while always L1.throw

theorem while_true_throw_exits_abruptly :
    (Except.error (), initial) ∈ (throwingLoop initial).results := by
  change WhileResult _ _ (some (Except.ok (), initial))
    (some (Except.error (), initial))
  apply WhileResult.step (next := Except.error ()) (nextState := initial)
    (by simp [always])
  · exact throw_abrupt
  · exact .stop (by simp)

/-! ## SIMPL semantics and proof-producing conversion -/

def nextX : Simpl.StateRel State :=
  fun pair => pair.2 = bumpX pair.1

def representativeSource : Command :=
  .Seq
    (.Cond xLtY (.Basic bumpX) .Skip)
    (.Seq
      (.Guard () xLtY (.While never .Skip))
      (.Catch .Throw (.Spec nextX)))

def representativeSupported : SimplConv.Kernel.Supported representativeSource :=
  .seq
    (.cond xLtY (.basic bumpX) .skip)
    (.seq
      (.guard () xLtY (.while never .skip))
      (.catch .throw (.spec nextX)))

def representativeCertificate :=
  ML.SimplConv.simplConv false env representativeSupported

theorem simpl_to_l1_representative_shape :
    representativeCertificate.target =
      .seq
        (.condition xLtY (.modify bumpX) .skip)
        (.seq
          (.seq (.guard xLtY) (.while never .skip))
          (.catch .throw (.spec nextX))) := by
  rfl

theorem simpl_to_l1_representative_correspondence :
    L1.L1Corres false env representativeCertificate.target.denote
      representativeSource :=
  representativeCertificate.corres

theorem simpl_throw_execution :
    Simpl.Exec env (.Throw : Command) (.normal initial) (.abrupt initial) :=
  .throw

theorem converted_throw_matches_execution :
    L1.Matches (L1.throw : Program) initial
      (.abrupt initial : Simpl.XState State Unit) := by
  simpa [L1.Matches] using throw_abrupt

def falseGuardSource : Command := .Guard () yLtX .Skip

theorem simpl_false_guard_faults :
    Simpl.Exec env falseGuardSource (.normal initial) (.fault ()) :=
  .guardFault (by simp [yLtX, initial])

theorem simpl_fault_propagates_through_sequence :
    Simpl.Exec env (.Seq falseGuardSource (.Basic bumpX))
      (.normal initial) (.fault ()) :=
  .seq simpl_false_guard_faults .faultProp

theorem simpl_fault_propagates_through_catch :
    Simpl.Exec env (.Catch falseGuardSource (.Basic bumpX))
      (.normal initial) (.fault ()) :=
  .catchMiss simpl_false_guard_faults (by simp [Simpl.XState.IsAbrupt])

/-! ## Exact closed SSA bridge -/

theorem closed_ssa_bridge_eval_exact :
    cast (by simp only [SSABridge.outcomeTy_type])
      (Zag.Lang.SSA.SSAExpr.evalM? (L1.toSSA caughtThrow).ctx []
        SSABridge.outcomeTy (L1.toSSA caughtThrow).expr) =
      some (SSABridge.suspend caughtThrow) :=
  L1.toSSA_eval caughtThrow

end Zag.Test.L1
