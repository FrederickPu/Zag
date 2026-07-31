import Lang.AutoCorres.Nondet_Monad

/-!
# Extended nondeterministic monad operations

Corresponds to [`tools/autocorres/NonDetMonadEx.thy`](https://github.com/seL4/l4v/blob/bc2599a59c43e673dca021b10b9841e9b8da4430/tools/autocorres/NonDetMonadEx.thy).
-/

namespace Zag.Lang.AutoCorres

/-- Fail unless the current state satisfies `condition`. -/
def guard (condition : σ → Prop) : Nondet σ Unit := fun state =>
  { results := fun result => condition state ∧ result = ((), state)
    failed := ¬ condition state }

/-- Choose a related post-state, failing exactly when none exists. -/
def spec (relation : Set (σ × σ)) : Nondet σ Unit := fun state =>
  { results := fun result => (state, result.2) ∈ relation ∧ result.1 = ()
    failed := ¬ ∃ newState, (state, newState) ∈ relation }

@[simp] theorem mem_guard {condition : σ → Prop} {state post : σ} {result : Unit} :
    (result, post) ∈ (guard condition state).results ↔
      condition state ∧ result = () ∧ post = state := by
  change (condition state ∧ (result, post) = ((), state)) ↔ _
  constructor
  · rintro ⟨holds, equality⟩
    cases equality
    exact ⟨holds, rfl, rfl⟩
  · rintro ⟨holds, rfl, rfl⟩
    exact ⟨holds, rfl⟩

@[simp] theorem failed_guard {condition : σ → Prop} {state : σ} :
    (guard condition state).failed ↔ ¬ condition state :=
  Iff.rfl

@[simp] theorem mem_spec {relation : Set (σ × σ)}
    {state post : σ} {result : Unit} :
    (result, post) ∈ (spec relation state).results ↔
      (state, post) ∈ relation ∧ result = () :=
  Iff.rfl

@[simp] theorem failed_spec {relation : Set (σ × σ)} {state : σ} :
    (spec relation state).failed ↔ ¬ ∃ post, (state, post) ∈ relation :=
  Iff.rfl

end Zag.Lang.AutoCorres
