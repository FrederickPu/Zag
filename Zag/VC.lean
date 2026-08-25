import Zag.EvalState
import Zag.EvalTriple
import Std.Do

/-!
# Relational weakest preconditions

Zag evaluation is a partial relation, not a total Lean function. This module reuses `Std.Do`'s
state-indexed assertions and postconditions while defining weakest preconditions directly from a
relation.
-/

namespace Zag.VC

open scoped Std.Do

universe u

/-- The total-correctness weakest precondition of a successful-result relation. Exception
conditions are irrelevant because the relation exposes no exceptional outcomes. -/
def wp {α : Type u} {ps : Std.Do.PostShape} (relation : α → Prop)
    (Q : Std.Do.PostCond α ps) : Std.Do.Assertion ps :=
  spred(∃ value, ⌜relation value⌝ ∧ Q.1 value)

/-- A Hoare-style specification for a partial relation. Unlike `Std.Do.Triple`, the subject is a
relation and no total Lean function or `WP` instance is required. -/
def Triple {α : Type u} {ps : Std.Do.PostShape} (relation : α → Prop)
    (P : Std.Do.Assertion ps) (Q : Std.Do.PostCond α ps) : Prop :=
  P ⊢ₛ wp relation Q

namespace Triple

theorem iff {α : Type u} {ps : Std.Do.PostShape} {relation : α → Prop}
    {P : Std.Do.Assertion ps} {Q : Std.Do.PostCond α ps} :
    Triple relation P Q ↔ P ⊢ₛ wp relation Q := by
  rfl

theorem conseq {α : Type u} {ps : Std.Do.PostShape} {relation : α → Prop}
    {P P' : Std.Do.Assertion ps} {Q Q' : Std.Do.PostCond α ps}
    (h : Triple relation P Q) (hpre : P' ⊢ₛ P) (hpost : Q ⊢ₚ Q') :
    Triple relation P' Q' := by
  apply hpre.trans
  apply h.trans
  apply Std.Do.SPred.exists_mono
  intro value
  exact Std.Do.SPred.and_mono .rfl (hpost.1 value)

theorem of_result {α : Type u} {ps : Std.Do.PostShape} {relation : α → Prop}
    {P : Std.Do.Assertion ps} {Q : Std.Do.PostCond α ps} {value : α}
    (hrelation : relation value) (hpost : P ⊢ₛ Q.1 value) :
    Triple relation P Q := by
  exact Std.Do.SPred.exists_intro' value
    (Std.Do.SPred.and_intro (Std.Do.SPred.pure_intro hrelation) hpost)

/-- For pure assertions, a relational triple is the expected proposition-level
total-correctness statement. -/
theorem iff_pure {α : Type} {relation : α → Prop} {P : Prop} {Q : α → Prop} :
    Triple (ps := .pure) relation (Std.Do.SPred.pure P)
        (Std.Do.PostCond.noThrow fun value => Std.Do.SPred.pure (Q value)) ↔
      (P → ∃ value, relation value ∧ Q value) := by
  rfl

end Triple

/-- The total-correctness weakest precondition of a successful state transition. -/
def stateWp {σ α : Type u} (relation : σ → α → σ → Prop)
    (Q : Std.Do.PostCond α (.arg σ .pure)) : Std.Do.Assertion (.arg σ .pure) :=
  fun initial => ULift.up <| ∃ value final,
    relation initial value final ∧ (Q.1 value final).down

/-- A Hoare-style specification for a deeply embedded state transition. -/
def StateTriple {σ α : Type u} (relation : σ → α → σ → Prop)
    (P : Std.Do.Assertion (.arg σ .pure))
    (Q : Std.Do.PostCond α (.arg σ .pure)) : Prop :=
  P ⊢ₛ stateWp relation Q

namespace StateTriple

theorem iff {σ α : Type u} {relation : σ → α → σ → Prop}
    {P : Std.Do.Assertion (.arg σ .pure)} {Q : Std.Do.PostCond α (.arg σ .pure)} :
    StateTriple relation P Q ↔ ∀ initial, (P initial).down →
      ∃ value final, relation initial value final ∧ (Q.1 value final).down := by
  rfl

theorem of_result {σ α : Type u} {relation : σ → α → σ → Prop}
    {P : Std.Do.Assertion (.arg σ .pure)} {Q : Std.Do.PostCond α (.arg σ .pure)}
    {initial final : σ} {value : α} (hrelation : relation initial value final)
    (hpost : P ⊢ₛ fun current =>
      ULift.up (current = initial ∧ (Q.1 value final).down)) :
    StateTriple relation P Q := by
  intro current hpre
  rcases hpost current hpre with ⟨rfl, hQ⟩
  exact ⟨value, final, hrelation, hQ⟩

end StateTriple

end Zag.VC
