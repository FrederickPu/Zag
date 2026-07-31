import Lang.AutoCorres.L1

/-!
# L1 peephole optimizations

Corresponds only to [`tools/autocorres/L1Peephole.thy`](https://github.com/seL4/l4v/blob/bc2599a59c43e673dca021b10b9841e9b8da4430/tools/autocorres/L1Peephole.thy).
-/

namespace Zag.Lang.AutoCorres.L1Peephole

open Zag.Lang.AutoCorres

universe u

private theorem behavior_ext {left right : Behavior State Value}
    (results : left.results = right.results) (failed : left.failed = right.failed) :
    left = right := by
  cases left
  cases right
  simp_all

private theorem seq_mem_ok {first second : _root_.Zag.Lang.AutoCorres.L1.L1Program State} :
    (Except.ok (), post) ∈
        (_root_.Zag.Lang.AutoCorres.L1.seq first second state).results ↔
      ∃ middle, (Except.ok (), middle) ∈ (first state).results ∧
        (Except.ok (), post) ∈ (second middle).results := by
  unfold _root_.Zag.Lang.AutoCorres.L1.seq
  rw [mem_bindE_ok]
  constructor
  · rintro ⟨value, middle, member, next⟩
    cases value
    exact ⟨middle, member, next⟩
  · rintro ⟨middle, member, next⟩
    exact ⟨(), middle, member, next⟩

private theorem seq_mem_error
    {first second : _root_.Zag.Lang.AutoCorres.L1.L1Program State} :
    (Except.error (), post) ∈
        (_root_.Zag.Lang.AutoCorres.L1.seq first second state).results ↔
      (Except.error (), post) ∈ (first state).results ∨
        ∃ middle, (Except.ok (), middle) ∈ (first state).results ∧
          (Except.error (), post) ∈ (second middle).results := by
  unfold _root_.Zag.Lang.AutoCorres.L1.seq bindE
  rw [mem_bind]
  constructor
  · rintro ⟨result, middle, member, next⟩
    cases result with
    | error exception =>
        cases exception
        left
        change (Except.error (), post) = (Except.error (), middle) at next
        cases next
        exact member
    | ok value =>
        cases value
        exact Or.inr ⟨middle, member, next⟩
  · rintro (member | ⟨middle, member, next⟩)
    · exact ⟨Except.error (), post, member, rfl⟩
    · exact ⟨Except.ok (), middle, member, next⟩

private theorem seq_failed
    {first second : _root_.Zag.Lang.AutoCorres.L1.L1Program State} :
    (_root_.Zag.Lang.AutoCorres.L1.seq first second state).failed ↔
      (first state).failed ∨
        ∃ middle, (Except.ok (), middle) ∈ (first state).results ∧
          (second middle).failed := by
  unfold _root_.Zag.Lang.AutoCorres.L1.seq bindE bind
  constructor
  · rintro (failed | ⟨result, middle, member, nextFailed⟩)
    · exact Or.inl failed
    · cases result with
      | error exception => simp [_root_.Zag.Lang.AutoCorres.throw,
          _root_.Zag.Lang.AutoCorres.pure] at nextFailed
      | ok value =>
          cases value
          exact Or.inr ⟨middle, member, nextFailed⟩
  · rintro (failed | ⟨middle, member, nextFailed⟩)
    · exact Or.inl failed
    · exact Or.inr ⟨Except.ok (), middle, member, nextFailed⟩

/-- Normalize nested L1 sequencing to right-associated form. -/
theorem seq_assoc
    (first second third : _root_.Zag.Lang.AutoCorres.L1.L1Program State) :
    _root_.Zag.Lang.AutoCorres.L1.seq
        (_root_.Zag.Lang.AutoCorres.L1.seq first second) third =
      _root_.Zag.Lang.AutoCorres.L1.seq first
        (_root_.Zag.Lang.AutoCorres.L1.seq second third) := by
  funext state
  apply behavior_ext
  · funext result
    rcases result with ⟨result, post⟩
    cases result with
    | error exception =>
        cases exception
        apply propext
        change ((Except.error (), post) ∈
            (_root_.Zag.Lang.AutoCorres.L1.seq
              (_root_.Zag.Lang.AutoCorres.L1.seq first second) third state).results) ↔
          (Except.error (), post) ∈
            (_root_.Zag.Lang.AutoCorres.L1.seq first
              (_root_.Zag.Lang.AutoCorres.L1.seq second third) state).results
        simp only [seq_mem_error, seq_mem_ok]
        grind
    | ok value =>
        cases value
        apply propext
        change ((Except.ok (), post) ∈
            (_root_.Zag.Lang.AutoCorres.L1.seq
              (_root_.Zag.Lang.AutoCorres.L1.seq first second) third state).results) ↔
          (Except.ok (), post) ∈
            (_root_.Zag.Lang.AutoCorres.L1.seq first
              (_root_.Zag.Lang.AutoCorres.L1.seq second third) state).results
        simp only [seq_mem_ok]
        grind
  · apply propext
    change (_root_.Zag.Lang.AutoCorres.L1.seq
        (_root_.Zag.Lang.AutoCorres.L1.seq first second) third state).failed ↔
      (_root_.Zag.Lang.AutoCorres.L1.seq first
        (_root_.Zag.Lang.AutoCorres.L1.seq second third) state).failed
    simp only [seq_failed, seq_mem_ok]
    grind

end Zag.Lang.AutoCorres.L1Peephole
