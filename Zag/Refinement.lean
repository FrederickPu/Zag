namespace Zag

universe u

/-- A proof-producing rule for an arbitrary reflected judgment. -/
structure Refinement {Goal : Type u} (Holds : Goal → Prop) (goal : Goal) where
  goals : List Goal
  prove : (∀ subgoal, subgoal ∈ goals → Holds subgoal) → Holds goal

abbrev Tactic {Goal : Type u} (Holds : Goal → Prop) :=
  (goal : Goal) → Refinement Holds goal

abbrev Tactic? {Goal : Type u} (Holds : Goal → Prop) :=
  (goal : Goal) → Option (Refinement Holds goal)

namespace Refinement

variable {Goal : Type u} {Holds : Goal → Prop}

def lift {goal : Goal} (proof : Holds goal) : Refinement Holds goal where
  goals := []
  prove := fun _ => proof

def stuck (goal : Goal) : Refinement Holds goal where
  goals := [goal]
  prove := fun proveSubgoals => proveSubgoals goal (by simp)

inductive InterpretsGoals (Holds : Goal → Prop) : List Goal → Prop where
  | nil : InterpretsGoals Holds []
  | cons {goal : Goal} {rest : List Goal} :
      Holds goal → InterpretsGoals Holds rest → InterpretsGoals Holds (goal :: rest)

theorem InterpretsGoals.get {goals : List Goal}
    (proofs : InterpretsGoals Holds goals) {goal : Goal} (hgoal : goal ∈ goals) : Holds goal := by
  induction proofs with
  | nil => simp at hgoal
  | cons head _ ih =>
      simp only [List.mem_cons] at hgoal
      cases hgoal with
      | inl h => exact h ▸ head
      | inr h => exact ih h

theorem sound {goal : Goal} (refinement : Refinement Holds goal)
    (subgoals : InterpretsGoals Holds refinement.goals) : Holds goal :=
  refinement.prove fun _ hsubgoal => subgoals.get hsubgoal

end Refinement

abbrev PropRefinement (goal : Prop) :=
  Refinement (fun proposition : Prop => proposition) goal

namespace PropRefinement

/-- The ordinary natural-number induction rule as a proof-carrying refinement. -/
def natInduction {motive : Nat → Prop} (target : Nat) : PropRefinement (motive target) where
  goals := [motive 0, ∀ n, motive n → motive (n + 1)]
  prove := by
    intro proveSubgoals
    have base := proveSubgoals (motive 0) (by simp)
    have step := proveSubgoals (∀ n, motive n → motive (n + 1)) (by simp)
    exact Nat.rec base (fun n ih => step n ih) target

end PropRefinement

end Zag
