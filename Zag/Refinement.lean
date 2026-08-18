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

theorem close {goal : Goal} (refinement : Refinement Holds goal)
    (closed : refinement.goals = []) : Holds goal := by
  apply refinement.prove
  intro subgoal hsubgoal
  rw [closed] at hsubgoal
  cases hsubgoal

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

def refine {goal : Goal} (refinement : Refinement Holds goal)
    (next : ∀ subgoal, subgoal ∈ refinement.goals → Refinement Holds subgoal) :
    Refinement Holds goal where
  goals := refinement.goals.attach.flatMap fun subgoal =>
    (next subgoal.val subgoal.property).goals
  prove := by
    intro proveGenerated
    apply refinement.prove
    intro subgoal hsubgoal
    apply (next subgoal hsubgoal).prove
    intro generated hgenerated
    apply proveGenerated
    exact List.mem_flatMap.mpr ⟨⟨subgoal, hsubgoal⟩, by simp, hgenerated⟩

def andThen {goal : Goal} (refinement : Refinement Holds goal)
    (next : Tactic Holds) : Refinement Holds goal :=
  refinement.refine fun subgoal _ => next subgoal

def invertible {goal : Goal} (refinement : Refinement Holds goal) : Prop :=
  Holds goal → ∀ subgoal, subgoal ∈ refinement.goals → Holds subgoal

theorem lift_invertible {goal : Goal} (proof : Holds goal) :
    invertible (lift proof) := by
  intro _ subgoal hsubgoal
  simp [lift] at hsubgoal

theorem stuck_invertible (goal : Goal) : invertible (stuck (Holds := Holds) goal) := by
  intro hgoal subgoal hsubgoal
  simp [stuck] at hsubgoal
  exact hsubgoal ▸ hgoal

theorem refine_invertible {goal : Goal} (refinement : Refinement Holds goal)
    (next : ∀ subgoal, subgoal ∈ refinement.goals → Refinement Holds subgoal)
    (hrefinement : invertible refinement)
    (hnext : ∀ subgoal hsubgoal, invertible (next subgoal hsubgoal)) :
    invertible (refinement.refine next) := by
  intro hgoal generated hgenerated
  rcases List.mem_flatMap.mp hgenerated with ⟨attached, _hattached, hgeneratedNext⟩
  rcases attached with ⟨subgoal, hsubgoal⟩
  exact hnext subgoal hsubgoal (hrefinement hgoal subgoal hsubgoal) generated hgeneratedNext

end Refinement

namespace Tactic

variable {Goal : Type u} {Holds : Goal → Prop}

def stuck : Tactic Holds := Refinement.stuck

def andThen (first second : Tactic Holds) : Tactic Holds :=
  fun goal => (first goal).andThen second

def iterate (fuel : Nat) (step : Tactic Holds) : Tactic Holds
| goal =>
    match fuel with
    | 0 => step goal
    | n + 1 => (step goal).refine fun subgoal _ => iterate n step subgoal

def invertible (tactic : Tactic Holds) : Prop :=
  ∀ goal, Refinement.invertible (tactic goal)

theorem iterate_invertible {step : Tactic Holds} (hstep : invertible step) :
    ∀ fuel, invertible (iterate fuel step)
| 0 => hstep
| n + 1 => fun goal =>
    Refinement.refine_invertible _ _ (hstep goal)
      (fun subgoal _ => iterate_invertible hstep n subgoal)

def CompleteOn (tactic : Tactic Holds) (domain : Goal → Prop) : Prop :=
  ∀ goal, domain goal → Holds goal → (tactic goal).goals = []

theorem decides {tactic : Tactic Holds} {domain : Goal → Prop}
    (hcomplete : CompleteOn tactic domain) (goal : Goal) (hdomain : domain goal) :
    Holds goal ↔ (tactic goal).goals = [] :=
  ⟨hcomplete goal hdomain, fun hclosed => (tactic goal).close hclosed⟩

end Tactic

namespace Tactic?

variable {Goal : Type u} {Holds : Goal → Prop}

def orElse (first second : Tactic? Holds) : Tactic? Holds :=
  fun goal => (first goal).orElse (fun _ => second goal)

def firstOf : List (Tactic? Holds) → Tactic? Holds
| [] => fun _ => none
| tactic :: rest => orElse tactic (firstOf rest)

def toTactic (tactic : Tactic? Holds) : Tactic Holds :=
  fun goal => (tactic goal).getD (Refinement.stuck goal)

end Tactic?

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
