import Lang.AutoCorres.CorresXF

/-!
# Execution across state representations

Corresponds to [`tools/autocorres/ExecConcrete.thy`](https://github.com/seL4/l4v/blob/bc2599a59c43e673dca021b10b9841e9b8da4430/tools/autocorres/ExecConcrete.thy).
-/

namespace Zag.Lang.AutoCorres

universe u v w x y z

private theorem behavior_ext {left right : Behavior State Return}
    (results : left.results = right.results)
    (failed : left.failed = right.failed) : left = right := by
  cases left
  cases right
  cases results
  cases failed
  rfl

/-- Upstream `corresXF_simple`, used by the execution correspondence lemmas. -/
def CorresXFSimple {ConcreteState : Type u} {AbstractState : Type v}
    {ConcreteResult : Type w} {AbstractResult : Type x}
    (stateMap : ConcreteState → AbstractState)
    (resultMap : ConcreteResult → ConcreteState → AbstractResult)
    (precondition : ConcreteState → Prop)
    (abstract : Nondet AbstractState AbstractResult)
    (concrete : Nondet ConcreteState ConcreteResult) : Prop :=
  ∀ state, precondition state ∧ ¬ (abstract (stateMap state)).failed →
    (∀ result post, (result, post) ∈ (concrete state).results →
      (resultMap result post, stateMap post) ∈
        (abstract (stateMap state)).results) ∧
    ¬ (concrete state).failed

/-! ## Concrete execution -/

/--
Execute a program after relationally selecting a concrete preimage of the
current abstract state, then map every resulting state back to the abstract
state space.
-/
def exec_concrete (stateMap : ConcreteState → AbstractState)
    (program : Nondet ConcreteState Return) : Nondet AbstractState Return :=
  fun state =>
    { results := fun outcome =>
        ∃ source post,
          state = stateMap source ∧
          outcome.2 = stateMap post ∧
          (outcome.1, post) ∈ (program source).results
      failed := ∃ source, state = stateMap source ∧ (program source).failed }

theorem in_exec_concrete
    {stateMap : ConcreteState → AbstractState}
    {program : Nondet ConcreteState Return}
    {result : Return} {state post : AbstractState} :
    (result, post) ∈ (exec_concrete stateMap program state).results ↔
      ∃ source concretePost,
        stateMap source = state ∧
        stateMap concretePost = post ∧
        (result, concretePost) ∈ (program source).results := by
  constructor
  · rintro ⟨source, concretePost, initial, final, member⟩
    exact ⟨source, concretePost, initial.symm, final.symm, member⟩
  · rintro ⟨source, concretePost, initial, final, member⟩
    exact ⟨source, concretePost, initial.symm, final.symm, member⟩

theorem snd_exec_concrete
    {stateMap : ConcreteState → AbstractState}
    {program : Nondet ConcreteState Return} {state : AbstractState} :
    (exec_concrete stateMap program state).failed ↔
      ∃ source, stateMap source = state ∧ (program source).failed := by
  constructor
  · rintro ⟨source, equality, failed⟩
    exact ⟨source, equality.symm, failed⟩
  · rintro ⟨source, equality, failed⟩
    exact ⟨source, equality.symm, failed⟩

@[simp] theorem exec_concrete_id (program : Nondet State Return) :
    exec_concrete id program = program := by
  funext state
  have resultsEqual :
      (exec_concrete id program state).results = (program state).results := by
    funext outcome
    apply propext
    change (∃ source post,
      state = source ∧ outcome.2 = post ∧
        (program source).results (outcome.1, post)) ↔
      (program state).results outcome
    constructor
    · rintro ⟨source, post, initial, final, member⟩
      subst source
      subst post
      simpa only [Prod.eta] using member
    · intro member
      exact ⟨state, outcome.2, rfl, rfl, by simpa only [Prod.eta] using member⟩
  have failedEqual :
      (exec_concrete id program state).failed = (program state).failed := by
    apply propext
    change (∃ source, state = source ∧ (program source).failed) ↔ _
    constructor
    · rintro ⟨source, equality, branchFailed⟩
      subst source
      exact branchFailed
    · intro branchFailed
      exact ⟨state, rfl, branchFailed⟩
  exact behavior_ext resultsEqual failedEqual

theorem corresXF_simple_exec_concrete
    (stateMap : ConcreteState → AbstractState)
    (precondition : ConcreteState → Prop)
    (program : Nondet ConcreteState Return) :
    CorresXFSimple stateMap (fun result _ => result) precondition
      (exec_concrete stateMap program) program := by
  intro state hypothesis
  refine ⟨?_, ?_⟩
  · intro result post member
    exact ⟨state, post, rfl, rfl, member⟩
  · intro failed
    exact hypothesis.2 ⟨state, rfl, failed⟩

theorem corresXF_exec_concrete_self
    (stateMap : ConcreteState → AbstractState)
    (precondition : ConcreteState → Prop)
    (program : Nondet ConcreteState (Except Exception Return)) :
    CorresXF stateMap (fun result _ => result) (fun exception _ => exception)
      precondition (exec_concrete stateMap program) program := by
  intro state hypothesis
  refine ⟨?_, ?_⟩
  · intro result post member
    cases result <;> exact ⟨state, post, rfl, rfl, member⟩
  · intro failed
    exact hypothesis.2 ⟨state, rfl, failed⟩

theorem corresXF_exec_concrete
    {stateMap : ConcreteState → AbstractState}
    {normalMap : ConcreteResult → ConcreteState → AbstractResult}
    {exceptionMap : ConcreteException → ConcreteState → AbstractException}
    {precondition : ConcreteState → Prop}
    {abstract : Nondet ConcreteState (Except AbstractException AbstractResult)}
    {concrete : Nondet ConcreteState (Except ConcreteException ConcreteResult)}
    (correspondence :
      CorresXF id normalMap exceptionMap precondition abstract concrete) :
    CorresXF stateMap normalMap exceptionMap precondition
      (exec_concrete stateMap abstract) concrete := by
  intro state hypothesis
  have abstractNoFailure : ¬ (abstract state).failed := by
    intro failed
    exact hypothesis.2 ⟨state, rfl, failed⟩
  have source := correspondence state ⟨hypothesis.1, abstractNoFailure⟩
  refine ⟨?_, source.2⟩
  intro result post member
  have mapped := source.1 result post member
  cases result with
  | error exception => exact ⟨state, post, rfl, rfl, mapped⟩
  | ok value => exact ⟨state, post, rfl, rfl, mapped⟩

/-! ## Abstract execution -/

/--
Execute in the mapped abstract state and retain exactly those post-states that
map to a result state produced by the abstract program.
-/
def exec_abstract (stateMap : ConcreteState → AbstractState)
    (program : Nondet AbstractState Return) : Nondet ConcreteState Return :=
  fun state =>
    { results := fun outcome =>
        ∃ post,
          post = stateMap outcome.2 ∧
          (outcome.1, post) ∈ (program (stateMap state)).results
      failed := ∃ mapped, mapped = stateMap state ∧
        (program (stateMap state)).failed }

theorem in_exec_abstract
    {stateMap : ConcreteState → AbstractState}
    {program : Nondet AbstractState Return}
    {result : Return} {state post : ConcreteState} :
    (result, post) ∈ (exec_abstract stateMap program state).results ↔
      ∃ mappedPost,
        stateMap post = mappedPost ∧
        (result, mappedPost) ∈ (program (stateMap state)).results := by
  constructor
  · rintro ⟨mappedPost, equality, member⟩
    exact ⟨mappedPost, equality.symm, member⟩
  · rintro ⟨mappedPost, equality, member⟩
    exact ⟨mappedPost, equality.symm, member⟩

theorem snd_exec_abstract
    {stateMap : ConcreteState → AbstractState}
    {program : Nondet AbstractState Return} {state : ConcreteState} :
    (exec_abstract stateMap program state).failed ↔
      (program (stateMap state)).failed := by
  constructor
  · rintro ⟨_, _, failed⟩
    exact failed
  · intro failed
    exact ⟨stateMap state, rfl, failed⟩

@[simp] theorem exec_abstract_id (program : Nondet State Return) :
    exec_abstract id program = program := by
  funext state
  have resultsEqual :
      (exec_abstract id program state).results = (program state).results := by
    funext outcome
    apply propext
    change (∃ post, post = outcome.2 ∧
      (program state).results (outcome.1, post)) ↔
      (program state).results outcome
    constructor
    · rintro ⟨post, equality, member⟩
      subst post
      simpa only [Prod.eta] using member
    · intro member
      exact ⟨outcome.2, rfl, by simpa only [Prod.eta] using member⟩
  have failedEqual :
      (exec_abstract id program state).failed = (program state).failed := by
    apply propext
    change (∃ mapped, mapped = state ∧ (program state).failed) ↔ _
    constructor
    · rintro ⟨_, _, branchFailed⟩
      exact branchFailed
    · intro branchFailed
      exact ⟨state, rfl, branchFailed⟩
  exact behavior_ext resultsEqual failedEqual

theorem corresXF_simple_exec_abstract
    (stateMap : ConcreteState → AbstractState)
    (precondition : ConcreteState → Prop)
    (program : Nondet AbstractState Return) :
    CorresXFSimple stateMap (fun result _ => result) precondition
      program (exec_abstract stateMap program) := by
  intro state hypothesis
  refine ⟨?_, ?_⟩
  · intro result post member
    rcases member with ⟨mappedPost, equality, mapped⟩
    simpa [equality] using mapped
  · simpa [snd_exec_abstract] using hypothesis.2

theorem corresXF_exec_abstract_self
    (stateMap : ConcreteState → AbstractState)
    (precondition : ConcreteState → Prop)
    (program : Nondet AbstractState (Except Exception Return)) :
    CorresXF stateMap (fun result _ => result) (fun exception _ => exception)
      precondition program (exec_abstract stateMap program) := by
  intro state hypothesis
  refine ⟨?_, ?_⟩
  · intro result post member
    rcases member with ⟨mappedPost, equality, mapped⟩
    cases result <;> simpa [equality] using mapped
  · simpa [snd_exec_abstract] using hypothesis.2

theorem corresXF_exec_abstract
    {stateMap : ConcreteState → AbstractState}
    {normalMap : ConcreteResult → ConcreteState → AbstractResult}
    {exceptionMap : ConcreteException → ConcreteState → AbstractException}
    {precondition : ConcreteState → Prop}
    {abstract : Nondet AbstractState (Except AbstractException AbstractResult)}
    {concrete : Nondet ConcreteState (Except ConcreteException ConcreteResult)}
    (correspondence :
      CorresXF stateMap normalMap exceptionMap precondition abstract concrete) :
    CorresXF id normalMap exceptionMap precondition
      (exec_abstract stateMap abstract) concrete := by
  intro state hypothesis
  have abstractNoFailure : ¬ (abstract (stateMap state)).failed := by
    simpa [snd_exec_abstract] using hypothesis.2
  have source := correspondence state ⟨hypothesis.1, abstractNoFailure⟩
  refine ⟨?_, source.2⟩
  intro result post member
  have mapped := source.1 result post member
  cases result with
  | error exception => exact ⟨stateMap post, rfl, mapped⟩
  | ok value => exact ⟨stateMap post, rfl, mapped⟩

end Zag.Lang.AutoCorres
