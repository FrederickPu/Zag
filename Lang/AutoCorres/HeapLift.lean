import Lang.AutoCorres.L2
import Lang.AutoCorres.ExecConcrete
import Lang.AutoCorres.TypHeapSimple

/-!
# Heap lifting

Corresponds only to [`tools/autocorres/HeapLift.thy`](https://github.com/seL4/l4v/blob/bc2599a59c43e673dca021b10b9841e9b8da4430/tools/autocorres/HeapLift.thy).

The local model has no C parser, UMM type descriptors, `c_type`, or
`packed_type` classes. `ValidStructField` therefore takes the parser's exact
layout-matching proposition as an explicit parameter and stores its proof.
No layout or field-address premise is inferred or discarded.
-/

namespace Zag.Lang.AutoCorres.HeapLift

open TypHeapSimple

universe u v w x y

variable {ConcreteState : Type u} {AbstractState : Type v}
variable {State : Type u} {View : Type v}
variable {Exception : Type w} {Value : Type x} {Return : Type y}
variable {Tag : Type u}

/-- The exact upstream `L2Tcorres` specialization of `CorresXF`. -/
def L2Tcorres {ConcreteState : Type u} {AbstractState : Type v}
    {Exception : Type w} {Result : Type x}
    (stateMap : ConcreteState → AbstractState)
    (abstract : L2.L2Program AbstractState Exception Result)
    (concrete : L2.L2Program ConcreteState Exception Result) : Prop :=
  CorresXF stateMap (fun result _ => result) (fun exception _ => exception)
    (fun _ => True) abstract concrete

theorem L2Tcorres_id
    (program : L2.L2Program State Exception Return) :
    L2Tcorres id program program := by
  exact CorresXF.refl (fun _ => True) program

/-- Heap lifting as an exact refinement between its closed L2 SSA endpoints. -/
def L2Tcorres.toSSA
    {ConcreteState AbstractState Exception Result : Type}
    [Repr (Except Exception Result)]
    {stateMap : ConcreteState → AbstractState}
    {abstract : L2.L2Program AbstractState Exception Result}
    {concrete : L2.L2Program ConcreteState Exception Result}
    (certificate : L2Tcorres stateMap abstract concrete) :
    SSABridge.Refinement (L2.toSSA concrete) (L2.toSSA abstract) :=
  SSABridge.Refinement.ofCorresXF stateMap (fun result _ => result)
    (fun exception _ => exception) (fun _ => True) certificate

/-- Identity heap lifting induces an identity refinement of the closed SSA endpoint. -/
def L2Tcorres.id_toSSA
    {State Exception Result : Type} [Repr (Except Exception Result)]
    (program : L2.L2Program State Exception Result) :
    SSABridge.Refinement (L2.toSSA program) (L2.toSSA program) :=
  (L2Tcorres_id program).toSSA

theorem L2Tcorres_fail
    (stateMap : ConcreteState → AbstractState)
    (concrete : L2.L2Program ConcreteState Exception Return) :
    L2Tcorres stateMap L2.fail concrete := by
  intro state hypothesis
  exact False.elim (hypothesis.2 (by simp [L2.fail]))

/-! ## Abstraction relations for inner expressions -/

/-- An abstract guard is strong enough to establish its concrete guard. -/
def abs_guard (stateMap : ConcreteState → AbstractState)
    (abstract : AbstractState → Prop) (concrete : ConcreteState → Prop) : Prop :=
  ∀ state, abstract (stateMap state) → concrete state

/-- Under an abstract precondition, concrete and abstract expressions agree. -/
def abs_expr (stateMap : ConcreteState → AbstractState)
    (precondition : AbstractState → Prop) (abstract : AbstractState → Value)
    (concrete : ConcreteState → Value) : Prop :=
  ∀ state, precondition (stateMap state) →
    concrete state = abstract (stateMap state)

/-- Under an abstract precondition, a concrete update commutes with abstraction. -/
def abs_modifies (stateMap : ConcreteState → AbstractState)
    (precondition : AbstractState → Prop)
    (abstract : AbstractState → AbstractState)
    (concrete : ConcreteState → ConcreteState) : Prop :=
  ∀ state, precondition (stateMap state) →
    stateMap (concrete state) = abstract (stateMap state)

/-- Parser-level expression rewriting, before changing state representations. -/
def struct_rewrite_guard (rewritten concrete : State → Prop) : Prop :=
  ∀ state, rewritten state → concrete state

/-- Parser-level value rewriting, before changing state representations. -/
def struct_rewrite_expr (precondition : State → Prop)
    (rewritten concrete : State → Value) : Prop :=
  ∀ state, precondition state → concrete state = rewritten state

/-- Parser-level update rewriting, before changing state representations. -/
def struct_rewrite_modifies (precondition : State → Prop)
    (rewritten concrete : State → State) : Prop :=
  ∀ state, precondition state → concrete state = rewritten state

theorem abs_expr_fun_app2 {Argument : Type y} {Output : Type w}
    {abstractF : AbstractState → Argument → Value → Output}
    {concreteF : ConcreteState → Argument → Value → Output}
    {abstractG : AbstractState → Argument → Value}
    {concreteG : ConcreteState → Argument → Value}
    {stateMap : ConcreteState → AbstractState} {P Q : AbstractState → Prop}
    (hf : abs_expr stateMap P abstractF concreteF)
    (hg : abs_expr stateMap Q abstractG concreteG) :
    abs_expr stateMap (fun state => P state ∧ Q state)
      (fun state argument => abstractF state argument (abstractG state argument))
      (fun state argument => concreteF state argument (concreteG state argument)) := by
  intro state hypothesis
  funext argument
  change concreteF state argument (concreteG state argument) =
    abstractF (stateMap state) argument (abstractG (stateMap state) argument)
  rw [hg state hypothesis.2, hf state hypothesis.1]

theorem abs_expr_fun_app {Input : Type y} {Output : Type w}
    {abstractB : AbstractState → Input} {concreteB : ConcreteState → Input}
    {abstractA : AbstractState → Input → Output}
    {concreteA : ConcreteState → Input → Output}
    {stateMap : ConcreteState → AbstractState} {X Y : AbstractState → Prop}
    (hb : abs_expr stateMap Y abstractB concreteB)
    (ha : abs_expr stateMap X abstractA concreteA) :
    abs_expr stateMap (fun state => X state ∧ Y state)
      (fun state => abstractA state (abstractB state))
      (fun state => concreteA state (concreteB state)) := by
  intro state hypothesis
  change concreteA state (concreteB state) =
    abstractA (stateMap state) (abstractB (stateMap state))
  rw [hb state hypothesis.2, ha state hypothesis.1]

theorem abs_expr_constant (value : Value) :
    abs_expr stateMap (fun _ => True) (fun _ => value) (fun _ => value) := by
  intro _ _
  rfl

theorem abs_guard_expr
    (expression : abs_expr stateMap P abstract concrete) :
    abs_guard stateMap (fun state => P state ∧ abstract state) concrete := by
  intro state hypothesis
  rw [expression state hypothesis.1]
  exact hypothesis.2

theorem abs_guard_constant (proposition : Prop) :
    abs_guard stateMap (fun _ => proposition) (fun _ => proposition) := by
  intro _ holds
  exact holds

theorem abs_guard_conj
    (left : abs_guard stateMap abstractLeft concreteLeft)
    (right : abs_guard stateMap abstractRight concreteRight) :
    abs_guard stateMap (fun state => abstractLeft state ∧ abstractRight state)
      (fun state => concreteLeft state ∧ concreteRight state) := by
  intro state hypothesis
  exact ⟨left state hypothesis.1, right state hypothesis.2⟩

@[simp] theorem mem_L2_modify {update : State → State}
    {result : Except Exception Unit} {state post : State} :
    (result, post) ∈ (L2.modify update state).results ↔
      result = .ok () ∧ post = update state := by
  unfold L2.modify
  rw [L2.mem_liftE_iff]
  constructor
  · rintro ⟨value, equality, member⟩
    rw [mem_modify] at member
    rcases member with ⟨rfl, rfl⟩
    exact ⟨equality, rfl⟩
  · rintro ⟨rfl, rfl⟩
    exact ⟨(), rfl, mem_modify.mpr ⟨rfl, rfl⟩⟩

@[simp] theorem failed_L2_modify {update : State → State} {state : State} :
    ¬ (L2.modify (Exception := Exception) update state).failed := by
  simp [L2.modify, liftE, bind, returnOk, pure, AutoCorres.modify]

@[simp] theorem mem_L2_gets {read : State → Value} {names : List String}
    {result : Except Exception Value} {state post : State} :
    (result, post) ∈ (L2.gets read names state).results ↔
      result = .ok (read state) ∧ post = state := by
  unfold L2.gets
  rw [L2.mem_liftE_iff]
  constructor
  · rintro ⟨value, equality, member⟩
    rw [mem_gets] at member
    rcases member with ⟨rfl, rfl⟩
    exact ⟨equality, rfl⟩
  · rintro ⟨resultEq, postEq⟩
    exact ⟨read state, resultEq, mem_gets.mpr ⟨rfl, postEq⟩⟩

@[simp] theorem failed_L2_gets {read : State → Value} {names : List String}
    {state : State} :
    ¬ (L2.gets (Exception := Exception) read names state).failed := by
  simp [L2.gets, liftE, bind, returnOk, pure, AutoCorres.gets]

@[simp] theorem mem_L2_guard {condition : State → Prop}
    {result : Except Exception Unit} {state post : State} :
    (result, post) ∈ (L2.guard condition state).results ↔
      condition state ∧ result = .ok () ∧ post = state := by
  unfold L2.guard
  rw [L2.mem_liftE_iff]
  constructor
  · rintro ⟨value, equality, member⟩
    rw [mem_guard] at member
    rcases member with ⟨holds, rfl, rfl⟩
    exact ⟨holds, equality, rfl⟩
  · rintro ⟨holds, rfl, rfl⟩
    exact ⟨(), rfl, mem_guard.mpr ⟨holds, rfl, rfl⟩⟩

@[simp] theorem failed_L2_guard {condition : State → Prop} {state : State} :
    (L2.guard (Exception := Exception) condition state).failed ↔
      ¬ condition state := by
  simp [L2.guard, liftE, bind, returnOk, pure, AutoCorres.guard]

@[simp] theorem mem_L2_guarded {condition : State → Prop}
    {next : Unit → L2.L2Program State Exception Value}
    {result : Except Exception Value} {state post : State} :
    (result, post) ∈ (L2.seq (L2.guard condition) next state).results ↔
      condition state ∧ (result, post) ∈ (next () state).results := by
  constructor
  · rintro ⟨sourceResult, middle, first, rest⟩
    rw [mem_L2_guard] at first
    rcases first with ⟨holds, rfl, rfl⟩
    exact ⟨holds, rest⟩
  · rintro ⟨holds, rest⟩
    exact ⟨Except.ok (), state, (mem_L2_guard.mpr ⟨holds, rfl, rfl⟩), rest⟩

@[simp] theorem failed_L2_guarded {condition : State → Prop}
    {next : Unit → L2.L2Program State Exception Value} {state : State} :
    (L2.seq (L2.guard condition) next state).failed ↔
      ¬ condition state ∨ (condition state ∧ (next () state).failed) := by
  constructor
  · rintro (failed | ⟨sourceResult, middle, first, rest⟩)
    · exact Or.inl ((failed_L2_guard.mp failed))
    · rw [mem_L2_guard] at first
      rcases first with ⟨holds, rfl, rfl⟩
      exact Or.inr ⟨holds, rest⟩
  · rintro (failed | ⟨holds, failed⟩)
    · exact Or.inl (failed_L2_guard.mpr failed)
    · exact Or.inr ⟨Except.ok (), state,
        mem_L2_guard.mpr ⟨holds, rfl, rfl⟩, failed⟩

/-! ## Principal correspondence rules -/

theorem L2Tcorres_modify
    {Exception : Type w}
    (rewrite : struct_rewrite_modifies P rewrittenUpdate concreteUpdate)
    (guardAbstracts : abs_guard stateMap abstractRewriteGuard P)
    (updateAbstracts : abs_modifies stateMap abstractUpdateGuard
      abstractUpdate rewrittenUpdate) :
    L2Tcorres (Exception := Exception) stateMap
      (L2.seq (L2.guard fun state =>
          abstractRewriteGuard state ∧ abstractUpdateGuard state)
        fun _ => L2.modify abstractUpdate)
      (L2.modify concreteUpdate) := by
  intro state hypothesis
  have guards : abstractRewriteGuard (stateMap state) ∧
      abstractUpdateGuard (stateMap state) := by
    apply Classical.byContradiction
    intro absent
    apply hypothesis.2
    exact failed_L2_guarded.mpr (Or.inl absent)
  have rewritten := rewrite state (guardAbstracts state guards.1)
  have mapped := updateAbstracts state guards.2
  refine ⟨?_, ?_⟩
  · intro result post member
    rw [mem_L2_modify] at member
    rcases member with ⟨rfl, rfl⟩
    apply mem_L2_guarded.mpr
    refine ⟨guards, mem_L2_modify.mpr ⟨rfl, ?_⟩⟩
    exact (congrArg stateMap rewritten).trans mapped
  · exact failed_L2_modify

theorem L2Tcorres_gets
    {Exception : Type w}
    (rewrite : struct_rewrite_expr P rewrittenExpr concreteExpr)
    (guardAbstracts : abs_guard stateMap abstractRewriteGuard P)
    (expressionAbstracts : abs_expr stateMap abstractExprGuard
      abstractExpr rewrittenExpr) :
    L2Tcorres (Exception := Exception) stateMap
      (L2.seq (L2.guard fun state =>
          abstractRewriteGuard state ∧ abstractExprGuard state)
        fun _ => L2.gets abstractExpr names)
      (L2.gets concreteExpr names) := by
  intro state hypothesis
  have guards : abstractRewriteGuard (stateMap state) ∧
      abstractExprGuard (stateMap state) := by
    apply Classical.byContradiction
    intro absent
    apply hypothesis.2
    exact failed_L2_guarded.mpr (Or.inl absent)
  have rewritten := rewrite state (guardAbstracts state guards.1)
  have valueEq := expressionAbstracts state guards.2
  refine ⟨?_, ?_⟩
  · intro result post member
    rw [mem_L2_gets] at member
    rcases member with ⟨rfl, rfl⟩
    apply mem_L2_guarded.mpr
    refine ⟨guards, mem_L2_gets.mpr ⟨?_, rfl⟩⟩
    exact congrArg Except.ok (rewritten.trans valueEq)
  · exact failed_L2_gets

theorem L2Tcorres_gets_const (stateMap : ConcreteState → AbstractState)
    (value : Value) (names : List String) (Exception : Type w) :
    L2Tcorres (Exception := Exception) stateMap (L2.gets (fun _ => value) names)
      (L2.gets (fun _ => value) names) := by
  intro state _
  refine ⟨?_, failed_L2_gets⟩
  intro result post member
  rw [mem_L2_gets] at member
  rcases member with ⟨rfl, rfl⟩
  exact mem_L2_gets.mpr ⟨rfl, rfl⟩

theorem L2Tcorres_guard
    {Exception : Type w}
    (rewrite : struct_rewrite_guard rewrittenGuard concreteGuard)
    (guardAbstracts : abs_guard stateMap abstractGuard rewrittenGuard) :
    L2Tcorres (Exception := Exception) stateMap
      (L2.guard abstractGuard) (L2.guard concreteGuard) := by
  intro state hypothesis
  have abstractHolds : abstractGuard (stateMap state) := by
    apply Classical.byContradiction
    intro absent
    exact hypothesis.2 (failed_L2_guard.mpr absent)
  have concreteHolds := rewrite state (guardAbstracts state abstractHolds)
  refine ⟨?_, fun failed => (failed_L2_guard.mp failed) concreteHolds⟩
  intro result post member
  rw [mem_L2_guard] at member
  rcases member with ⟨_, rfl, rfl⟩
  exact mem_L2_guard.mpr ⟨abstractHolds, rfl, rfl⟩

/-- Upstream `abs_spec`, including its nonfailure direction. -/
def abs_spec (stateMap : ConcreteState → AbstractState)
    (precondition : AbstractState → Prop)
    (abstract : Set (AbstractState × AbstractState))
    (concrete : Set (ConcreteState × ConcreteState)) : Prop :=
  (∀ source target, precondition (stateMap source) →
      (source, target) ∈ concrete →
      (stateMap source, stateMap target) ∈ abstract) ∧
  (∀ source, precondition (stateMap source) →
      (∃ target, (stateMap source, target) ∈ abstract) →
      ∃ target, (source, target) ∈ concrete)

theorem L2Tcorres_spec
    (specAbstracts : abs_spec stateMap precondition abstractRelation
      concreteRelation) :
    L2Tcorres stateMap
      (L2.seq (L2.guard precondition) fun _ =>
        L2.spec (Exception := Exception) (Value := Value) abstractRelation)
      (L2.spec concreteRelation) := by
  intro state hypothesis
  have preconditionHolds : precondition (stateMap state) := by
    apply Classical.byContradiction
    intro absent
    exact hypothesis.2 (failed_L2_guarded.mpr (Or.inl absent))
  have abstractSpecNoFail :
      ¬ (L2.spec (Exception := Exception) (Value := Value) abstractRelation
        (stateMap state)).failed := by
    intro failed
    exact hypothesis.2
      (failed_L2_guarded.mpr (Or.inr ⟨preconditionHolds, failed⟩))
  refine ⟨?_, ?_⟩
  · intro result post member
    rw [(L2.spec_behavior concreteRelation state).1] at member
    rcases member with ⟨related, value, resultEq⟩
    cases result with
    | error exception => cases resultEq
    | ok result =>
        have valueEq : result = value := Except.ok.inj resultEq
        apply mem_L2_guarded.mpr
        refine ⟨preconditionHolds, ?_⟩
        rw [(L2.spec_behavior abstractRelation (stateMap state)).1]
        exact ⟨specAbstracts.1 state post preconditionHolds related,
          value, congrArg Except.ok valueEq⟩
  · intro concreteFailed
    rw [(L2.spec_behavior concreteRelation state).2] at concreteFailed
    rw [(L2.spec_behavior abstractRelation (stateMap state)).2] at abstractSpecNoFail
    apply concreteFailed
    exact specAbstracts.2 state preconditionHolds
      (Classical.byContradiction abstractSpecNoFail)

theorem L2Tcorres_condition
    (leftCorres : L2Tcorres stateMap abstractLeft concreteLeft)
    (rightCorres : L2Tcorres stateMap abstractRight concreteRight)
    (rewrite : struct_rewrite_expr P rewrittenTest concreteTest)
    (guardAbstracts : abs_guard stateMap abstractRewriteGuard P)
    (testAbstracts : abs_expr stateMap abstractTestGuard abstractTest rewrittenTest) :
    L2Tcorres stateMap
      (L2.seq (L2.guard fun state =>
          abstractRewriteGuard state ∧ abstractTestGuard state)
        fun _ => L2.condition abstractTest abstractLeft abstractRight)
      (L2.condition concreteTest concreteLeft concreteRight) := by
  intro state hypothesis
  have guards : abstractRewriteGuard (stateMap state) ∧
      abstractTestGuard (stateMap state) := by
    apply Classical.byContradiction
    intro absent
    apply hypothesis.2
    exact failed_L2_guarded.mpr (Or.inl absent)
  have rewritten := rewrite state (guardAbstracts state guards.1)
  have testEq := (testAbstracts state guards.2).symm.trans rewritten.symm
  have conditionNoFail :
      ¬ (L2.condition abstractTest abstractLeft abstractRight
        (stateMap state)).failed := by
    intro failed
    exact hypothesis.2 (failed_L2_guarded.mpr (Or.inr ⟨guards, failed⟩))
  by_cases concreteHolds : concreteTest state
  · have abstractHolds : abstractTest (stateMap state) := by
      simpa [testEq] using concreteHolds
    have branch := leftCorres state ⟨True.intro, by
      simpa [L2.condition, abstractHolds] using conditionNoFail⟩
    refine ⟨?_, ?_⟩
    · intro result post member
      have sourceMember : (result, post) ∈ (concreteLeft state).results := by
        simpa [L2.condition, concreteHolds] using member
      exact mem_L2_guarded.mpr ⟨guards, by
        simpa [L2.condition, abstractHolds] using
          branch.1 result post sourceMember⟩
    · intro failed
      apply branch.2
      simpa [L2.condition, concreteHolds] using failed
  · have abstractDoesNotHold : ¬ abstractTest (stateMap state) := by
      simpa [testEq] using concreteHolds
    have branch := rightCorres state ⟨True.intro, by
      simpa [L2.condition, abstractDoesNotHold] using conditionNoFail⟩
    refine ⟨?_, ?_⟩
    · intro result post member
      have sourceMember : (result, post) ∈ (concreteRight state).results := by
        simpa [L2.condition, concreteHolds] using member
      exact mem_L2_guarded.mpr ⟨guards, by
        simpa [L2.condition, abstractDoesNotHold] using
          branch.1 result post sourceMember⟩
    · intro failed
      apply branch.2
      simpa [L2.condition, concreteHolds] using failed

theorem L2Tcorres_seq
    (firstCorres : L2Tcorres stateMap abstractFirst concreteFirst)
    (nextCorres : ∀ value, L2Tcorres stateMap (abstractNext value)
      (concreteNext value)) :
    L2Tcorres stateMap (L2.seq abstractFirst abstractNext)
      (L2.seq concreteFirst concreteNext) := by
  intro state hypothesis
  have firstNoFail : ¬ (abstractFirst (stateMap state)).failed := by
    intro failed
    exact hypothesis.2 (Or.inl failed)
  have firstRule := firstCorres state ⟨True.intro, firstNoFail⟩
  refine ⟨?_, ?_⟩
  · intro result post member
    rcases member with ⟨sourceResult, middle, sourceMember, continuationMember⟩
    cases sourceResult with
    | error exception =>
        have mapped := firstRule.1 (Except.error exception) middle sourceMember
        change (result, post) = (Except.error exception, middle) at continuationMember
        cases continuationMember
        exact ⟨Except.error exception, stateMap post, mapped, rfl⟩
    | ok value =>
        have mappedFirst := firstRule.1 (Except.ok value) middle sourceMember
        have nextNoFail : ¬ (abstractNext value (stateMap middle)).failed := by
          intro failed
          exact hypothesis.2 (Or.inr ⟨Except.ok value, stateMap middle,
            mappedFirst, failed⟩)
        have mappedNext := (nextCorres value) middle ⟨True.intro, nextNoFail⟩
        exact ⟨Except.ok value, stateMap middle, mappedFirst,
          mappedNext.1 result post continuationMember⟩
  · intro concreteFailed
    apply hypothesis.2
    rcases concreteFailed with concreteFailed |
        ⟨sourceResult, middle, sourceMember, failed⟩
    · exact False.elim (firstRule.2 concreteFailed)
    · cases sourceResult with
      | error exception => exact False.elim failed
      | ok value =>
          have mappedFirst := firstRule.1 (Except.ok value) middle sourceMember
          have nextNoFail : ¬ (abstractNext value (stateMap middle)).failed := by
            intro nextFailed
            exact hypothesis.2 (Or.inr ⟨Except.ok value, stateMap middle,
              mappedFirst, nextFailed⟩)
          exact (((nextCorres value) middle ⟨True.intro, nextNoFail⟩).2 failed).elim

theorem L2Tcorres_catch
    (bodyCorres : L2Tcorres stateMap abstractBody concreteBody)
    (handlerCorres : ∀ exception, L2Tcorres stateMap
      (abstractHandler exception) (concreteHandler exception)) :
    L2Tcorres stateMap (L2.catch abstractBody abstractHandler)
      (L2.catch concreteBody concreteHandler) := by
  intro state hypothesis
  have bodyNoFail : ¬ (abstractBody (stateMap state)).failed := by
    intro failed
    exact hypothesis.2 (Or.inl failed)
  have bodyRule := bodyCorres state ⟨True.intro, bodyNoFail⟩
  refine ⟨?_, ?_⟩
  · intro result post member
    rcases member with ⟨sourceResult, middle, sourceMember, continuationMember⟩
    cases sourceResult with
    | ok value =>
        have mapped := bodyRule.1 (Except.ok value) middle sourceMember
        change (result, post) = (Except.ok value, middle) at continuationMember
        cases continuationMember
        exact ⟨Except.ok value, stateMap post, mapped, rfl⟩
    | error exception =>
        have mappedBody := bodyRule.1 (Except.error exception) middle sourceMember
        have handlerNoFail :
            ¬ (abstractHandler exception (stateMap middle)).failed := by
          intro failed
          exact hypothesis.2 (Or.inr ⟨Except.error exception, stateMap middle,
            mappedBody, failed⟩)
        exact ⟨Except.error exception, stateMap middle, mappedBody,
          ((handlerCorres exception) middle ⟨True.intro, handlerNoFail⟩).1
            result post continuationMember⟩
  · intro concreteFailed
    apply hypothesis.2
    rcases concreteFailed with concreteFailed |
        ⟨sourceResult, middle, sourceMember, failed⟩
    · exact False.elim (bodyRule.2 concreteFailed)
    · cases sourceResult with
      | ok value => exact False.elim failed
      | error exception =>
          have mappedBody := bodyRule.1 (Except.error exception) middle sourceMember
          have handlerNoFail :
              ¬ (abstractHandler exception (stateMap middle)).failed := by
            intro handlerFailed
            exact hypothesis.2 (Or.inr ⟨Except.error exception, stateMap middle,
              mappedBody, handlerFailed⟩)
          exact (((handlerCorres exception) middle
            ⟨True.intro, handlerNoFail⟩).2 failed).elim

theorem L2Tcorres_seq_unused_result
    (left : L2Tcorres stateMap abstractLeft concreteLeft)
    (right : L2Tcorres stateMap abstractRight concreteRight) :
    L2Tcorres stateMap (L2.seq abstractLeft fun _ => abstractRight)
      (L2.seq concreteLeft fun _ => concreteRight) :=
  L2Tcorres_seq left fun _ => right

theorem abs_expr_id (expression : State → Value) :
    abs_expr id (fun _ => True) expression expression := by
  intro _ _
  rfl

theorem abs_expr_lambda_null
    {Argument : Type y}
    (expression : abs_expr stateMap P abstract concrete) :
    abs_expr stateMap P (fun state (_ : Argument) => abstract state)
      (fun state (_ : Argument) => concrete state) := by
  intro state hypothesis
  funext _
  exact expression state hypothesis

theorem abs_modify_id (update : State → State) :
    abs_modifies id (fun _ => True) update update := by
  intro _ _
  rfl

/-! ## Read/write and typed-heap validity -/

/-- The four exact upstream read/write lens laws. -/
structure ReadWriteValid (read : State → View)
    (write : (View → View) → State → State) : Prop where
  readWrite : ∀ (transform : View → View) (state : State),
    read (write transform state) = transform (read state)
  writeSame : ∀ (transform : View → View) (state : State),
    transform (read state) = read state →
    write transform state = state
  writeCongr : ∀ (left right : View → View) (state : State),
    left (read state) = right (read state) →
    write left state = write right state
  writeCompose : ∀ (outer inner : View → View) (state : State),
    write outer (write inner state) =
      write (fun value => outer (inner value)) state

theorem read_write_validI
    {read : State → View} {write : (View → View) → State → State}
    (readWrite : ∀ (transform : View → View) (state : State),
      read (write transform state) = transform (read state))
    (writeSame : ∀ (transform : View → View) (state : State),
      transform (read state) = read state →
      write transform state = state)
    (writeCongr : ∀ (left right : View → View) (state : State),
      left (read state) = right (read state) →
      write left state = write right state)
    (writeCompose : ∀ (outer inner : View → View) (state : State),
      write outer (write inner state) =
        write (fun value => outer (inner value)) state) :
    ReadWriteValid read write :=
  ⟨readWrite, writeSame, writeCongr, writeCompose⟩

theorem read_write_write_id
    {read : State → View} {write : (View → View) → State → State}
    (valid : ReadWriteValid read write) (state : State) :
    write (fun value => value) state = state :=
  valid.writeSame _ _ rfl

theorem read_write_valid_def1
    {read : State → View} {write : (View → View) → State → State}
    (valid : ReadWriteValid read write) (transform : View → View)
    (state : State) :
    read (write transform state) = transform (read state) :=
  valid.readWrite transform state

theorem read_write_valid_def2
    {read : State → View} {write : (View → View) → State → State}
    (valid : ReadWriteValid read write) (transform : View → View)
    (state : State)
    (same : transform (read state) = read state) :
    write transform state = state :=
  valid.writeSame transform state same

theorem read_write_valid_def3
    {read : State → View} {write : (View → View) → State → State}
    (valid : ReadWriteValid read write) (left right : View → View)
    (state : State)
    (equal : left (read state) = right (read state)) :
    write left state = write right state :=
  valid.writeCongr left right state equal

theorem read_write_o
    {read : State → View} {write : (View → View) → State → State}
    (valid : ReadWriteValid read write) (outer inner combined : View → View)
    (state : State)
    (pointwise : ∀ value, combined value = outer (inner value)) :
    write outer (write inner state) = write combined state := by
  rw [valid.writeCompose]
  apply valid.writeCongr
  exact (pointwise (read state)).symm

/-- Validity of a pointer entails the concrete C pointer guard. -/
def valid_implies_cguard (stateMap : ConcreteState → AbstractState)
    (valid : AbstractState → Ptr Value → Prop) (spec : TypeSpec Tag Value) : Prop :=
  ∀ state pointer, valid (stateMap state) pointer →
    spec.guard pointer.val = true

/-- Abstract reads decode the bytes of every valid concrete object. -/
def heap_decode_bytes (stateMap : ConcreteState → AbstractState)
    (valid : AbstractState → Ptr Value → Prop)
    (read : AbstractState → Ptr Value → Value)
    (rawRead : ConcreteState → HeapRawState Tag)
    (spec : TypeSpec Tag Value) : Prop :=
  ∀ state pointer, valid (stateMap state) pointer →
    read (stateMap state) pointer = hVal spec (rawRead state).mem pointer

/-- Concrete byte writes commute with abstract typed-map writes. -/
def heap_encode_bytes (stateMap : ConcreteState → AbstractState)
    (valid : AbstractState → Ptr Value → Prop)
    (write : ((Ptr Value → Value) → Ptr Value → Value) →
      AbstractState → AbstractState)
    (rawWrite : (HeapRawState Tag → HeapRawState Tag) →
      ConcreteState → ConcreteState)
    (spec : TypeSpec Tag Value) : Prop :=
  ∀ state pointer value, valid (stateMap state) pointer →
    stateMap (rawWrite (memUpdate (heapUpdate spec pointer value)) state) =
      write (fun heap => updateAt heap pointer value) (stateMap state)

/-- Typed writes preserve validity at every previously valid pointer. -/
def write_preserves_valid
    (valid : AbstractState → Ptr Value → Prop)
    (write : ((Ptr Value → Value) → Ptr Value → Value) →
      AbstractState → AbstractState) : Prop :=
  ∀ pointer transform state, valid state pointer →
    valid (write transform state) pointer

/--
The complete upstream `valid_typ_heap` certificate, specialized to the local
raw-byte and explicit-codec model.
-/
structure ValidTypedHeap (stateMap : ConcreteState → AbstractState)
    (read : AbstractState → Ptr Value → Value)
    (write : ((Ptr Value → Value) → Ptr Value → Value) →
      AbstractState → AbstractState)
    (validRead : AbstractState → Ptr Value → Prop)
    (validWrite : ((Ptr Value → Prop) → Ptr Value → Prop) →
      AbstractState → AbstractState)
    (rawRead : ConcreteState → HeapRawState Tag)
    (rawWrite : (HeapRawState Tag → HeapRawState Tag) →
      ConcreteState → ConcreteState)
    (spec : TypeSpec Tag Value) : Prop where
  heapReadWrite : ReadWriteValid read write
  validReadWrite : ReadWriteValid validRead validWrite
  rawReadWrite : ReadWriteValid rawRead rawWrite
  validImpliesGuard : valid_implies_cguard stateMap validRead spec
  decodeBytes : heap_decode_bytes stateMap validRead read rawRead spec
  encodeBytes : heap_encode_bytes stateMap validRead write rawWrite spec
  writePreservesValid : write_preserves_valid validRead write

theorem valid_typ_heapI
    {stateMap : ConcreteState → AbstractState}
    {read : AbstractState → Ptr Value → Value}
    {write : ((Ptr Value → Value) → Ptr Value → Value) →
      AbstractState → AbstractState}
    {validRead : AbstractState → Ptr Value → Prop}
    {validWrite : ((Ptr Value → Prop) → Ptr Value → Prop) →
      AbstractState → AbstractState}
    {rawRead : ConcreteState → HeapRawState Tag}
    {rawWrite : (HeapRawState Tag → HeapRawState Tag) →
      ConcreteState → ConcreteState}
    {typeSpec : TypeSpec Tag Value}
    (heapReadWrite : ReadWriteValid read write)
    (validReadWrite : ReadWriteValid validRead validWrite)
    (rawReadWrite : ReadWriteValid rawRead rawWrite)
    (validImpliesGuard : valid_implies_cguard stateMap validRead typeSpec)
    (decodeBytes : heap_decode_bytes stateMap validRead read rawRead typeSpec)
    (encodeBytes : heap_encode_bytes stateMap validRead write rawWrite typeSpec)
    (writePreservesValid : write_preserves_valid validRead write) :
    ValidTypedHeap stateMap read write validRead validWrite rawRead rawWrite typeSpec :=
  ⟨heapReadWrite, validReadWrite, rawReadWrite, validImpliesGuard,
    decodeBytes, encodeBytes, writePreservesValid⟩

/-!
`ParserLayout` is deliberately a proposition parameter. In generated C theory
it is instantiated by the unavailable equality between `field_ti` and
`adjust_ti`, including the field path and adjusted getter/setter descriptor.
-/
structure ValidStructField
    (parserLayout : TypeSpec Tag Parent → List String → TypeSpec Tag Field →
      (Parent → Field) →
      ((Field → Field) → Parent → Parent) →
      (Ptr Parent → Ptr Field) → Prop)
    (parentSpec : TypeSpec Tag Parent) (fieldName : List String)
    (fieldSpec : TypeSpec Tag Field) (fieldGet : Parent → Field)
    (fieldSet : (Field → Field) → Parent → Parent)
    (fieldAddress : Ptr Parent → Ptr Field)
    (rawRead : ConcreteState → HeapRawState Tag)
    (rawWrite : (HeapRawState Tag → HeapRawState Tag) →
      ConcreteState → ConcreteState) : Prop where
  fieldReadWrite : ReadWriteValid fieldGet fieldSet
  parserLayoutMatches : parserLayout parentSpec fieldName fieldSpec
    fieldGet fieldSet fieldAddress
  guardPreserved : ∀ pointer, parentSpec.guard pointer.val = true →
    fieldSpec.guard (fieldAddress pointer).val = true
  rawReadWrite : ReadWriteValid rawRead rawWrite

/-- The four direct laws used upstream for non-packed legacy fields. -/
structure ValidStructFieldLegacy
    (stateMap : ConcreteState → AbstractState)
    (fieldName : List String) (fieldGet : Parent → Field)
    (fieldSet : Field → Parent → Parent)
    (fieldAddress : List String → Ptr Parent → Ptr Field)
    (read : AbstractState → Ptr Parent → Parent)
    (write : ((Ptr Parent → Parent) → Ptr Parent → Parent) →
      AbstractState → AbstractState)
    (validRead : AbstractState → Ptr Parent → Prop)
    (_validWrite : ((Ptr Parent → Prop) → Ptr Parent → Prop) →
      AbstractState → AbstractState)
    (rawRead : ConcreteState → HeapRawState Tag)
    (rawWrite : (HeapRawState Tag → HeapRawState Tag) →
      ConcreteState → ConcreteState)
    (parentSpec : TypeSpec Tag Parent) (fieldSpec : TypeSpec Tag Field) : Prop where
  fieldDecode : ∀ state pointer, validRead (stateMap state) pointer →
    hVal fieldSpec (rawRead state).mem (fieldAddress fieldName pointer) =
      fieldGet (read (stateMap state) pointer)
  fieldEncode : ∀ state pointer value, validRead (stateMap state) pointer →
    stateMap (rawWrite
      (memUpdate (heapUpdate fieldSpec (fieldAddress fieldName pointer) value)) state) =
      write (fun heap => updateAt heap pointer
        (fieldSet value (heap pointer))) (stateMap state)
  parentSafe : ∀ state pointer, validRead (stateMap state) pointer →
    parentSpec.guard pointer.val = true
  fieldSafe : ∀ pointer, parentSpec.guard pointer.val = true →
    fieldSpec.guard (fieldAddress fieldName pointer).val = true

theorem valid_typ_heap_get_hvalD
    {stateMap : ConcreteState → AbstractState}
    {read : AbstractState → Ptr Value → Value}
    {write : ((Ptr Value → Value) → Ptr Value → Value) →
      AbstractState → AbstractState}
    {validRead : AbstractState → Ptr Value → Prop}
    {validWrite : ((Ptr Value → Prop) → Ptr Value → Prop) →
      AbstractState → AbstractState}
    {rawRead : ConcreteState → HeapRawState Tag}
    {rawWrite : (HeapRawState Tag → HeapRawState Tag) →
      ConcreteState → ConcreteState}
    {typeSpec : TypeSpec Tag Value} {state : ConcreteState}
    {pointer : Ptr Value}
    (valid : ValidTypedHeap stateMap read write validRead validWrite
      rawRead rawWrite typeSpec)
    (pointerValid : validRead (stateMap state) pointer) :
    hVal typeSpec (rawRead state).mem pointer = read (stateMap state) pointer :=
  (valid.decodeBytes state pointer pointerValid).symm

theorem valid_typ_heap_raw_updateD
    {stateMap : ConcreteState → AbstractState}
    {read : AbstractState → Ptr Value → Value}
    {write : ((Ptr Value → Value) → Ptr Value → Value) →
      AbstractState → AbstractState}
    {validRead : AbstractState → Ptr Value → Prop}
    {validWrite : ((Ptr Value → Prop) → Ptr Value → Prop) →
      AbstractState → AbstractState}
    {rawRead : ConcreteState → HeapRawState Tag}
    {rawWrite : (HeapRawState Tag → HeapRawState Tag) →
      ConcreteState → ConcreteState}
    {typeSpec : TypeSpec Tag Value} {state : ConcreteState}
    {pointer : Ptr Value} {value : Value}
    (valid : ValidTypedHeap stateMap read write validRead validWrite
      rawRead rawWrite typeSpec)
    (pointerValid : validRead (stateMap state) pointer) :
    stateMap (rawWrite (memUpdate (heapUpdate typeSpec pointer value)) state) =
      write (fun heap => updateAt heap pointer value) (stateMap state) :=
  valid.encodeBytes state pointer value pointerValid

theorem heap_abs_expr_guard
    {stateMap : ConcreteState → AbstractState}
    {read : AbstractState → Ptr Value → Value}
    {write : ((Ptr Value → Value) → Ptr Value → Value) →
      AbstractState → AbstractState}
    {validRead : AbstractState → Ptr Value → Prop}
    {validWrite : ((Ptr Value → Prop) → Ptr Value → Prop) →
      AbstractState → AbstractState}
    {rawRead : ConcreteState → HeapRawState Tag}
    {rawWrite : (HeapRawState Tag → HeapRawState Tag) →
      ConcreteState → ConcreteState}
    {typeSpec : TypeSpec Tag Value} {P : AbstractState → Prop}
    {abstractPointer : AbstractState → Ptr Value}
    {concretePointer : ConcreteState → Ptr Value}
    (valid : ValidTypedHeap stateMap read write validRead validWrite
      rawRead rawWrite typeSpec)
    (pointerAbstracts : abs_expr stateMap P abstractPointer concretePointer) :
    abs_guard stateMap
      (fun state => P state ∧ validRead state (abstractPointer state))
      (fun state => typeSpec.guard (concretePointer state).val = true) := by
  intro state hypothesis
  rw [pointerAbstracts state hypothesis.1]
  exact valid.validImpliesGuard state (abstractPointer (stateMap state)) hypothesis.2

theorem heap_abs_expr_h_val
    {stateMap : ConcreteState → AbstractState}
    {read : AbstractState → Ptr Value → Value}
    {write : ((Ptr Value → Value) → Ptr Value → Value) →
      AbstractState → AbstractState}
    {validRead : AbstractState → Ptr Value → Prop}
    {validWrite : ((Ptr Value → Prop) → Ptr Value → Prop) →
      AbstractState → AbstractState}
    {rawRead : ConcreteState → HeapRawState Tag}
    {rawWrite : (HeapRawState Tag → HeapRawState Tag) →
      ConcreteState → ConcreteState}
    {typeSpec : TypeSpec Tag Value} {P : AbstractState → Prop}
    {abstractPointer : AbstractState → Ptr Value}
    {concretePointer : ConcreteState → Ptr Value}
    (valid : ValidTypedHeap stateMap read write validRead validWrite
      rawRead rawWrite typeSpec)
    (pointerAbstracts : abs_expr stateMap P abstractPointer concretePointer) :
    abs_expr stateMap
      (fun state => P state ∧ validRead state (abstractPointer state))
      (fun state => read state (abstractPointer state))
      (fun state => hVal typeSpec (rawRead state).mem (concretePointer state)) := by
  intro state hypothesis
  change hVal typeSpec (rawRead state).mem (concretePointer state) =
    read (stateMap state) (abstractPointer (stateMap state))
  rw [pointerAbstracts state hypothesis.1]
  exact valid.decodeBytes state (abstractPointer (stateMap state)) hypothesis.2 |>.symm

theorem heap_abs_modifies_heap_update
    {stateMap : ConcreteState → AbstractState}
    {read : AbstractState → Ptr Value → Value}
    {write : ((Ptr Value → Value) → Ptr Value → Value) →
      AbstractState → AbstractState}
    {validRead : AbstractState → Ptr Value → Prop}
    {validWrite : ((Ptr Value → Prop) → Ptr Value → Prop) →
      AbstractState → AbstractState}
    {rawRead : ConcreteState → HeapRawState Tag}
    {rawWrite : (HeapRawState Tag → HeapRawState Tag) →
      ConcreteState → ConcreteState}
    {typeSpec : TypeSpec Tag Value}
    {pointerPre valuePre : AbstractState → Prop}
    {abstractPointer : AbstractState → Ptr Value}
    {concretePointer : ConcreteState → Ptr Value}
    {abstractValue : AbstractState → Value}
    {concreteValue : ConcreteState → Value}
    (valid : ValidTypedHeap stateMap read write validRead validWrite
      rawRead rawWrite typeSpec)
    (pointerAbstracts : abs_expr stateMap pointerPre abstractPointer concretePointer)
    (valueAbstracts : abs_expr stateMap valuePre abstractValue concreteValue) :
    abs_modifies stateMap
      (fun state => pointerPre state ∧ valuePre state ∧
        validRead state (abstractPointer state))
      (fun state => write (fun heap => updateAt heap (abstractPointer state)
        (abstractValue state)) state)
      (fun state => rawWrite
        (memUpdate (heapUpdate typeSpec (concretePointer state)
          (concreteValue state))) state) := by
  intro state hypothesis
  change stateMap (rawWrite
      (memUpdate (heapUpdate typeSpec (concretePointer state)
        (concreteValue state))) state) =
    write (fun heap => updateAt heap (abstractPointer (stateMap state))
      (abstractValue (stateMap state))) (stateMap state)
  rw [pointerAbstracts state hypothesis.1, valueAbstracts state hypothesis.2.1]
  exact valid.encodeBytes state (abstractPointer (stateMap state))
    (abstractValue (stateMap state)) hypothesis.2.2

theorem struct_rewrite_guard_expr
    (expression : struct_rewrite_expr P rewritten concrete) :
    struct_rewrite_guard (fun state => P state ∧ rewritten state) concrete := by
  intro state hypothesis
  rw [expression state hypothesis.1]
  exact hypothesis.2

theorem struct_rewrite_guard_constant (proposition : Prop) :
    struct_rewrite_guard (State := State)
      (fun _ => proposition) (fun _ => proposition) := by
  intro _ holds
  exact holds

theorem struct_rewrite_guard_conj
    (right : struct_rewrite_guard rewrittenRight concreteRight)
    (left : struct_rewrite_guard rewrittenLeft concreteLeft) :
    struct_rewrite_guard
      (fun state => rewrittenLeft state ∧ rewrittenRight state)
      (fun state => concreteLeft state ∧ concreteRight state) := by
  intro state hypothesis
  exact ⟨left state hypothesis.1, right state hypothesis.2⟩

theorem struct_rewrite_expr_id (expression : State → Value) :
    struct_rewrite_expr (fun _ => True) expression expression := by
  intro _ _
  rfl

theorem struct_rewrite_expr_fun_app2 {Argument : Type y} {Output : Type w}
    {rewrittenF concreteF : State → Argument → Value → Output}
    {rewrittenG concreteG : State → Argument → Value}
    {P Q : State → Prop}
    (hf : struct_rewrite_expr P rewrittenF concreteF)
    (hg : struct_rewrite_expr Q rewrittenG concreteG) :
    struct_rewrite_expr (fun state => P state ∧ Q state)
      (fun state argument => rewrittenF state argument (rewrittenG state argument))
      (fun state argument => concreteF state argument (concreteG state argument)) := by
  intro state hypothesis
  funext argument
  change concreteF state argument (concreteG state argument) =
    rewrittenF state argument (rewrittenG state argument)
  rw [hg state hypothesis.2, hf state hypothesis.1]

theorem struct_rewrite_expr_fun_app {Input : Type y} {Output : Type w}
    {rewrittenB concreteB : State → Input}
    {rewrittenA concreteA : State → Input → Output}
    {X Y : State → Prop}
    (hb : struct_rewrite_expr Y rewrittenB concreteB)
    (ha : struct_rewrite_expr X rewrittenA concreteA) :
    struct_rewrite_expr (fun state => X state ∧ Y state)
      (fun state => rewrittenA state (rewrittenB state))
      (fun state => concreteA state (concreteB state)) := by
  intro state hypothesis
  change concreteA state (concreteB state) =
    rewrittenA state (rewrittenB state)
  rw [hb state hypothesis.2, ha state hypothesis.1]

theorem struct_rewrite_expr_constant (value : Value) :
    struct_rewrite_expr (State := State)
      (fun _ => True) (fun _ => value) (fun _ => value) := by
  intro _ _
  rfl

theorem struct_rewrite_expr_lambda_null
    {Argument : Type y}
    (expression : struct_rewrite_expr P rewritten concrete) :
    struct_rewrite_expr P (fun state (_ : Argument) => rewritten state)
      (fun state (_ : Argument) => concrete state) := by
  intro state hypothesis
  funext _
  exact expression state hypothesis

theorem struct_rewrite_modifies_id (update : State → State) :
    struct_rewrite_modifies (fun _ => True) update update := by
  intro _ _
  rfl

/-! ## Certified conversion kernel interface -/

namespace Kernel

/-- Compatibility alias for the canonical L2 syntax consumed by heap lifting. -/
abbrev Source (State : Type u) (Exception : Type v) (Result : Type) :=
  L2.Syntax State Exception Result

namespace Source

export L2.Syntax
  (gets modify guard condition seq «catch» spec unknown throw fail «while»)

/-- Compatibility name for the canonical L2 denotation. -/
noncomputable abbrev denote {State : Type u} {Exception : Type v}
    {Result : Type} :
    Source State Exception Result -> L2.L2Program State Exception Result :=
  L2.Syntax.denote

end Source

/--
Target syntax records generated guards rather than hiding them in an arbitrary
program leaf. The two guards on expressions and updates remain separate data
and are conjoined only by denotation, exactly as in the principal rules.
-/
inductive Target (State : Type u) (Exception : Type v) :
    Type -> Type (max (u + 1) (v + 1)) where
  | guardedGets {Result : Type} (rewriteGuard expressionGuard : State -> Prop)
      (read : State -> Result) (names : List String) : Target State Exception Result
  | guardedModify (rewriteGuard updateGuard : State -> Prop)
      (update : State -> State) : Target State Exception Unit
  | guard (condition : State -> Prop) : Target State Exception Unit
  | guardedCondition {Result : Type}
      (rewriteGuard testGuard : State -> Prop) (test : State -> Prop)
      (thenBranch elseBranch : Target State Exception Result) :
      Target State Exception Result
  | seq {First Result : Type} (first : Target State Exception First)
      (next : First -> Target State Exception Result) : Target State Exception Result
  | «catch» {Result : Type} (body : Target State Exception Result)
      (handler : Exception -> Target State Exception Result) :
      Target State Exception Result
  | guardedSpec {Result : Type} (precondition : State -> Prop)
      (relation : Set (State × State)) : Target State Exception Result
  | unknown {Result : Type} (names : List String) : Target State Exception Result
  | throw {Result : Type} (exception : Exception) (names : List String) :
      Target State Exception Result
  | fail {Result : Type} : Target State Exception Result

/-- Target denotation is kept separate from the computable syntax conversion. -/
noncomputable def Target.denote {State : Type u} {Exception : Type v}
    {Result : Type} :
    Target State Exception Result -> L2.L2Program State Exception Result
  | .guardedGets rewriteGuard expressionGuard read names =>
      L2.seq (L2.guard fun state => rewriteGuard state ∧ expressionGuard state)
        fun _ => L2.gets read names
  | .guardedModify rewriteGuard updateGuard update =>
      L2.seq (L2.guard fun state => rewriteGuard state ∧ updateGuard state)
        fun _ => L2.modify update
  | .guard condition => L2.guard condition
  | .guardedCondition rewriteGuard testGuard test thenBranch elseBranch =>
      L2.seq (L2.guard fun state => rewriteGuard state ∧ testGuard state)
        fun _ => L2.condition test thenBranch.denote elseBranch.denote
  | .seq first next => L2.seq first.denote fun value => (next value).denote
  | .catch body handler => L2.catch body.denote fun exception =>
      (handler exception).denote
  | .guardedSpec precondition relation =>
      L2.seq (L2.guard precondition) fun _ => L2.spec relation
  | .unknown names => L2.unknown names
  | .throw exception names => L2.throw exception names
  | .fail => L2.fail

/-- All three premises needed to heap-lift one concrete value expression. -/
structure ExprEvidence {Value : Type} (stateMap : ConcreteState -> AbstractState)
    (concrete : ConcreteState -> Value) where
  rewritePrecondition : ConcreteState -> Prop
  rewritten : ConcreteState -> Value
  abstractRewriteGuard : AbstractState -> Prop
  abstractExpressionGuard : AbstractState -> Prop
  abstract : AbstractState -> Value
  rewrite : struct_rewrite_expr rewritePrecondition rewritten concrete
  rewriteGuardAbstracts : abs_guard stateMap abstractRewriteGuard rewritePrecondition
  expressionAbstracts : abs_expr stateMap abstractExpressionGuard abstract rewritten

/-- All three premises needed to heap-lift one concrete state update. -/
structure UpdateEvidence (stateMap : ConcreteState -> AbstractState)
    (concrete : ConcreteState -> ConcreteState) where
  rewritePrecondition : ConcreteState -> Prop
  rewritten : ConcreteState -> ConcreteState
  abstractRewriteGuard : AbstractState -> Prop
  abstractUpdateGuard : AbstractState -> Prop
  abstract : AbstractState -> AbstractState
  rewrite : struct_rewrite_modifies rewritePrecondition rewritten concrete
  rewriteGuardAbstracts : abs_guard stateMap abstractRewriteGuard rewritePrecondition
  updateAbstracts : abs_modifies stateMap abstractUpdateGuard abstract rewritten

/-- The parser rewrite and abstraction premise for one concrete guard. -/
structure GuardEvidence (stateMap : ConcreteState -> AbstractState)
    (concrete : ConcreteState -> Prop) where
  rewritten : ConcreteState -> Prop
  abstract : AbstractState -> Prop
  rewrite : struct_rewrite_guard rewritten concrete
  guardAbstracts : abs_guard stateMap abstract rewritten

/--
The exact `abs_spec` premise for a concrete specification. The current theory
has no separate `struct_rewrite_spec` premise, so none is fabricated here.
-/
structure SpecEvidence (stateMap : ConcreteState -> AbstractState)
    (concrete : Set (ConcreteState × ConcreteState)) where
  precondition : AbstractState -> Prop
  abstract : Set (AbstractState × AbstractState)
  specificationAbstracts : abs_spec stateMap precondition abstract concrete

/-- A source is supported only when every primitive and child has exact evidence. -/
inductive Supported {ConcreteState : Type u} {AbstractState : Type v}
    {Exception : Type w} (stateMap : ConcreteState -> AbstractState) :
    {Result : Type} -> Source ConcreteState Exception Result ->
      Type (max (u + 1) (max (v + 1) (w + 1))) where
  | gets {Result : Type} {read : ConcreteState -> Result} (names : List String)
      (evidence : ExprEvidence stateMap read) : Supported stateMap (.gets read names)
  | modify {update : ConcreteState -> ConcreteState}
      (evidence : UpdateEvidence stateMap update) : Supported stateMap (.modify update)
  | guard {condition : ConcreteState -> Prop}
      (evidence : GuardEvidence stateMap condition) : Supported stateMap (.guard condition)
  | condition {Result : Type} {test : ConcreteState -> Prop}
      {thenBranch elseBranch : Source ConcreteState Exception Result}
      (testEvidence : ExprEvidence stateMap test)
      (thenSupported : Supported stateMap thenBranch)
      (elseSupported : Supported stateMap elseBranch) :
      Supported stateMap (.condition test thenBranch elseBranch)
  | seq {First Result : Type} {first : Source ConcreteState Exception First}
      {next : First -> Source ConcreteState Exception Result}
      (firstSupported : Supported stateMap first)
      (nextSupported : (value : First) -> Supported stateMap (next value)) :
      Supported stateMap (.seq first next)
  | «catch» {Result : Type} {body : Source ConcreteState Exception Result}
      {handler : Exception -> Source ConcreteState Exception Result}
      (bodySupported : Supported stateMap body)
      (handlerSupported : (exception : Exception) -> Supported stateMap (handler exception)) :
      Supported stateMap (.catch body handler)
  | spec {Result : Type} {relation : Set (ConcreteState × ConcreteState)}
      (evidence : SpecEvidence stateMap relation) : Supported stateMap (.spec relation)
  | unknown {Result : Type} (names : List String) :
      Supported stateMap (.unknown names)
  | throw {Result : Type} (exception : Exception) (names : List String) :
      Supported stateMap (.throw exception names)
  | fail {Result : Type} : Supported stateMap .fail

/-- The generated target paired with the exact `L2Tcorres` theorem. -/
structure Certificate {Result : Type} (stateMap : ConcreteState -> AbstractState)
    (source : Source ConcreteState Exception Result) where
  target : Target AbstractState Exception Result
  correctness : L2Tcorres stateMap target.denote source.denote

/-- The dependent implementation hole filled by the ML transform. -/
abbrev Challenge {ConcreteState : Type u} {AbstractState : Type v}
    {Exception : Type w} (stateMap : ConcreteState -> AbstractState) :
    Type (max (u + 1) (max (v + 1) (w + 1))) :=
  {Result : Type} -> {source : Source ConcreteState Exception Result} ->
    Supported stateMap source -> Certificate stateMap source

end Kernel

end Zag.Lang.AutoCorres.HeapLift
