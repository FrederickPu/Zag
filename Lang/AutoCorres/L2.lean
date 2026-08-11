import Lang.AutoCorres.CorresXF
import Lang.AutoCorres.L1

/-!
# AutoCorres 1 L2 definitions

Corresponds to [`tools/autocorres/L2Defs.thy`](https://github.com/seL4/l4v/blob/bc2599a59c43e673dca021b10b9841e9b8da4430/tools/autocorres/L2Defs.thy).

The string lists retained by some combinators are source-variable metadata and
have no effect on execution.  This module defines their semantics and the
correspondence predicate used by local-variable extraction; it does not
implement the extraction translator itself.
-/

namespace Zag.Lang.AutoCorres.L2

universe u v w x

/-- AutoCorres 1's exception-aware L2 nondeterministic state program. -/
abbrev L2Program (State : Type u) (Exception : Type v) (Result : Type w) :=
  Nondet State (Except Exception Result)

/-- Return an arbitrary value.  Names are retained only as source metadata. -/
def unknown (_names : List String) : L2Program State Exception Value :=
  liftE (select fun _ => True)

/-- Sequence normal results and propagate exceptions. -/
def seq (first : L2Program State Exception α)
    (next : α → L2Program State Exception β) : L2Program State Exception β :=
  bindE first next

/-- Update the L2 state. -/
def modify (update : State → State) : L2Program State Exception Unit :=
  liftE (AutoCorres.modify update)

/-- Read a value from the L2 state.  Names are retained only as source metadata. -/
def gets (read : State → Value) (_names : List String) : L2Program State Exception Value :=
  liftE (AutoCorres.gets read)

/-- Select a branch from a predicate on the current state. -/
noncomputable def condition (predicate : State → Prop)
    (thenProgram elseProgram : L2Program State Exception Value) :
    L2Program State Exception Value := by
  classical
  exact fun state => if predicate state then thenProgram state else elseProgram state

/-- Handle exceptional results, possibly changing the exception type. -/
def «catch» (program : L2Program State Exception Value)
    (handler : Exception → L2Program State NewException Value) :
    L2Program State NewException Value :=
  handle program handler

/-- Exception-aware L2 loop.  Names are retained only as source metadata. -/
def «while» (test : Value → State → Prop)
    (body : Value → L2Program State Exception Value) (initial : Value)
    (_names : List String) : L2Program State Exception Value :=
  whileLoopE test body initial

/-- Return an exceptional value.  Names are retained only as source metadata. -/
def throw (exception : Exception) (_names : List String) :
    L2Program State Exception Value :=
  AutoCorres.throw exception

/--
Choose a related post-state and then an arbitrary result, exactly as upstream
`L2_spec r = liftE (spec r >>= (\<lambda>_. select UNIV))`.
-/
def spec (relation : Set (State × State)) : L2Program State Exception Value :=
  liftE (bind (AutoCorres.spec relation) fun _ => select fun _ => True)

/-- Fail unless the state satisfies the predicate. -/
def guard (predicate : State → Prop) : L2Program State Exception Unit :=
  liftE (AutoCorres.guard predicate)

/-- Unconditional monadic failure. -/
def fail : L2Program State Exception Value :=
  AutoCorres.fail

/-- Keep normal returns and turn every exception branch into failure. -/
def «call» (program : L2Program State InnerException Value) :
    L2Program State Exception Value :=
  handle program fun _ => (AutoCorres.fail : L2Program State Exception Value)

/-- Fail when the recursion measure is zero; otherwise execute the body. -/
noncomputable def recguard (measure : Nat) (body : L2Program State Exception Value) :
    L2Program State Exception Value :=
  condition (fun _ => measure = 0) fail body

/-- Return unit without changing state. -/
def skip : L2Program State Exception Unit :=
  gets (fun _ => ()) []

/-! ## Canonical reified L2 syntax -/

/--
The shared typed L2 syntax produced by local-variable extraction and consumed by
heap lifting. Its result index makes dependent sequencing and exception
handlers explicit without changing the existing L2 denotation.
-/
inductive Syntax (State : Type u) (Exception : Type v) :
    Type -> Type (max (u + 1) (v + 1)) where
  | gets {Result : Type} (read : State -> Result) (names : List String) :
      Syntax State Exception Result
  | modify (update : State -> State) : Syntax State Exception Unit
  | guard (predicate : State -> Prop) : Syntax State Exception Unit
  | condition {Result : Type} (test : State -> Prop)
      (thenBranch elseBranch : Syntax State Exception Result) :
      Syntax State Exception Result
  | seq {First Result : Type} (first : Syntax State Exception First)
      (next : First -> Syntax State Exception Result) :
      Syntax State Exception Result
  | «catch» {Result : Type} (body : Syntax State Exception Result)
      (handler : Exception -> Syntax State Exception Result) :
      Syntax State Exception Result
  | spec {Result : Type} (relation : Set (State × State)) :
      Syntax State Exception Result
  | unknown {Result : Type} (names : List String) :
      Syntax State Exception Result
  | throw {Result : Type} (exception : Exception) (names : List String) :
      Syntax State Exception Result
  | fail {Result : Type} : Syntax State Exception Result
  | «while» {Result : Type} (test : Result -> State -> Prop)
      (body : Result -> Syntax State Exception Result) (initial : Result)
      (names : List String) : Syntax State Exception Result
  /-- A statically resolved procedure body. Exception behavior is preserved. -/
  | «call» {Result : Type} (body : Syntax State Exception Result) :
      Syntax State Exception Result

/-- Interpret canonical syntax with the existing L2 combinator semantics. -/
@[simp] noncomputable def Syntax.denote {Result : Type} :
    Syntax State Exception Result -> L2Program State Exception Result
  | .gets read names => L2.gets read names
  | .modify update => L2.modify update
  | .guard predicate => L2.guard predicate
  | .condition test thenBranch elseBranch =>
      L2.condition test thenBranch.denote elseBranch.denote
  | .seq first next => L2.seq first.denote fun value => (next value).denote
  | .catch body handler => L2.catch body.denote fun exception =>
      (handler exception).denote
  | .spec relation => L2.spec relation
  | .unknown names => L2.unknown names
  | .throw exception names => L2.throw exception names
  | .fail => L2.fail
  | .while test body initial names =>
      L2.while test (fun value => (body value).denote) initial names
  | .call body => body.denote

@[simp] theorem mem_liftE_iff {program : Nondet State Value}
    {state post : State} {result : Except Exception Value} :
    (result, post) ∈ (liftE program state).results ↔
      ∃ value, result = Except.ok value ∧ (value, post) ∈ (program state).results := by
  cases result with
  | error exception =>
      constructor
      · rintro ⟨value, middle, member, continuation⟩
        change (Except.error exception, post) = (Except.ok value, middle) at continuation
        cases continuation
      · rintro ⟨value, equality, _⟩
        cases equality
  | ok result =>
      constructor
      · rintro ⟨value, middle, member, continuation⟩
        change (Except.ok result, post) = (Except.ok value, middle) at continuation
        cases continuation
        exact ⟨result, rfl, member⟩
      · rintro ⟨value, equality, member⟩
        cases equality
        exact ⟨result, post, member, rfl⟩

@[simp] theorem failed_liftE {program : Nondet State Value} {state : State} :
    (liftE (ε := Exception) program state).failed ↔ (program state).failed := by
  simp [liftE, bind, returnOk, pure]

/-! ## L2/L1 correspondence -/

/--
The exact upstream `L2corres` specialization of `CorresXF`.  L1 reports only
unit normal/exceptional markers; the L2 value is extracted from the concrete
L1 final state.
-/
def L2Corres {ConcreteState : Type u} {State : Type v}
    {Exception : Type w} {Value : Type x}
    (stateProject : ConcreteState → State)
    (returnExtract : ConcreteState → Value)
    (exceptionExtract : ConcreteState → Exception)
    (precondition : ConcreteState → Prop)
    (abstract : L2Program State Exception Value)
    (concrete : L1.L1Program ConcreteState) : Prop :=
  CorresXF stateProject (fun _ state => returnExtract state)
    (fun _ state => exceptionExtract state) precondition abstract concrete

/-- Reading an extracted value corresponds to an L1 skip. -/
theorem corres_gets_skip
    {stateProject : ConcreteState → State} {returnExtract : ConcreteState → Value}
    {exceptionExtract : ConcreteState → Exception} {precondition : ConcreteState → Prop}
    {read : State → Value} {names : List String}
    (extracts : ∀ state, precondition state →
      returnExtract state = read (stateProject state)) :
    L2Corres stateProject returnExtract exceptionExtract precondition
      (gets read names) (returnOk ()) := by
  intro state hypothesis
  refine ⟨?_, ?_⟩
  · intro result post member
    simp [returnOk, pure] at member
    rcases member with ⟨rfl, rfl⟩
    rw [gets, mem_liftE, mem_gets]
    exact ⟨extracts state hypothesis.1, rfl⟩
  · simp [returnOk, pure]

/-- L2 skip corresponds to the concrete L1 skip. -/
theorem corres_skip
    {stateProject : ConcreteState → State} {returnExtract : ConcreteState → Unit}
    {exceptionExtract : ConcreteState → Exception} {precondition : ConcreteState → Prop} :
    L2Corres stateProject returnExtract exceptionExtract precondition
      skip (returnOk ()) := by
  apply corres_gets_skip
  intro state _
  exact Subsingleton.elim _ _

/-- A local concrete update may be represented by reading its extracted value at L2. -/
theorem corres_gets_modify
    {stateProject : ConcreteState → State} {returnExtract : ConcreteState → Value}
    {exceptionExtract : ConcreteState → Exception} {precondition : ConcreteState → Prop}
    {read : State → Value} {update : ConcreteState → ConcreteState}
    {names : List String}
    (preservesState : ∀ state, precondition state →
      stateProject state = stateProject (update state))
    (extracts : ∀ state, precondition state →
      returnExtract (update state) = read (stateProject state)) :
    L2Corres stateProject returnExtract exceptionExtract precondition
      (gets read names) (liftE (AutoCorres.modify update)) := by
  intro state hypothesis
  refine ⟨?_, ?_⟩
  · intro result post member
    rw [mem_liftE_iff] at member
    rcases member with ⟨value, rfl, member⟩
    rw [mem_modify] at member
    rcases member with ⟨rfl, rfl⟩
    rw [gets, mem_liftE, mem_gets]
    exact ⟨extracts state hypothesis.1,
      (preservesState state hypothesis.1).symm⟩
  · simp [failed_liftE, AutoCorres.modify]

/-- Matching state guards correspond. -/
theorem corres_guard
    {stateProject : ConcreteState → State} {returnExtract : ConcreteState → Unit}
    {exceptionExtract : ConcreteState → Exception} {precondition : ConcreteState → Prop}
    {abstractGuard : State → Prop} {concreteGuard : ConcreteState → Prop}
    (matchGuard : ∀ state, precondition state →
      (concreteGuard state ↔ abstractGuard (stateProject state))) :
    L2Corres stateProject returnExtract exceptionExtract precondition
      (guard abstractGuard) (liftE (AutoCorres.guard concreteGuard)) := by
  intro state hypothesis
  have guardMatch : concreteGuard state ↔ abstractGuard (stateProject state) :=
    matchGuard state hypothesis.1
  refine ⟨?_, ?_⟩
  · intro result post member
    rw [mem_liftE_iff] at member
    rcases member with ⟨value, rfl, member⟩
    rw [mem_guard] at member
    rcases member with ⟨holds, rfl, rfl⟩
    rw [guard, mem_liftE, mem_guard]
    exact ⟨guardMatch.mp holds, Subsingleton.elim _ _, rfl⟩
  · rw [failed_liftE]
    change ¬¬ concreteGuard state
    intro concreteFails
    apply hypothesis.2
    rw [guard, failed_liftE]
    exact fun abstractHolds => concreteFails (guardMatch.mpr abstractHolds)

/-- A failed abstract target corresponds to every concrete L1 program. -/
theorem corres_fail
    {stateProject : ConcreteState → State} {returnExtract : ConcreteState → Value}
    {exceptionExtract : ConcreteState → Exception} {precondition : ConcreteState → Prop}
    {concrete : Nondet ConcreteState (Except Unit Unit)} :
    L2Corres stateProject returnExtract exceptionExtract precondition fail concrete := by
  intro state hypothesis
  exact False.elim (hypothesis.2 (by simp [fail]))

/-- An extracted L1 throw corresponds to the matching L2 exception. -/
theorem corres_throw
    {stateProject : ConcreteState → State} {returnExtract : ConcreteState → Value}
    {exceptionExtract : ConcreteState → Exception} {precondition : ConcreteState → Prop}
    {exception : Exception} {names : List String}
    (extracts : ∀ state, precondition state → exceptionExtract state = exception) :
    L2Corres stateProject returnExtract exceptionExtract precondition
      (throw (Value := Value) exception names) (AutoCorres.throw ()) := by
  intro state hypothesis
  refine ⟨?_, ?_⟩
  · intro result post member
    simp [AutoCorres.throw, pure] at member
    rcases member with ⟨rfl, rfl⟩
    rw [throw, mem_throw]
    exact ⟨extracts state hypothesis.1, rfl⟩
  · simp [AutoCorres.throw, pure]

/-- Matching global state updates correspond. -/
theorem corres_modify
    {stateProject : ConcreteState → State} {returnExtract : ConcreteState → Unit}
    {exceptionExtract : ConcreteState → Exception} {precondition : ConcreteState → Prop}
    {abstractUpdate : State → State} {concreteUpdate : ConcreteState → ConcreteState}
    (matchState : ∀ state, precondition state →
      abstractUpdate (stateProject state) = stateProject (concreteUpdate state)) :
    L2Corres stateProject returnExtract exceptionExtract precondition
      (modify abstractUpdate) (liftE (AutoCorres.modify concreteUpdate)) := by
  intro state hypothesis
  refine ⟨?_, ?_⟩
  · intro result post member
    rw [mem_liftE_iff] at member
    rcases member with ⟨value, rfl, member⟩
    rw [mem_modify] at member
    rcases member with ⟨rfl, rfl⟩
    rw [modify, mem_liftE, mem_modify]
    exact ⟨Subsingleton.elim _ _, (matchState state hypothesis.1).symm⟩
  · simp [failed_liftE, AutoCorres.modify]

/-! ## Compositional local-variable extraction rules -/

/-- Upstream `L2corres_seq`, with its Hoare premise stated over normal results. -/
theorem L2corres_seq
    {stateProject : ConcreteState → State}
    {returnExtract : ConcreteState → Value}
    {nextReturnExtract : ConcreteState → NextValue}
    {exceptionExtract : ConcreteState → Exception}
    {precondition : ConcreteState → Prop}
    {nextPrecondition : Value → ConcreteState → Prop}
    {required : ConcreteState → Prop}
    {first : L2Program State Exception Value}
    {next : Value → L2Program State Exception NextValue}
    {concreteFirst concreteNext : L1.L1Program ConcreteState}
    (firstCorres : L2Corres stateProject returnExtract exceptionExtract
      precondition first concreteFirst)
    (nextCorres : ∀ value, L2Corres stateProject nextReturnExtract exceptionExtract
      (nextPrecondition value) (next value) concreteNext)
    (normalPost : ∀ state, required state → ∀ post,
      (Except.ok (), post) ∈ (concreteFirst state).results →
        nextPrecondition (returnExtract post) post)
    (requiredImplies : ∀ state, required state → precondition state) :
    L2Corres stateProject nextReturnExtract exceptionExtract required
      (seq first next) (L1.seq concreteFirst concreteNext) := by
  intro state hypothesis
  have firstNoFail : ¬ (first (stateProject state)).failed := by
    intro failed
    apply hypothesis.2
    exact Or.inl failed
  have firstRule := firstCorres state
    ⟨requiredImplies state hypothesis.1, firstNoFail⟩
  refine ⟨?_, ?_⟩
  · intro result post member
    rcases member with ⟨sourceResult, middle, sourceMember, continuationMember⟩
    cases sourceResult with
    | error exception =>
        have mapped := firstRule.1 (Except.error exception) middle sourceMember
        change (result, post) = (Except.error (), middle) at continuationMember
        cases continuationMember
        exact ⟨Except.error (exceptionExtract post), stateProject post,
          mapped, rfl⟩
    | ok value =>
        have mappedFirst := firstRule.1 (Except.ok value) middle sourceMember
        have nextNoFail : ¬ (next (returnExtract middle) (stateProject middle)).failed := by
          intro failed
          apply hypothesis.2
          exact Or.inr ⟨Except.ok (returnExtract middle), stateProject middle,
            mappedFirst, failed⟩
        have mappedNext := (nextCorres (returnExtract middle)) middle
          ⟨normalPost state hypothesis.1 middle sourceMember, nextNoFail⟩
        exact ⟨Except.ok (returnExtract middle), stateProject middle,
          mappedFirst, mappedNext.1 result post continuationMember⟩
  · intro concreteFailed
    apply hypothesis.2
    rcases concreteFailed with concreteFailed | ⟨sourceResult, middle, sourceMember, failed⟩
    · exact False.elim (firstRule.2 concreteFailed)
    · cases sourceResult with
      | error exception => exact False.elim failed
      | ok value =>
          have mappedFirst := firstRule.1 (Except.ok value) middle sourceMember
          have nextNoFail : ¬ (next (returnExtract middle) (stateProject middle)).failed := by
            intro nextFailed
            apply hypothesis.2
            exact Or.inr ⟨Except.ok (returnExtract middle), stateProject middle,
              mappedFirst, nextFailed⟩
          exact (((nextCorres (returnExtract middle)) middle
            ⟨normalPost state hypothesis.1 middle sourceMember, nextNoFail⟩).2 failed).elim

/-- Upstream `L2corres_catch`, with its exceptional Hoare postcondition explicit. -/
theorem L2corres_catch
    {stateProject : ConcreteState → State}
    {returnExtract : ConcreteState → Value}
    {exceptionExtract : ConcreteState → Exception}
    {nextExceptionExtract : ConcreteState → NextException}
    {precondition : ConcreteState → Prop}
    {handlerPrecondition : Exception → ConcreteState → Prop}
    {required : ConcreteState → Prop}
    {body : L2Program State Exception Value}
    {handler : Exception → L2Program State NextException Value}
    {concreteBody concreteHandler : L1.L1Program ConcreteState}
    (bodyCorres : L2Corres stateProject returnExtract exceptionExtract
      precondition body concreteBody)
    (handlerCorres : ∀ exception,
      L2Corres stateProject returnExtract nextExceptionExtract
        (handlerPrecondition exception) (handler exception) concreteHandler)
    (exceptionPost : ∀ state, required state → ∀ post,
      (Except.error (), post) ∈ (concreteBody state).results →
        handlerPrecondition (exceptionExtract post) post)
    (requiredImplies : ∀ state, required state → precondition state) :
    L2Corres stateProject returnExtract nextExceptionExtract required
      («catch» body handler) (L1.catch concreteBody concreteHandler) := by
  intro state hypothesis
  have bodyNoFail : ¬ (body (stateProject state)).failed := by
    intro failed
    apply hypothesis.2
    exact Or.inl failed
  have bodyRule := bodyCorres state
    ⟨requiredImplies state hypothesis.1, bodyNoFail⟩
  refine ⟨?_, ?_⟩
  · intro result post member
    rcases member with ⟨sourceResult, middle, sourceMember, continuationMember⟩
    cases sourceResult with
    | ok value =>
        have mapped := bodyRule.1 (Except.ok value) middle sourceMember
        change (result, post) = (Except.ok value, middle) at continuationMember
        cases continuationMember
        exact ⟨Except.ok (returnExtract post), stateProject post, mapped, rfl⟩
    | error exception =>
        have mappedBody := bodyRule.1 (Except.error exception) middle sourceMember
        have handlerNoFail :
            ¬ (handler (exceptionExtract middle) (stateProject middle)).failed := by
          intro failed
          apply hypothesis.2
          exact Or.inr ⟨Except.error (exceptionExtract middle), stateProject middle,
            mappedBody, failed⟩
        exact ⟨Except.error (exceptionExtract middle), stateProject middle,
          mappedBody, ((handlerCorres (exceptionExtract middle)) middle
            ⟨exceptionPost state hypothesis.1 middle sourceMember, handlerNoFail⟩).1
              result post continuationMember⟩
  · intro concreteFailed
    apply hypothesis.2
    rcases concreteFailed with concreteFailed | ⟨sourceResult, middle, sourceMember, failed⟩
    · exact False.elim (bodyRule.2 concreteFailed)
    · cases sourceResult with
      | ok value => exact False.elim failed
      | error exception =>
          have mappedBody := bodyRule.1 (Except.error exception) middle sourceMember
          have handlerNoFail :
              ¬ (handler (exceptionExtract middle) (stateProject middle)).failed := by
            intro handlerFailed
            apply hypothesis.2
            exact Or.inr ⟨Except.error (exceptionExtract middle), stateProject middle,
              mappedBody, handlerFailed⟩
          exact (((handlerCorres (exceptionExtract middle)) middle
            ⟨exceptionPost state hypothesis.1 middle sourceMember,
              handlerNoFail⟩).2 failed).elim

/-- Upstream `L2corres_cond`: corresponding branches under matching tests. -/
theorem L2corres_cond
    {stateProject : ConcreteState → State}
    {returnExtract : ConcreteState → Value}
    {exceptionExtract : ConcreteState → Exception}
    {thenPrecondition elsePrecondition required : ConcreteState → Prop}
    {abstractTest : State → Prop} {concreteTest : ConcreteState → Prop}
    {abstractThen abstractElse : L2Program State Exception Value}
    {concreteThen concreteElse : L1.L1Program ConcreteState}
    (thenCorres : L2Corres stateProject returnExtract exceptionExtract
      thenPrecondition abstractThen concreteThen)
    (elseCorres : L2Corres stateProject returnExtract exceptionExtract
      elsePrecondition abstractElse concreteElse)
    (thenPre : ∀ state, required state → thenPrecondition state)
    (elsePre : ∀ state, required state → elsePrecondition state)
    (testMatches : ∀ state, required state →
      (concreteTest state ↔ abstractTest (stateProject state))) :
    L2Corres stateProject returnExtract exceptionExtract required
      (condition abstractTest abstractThen abstractElse)
      (L1.condition concreteTest concreteThen concreteElse) := by
  intro state hypothesis
  have testMatch := testMatches state hypothesis.1
  by_cases concreteHolds : concreteTest state
  · have abstractHolds := testMatch.mp concreteHolds
    simp [condition, L1.condition, concreteHolds, abstractHolds] at hypothesis ⊢
    exact thenCorres state ⟨thenPre state hypothesis.1, hypothesis.2⟩
  · have abstractDoesNotHold : ¬ abstractTest (stateProject state) :=
      fun holds => concreteHolds (testMatch.mpr holds)
    simp [condition, L1.condition, concreteHolds, abstractDoesNotHold] at hypothesis ⊢
    exact elseCorres state ⟨elsePre state hypothesis.1, hypothesis.2⟩

/-- Upstream `L2corres_inject_return`, with its normal postcondition explicit. -/
theorem L2corres_inject_return
    {stateProject : ConcreteState → State}
    {returnExtract : ConcreteState → Value}
    {injectedExtract : ConcreteState → Injected}
    {exceptionExtract : ConcreteState → Exception}
    {precondition required : ConcreteState → Prop}
    {program : L2Program State Exception Value}
    {concrete : L1.L1Program ConcreteState}
    {inject : Value → Injected} {names : List String}
    (programCorres : L2Corres stateProject returnExtract exceptionExtract
      precondition program concrete)
    (normalPost : ∀ state, required state → ∀ post,
      (Except.ok (), post) ∈ (concrete state).results →
        inject (returnExtract post) = injectedExtract post)
    (requiredImplies : ∀ state, required state → precondition state) :
    L2Corres stateProject injectedExtract exceptionExtract required
      (seq program fun value => gets (fun _ => inject value) names) concrete := by
  intro state hypothesis
  have programNoFail : ¬ (program (stateProject state)).failed := by
    intro failed
    apply hypothesis.2
    exact Or.inl failed
  have programRule := programCorres state
    ⟨requiredImplies state hypothesis.1, programNoFail⟩
  refine ⟨?_, programRule.2⟩
  intro result post member
  have mapped := programRule.1 result post member
  cases result with
  | error exception =>
      exact ⟨Except.error (exceptionExtract post), stateProject post, mapped, rfl⟩
  | ok value =>
      refine ⟨Except.ok (returnExtract post), stateProject post, mapped, ?_⟩
      change (Except.ok (injectedExtract post), stateProject post) ∈
        (liftE (AutoCorres.gets fun _ => inject (returnExtract post))
          (stateProject post)).results
      rw [mem_liftE_iff]
      exact ⟨inject (returnExtract post),
        congrArg Except.ok (normalPost state hypothesis.1 post member).symm,
        rfl⟩

private theorem whileLoop_body_noFail
    {Acc : Type u} {State : Type v}
    {test : Acc → State → Prop} {body : Acc → Nondet State Acc}
    {value : Acc} {state : State}
    (loopNoFail : ¬ (whileLoop test body value state).failed)
    (holds : test value state) : ¬ (body value state).failed := by
  intro failed
  exact loopNoFail (Or.inl (.bodyFailure holds failed))

private theorem whileLoop_rest_noFail
    {Acc : Type u} {State : Type v}
    {test : Acc → State → Prop} {body : Acc → Nondet State Acc}
    {value next : Acc} {state nextState : State}
    (loopNoFail : ¬ (whileLoop test body value state).failed)
    (holds : test value state)
    (member : (next, nextState) ∈ (body value state).results) :
    ¬ (whileLoop test body next nextState).failed := by
  intro failed
  rcases failed with finiteFailure | notTerminates
  · exact loopNoFail (Or.inl (.step holds member finiteFailure))
  · apply loopNoFail
    apply Or.inr
    intro terminates
    cases terminates with
    | stop doesNotHold => exact doesNotHold holds
    | step _ branches => exact notTerminates (branches next nextState member)

private theorem whileResult_test_congr
    {Acc : Type u} {State : Type v}
    {sourceTest targetTest : Acc → State → Prop}
    {body : Acc → Nondet State Acc} {initial result : Option (Acc × State)}
    (testIff : ∀ value state, sourceTest value state ↔ targetTest value state)
    (execution : WhileResult sourceTest body initial result) :
    WhileResult targetTest body initial result := by
  induction execution with
  | stop doesNotHold =>
      exact .stop (fun holds => doesNotHold ((testIff _ _).mpr holds))
  | bodyFailure holds failed =>
      exact .bodyFailure ((testIff _ _).mp holds) failed
  | step holds member rest inductionHypothesis =>
      exact .step ((testIff _ _).mp holds) member inductionHypothesis

private def loopValueMatches
    (returnExtract : ConcreteState → Value)
    (exceptionExtract : ConcreteState → Exception)
    (invariant : Value → ConcreteState → Prop)
    (concreteValue : Except Unit Unit) (concreteState : ConcreteState)
    (abstractValue : Except Exception Value) : Prop :=
  match concreteValue with
  | .error _ => abstractValue = .error (exceptionExtract concreteState)
  | .ok _ => abstractValue = .ok (returnExtract concreteState) ∧
      invariant (returnExtract concreteState) concreteState

private def mapLoopResult
    (returnExtract : ConcreteState → Value)
    (exceptionExtract : ConcreteState → Exception)
    (result : Except Unit Unit) (post : ConcreteState) : Except Exception Value :=
  match result with
  | .error _ => .error (exceptionExtract post)
  | .ok _ => .ok (returnExtract post)

private theorem whileResult_corres
    {stateProject : ConcreteState → State}
    {returnExtract : ConcreteState → Value}
    {exceptionExtract : ConcreteState → Exception}
    {invariant : Value → ConcreteState → Prop}
    {bodyPrecondition : Value → ConcreteState → Prop}
    {abstractTest : Value → State → Prop}
    {concreteTest : ConcreteState → Prop}
    {concreteLoopTest : Except Unit Unit → ConcreteState → Prop}
    {abstractBody : Value → L2Program State Exception Value}
    {concreteBody : L1.L1Program ConcreteState}
    (bodyCorres : ∀ value, L2Corres stateProject returnExtract exceptionExtract
      (bodyPrecondition value) (abstractBody value) concreteBody)
    (invariantPost : ∀ state, invariant (returnExtract state) state → ∀ post,
      (Except.ok (), post) ∈ (concreteBody state).results →
        invariant (returnExtract post) post)
    (testMatches : ∀ state, invariant (returnExtract state) state →
      (concreteTest state ↔
        abstractTest (returnExtract state) (stateProject state)))
    (loopTestError : ∀ exception state,
      ¬ concreteLoopTest (.error exception) state)
    (loopTestOk : ∀ value state,
      concreteLoopTest (.ok value) state ↔ concreteTest state)
    (invariantImplies : ∀ state value, invariant value state →
      bodyPrecondition value state)
    {concreteValue : Except Unit Unit} {concreteState : ConcreteState}
    {abstractValue : Except Exception Value} {abstractState : State}
    {result : Except Unit Unit} {post : ConcreteState}
    {concreteInitial concreteFinal : Option (Except Unit Unit × ConcreteState)}
    (initialMatches : some (concreteValue, concreteState) = concreteInitial)
    (finalMatches : some (result, post) = concreteFinal)
    (stateMatches : abstractState = stateProject concreteState)
    (valueMatches : loopValueMatches returnExtract exceptionExtract invariant
      concreteValue concreteState abstractValue)
    (loopNoFail : ¬ (whileLoop
      (fun value state => match value with
        | .error _ => False
        | .ok value => abstractTest value state)
      (whileLoopEBody abstractBody) abstractValue abstractState).failed)
    (execution : WhileResult
      concreteLoopTest
      (whileLoopEBody fun _ => concreteBody)
      concreteInitial concreteFinal) :
    WhileResult
      (fun value state => match value with
        | .error _ => False
        | .ok value => abstractTest value state)
      (whileLoopEBody abstractBody)
      (some (abstractValue, abstractState))
      (some (mapLoopResult returnExtract exceptionExtract result post,
        stateProject post)) := by
  induction execution generalizing concreteValue concreteState abstractValue abstractState
      result post with
  | stop doesNotHold =>
      cases initialMatches
      cases finalMatches
      rename_i currentValue currentState
      cases currentValue with
      | error exception =>
          cases stateMatches
          rw [loopValueMatches] at valueMatches
          rw [valueMatches]
          exact .stop not_false
      | ok value =>
          change abstractValue = .ok (returnExtract currentState) ∧
            invariant (returnExtract currentState) currentState at valueMatches
          rcases valueMatches with ⟨rfl, invariantHolds⟩
          cases stateMatches
          apply WhileResult.stop
          intro abstractHolds
          exact doesNotHold ((loopTestOk value currentState).mpr
            ((testMatches currentState invariantHolds).mpr abstractHolds))
  | bodyFailure holds failed => cases finalMatches
  | step holds member rest inductionHypothesis =>
      cases initialMatches
      rename_i currentValue currentState next nextState final
      cases currentValue with
      | error exception => exact False.elim (loopTestError exception currentState holds)
      | ok value =>
          change abstractValue = .ok (returnExtract currentState) ∧
            invariant (returnExtract currentState) currentState at valueMatches
          rcases valueMatches with ⟨rfl, invariantHolds⟩
          cases stateMatches
          have concreteHolds : concreteTest currentState :=
            (loopTestOk value currentState).mp holds
          have abstractHolds :
              abstractTest (returnExtract currentState)
                (stateProject currentState) :=
            (testMatches currentState invariantHolds).mp concreteHolds
          have bodyNoFail :
              ¬ (abstractBody (returnExtract currentState)
                (stateProject currentState)).failed :=
            whileLoop_body_noFail loopNoFail abstractHolds
          have bodyRule := (bodyCorres (returnExtract currentState)) currentState
            ⟨invariantImplies currentState (returnExtract currentState)
              invariantHolds, bodyNoFail⟩
          change (next, nextState) ∈ (concreteBody currentState).results at member
          have mapped := bodyRule.1 next nextState member
          have restNoFail := whileLoop_rest_noFail loopNoFail abstractHolds mapped
          cases next with
          | error exception =>
              exact .step abstractHolds mapped (inductionHypothesis
                (concreteValue := .error ()) (concreteState := nextState)
                (abstractValue := .error (exceptionExtract nextState))
                (abstractState := stateProject nextState)
                rfl finalMatches rfl (by simp [loopValueMatches]) restNoFail)
          | ok value =>
              exact .step abstractHolds mapped (inductionHypothesis
                (concreteValue := .ok ()) (concreteState := nextState)
                (abstractValue := .ok (returnExtract nextState))
                (abstractState := stateProject nextState)
                rfl finalMatches rfl
                (by exact ⟨rfl,
                  invariantPost currentState invariantHolds nextState member⟩)
                restNoFail)

private theorem whileFailure_impossible
    {stateProject : ConcreteState → State}
    {returnExtract : ConcreteState → Value}
    {exceptionExtract : ConcreteState → Exception}
    {invariant : Value → ConcreteState → Prop}
    {bodyPrecondition : Value → ConcreteState → Prop}
    {abstractTest : Value → State → Prop}
    {concreteTest : ConcreteState → Prop}
    {concreteLoopTest : Except Unit Unit → ConcreteState → Prop}
    {abstractBody : Value → L2Program State Exception Value}
    {concreteBody : L1.L1Program ConcreteState}
    (bodyCorres : ∀ value, L2Corres stateProject returnExtract exceptionExtract
      (bodyPrecondition value) (abstractBody value) concreteBody)
    (invariantPost : ∀ state, invariant (returnExtract state) state → ∀ post,
      (Except.ok (), post) ∈ (concreteBody state).results →
        invariant (returnExtract post) post)
    (testMatches : ∀ state, invariant (returnExtract state) state →
      (concreteTest state ↔
        abstractTest (returnExtract state) (stateProject state)))
    (loopTestError : ∀ exception state,
      ¬ concreteLoopTest (.error exception) state)
    (loopTestOk : ∀ value state,
      concreteLoopTest (.ok value) state ↔ concreteTest state)
    (invariantImplies : ∀ state value, invariant value state →
      bodyPrecondition value state)
    {concreteValue : Except Unit Unit} {concreteState : ConcreteState}
    {abstractValue : Except Exception Value} {abstractState : State}
    {concreteInitial concreteFinal : Option (Except Unit Unit × ConcreteState)}
    (initialMatches : some (concreteValue, concreteState) = concreteInitial)
    (finalMatches : none = concreteFinal)
    (stateMatches : abstractState = stateProject concreteState)
    (valueMatches : loopValueMatches returnExtract exceptionExtract invariant
      concreteValue concreteState abstractValue)
    (loopNoFail : ¬ (whileLoop
      (fun value state => match value with
        | .error _ => False
        | .ok value => abstractTest value state)
      (whileLoopEBody abstractBody) abstractValue abstractState).failed)
    (failure : WhileResult
      concreteLoopTest
      (whileLoopEBody fun _ => concreteBody)
      concreteInitial concreteFinal) : False := by
  induction failure generalizing concreteValue concreteState abstractValue abstractState with
  | stop doesNotHold => cases finalMatches
  | bodyFailure holds failed =>
      cases initialMatches
      rename_i currentValue currentState
      cases currentValue with
      | error exception => exact loopTestError exception currentState holds
      | ok value =>
          change abstractValue = .ok (returnExtract currentState) ∧
            invariant (returnExtract currentState) currentState at valueMatches
          rcases valueMatches with ⟨rfl, invariantHolds⟩
          cases stateMatches
          have abstractHolds :=
            (testMatches currentState invariantHolds).mp
              ((loopTestOk value currentState).mp holds)
          have bodyNoFail :
              ¬ (abstractBody (returnExtract currentState)
                (stateProject currentState)).failed :=
            whileLoop_body_noFail loopNoFail abstractHolds
          have bodyRule := (bodyCorres (returnExtract currentState)) currentState
            ⟨invariantImplies currentState (returnExtract currentState)
              invariantHolds, bodyNoFail⟩
          exact bodyRule.2 failed
  | step holds member rest inductionHypothesis =>
      cases initialMatches
      rename_i currentValue currentState next nextState final
      cases currentValue with
      | error exception => exact loopTestError exception currentState holds
      | ok value =>
          change abstractValue = .ok (returnExtract currentState) ∧
            invariant (returnExtract currentState) currentState at valueMatches
          rcases valueMatches with ⟨rfl, invariantHolds⟩
          cases stateMatches
          have abstractHolds :=
            (testMatches currentState invariantHolds).mp
              ((loopTestOk value currentState).mp holds)
          have bodyNoFail :
              ¬ (abstractBody (returnExtract currentState)
                (stateProject currentState)).failed :=
            whileLoop_body_noFail loopNoFail abstractHolds
          have bodyRule := (bodyCorres (returnExtract currentState)) currentState
            ⟨invariantImplies currentState (returnExtract currentState)
              invariantHolds, bodyNoFail⟩
          change (next, nextState) ∈ (concreteBody currentState).results at member
          have mapped := bodyRule.1 next nextState member
          have restNoFail := whileLoop_rest_noFail loopNoFail abstractHolds mapped
          cases next with
          | error exception =>
              exact inductionHypothesis
                (concreteValue := .error ()) (concreteState := nextState)
                (abstractValue := .error (exceptionExtract nextState))
                (abstractState := stateProject nextState)
                rfl finalMatches rfl (by simp [loopValueMatches]) restNoFail
          | ok value =>
              exact inductionHypothesis
                (concreteValue := .ok ()) (concreteState := nextState)
                (abstractValue := .ok (returnExtract nextState))
                (abstractState := stateProject nextState)
                rfl finalMatches rfl
                (by exact ⟨rfl,
                  invariantPost currentState invariantHolds nextState member⟩)
                restNoFail

private theorem whileTerminates_corres
    {stateProject : ConcreteState → State}
    {returnExtract : ConcreteState → Value}
    {exceptionExtract : ConcreteState → Exception}
    {invariant : Value → ConcreteState → Prop}
    {bodyPrecondition : Value → ConcreteState → Prop}
    {abstractTest : Value → State → Prop}
    {concreteTest : ConcreteState → Prop}
    {concreteLoopTest : Except Unit Unit → ConcreteState → Prop}
    {abstractBody : Value → L2Program State Exception Value}
    {concreteBody : L1.L1Program ConcreteState}
    (bodyCorres : ∀ value, L2Corres stateProject returnExtract exceptionExtract
      (bodyPrecondition value) (abstractBody value) concreteBody)
    (invariantPost : ∀ state, invariant (returnExtract state) state → ∀ post,
      (Except.ok (), post) ∈ (concreteBody state).results →
        invariant (returnExtract post) post)
    (testMatches : ∀ state, invariant (returnExtract state) state →
      (concreteTest state ↔
        abstractTest (returnExtract state) (stateProject state)))
    (loopTestError : ∀ exception state,
      ¬ concreteLoopTest (.error exception) state)
    (loopTestOk : ∀ value state,
      concreteLoopTest (.ok value) state ↔ concreteTest state)
    (invariantImplies : ∀ state value, invariant value state →
      bodyPrecondition value state)
    {concreteValue : Except Unit Unit} {concreteState : ConcreteState}
    {abstractValue : Except Exception Value} {abstractState : State}
    (stateMatches : abstractState = stateProject concreteState)
    (valueMatches : loopValueMatches returnExtract exceptionExtract invariant
      concreteValue concreteState abstractValue)
    (loopNoFail : ¬ (whileLoop
      (fun value state => match value with
        | .error _ => False
        | .ok value => abstractTest value state)
      (whileLoopEBody abstractBody) abstractValue abstractState).failed)
    (terminates : WhileTerminates
      (fun value state => match value with
        | .error _ => False
        | .ok value => abstractTest value state)
      (whileLoopEBody abstractBody) abstractValue abstractState) :
    WhileTerminates
      concreteLoopTest
      (whileLoopEBody fun _ => concreteBody) concreteValue concreteState := by
  induction terminates generalizing concreteValue concreteState with
  | stop doesNotHold =>
      rename_i currentAbstractValue currentAbstractState
      cases concreteValue with
      | error exception => exact .stop (loopTestError exception concreteState)
      | ok value =>
          change currentAbstractValue = .ok (returnExtract concreteState) ∧
            invariant (returnExtract concreteState) concreteState at valueMatches
          rcases valueMatches with ⟨rfl, invariantHolds⟩
          cases stateMatches
          apply WhileTerminates.stop
          intro concreteHolds
          exact doesNotHold ((testMatches concreteState invariantHolds).mp
            ((loopTestOk value concreteState).mp concreteHolds))
  | step holds branches inductionHypothesis =>
      rename_i currentAbstractValue currentAbstractState
      cases concreteValue with
      | error exception =>
          change currentAbstractValue = .error (exceptionExtract concreteState) at valueMatches
          cases stateMatches
          rw [valueMatches] at holds
          exact False.elim holds
      | ok value =>
          change currentAbstractValue = .ok (returnExtract concreteState) ∧
            invariant (returnExtract concreteState) concreteState at valueMatches
          rcases valueMatches with ⟨abstractValueEq, invariantHolds⟩
          cases stateMatches
          cases abstractValueEq
          have concreteHolds : concreteLoopTest (.ok value) concreteState :=
            (loopTestOk value concreteState).mpr
              ((testMatches concreteState invariantHolds).mpr holds)
          have bodyNoFail :
              ¬ (abstractBody (returnExtract concreteState)
                (stateProject concreteState)).failed :=
            whileLoop_body_noFail loopNoFail holds
          have bodyRule := (bodyCorres (returnExtract concreteState)) concreteState
            ⟨invariantImplies concreteState (returnExtract concreteState)
              invariantHolds, bodyNoFail⟩
          apply WhileTerminates.step concreteHolds
          intro next nextState member
          change (next, nextState) ∈ (concreteBody concreteState).results at member
          have mapped := bodyRule.1 next nextState member
          have restNoFail := whileLoop_rest_noFail loopNoFail holds mapped
          cases next with
          | error exception =>
              exact inductionHypothesis _ _ mapped
                (concreteValue := .error ()) (concreteState := nextState)
                rfl (by simp [loopValueMatches]) restNoFail
          | ok value =>
              exact inductionHypothesis _ _ mapped
                (concreteValue := .ok ()) (concreteState := nextState)
                rfl (by exact ⟨rfl,
                  invariantPost concreteState invariantHolds nextState member⟩)
                restNoFail

/--
Upstream `L2corres_while`.  Its invariant Hoare triple is represented by
`invariantPost`, quantified directly over every normal result of the concrete
body; exceptional body results stop both loops and require no invariant.
-/
theorem L2corres_while
    {stateProject : ConcreteState → State}
    {returnExtract : ConcreteState → Value}
    {exceptionExtract : ConcreteState → Exception}
    {invariant : Value → ConcreteState → Prop}
    {bodyPrecondition : Value → ConcreteState → Prop}
    {required : Value → ConcreteState → Prop}
    {abstractTest : Value → State → Prop}
    {concreteTest : ConcreteState → Prop}
    {abstractBody : Value → L2Program State Exception Value}
    {concreteBody : L1.L1Program ConcreteState}
    {initial : Value} {names : List String}
    (bodyCorres : ∀ value, L2Corres stateProject returnExtract exceptionExtract
      (bodyPrecondition value) (abstractBody value) concreteBody)
    (invariantPost : ∀ state, invariant (returnExtract state) state → ∀ post,
      (Except.ok (), post) ∈ (concreteBody state).results →
        invariant (returnExtract post) post)
    (testMatches : ∀ state, invariant (returnExtract state) state →
      (concreteTest state ↔
        abstractTest (returnExtract state) (stateProject state)))
    (invariantImplies : ∀ state value, invariant value state →
      bodyPrecondition value state)
    (invariantExtracts : ∀ state value, invariant value state →
      returnExtract state = value)
    (requiredImplies : ∀ state, required initial state → invariant initial state) :
    L2Corres stateProject returnExtract exceptionExtract (required initial)
      («while» abstractTest abstractBody initial names)
      (L1.while concreteTest concreteBody) := by
  intro state hypothesis
  have initialInvariant := requiredImplies state hypothesis.1
  have initialExtract := invariantExtracts state initial initialInvariant
  have loopInvariant : invariant (returnExtract state) state := by
    simpa [initialExtract] using initialInvariant
  unfold «while» at hypothesis
  unfold L1.«while»
  unfold whileLoopE at hypothesis ⊢
  have abstractTerminates : WhileTerminates
      (fun value state => match value with
        | .error _ => False
        | .ok value => abstractTest value state)
      (whileLoopEBody abstractBody) (Except.ok initial) (stateProject state) :=
    Classical.byContradiction fun notTerminates =>
      hypothesis.2 (Or.inr notTerminates)
  refine ⟨?_, ?_⟩
  · intro result post member
    unfold whileLoop at member
    simp only [Membership.mem] at member
    have abstractExecution :=
      whileResult_corres bodyCorres invariantPost testMatches
      (fun _ _ holds => holds) (fun _ _ => Iff.rfl) invariantImplies
      (concreteValue := .ok ()) (concreteState := state)
      (abstractValue := .ok initial) (abstractState := stateProject state)
      (result := result) (post := post) rfl rfl rfl
      (by exact ⟨congrArg Except.ok initialExtract.symm, loopInvariant⟩)
      hypothesis.2 member
    unfold «while» whileLoopE whileLoop
    simp only [Membership.mem]
    cases result <;> simp only [mapLoopResult] at abstractExecution ⊢
    all_goals
      exact whileResult_test_congr
        (sourceTest := fun (value : Except Exception Value) state => match value with
          | .error _ => False
          | .ok value => abstractTest value state)
        (targetTest := fun (value : Except Exception Value) state => match value with
          | .error _ => False
          | .ok value => abstractTest value state)
        (fun _ _ => Iff.rfl) abstractExecution
  · intro concreteFailed
    rcases concreteFailed with finiteFailure | notTerminates
    · exact whileFailure_impossible bodyCorres invariantPost testMatches
        (fun _ _ holds => holds) (fun _ _ => Iff.rfl) invariantImplies
        (concreteValue := .ok ()) (concreteState := state)
        (abstractValue := .ok initial) (abstractState := stateProject state)
        rfl rfl rfl
        (by exact ⟨congrArg Except.ok initialExtract.symm, loopInvariant⟩)
        hypothesis.2 finiteFailure
    · apply notTerminates
      exact whileTerminates_corres bodyCorres invariantPost testMatches
          (fun _ _ holds => holds) (fun _ _ => Iff.rfl) invariantImplies
          (concreteValue := .ok ()) (concreteState := state)
          (abstractValue := .ok initial) (abstractState := stateProject state)
          rfl (by exact ⟨congrArg Except.ok initialExtract.symm, loopInvariant⟩)
          hypothesis.2 abstractTerminates

/-- Upstream `L2corres_recguard`: matching recursion guards preserve correspondence. -/
theorem L2corres_recguard
    {stateProject : ConcreteState → State}
    {returnExtract : ConcreteState → Value}
    {exceptionExtract : ConcreteState → Exception}
    {bodyPrecondition required : ConcreteState → Prop}
    {body : L2Program State Exception Value}
    {concreteBody : L1.L1Program ConcreteState}
    {measure : Nat}
    (bodyCorres : L2Corres stateProject returnExtract exceptionExtract
      bodyPrecondition body concreteBody)
    (requiredImplies : ∀ state, required state → bodyPrecondition state) :
    L2Corres stateProject returnExtract exceptionExtract required
      (recguard measure body) (L1.recguard measure concreteBody) := by
  by_cases zero : measure = 0
  · subst measure
    rw [show recguard 0 body = fail by
      funext state
      simp [recguard, condition]]
    exact corres_fail
  · have abstractEq : recguard measure body = body := by
      funext state
      simp [recguard, condition, zero]
    have concreteEq : L1.recguard measure concreteBody = concreteBody := by
      funext state
      simp [L1.recguard, L1.condition, zero]
    rw [abstractEq, concreteEq]
    intro state hypothesis
    exact bodyCorres state
      ⟨requiredImplies state hypothesis.1, hypothesis.2⟩

/-- A zero L2 recursion guard corresponds to every concrete program. -/
theorem L2corres_recguard_zero
    {stateProject : ConcreteState → State}
    {returnExtract : ConcreteState → Value}
    {exceptionExtract : ConcreteState → Exception}
    {precondition : ConcreteState → Prop}
    {body : L2Program State Exception Value}
    {concrete : L1.L1Program ConcreteState} :
    L2Corres stateProject returnExtract exceptionExtract precondition
      (recguard 0 (State := State) (Exception := Exception)
        (Value := Value) body) concrete := by
  rw [show recguard 0 body = fail by
    funext state
    simp [recguard, condition]]
  exact corres_fail

/-- Upstream `L2_recguard_cong`: the body is irrelevant at measure zero. -/
theorem L2_recguard_cong
    {measure measure' : Nat}
    {body body' : L2Program State Exception Value}
    (measureEq : measure = measure')
    (bodyEq : measure ≠ 0 → body = body') :
    recguard measure body = recguard measure' body' := by
  subst measure'
  by_cases zero : measure = 0
  · subst measure
    funext state
    simp [recguard, condition]
  · rw [bodyEq zero]

/-- A zero recursion guard is exactly monadic failure. -/
@[simp] theorem L2_recguard_zero
    (body : L2Program State Exception Value) : recguard 0 body = fail := by
  funext state
  simp [recguard, condition]

/-- Upstream spelling of the zero-measure correspondence rule. -/
theorem L2corres_recguard_0
    {stateProject : ConcreteState → State}
    {returnExtract : ConcreteState → Value}
    {exceptionExtract : ConcreteState → Exception}
    {precondition : ConcreteState → Prop}
    {body : L2Program State Exception Value}
    {concrete : L1.L1Program ConcreteState} :
    L2Corres stateProject returnExtract exceptionExtract precondition
      (recguard 0 body) concrete :=
  L2corres_recguard_zero

/-! ## Semantic regression pins -/

/-- Package an L2 program as an exact closed call into an SSA `PrimFuncCtx`. -/
def toSSA {State Exception Result : Type} [Repr (Except Exception Result)]
    (program : L2Program State Exception Result) :
    SSABridge.ClosedProgram State (Except Exception Result) :=
  ⟨program⟩

/-- The L2 package exposes the generic bridge's exact evaluation theorem. -/
theorem toSSA_eval {State Exception Result : Type} [Repr (Except Exception Result)]
    (program : L2Program State Exception Result) :
    cast (by simp only [SSABridge.outcomeTy_type])
      (Zag.Lang.SSA.SSAExpr.evalM? (toSSA program).ctx [] SSABridge.outcomeTy
        (toSSA program).expr) = some (SSABridge.suspend program) :=
  SSABridge.ClosedProgram.eval_exact (toSSA program)

/-- Local-variable extraction as an exact refinement between its closed SSA endpoints. -/
def L2Corres.toSSA
    {ConcreteState State Exception Value : Type}
    [Repr (Except Exception Value)]
    {stateProject : ConcreteState → State}
    {returnExtract : ConcreteState → Value}
    {exceptionExtract : ConcreteState → Exception}
    {precondition : ConcreteState → Prop}
    {abstract : L2Program State Exception Value}
    {concrete : L1.L1Program ConcreteState}
    (certificate : L2Corres stateProject returnExtract exceptionExtract
      precondition abstract concrete) :
    SSABridge.Refinement (L1.toSSA concrete) (toSSA abstract) :=
  SSABridge.Refinement.ofCorresXF stateProject
    (fun _ state => returnExtract state)
    (fun _ state => exceptionExtract state) precondition certificate

/-- L2 skip evaluates through SSA as exactly its suspended shallow semantics. -/
theorem skip_toSSA_eval {State Exception : Type} [Repr Exception] :
    cast (by simp only [SSABridge.outcomeTy_type])
      (Zag.Lang.SSA.SSAExpr.evalM?
        (toSSA (skip : L2Program State Exception Unit)).ctx [] SSABridge.outcomeTy
        (toSSA (skip : L2Program State Exception Unit)).expr) =
        some (SSABridge.suspend (skip : L2Program State Exception Unit)) :=
  toSSA_eval skip

/-- `unknown` returns every value in the unchanged state and never fails. -/
theorem unknown_behavior (names : List String) (state : State) :
    ((unknown (State := State) (Exception := Exception) (Value := Value) names state).results =
        fun result => ∃ value, result = (Except.ok value, state)) ∧
    ¬ (unknown (State := State) (Exception := Exception) (Value := Value) names state).failed := by
  constructor
  · funext result
    rcases result with ⟨result, post⟩
    apply propext
    change ((result, post) ∈
      (liftE (select fun _ : Value => True) state : Behavior State (Except Exception Value)).results) ↔ _
    rw [mem_liftE_iff]
    constructor
    · rintro ⟨value, equality, _, postEquality⟩
      cases equality
      cases postEquality
      exact ⟨value, rfl⟩
    · rintro ⟨value, equality⟩
      cases equality
      exact ⟨value, rfl, True.intro, rfl⟩
  · simp [unknown, select]

/-- `spec` returns every value at each related state and fails exactly if none exists. -/
theorem spec_behavior (relation : Set (State × State)) (state : State) :
    ((spec (Exception := Exception) (Value := Value) relation state).results =
        fun result => (state, result.2) ∈ relation ∧ ∃ value, result.1 = Except.ok value) ∧
    ((spec (Exception := Exception) (Value := Value) relation state).failed ↔
      ¬ ∃ post, (state, post) ∈ relation) := by
  constructor
  · funext result
    rcases result with ⟨result, post⟩
    apply propext
    change ((result, post) ∈
      (liftE (bind (AutoCorres.spec relation) fun _ => select fun _ : Value => True) state :
        Behavior State (Except Exception Value)).results) ↔ _
    rw [mem_liftE_iff]
    simp only [mem_bind, mem_spec, mem_select]
    simp
    constructor
    · rintro ⟨value, equality, relationMember, _⟩
      exact ⟨relationMember, value, equality⟩
    · rintro ⟨relationMember, value, equality⟩
      exact ⟨value, equality, relationMember, True.intro⟩
  · rw [spec, failed_liftE, failed_bind, failed_spec]
    simp [select]

/-- `call` has no exceptional results; each reachable source exception makes it fail. -/
theorem call_exception_behavior
    (program : L2Program State InnerException Value) (state post : State)
    (exception : InnerException)
    (member : (Except.error exception, post) ∈ (program state).results) :
    («call» (Exception := Exception) program state).failed ∧
      ∀ output, ¬ (Except.error output, post) ∈
        («call» (Exception := Exception) program state).results := by
  constructor
  · exact bind_observes_branch_failure member True.intro
  · intro output outputMember
    rcases outputMember with ⟨sourceResult, middle, sourceMember, continuationMember⟩
    cases sourceResult with
    | error exception => exact mem_fail continuationMember
    | ok value =>
        change (Except.error output, post) = (Except.ok value, middle) at continuationMember
        cases continuationMember

/-- A zero recursion measure is failure, while a positive measure is exactly the body. -/
theorem recguard_behavior (body : L2Program State Exception Value) (state : State) :
    recguard 0 body state = fail state ∧
      (∀ measure, measure ≠ 0 → recguard measure body state = body state) := by
  constructor
  · simp [recguard, condition]
  · intro measure nonzero
    simp [recguard, condition, nonzero]

end Zag.Lang.AutoCorres.L2
