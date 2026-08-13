import Std

/-!
# Nondeterministic state monad with failure

Corresponds to [`lib/Monads/nondet/Nondet_Monad.thy`](https://github.com/seL4/l4v/blob/bc2599a59c43e673dca021b10b9841e9b8da4430/lib/Monads/nondet/Nondet_Monad.thy).

The upstream monad returns a set of value/state pairs and a failure flag.
`Behavior.failed` is the propositional observation that this flag is true.
-/

namespace Zag.Lang.AutoCorres

universe u v w

/-- Extensional sets, matching Isabelle/HOL sets without a computability demand. -/
abbrev Set (α : Type u) := α → Prop

instance : Membership α (Set α) := ⟨fun set value => set value⟩

instance : EmptyCollection (Set α) := ⟨fun _ => False⟩

/-- An upstream result is a returned value paired with its post-state. -/
abbrev Result (σ : Type u) (α : Type v) := α × σ

/-- The result set and failure observation of one monadic execution. -/
structure Behavior (σ : Type u) (α : Type v) where
  results : Set (Result σ α)
  /-- This proposition holds exactly when upstream's failure flag is true. -/
  failed : Prop

/-- AutoCorres' nondeterministic state monad with failure. -/
abbrev Nondet (σ : Type u) (α : Type v) := σ → Behavior σ α

/-- Return one value without changing state or failing. -/
def pure (value : α) : Nondet σ α := fun state =>
  { results := fun result => result = (value, state)
    failed := False }

/-- Sequential composition, including failure on any reachable branch. -/
def bind (m : Nondet σ α) (f : α → Nondet σ β) : Nondet σ β := fun state =>
  { results := fun result => ∃ value middle,
      (value, middle) ∈ (m state).results ∧ result ∈ (f value middle).results
    failed := (m state).failed ∨ ∃ value middle,
      (value, middle) ∈ (m state).results ∧ (f value middle).failed }

/-- Let Zag contexts select this semantics through `PrimitiveCtx.M`. -/
instance instMonadNondet (σ : Type u) : Monad (Nondet σ) where
  pure := Zag.Lang.AutoCorres.pure
  bind := Zag.Lang.AutoCorres.bind

/-- Return the current state without changing it. -/
def get : Nondet σ σ := fun state =>
  { results := fun result => result = (state, state)
    failed := False }

/-- Replace the current state. -/
def put (newState : σ) : Nondet σ Unit := fun _ =>
  { results := fun result => result = ((), newState)
    failed := False }

/-- Choose any member of `choices`; an empty choice does not itself fail. -/
def select (choices : Set α) : Nondet σ α := fun state =>
  { results := fun result => result.1 ∈ choices ∧ result.2 = state
    failed := False }

/-- Nondeterministically execute either operand. -/
def alternative (left right : Nondet σ α) : Nondet σ α := fun state =>
  { results := fun result =>
      result ∈ (left state).results ∨ result ∈ (right state).results
    failed := (left state).failed ∨ (right state).failed }

/-- Produce no results and set the failure observation. -/
def fail : Nondet σ α := fun _ =>
  { results := ∅
    failed := True }

/-- Observe a function of the current state without changing it. -/
def gets (f : σ → α) : Nondet σ α := fun state =>
  { results := fun result => result = (f state, state)
    failed := False }

/-- Update the current state. -/
def modify (f : σ → σ) : Nondet σ Unit := fun state =>
  { results := fun result => result = ((), f state)
    failed := False }

@[simp] theorem mem_pure {value : α} {state post : σ} {result : α} :
    (result, post) ∈ (pure value state).results ↔ result = value ∧ post = state := by
  change (result, post) = (value, state) ↔ _
  constructor
  · intro equality
    cases equality
    exact ⟨rfl, rfl⟩
  · rintro ⟨rfl, rfl⟩
    rfl

@[simp] theorem mem_bind {m : Nondet σ α} {f : α → Nondet σ β}
    {state post : σ} {result : β} :
    (result, post) ∈ (bind m f state).results ↔
      ∃ value middle, (value, middle) ∈ (m state).results ∧
        (result, post) ∈ (f value middle).results :=
  Iff.rfl

@[simp] theorem failed_bind {m : Nondet σ α} {f : α → Nondet σ β} {state : σ} :
    (bind m f state).failed ↔
      (m state).failed ∨ ∃ value middle,
        (value, middle) ∈ (m state).results ∧ (f value middle).failed :=
  Iff.rfl

@[simp] theorem mem_get {state post result : σ} :
    (result, post) ∈ (get state).results ↔ result = state ∧ post = state := by
  change (result, post) = (state, state) ↔ _
  constructor
  · intro equality
    cases equality
    exact ⟨rfl, rfl⟩
  · rintro ⟨rfl, rfl⟩
    rfl

@[simp] theorem mem_put {newState state post : σ} {result : Unit} :
    (result, post) ∈ (put newState state).results ↔ result = () ∧ post = newState := by
  change (result, post) = ((), newState) ↔ _
  constructor
  · intro equality
    cases equality
    exact ⟨rfl, rfl⟩
  · rintro ⟨rfl, rfl⟩
    rfl

@[simp] theorem mem_select {choices : Set α} {state post : σ} {result : α} :
    (result, post) ∈ (select choices state).results ↔ result ∈ choices ∧ post = state :=
  Iff.rfl

@[simp] theorem mem_alternative {left right : Nondet σ α}
    {state post : σ} {result : α} :
    (result, post) ∈ (alternative left right state).results ↔
      (result, post) ∈ (left state).results ∨ (result, post) ∈ (right state).results :=
  Iff.rfl

@[simp] theorem mem_fail {state post : σ} {result : α} :
    ¬ (result, post) ∈ (fail state : Behavior σ α).results := by
  change ¬ False
  exact not_false

@[simp] theorem failed_fail {state : σ} : (fail state : Behavior σ α).failed := by
  simp [fail]

@[simp] theorem mem_gets {f : σ → α} {state post : σ} {result : α} :
    (result, post) ∈ (gets f state).results ↔ result = f state ∧ post = state := by
  change (result, post) = (f state, state) ↔ _
  constructor
  · intro equality
    cases equality
    exact ⟨rfl, rfl⟩
  · rintro ⟨rfl, rfl⟩
    rfl

@[simp] theorem mem_modify {f : σ → σ} {state post : σ} {result : Unit} :
    (result, post) ∈ (modify f state).results ↔ result = () ∧ post = f state := by
  change (result, post) = ((), f state) ↔ _
  constructor
  · intro equality
    cases equality
    exact ⟨rfl, rfl⟩
  · rintro ⟨rfl, rfl⟩
    rfl

/-! ## Exception monad combinators -/

/-- Return a normal value in the exception monad. -/
def returnOk (value : α) : Nondet σ (Except ε α) :=
  pure (.ok value)

/-- Return an exceptional value without setting the failure observation. -/
def throw (exception : ε) : Nondet σ (Except ε α) :=
  pure (.error exception)

/-- Continue normal results and propagate exceptional results unchanged. -/
def bindE (m : Nondet σ (Except ε α))
    (f : α → Nondet σ (Except ε β)) : Nondet σ (Except ε β) :=
  bind m fun result =>
    match result with
    | .error exception => throw exception
    | .ok value => f value

/-- Lift a non-exceptional computation by marking every result normal. -/
def liftE (m : Nondet σ α) : Nondet σ (Except ε α) :=
  bind m fun value => returnOk (ε := ε) value

/-- Handle exceptions, possibly changing the exception type. -/
def handle (m : Nondet σ (Except ε α))
    (handler : ε → Nondet σ (Except δ α)) : Nondet σ (Except δ α) :=
  bind m fun result =>
    match result with
    | .error exception => handler exception
    | .ok value => returnOk (ε := δ) value

@[simp] theorem mem_returnOk {value result : α} {state post : σ} :
    (Except.ok result, post) ∈ (returnOk (ε := ε) value state).results ↔
      result = value ∧ post = state := by
  simp [returnOk]

@[simp] theorem mem_throw {exception result : ε} {state post : σ} :
    (Except.error result, post) ∈ (throw (α := α) exception state).results ↔
      result = exception ∧ post = state := by
  simp [throw]

@[simp] theorem mem_bindE_ok {m : Nondet σ (Except ε α)}
    {f : α → Nondet σ (Except ε β)} {state post : σ} {result : β} :
    (Except.ok result, post) ∈ (bindE m f state).results ↔
      ∃ value middle, (Except.ok value, middle) ∈ (m state).results ∧
        (Except.ok result, post) ∈ (f value middle).results := by
  unfold bindE
  rw [mem_bind]
  constructor
  · rintro ⟨value, middle, member, next⟩
    cases value with
    | error exception =>
        change (Except.ok result, post) = (Except.error exception, middle) at next
        cases next
    | ok value => exact ⟨value, middle, member, next⟩
  · rintro ⟨value, middle, member, next⟩
    exact ⟨Except.ok value, middle, member, next⟩

@[simp] theorem mem_liftE {m : Nondet σ α} {state post : σ} {result : α} :
    (Except.ok result, post) ∈ (liftE (ε := ε) m state).results ↔
      (result, post) ∈ (m state).results := by
  simp [liftE]

@[simp] theorem mem_handle_error {m : Nondet σ (Except ε α)}
    {handler : ε → Nondet σ (Except δ α)} {state post : σ} {result : δ} :
    (Except.error result, post) ∈ (handle m handler state).results ↔
      ∃ exception middle,
        (Except.error exception, middle) ∈ (m state).results ∧
          (Except.error result, post) ∈ (handler exception middle).results := by
  unfold handle
  rw [mem_bind]
  constructor
  · rintro ⟨value, middle, member, next⟩
    cases value with
    | error exception => exact ⟨exception, middle, member, next⟩
    | ok value =>
        change (Except.error result, post) = (Except.ok value, middle) at next
        cases next
  · rintro ⟨exception, middle, member, next⟩
    exact ⟨Except.error exception, middle, member, next⟩

/-! ## Loops -/

/-- Finite executions of upstream `whileLoop`. -/
inductive WhileResult {State : Type u} {Acc : Type v}
    (test : Acc → State → Prop) (body : Acc → Nondet State Acc) :
    Option (Acc × State) → Option (Acc × State) → Prop where
  | stop (notTest : Not (test value state)) :
      WhileResult test body (some (value, state)) (some (value, state))
  | bodyFailure (holds : test value state) (failed : (body value state).failed) :
      WhileResult test body (some (value, state)) none
  | step (holds : test value state)
      (member : (next, nextState) ∈ (body value state).results)
      (rest : WhileResult test body (some (next, nextState)) result) :
      WhileResult test body (some (value, state)) result

/-- All-reachable-branches termination for `whileLoop`. -/
inductive WhileTerminates {State : Type u} {Acc : Type v}
    (test : Acc → State → Prop) (body : Acc → Nondet State Acc) :
    Acc → State → Prop where
  | stop (notTest : Not (test value state)) :
      WhileTerminates test body value state
  | step (holds : test value state)
      (rest : ∀ next nextState, (next, nextState) ∈ (body value state).results →
        WhileTerminates test body next nextState) :
      WhileTerminates test body value state

/-- Finite successful paths, finite body failure, and branch termination semantics. -/
def whileLoop {State : Type u} {Acc : Type v}
    (test : Acc → State → Prop) (body : Acc → Nondet State Acc)
    (initial : Acc) : Nondet State Acc := fun state =>
  { results := fun result =>
      WhileResult test body (some (initial, state)) (some result)
    failed := WhileResult test body (some (initial, state)) none ∨
      Not (WhileTerminates test body initial state) }

/-- Lift an exception body into the accumulator used by `whileLoop`. -/
def whileLoopEBody {State : Type u} {Acc : Type v} {Error : Type w}
    (body : Acc → Nondet State (Except Error Acc)) :
    Except Error Acc → Nondet State (Except Error Acc)
  | .error error => pure (.error error)
  | .ok value => body value

/-- Exception loop semantics: exceptional accumulators stop and are returned. -/
def whileLoopE {State : Type u} {Acc : Type v} {Error : Type w}
    (test : Acc → State → Prop)
    (body : Acc → Nondet State (Except Error Acc)) (initial : Acc) :
    Nondet State (Except Error Acc) :=
  whileLoop
    (fun result state => match result with
      | .error _ => False
      | .ok value => test value state)
    (whileLoopEBody body) (.ok initial)

/-! ## Functional computations -/

/-- A nondeterministic computation is functional when it has at most one complete
result and a successful result excludes every failure branch. -/
structure Nondet.Functional (program : Nondet State Value) : Prop where
  unique : ∀ state {left right : Result State Value},
    (program state).results left → (program state).results right → left = right
  success : ∀ state {result : Result State Value},
    (program state).results result → ¬(program state).failed

namespace Nondet.Functional

theorem pure (value : Value) : Functional (AutoCorres.pure (σ := State) value) := by
  constructor
  · intro state left right leftMember rightMember
    exact leftMember.trans rightMember.symm
  · simp [AutoCorres.pure]

theorem fail : Functional (AutoCorres.fail : Nondet State Value) := by
  constructor
  · intro state left right leftMember
    exact False.elim leftMember
  · intro state result member
    exact False.elim member

theorem gets (read : State → Value) : Functional (AutoCorres.gets read) := by
  constructor
  · intro state left right leftMember rightMember
    exact leftMember.trans rightMember.symm
  · simp [AutoCorres.gets]

theorem modify (update : State → State) : Functional (AutoCorres.modify update) := by
  constructor
  · intro state left right leftMember rightMember
    exact leftMember.trans rightMember.symm
  · simp [AutoCorres.modify]

theorem bind {first : Nondet State Alpha} {next : Alpha → Nondet State Beta}
    (firstFunctional : Functional first)
    (nextFunctional : ∀ value, Functional (next value)) :
    Functional (AutoCorres.bind first next) := by
  constructor
  · intro state left right leftMember rightMember
    obtain ⟨leftValue, leftState, leftFirst, leftNext⟩ := leftMember
    obtain ⟨rightValue, rightState, rightFirst, rightNext⟩ := rightMember
    have firstEq := firstFunctional.unique state leftFirst rightFirst
    cases firstEq
    exact (nextFunctional leftValue).unique leftState leftNext rightNext
  · intro state result member failed
    obtain ⟨value, middle, firstMember, nextMember⟩ := member
    rcases failed with firstFailed | ⟨otherValue, otherMiddle, otherMember, nextFailed⟩
    · exact firstFunctional.success state firstMember firstFailed
    · have firstEq := firstFunctional.unique state firstMember otherMember
      cases firstEq
      exact (nextFunctional value).success middle nextMember nextFailed

theorem returnOk (value : Value) :
    Functional (AutoCorres.returnOk (σ := State) (ε := Error) value) :=
  by simpa [AutoCorres.returnOk] using
    (pure (State := State) (Except.ok value : Except Error Value))

theorem throw (error : Error) :
    Functional (AutoCorres.throw (σ := State) (α := Value) error) :=
  by simpa [AutoCorres.throw] using
    (pure (State := State) (Except.error error : Except Error Value))

theorem bindE {first : Nondet State (Except Error Alpha)}
    {next : Alpha → Nondet State (Except Error Beta)}
    (firstFunctional : Functional first)
    (nextFunctional : ∀ value, Functional (next value)) :
    Functional (AutoCorres.bindE first next) := by
  apply bind firstFunctional
  intro result
  cases result with
  | error error => exact throw error
  | ok value => exact nextFunctional value

theorem liftE {program : Nondet State Value} (programFunctional : Functional program) :
    Functional (AutoCorres.liftE (ε := Error) program) := by
  apply bind programFunctional
  intro value
  exact returnOk value

theorem handle {body : Nondet State (Except Error Value)}
    {handler : Error → Nondet State (Except NewError Value)}
    (bodyFunctional : Functional body)
    (handlerFunctional : ∀ error, Functional (handler error)) :
    Functional (AutoCorres.handle body handler) := by
  apply bind bodyFunctional
  intro result
  cases result with
  | error error => exact handlerFunctional error
  | ok value => exact returnOk value

private theorem whileResult_deterministic
    {State : Type u} {Accumulator : Type v} {test : Accumulator → State → Prop}
    {body : Accumulator → Nondet State Accumulator}
    {input leftResult rightResult : Option (Accumulator × State)}
    (bodyFunctional : ∀ value, Functional (body value))
    (left : WhileResult test body input leftResult)
    (right : WhileResult test body input rightResult) :
    leftResult = rightResult := by
  induction left generalizing rightResult with
  | stop leftStopped =>
      cases right with
      | stop => rfl
      | bodyFailure rightHolds _ => exact False.elim (leftStopped rightHolds)
      | step rightHolds _ _ => exact False.elim (leftStopped rightHolds)
  | bodyFailure leftHolds leftFailed =>
      cases right with
      | stop rightStopped => exact False.elim (rightStopped leftHolds)
      | bodyFailure => rfl
      | step _ rightMember _ =>
          exact False.elim ((bodyFunctional _).success _ rightMember leftFailed)
  | step leftHolds leftMember leftRest induction =>
      cases right with
      | stop rightStopped => exact False.elim (rightStopped leftHolds)
      | bodyFailure _ rightFailed =>
          exact False.elim ((bodyFunctional _).success _ leftMember rightFailed)
      | step _ rightMember rightRest =>
          have nextEq := (bodyFunctional _).unique _ leftMember rightMember
          cases nextEq
          exact induction rightRest

private theorem whileResult_terminates
    {State : Type u} {Accumulator : Type v} {test : Accumulator → State → Prop}
    {body : Accumulator → Nondet State Accumulator}
    {input : Option (Accumulator × State)} {result : Accumulator × State}
    (bodyFunctional : ∀ value, Functional (body value))
    (success : WhileResult test body input (some result)) :
    ∀ value state, input = some (value, state) →
      WhileTerminates test body value state := by
  have general : ∀ {initial final}, WhileResult test body initial final →
      ∀ result, final = some result → ∀ value state,
        initial = some (value, state) → WhileTerminates test body value state := by
    intro initial final execution
    apply WhileResult.rec
      (motive := fun initial final _ => ∀ result, final = some result →
        ∀ value state, initial = some (value, state) →
          WhileTerminates test body value state)
    · intro current currentState stopped result finalEq value state inputEq
      cases Option.some.inj finalEq
      cases Option.some.inj inputEq
      exact .stop stopped
    · intro current currentState holds failed result finalEq
      cases finalEq
    · intro current currentState next nextState final holds member rest induction
      intro result finalEq value state inputEq
      cases Option.some.inj inputEq
      apply WhileTerminates.step holds
      intro otherValue otherState otherMember
      have nextEq := (bodyFunctional _).unique _ member otherMember
      cases nextEq
      exact induction result finalEq next nextState rfl
    · exact execution
  exact general success result rfl

theorem whileLoop {State : Type u} {Accumulator : Type v}
    {test : Accumulator → State → Prop}
    {body : Accumulator → Nondet State Accumulator}
    (bodyFunctional : ∀ value, Functional (body value)) (initial : Accumulator) :
    Functional (AutoCorres.whileLoop test body initial) := by
  constructor
  · intro state left right leftMember rightMember
    change WhileResult test body (some (initial, state)) (some left) at leftMember
    change WhileResult test body (some (initial, state)) (some right) at rightMember
    exact Option.some.inj (whileResult_deterministic bodyFunctional leftMember rightMember)
  · intro state result member failed
    change WhileResult test body (some (initial, state)) (some result) at member
    change WhileResult test body (some (initial, state)) none ∨
      ¬WhileTerminates test body initial state at failed
    rcases failed with failedRun | notTerminates
    · have impossible := whileResult_deterministic bodyFunctional member failedRun
      cases impossible
    · exact notTerminates (whileResult_terminates bodyFunctional member _ _ rfl)

/-- The closed exception loop used by canonical generated L2 syntax. -/
theorem whileLoopE0 {State Error Accumulator : Type}
    {test : Accumulator → State → Prop}
    {body : Accumulator → Nondet State (Except Error Accumulator)}
    (bodyFunctional : ∀ value, Functional (body value)) (initial : Accumulator) :
    Functional (AutoCorres.whileLoopE test body initial) := by
  unfold AutoCorres.whileLoopE
  apply whileLoop
  intro result
  cases result with
  | error error => exact pure (Except.error error)
  | ok value => exact bodyFunctional value

end Nondet.Functional

/-! ## Semantic regression pins -/

/-- Empty nondeterminism and failure have the same empty result set but differ in failure. -/
theorem empty_nonfailure_is_not_failure (state : σ) :
    (select (∅ : Set α) state).results = (fail state : Behavior σ α).results ∧
    ¬ (select (∅ : Set α) state).failed ∧
    (fail state : Behavior σ α).failed := by
  refine ⟨?_, ?_, ?_⟩
  · funext result
    apply propext
    change (False ∧ result.2 = state) ↔ False
    simp
  · exact id
  · exact True.intro

/-- A failure before a bind remains observable after the bind. -/
theorem bind_preserves_failure {m : Nondet σ α} {f : α → Nondet σ β} {state : σ}
    (failed : (m state).failed) : (bind m f state).failed :=
  Or.inl failed

/-- A failing reachable continuation also makes the whole bind fail. -/
theorem bind_observes_branch_failure {m : Nondet σ α} {f : α → Nondet σ β}
    {state middle : σ} {value : α}
    (member : (value, middle) ∈ (m state).results)
    (failed : (f value middle).failed) : (bind m f state).failed :=
  Or.inr ⟨value, middle, member, failed⟩

end Zag.Lang.AutoCorres
