import Std

/-!
# Reader option monad

Corresponds to [`lib/Monads/reader_option/Reader_Option_Monad.thy`](https://github.com/seL4/l4v/blob/bc2599a59c43e673dca021b10b9841e9b8da4430/lib/Monads/reader_option/Reader_Option_Monad.thy).

The loop follows the upstream finite-run relation. In particular, failure and
the absence of a finite run both denote `none`; no execution fuel is imposed.
-/

namespace Zag.Lang.AutoCorres

universe u v w

/-- A read-only state projection which may fail. -/
abbrev Lookup (State : Type u) (Value : Type v) := State → Option Value

/-- Sequential composition in the reader option monad. -/
def obind (first : Lookup State α) (next : α → Lookup State β) : Lookup State β :=
  fun state =>
    match first state with
    | none => none
    | some value => next value state

infixl:53 " |>> " => obind

/-- Return a value independently of the read-only state. -/
def oreturn (value : α) : Lookup State α :=
  fun _ => some value

/-- Fail independently of the read-only state. -/
def ofail : Lookup State α :=
  fun _ => none

/-- Read a function of the current state. -/
def ogets (read : State → α) : Lookup State α :=
  fun state => some (read state)

/-- Succeed with unit exactly when the state satisfies the guard. -/
def oguard (condition : State → Bool) : Lookup State Unit :=
  fun state =>
    match condition state with
    | true => some ()
    | false => none

/-- Select a reader-option computation from a state-dependent condition. -/
def ocondition (condition : State → Bool)
    (thenProgram elseProgram : Lookup State α) : Lookup State α :=
  fun state =>
    match condition state with
    | true => thenProgram state
    | false => elseProgram state

@[simp] theorem oreturn_bind (value : α) (next : α → Lookup State β) :
    oreturn value |>> next = next value := by
  rfl

@[simp] theorem obind_return (program : Lookup State α) :
    program |>> oreturn = program := by
  funext state
  cases programEq : program state <;> simp [obind, oreturn, programEq]

theorem obind_assoc (program : Lookup State α) (next : α → Lookup State β)
    (last : β → Lookup State γ) :
    (program |>> next) |>> last = program |>> fun value => next value |>> last := by
  funext state
  cases programEq : program state <;> simp [obind, programEq]

@[simp] theorem obind_fail (program : Lookup State α) :
    program |>> (fun _ => (ofail : Lookup State β)) = ofail := by
  funext state
  cases programEq : program state <;> simp [obind, ofail, programEq]

@[simp] theorem ofail_bind (next : α → Lookup State β) :
    (ofail : Lookup State α) |>> next = ofail := by
  rfl

@[simp] theorem oreturn_apply (value : α) (state : State) :
    oreturn value state = some value := by
  rfl

@[simp] theorem ofail_apply (state : State) :
    (ofail state : Option α) = none := by
  rfl

@[simp] theorem ogets_apply (read : State → α) (state : State) :
    ogets read state = some (read state) := by
  rfl

@[simp] theorem oguard_apply (condition : State → Bool) (state : State) :
    oguard condition state = if condition state then some () else none := by
  cases conditionEq : condition state <;> simp [oguard, conditionEq]

@[simp] theorem ocondition_apply (condition : State → Bool)
    (thenProgram elseProgram : Lookup State α) (state : State) :
    ocondition condition thenProgram elseProgram state =
      if condition state then thenProgram state else elseProgram state := by
  cases conditionEq : condition state <;> simp [ocondition, conditionEq]

/-- Finite executions of the plain option-monad while loop. -/
inductive OptionWhile (condition : α → Bool) (body : α → Option α) :
    Option α → Option α → Prop where
  | final (stopped : condition value = false) :
      OptionWhile condition body (some value) (some value)
  | fail (continues : condition value = true) (failed : body value = none) :
      OptionWhile condition body (some value) none
  | step (continues : condition value = true) (nextValue : body value = some next)
      (rest : OptionWhile condition body (some next) result) :
      OptionWhile condition body (some value) result

/-- The finite-run relation has at most one result for each input. -/
theorem OptionWhile.deterministic
    (left : OptionWhile condition body input leftResult)
    (right : OptionWhile condition body input rightResult) :
    leftResult = rightResult := by
  induction left with
  | final stopped =>
      cases right with
      | final => rfl
      | fail continues _ => simp [stopped] at continues
      | step continues _ _ => simp [stopped] at continues
  | fail continues failed =>
      cases right with
      | final stopped => simp [continues] at stopped
      | fail => rfl
      | step _ nextValue _ => simp [failed] at nextValue
  | step continues nextValue rest induction =>
      cases right with
      | final stopped => simp [continues] at stopped
      | fail _ failed => simp [nextValue] at failed
      | step _ nextValue' rest' =>
          cases Option.some.inj (nextValue.symm.trans nextValue')
          exact induction rest'

/--
The upstream option loop: choose its unique finite result, or return failure
when there is no finite run.
-/
noncomputable def optionWhile (condition : α → Bool) (body : α → Option α)
    (initial : α) : Option α := by
  classical
  exact if run : ∃ result, OptionWhile condition body (some initial) result then
      Classical.choose run
    else
      none

theorem optionWhile_eq_of_run
    (run : OptionWhile condition body (some initial) result) :
    optionWhile condition body initial = result := by
  rw [optionWhile]
  split
  · rename_i existsRun
    exact OptionWhile.deterministic (Classical.choose_spec existsRun) run
  · rename_i noRun
    exact False.elim (noRun ⟨result, run⟩)

theorem optionWhile_run_of_eq_some
    (success : optionWhile condition body initial = some result) :
    OptionWhile condition body (some initial) (some result) := by
  classical
  unfold optionWhile at success
  split at success
  · rename_i existsRun
    have run := Classical.choose_spec existsRun
    rw [success] at run
    exact run
  · simp_all

@[simp] theorem optionWhile_final (stopped : condition value = false) :
    optionWhile condition body value = some value :=
  optionWhile_eq_of_run (.final stopped)

@[simp] theorem optionWhile_fail (continues : condition value = true)
    (failed : body value = none) :
    optionWhile condition body value = none :=
  optionWhile_eq_of_run (.fail continues failed)

theorem optionWhile_step (continues : condition value = true)
    (nextValue : body value = some next) :
    optionWhile condition body value = optionWhile condition body next := by
  by_cases finite : ∃ result, OptionWhile condition body (some next) result
  · obtain ⟨result, rest⟩ := finite
    rw [optionWhile_eq_of_run rest]
    exact optionWhile_eq_of_run (.step continues nextValue rest)
  · have noCurrent : ¬ ∃ result, OptionWhile condition body (some value) result := by
      rintro ⟨result, run⟩
      cases run with
      | final stopped => simp [continues] at stopped
      | fail _ failed => simp [nextValue] at failed
      | step _ nextValue' rest =>
          cases Option.some.inj (nextValue.symm.trans nextValue')
          exact finite ⟨result, rest⟩
    simp [optionWhile, finite, noCurrent]

/-- A well-founded variant guarantees a finite success or failure run. -/
theorem optionWhile_exists_of_wellFounded
    (invariant : α → Prop) (relation : α → α → Prop)
    (wellFounded : WellFounded relation)
    (initialInvariant : invariant initial)
    (decreases : ∀ value next, invariant value → condition value = true →
      body value = some next → relation next value)
    (preserves : ∀ value next, invariant value → condition value = true →
      body value = some next → invariant next) :
    ∃ result, OptionWhile condition body (some initial) result := by
  induction initial using wellFounded.induction with
  | h value induction =>
      cases conditionEq : condition value with
      | false => exact ⟨some value, .final conditionEq⟩
      | true =>
          cases bodyEq : body value with
          | none => exact ⟨none, .fail conditionEq bodyEq⟩
          | some next =>
              obtain ⟨result, rest⟩ := induction next
                (decreases value next initialInvariant conditionEq bodyEq)
                (preserves value next initialInvariant conditionEq bodyEq)
              exact ⟨result, .step conditionEq bodyEq rest⟩

/-- Lift the option loop pointwise over the read-only state. -/
noncomputable def owhile (condition : α → State → Bool)
    (body : α → Lookup State α) (initial : α) : Lookup State α :=
  fun state => optionWhile (fun value => condition value state)
    (fun value => body value state) initial

/-- One-step unfolding of the relational reader-option loop. -/
theorem owhile_unroll (condition : α → State → Bool)
    (body : α → Lookup State α) (initial : α) :
    owhile condition body initial =
      ocondition (condition initial) (body initial |>> owhile condition body)
        (oreturn initial) := by
  funext state
  simp only [owhile, ocondition_apply]
  cases conditionEq : condition initial state with
  | false => simp [conditionEq]
  | true =>
      cases bodyEq : body initial state with
      | none =>
          rw [optionWhile_fail
            (condition := fun value => condition value state)
            (body := fun value => body value state) conditionEq bodyEq]
          simp [bodyEq, obind]
      | some next =>
          rw [optionWhile_step
            (condition := fun value => condition value state)
            (body := fun value => body value state) conditionEq bodyEq]
          simp [bodyEq, obind, owhile]

/-- Invariant rule for terminating reader-option loops. -/
theorem owhile_rule
    (condition : α → State → Bool) (body : α → Lookup State α)
    (invariant : α → State → Prop) (relation : α → α → Prop)
    (initial : α) (state : State) (postcondition : Option α → Prop)
    (initialInvariant : invariant initial state)
    (wellFounded : WellFounded relation)
    (decreases : ∀ value next, invariant value state → condition value state = true →
      body value state = some next → relation next value)
    (preserves : ∀ value next, invariant value state → condition value state = true →
      body value state = some next → invariant next state)
    (onFailure : ∀ value, invariant value state → condition value state = true →
      body value state = none → postcondition none)
    (onFinal : ∀ value, invariant value state → condition value state = false →
      postcondition (some value)) :
    postcondition (owhile condition body initial state) := by
  obtain ⟨result, run⟩ := optionWhile_exists_of_wellFounded
    (condition := fun value => condition value state)
    (body := fun value => body value state)
    (fun value => invariant value state) relation wellFounded initialInvariant decreases preserves
  change postcondition
    (optionWhile (fun value => condition value state) (fun value => body value state) initial)
  rw [optionWhile_eq_of_run run]
  have conclude : ∀ {input result},
      OptionWhile (fun value => condition value state) (fun value => body value state)
        input result →
      (∀ value, input = some value → invariant value state) → postcondition result := by
    intro input result execution
    induction execution with
    | final stopped =>
        intro holds
        exact onFinal _ (holds _ rfl) stopped
    | fail continues failed =>
        intro holds
        exact onFailure _ (holds _ rfl) continues failed
    | step continues nextValue _ induction =>
        intro holds
        apply induction
        intro value equality
        cases Option.some.inj equality
        exact preserves _ _ (holds _ rfl) continues nextValue
  apply conclude run
  intro value equality
  cases Option.some.inj equality
  exact initialInvariant

end Zag.Lang.AutoCorres
