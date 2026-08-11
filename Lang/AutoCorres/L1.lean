import Lang.AutoCorres.NonDetMonadEx
import Lang.AutoCorres.CorresXF
import Lang.AutoCorres.Simpl.Termination

/-!
# AutoCorres L1 definitions

Corresponds to [`tools/autocorres/L1Defs.thy`](https://github.com/seL4/l4v/blob/bc2599a59c43e673dca021b10b9841e9b8da4430/tools/autocorres/L1Defs.thy).
-/

namespace Zag.Lang.AutoCorres.L1

open Zag.Lang.AutoCorres

universe u v w x

/-- AutoCorres' first shallow IR: normal and abrupt unit returns over state. -/
abbrev L1Program (State : Type u) := Nondet State (Except Unit Unit)

/-- `L1_seq`: run the right operand only after a normal left result. -/
def seq (left right : L1Program State) : L1Program State :=
  bindE left fun _ => right

/-- `L1_skip`: terminate normally without changing the state. -/
def skip : L1Program State :=
  returnOk ()

/-- `L1_modify`: apply one deterministic state transformation. -/
def modify (transform : State -> State) : L1Program State :=
  liftE (AutoCorres.modify transform)

/-- `L1_condition`: inspect the current state and select exactly one branch. -/
noncomputable def condition (test : State -> Prop)
    (thenProgram elseProgram : L1Program State) : L1Program State := by
  classical
  exact fun state => if test state then thenProgram state else elseProgram state

/-- `L1_catch`: handle an abrupt unit result and leave normal results alone. -/
def «catch» (body handler : L1Program State) : L1Program State :=
  handle body fun _ => handler

/-- `L1_while`, the unit-specialized exception loop. -/
def «while» (test : State -> Prop) (body : L1Program State) : L1Program State :=
  whileLoopE (fun _ state => test state) (fun _ => body) ()

/-- `L1_throw`: terminate abruptly without changing the state. -/
def throw : L1Program State :=
  AutoCorres.throw ()

/-- `L1_spec`: nondeterministically choose a related post-state. -/
def spec (relation : Set (State × State)) : L1Program State :=
  liftE (AutoCorres.spec relation)

/-- `L1_guard`: fail unless the state predicate holds. -/
def guard (test : State -> Prop) : L1Program State :=
  liftE (AutoCorres.guard test)

/-- `L1_init`: assign an arbitrary value through a local-variable updater. -/
def init (update : (Value -> Value) -> State -> State) : L1Program State :=
  bindE (liftE (select fun _ : Value => True)) fun value =>
    liftE (AutoCorres.modify (update fun _ => value))

/-- `L1_fail`: fail with no result. -/
def fail : L1Program State :=
  AutoCorres.fail

/-! ## Reified syntax -/

/-- Canonical reified syntax shared by the structural L1 passes. -/
inductive Syntax (State : Type u) where
  | skip
  | seq (left right : Syntax State)
  | modify (transform : State -> State)
  | condition (test : State -> Prop) (thenProgram elseProgram : Syntax State)
  | «catch» (body handler : Syntax State)
  | «while» (test : State -> Prop) (body : Syntax State)
  | throw
  | spec (relation : Set (State × State))
  | guard (test : State -> Prop)
  | fail
  /-- A statically resolved call. The body is reified so recursive schedulers can
  instantiate it at the preceding recursion measure. -/
  | «call» (body : Syntax State)

namespace Syntax

/-- Interpret canonical L1 syntax using the existing shallow L1 semantics. -/
@[simp] noncomputable def denote : Syntax State -> L1Program State
  | .skip => L1.skip
  | .seq left right => L1.seq left.denote right.denote
  | .modify transform => L1.modify transform
  | .condition test thenProgram elseProgram =>
      L1.condition test thenProgram.denote elseProgram.denote
  | .catch body handler => L1.catch body.denote handler.denote
  | .while test body => L1.while test body.denote
  | .throw => L1.throw
  | .spec relation => L1.spec relation
  | .guard test => L1.guard test
  | .fail => L1.fail
  | .call body => body.denote

end Syntax

/-- `L1_recguard`: recursive calls at measure zero fail. -/
noncomputable def recguard (measure : Nat) (body : L1Program State) : L1Program State :=
  condition (fun _ => measure = 0) fail body

/-- Decrease the natural-number recursion guard, saturating at zero. -/
def recguard_dec (measure : Nat) : Nat :=
  measure - 1

@[simp] theorem recguard_dec_succ (measure : Nat) :
    recguard_dec (measure + 1) = measure := by
  simp [recguard_dec]

/-! ## SIMPL correspondence -/

/-- Map the two successful SIMPL outcomes to their exact L1 result. -/
def Matches (program : L1Program State) (initial : State) :
    Simpl.XState State Fault -> Prop
  | .normal state => (Except.ok (), state) ∈ (program initial).results
  | .abrupt state => (Except.error (), state) ∈ (program initial).results
  | .fault _ => False
  | .stuck => False

/--
Upstream `L1corres`. The L1 program is the abstract target: under its no-fail
premise, every SIMPL execution must map normal/abrupt exactly into its result
set, while fault and stuck are rejected. `checkTermination` independently
selects the SIMPL all-branches termination obligation.
-/
def L1Corres (checkTermination : Bool) (env : Simpl.Body State Proc Fault)
    (target : L1Program State) (source : Simpl.Com State Proc Fault) : Prop :=
  ∀ state, Not (target state).failed ->
    (∀ result, Simpl.Exec env source (.normal state) result ->
      Matches target state result) ∧
    (checkTermination = true -> Simpl.Terminates env source (.normal state))

/-! ## Primitive correspondence rules -/

theorem L1Corres_skip (checkTermination : Bool) (env : Simpl.Body State Proc Fault) :
    L1Corres checkTermination env (skip : L1Program State) .Skip := by
  intro state _
  constructor
  · intro result execution
    cases execution
    simp [Matches, skip, returnOk]
  · intro _
    exact .skip

theorem L1Corres_throw (checkTermination : Bool) (env : Simpl.Body State Proc Fault) :
    L1Corres checkTermination env (throw : L1Program State) .Throw := by
  intro state _
  constructor
  · intro result execution
    cases execution
    simp [Matches, throw, AutoCorres.throw]
  · intro _
    exact .throw

/-- A resolved SIMPL call corresponds to the already certified callee body. -/
theorem L1Corres_call {State : Type u} {Proc : Type v} {Fault : Type w}
    {checkTermination : Bool} {env : Simpl.Body State Proc Fault}
    {proc : Proc} {sourceBody : Simpl.Com State Proc Fault}
    {targetBody : L1Program State}
    (defined : env proc = some sourceBody)
    (bodyCorres : L1Corres checkTermination env targetBody sourceBody) :
    L1Corres checkTermination env targetBody (.Call proc) := by
  intro state noFail
  have bodyRule := bodyCorres state noFail
  constructor
  · intro result execution
    cases execution with
    | «call» found bodyExecution =>
        rw [defined] at found
        cases Option.some.inj found
        exact bodyRule.1 result bodyExecution
    | callUndefined missing =>
        rw [defined] at missing
        contradiction
  · intro check
    exact .call defined (bodyRule.2 check)

theorem L1Corres_seq {State : Type u} {Proc : Type v} {Fault : Type w}
    {checkTermination : Bool} {env : Simpl.Body State Proc Fault}
    {left right : L1Program State} {leftCom rightCom : Simpl.Com State Proc Fault}
    (leftCorres : L1Corres checkTermination env left leftCom)
    (rightCorres : L1Corres checkTermination env right rightCom) :
    L1Corres checkTermination env (seq left right) (.Seq leftCom rightCom) := by
  intro state noFail
  have leftNoFail : Not (left state).failed := by
    intro failed
    exact noFail (Or.inl failed)
  have leftRule := leftCorres state leftNoFail
  have rightNoFail {middle : State}
      (member : (Except.ok (), middle) ∈ (left state).results) :
      Not (right middle).failed := by
    intro failed
    exact noFail (Or.inr ⟨Except.ok (), middle, member, failed⟩)
  constructor
  · intro result execution
    cases execution with
    | seq firstExecution secondExecution =>
        have firstMatch := leftRule.1 _ firstExecution
        rename_i middle
        cases middle with
        | normal middle =>
            have secondRule := rightCorres middle (rightNoFail firstMatch)
            have secondMatch := secondRule.1 result secondExecution
            cases result with
            | normal post =>
                change (Except.ok (), post) ∈ (seq left right state).results
                exact ⟨Except.ok (), middle, firstMatch, secondMatch⟩
            | abrupt post =>
                change (Except.error (), post) ∈ (seq left right state).results
                exact ⟨Except.ok (), middle, firstMatch, secondMatch⟩
            | fault label => exact secondMatch
            | stuck => exact secondMatch
        | abrupt middle =>
            cases secondExecution
            change (Except.error (), middle) ∈ (seq left right state).results
            exact ⟨Except.error (), middle, firstMatch, rfl⟩
        | fault label => exact False.elim firstMatch
        | stuck => exact False.elim firstMatch
  · intro check
    apply Simpl.Terminates.seq (leftRule.2 check)
    intro middle execution
    have matched := leftRule.1 middle execution
    cases middle with
    | normal middle =>
        exact (rightCorres middle (rightNoFail matched)).2 check
    | abrupt middle => exact .abrupt
    | fault label => exact False.elim matched
    | stuck => exact False.elim matched

theorem L1Corres_modify (checkTermination : Bool) (env : Simpl.Body State Proc Fault)
    (transform : State -> State) :
    L1Corres checkTermination env (modify transform) (.Basic transform) := by
  intro state _
  constructor
  · intro result execution
    cases execution
    simp [Matches, modify, liftE, returnOk]
  · intro _
    exact .basic

theorem L1Corres_condition
    (left : L1Corres checkTermination env thenProgram thenCom)
    (right : L1Corres checkTermination env elseProgram elseCom) :
    L1Corres checkTermination env (condition test thenProgram elseProgram)
      (.Cond test thenCom elseCom) := by
  intro state noFail
  by_cases holds : test state
  · have branch := left state (by simpa [condition, holds] using noFail)
    constructor
    · intro result execution
      cases execution with
      | condTrue _ selected =>
          simpa [Matches, condition, holds] using branch.1 result selected
      | condFalse notHolds _ => exact False.elim (notHolds holds)
    · intro check
      exact .condTrue holds (branch.2 check)
  · have branch := right state (by simpa [condition, holds] using noFail)
    constructor
    · intro result execution
      cases execution with
      | condTrue isTrue _ => exact False.elim (holds isTrue)
      | condFalse _ selected =>
          simpa [Matches, condition, holds] using branch.1 result selected
    · intro check
      exact .condFalse holds (branch.2 check)

theorem L1Corres_catch {State : Type u} {Proc : Type v} {Fault : Type w}
    {checkTermination : Bool} {env : Simpl.Body State Proc Fault}
    {body handler : L1Program State} {bodyCom handlerCom : Simpl.Com State Proc Fault}
    (bodyCorres : L1Corres checkTermination env body bodyCom)
    (handlerCorres : L1Corres checkTermination env handler handlerCom) :
    L1Corres checkTermination env («catch» body handler) (.Catch bodyCom handlerCom) := by
  intro state noFail
  have bodyNoFail : Not (body state).failed := by
    intro failed
    exact noFail (Or.inl failed)
  have bodyRule := bodyCorres state bodyNoFail
  have handlerNoFail {thrown : State}
      (member : (Except.error (), thrown) ∈ (body state).results) :
      Not (handler thrown).failed := by
    intro failed
    exact noFail (Or.inr ⟨Except.error (), thrown, member, failed⟩)
  constructor
  · intro result execution
    cases execution with
    | catchMatch bodyExecution handlerExecution =>
        have bodyMatch := bodyRule.1 _ bodyExecution
        have handlerRule := handlerCorres _ (handlerNoFail bodyMatch)
        have handlerMatch := handlerRule.1 result handlerExecution
        cases result with
        | normal post =>
            change (Except.ok (), post) ∈ («catch» body handler state).results
            exact ⟨Except.error (), _, bodyMatch, handlerMatch⟩
        | abrupt post =>
            change (Except.error (), post) ∈ («catch» body handler state).results
            exact ⟨Except.error (), _, bodyMatch, handlerMatch⟩
        | fault label => exact handlerMatch
        | stuck => exact handlerMatch
    | catchMiss bodyExecution notAbrupt =>
        have bodyMatch := bodyRule.1 result bodyExecution
        cases result with
        | normal post =>
            change (Except.ok (), post) ∈ («catch» body handler state).results
            exact ⟨Except.ok (), post, bodyMatch, rfl⟩
        | abrupt post => exact False.elim (notAbrupt True.intro)
        | fault label => exact bodyMatch
        | stuck => exact bodyMatch
  · intro check
    apply Simpl.Terminates.catch (bodyRule.2 check)
    intro thrown execution
    have matched := bodyRule.1 _ execution
    exact (handlerCorres thrown (handlerNoFail matched)).2 check

private theorem while_exec_matches {State : Type u} {Proc : Type v} {Fault : Type w}
    {checkTermination : Bool} {env : Simpl.Body State Proc Fault}
    {body : L1Program State} {bodyCom : Simpl.Com State Proc Fault}
    {test : State -> Prop}
    (bodyCorres : L1Corres checkTermination env body bodyCom)
    {state : State} {result : Simpl.XState State Fault}
    (noFail : Not («while» test body state).failed)
    (execution : Simpl.Exec env (.While test bodyCom) (.normal state) result) :
    Matches («while» test body) state result := by
  generalize commandEq : Simpl.Com.While test bodyCom = command at execution
  generalize initialEq : Simpl.XState.normal state = initial at execution
  induction execution generalizing state
  case whileTrue test' body' source middleState final holds bodyExecution
      restExecution bodyIH restIH =>
      let current := state
      cases commandEq
      cases initialEq
      have bodyNoFail : Not (body current).failed := by
        intro failed
        apply noFail
        exact Or.inl (.bodyFailure holds failed)
      have bodyMatch := (bodyCorres current bodyNoFail).1 _ bodyExecution
      dsimp [current] at bodyMatch noFail ⊢
      cases middleState with
      | normal middle =>
          have restNoFail : Not («while» test body middle).failed := by
            intro failed
            rcases failed with failed | notTerminates
            · exact noFail (Or.inl (.step holds bodyMatch failed))
            · apply noFail
              apply Or.inr
              intro terminates
              cases terminates with
              | stop notHolds => exact notHolds holds
              | step _ branches => exact notTerminates (branches _ _ bodyMatch)
          have restMatch := restIH restNoFail rfl rfl
          cases final with
          | normal post => exact WhileResult.step holds bodyMatch restMatch
          | abrupt post => exact WhileResult.step holds bodyMatch restMatch
          | fault label => exact restMatch
          | stuck => exact restMatch
      | abrupt middle =>
          cases restExecution
          change WhileResult _ _ (some (Except.ok (), current))
            (some (Except.error (), middle))
          exact .step holds bodyMatch (.stop not_false)
      | fault label => exact False.elim bodyMatch
      | stuck => exact False.elim bodyMatch
  case whileFalse test' body' source notHolds =>
      let current := state
      cases commandEq
      cases initialEq
      change WhileResult _ _ (some (Except.ok (), current))
        (some (Except.ok (), current))
      exact .stop notHolds
  all_goals cases commandEq <;> cases initialEq

private theorem while_terminates {State : Type u} {Proc : Type v} {Fault : Type w}
    {checkTermination : Bool} {env : Simpl.Body State Proc Fault}
    {body : L1Program State} {bodyCom : Simpl.Com State Proc Fault}
    {test : State -> Prop} {loopTest : Except Unit Unit -> State -> Prop}
    (testOk : ∀ state, loopTest (Except.ok ()) state ↔ test state)
    (bodyCorres : L1Corres checkTermination env body bodyCom)
    {state : State}
    (noFailure : Not (WhileResult loopTest (whileLoopEBody fun _ => body)
      (some (Except.ok (), state)) none))
    (monadTerminates : WhileTerminates loopTest
      (whileLoopEBody fun _ => body) (Except.ok ()) state)
    (check : checkTermination = true) :
    Simpl.Terminates env (.While test bodyCom) (.normal state) := by
  generalize valueEq : (Except.ok () : Except Unit Unit) = value at monadTerminates
  induction monadTerminates with
  | stop notHolds =>
      cases valueEq
      exact .whileFalse (fun holds => notHolds ((testOk _).mpr holds))
  | step holds branches branchIH =>
      cases valueEq
      rename_i current
      have testHolds : test current := (testOk current).mp holds
      have bodyNoFail : Not (body current).failed := by
        intro failed
        exact noFailure (.bodyFailure holds failed)
      have bodyRule := bodyCorres current bodyNoFail
      apply Simpl.Terminates.whileTrue testHolds (bodyRule.2 check)
      intro result execution
      have bodyMatch := bodyRule.1 result execution
      cases result with
      | normal middle =>
          have restNoFailure : Not (WhileResult loopTest
              (whileLoopEBody fun _ => body)
              (some (Except.ok (), middle)) none) := by
            intro failed
            exact noFailure (.step holds bodyMatch failed)
          exact branchIH _ _ bodyMatch restNoFailure rfl
      | abrupt middle => exact .abrupt
      | fault label => exact False.elim bodyMatch
      | stuck => exact False.elim bodyMatch

theorem L1Corres_while {State : Type u} {Proc : Type v} {Fault : Type w}
    {checkTermination : Bool} {env : Simpl.Body State Proc Fault}
    {body : L1Program State} {bodyCom : Simpl.Com State Proc Fault}
    {test : State -> Prop}
    (bodyCorres : L1Corres checkTermination env body bodyCom) :
    L1Corres checkTermination env («while» test body) (.While test bodyCom) := by
  intro state noFail
  constructor
  · intro result execution
    exact while_exec_matches bodyCorres noFail execution
  · intro check
    unfold «while» whileLoopE whileLoop at noFail
    have noFailure := fun failed => noFail (Or.inl failed)
    have monadTerminates := Classical.byContradiction fun notTerminates =>
      noFail (Or.inr notTerminates)
    apply while_terminates (fun _ => Iff.rfl) bodyCorres noFailure
      monadTerminates check

theorem L1Corres_guard {State : Type u} {Proc : Type v} {Fault : Type w}
    {checkTermination : Bool} {env : Simpl.Body State Proc Fault}
    {body : L1Program State} {bodyCom : Simpl.Com State Proc Fault}
    {test : State -> Prop}
    (bodyCorres : L1Corres checkTermination env body bodyCom)
    (fault : Fault) :
    L1Corres checkTermination env (seq (guard test) body)
      (.Guard fault test bodyCom) := by
  intro state noFail
  have holds : test state := Classical.byContradiction fun notHolds =>
    noFail (Or.inl (by simp [guard, liftE, notHolds]))
  have bodyNoFail : Not (body state).failed := by
    intro failed
    apply noFail
    exact Or.inr ⟨Except.ok (), state, by simp [guard, liftE, holds], failed⟩
  have branch := bodyCorres state bodyNoFail
  have guardMember : (Except.ok (), state) ∈ (guard test state).results := by
    simp [guard, liftE, holds]
  constructor
  · intro result execution
    cases execution with
    | guard _ selected =>
        have matched := branch.1 result selected
        cases result with
        | normal post =>
            change (Except.ok (), post) ∈ (body state).results at matched
            change (Except.ok (), post) ∈ (seq (guard test) body state).results
            unfold seq bindE
            exact ⟨Except.ok (), state, guardMember, matched⟩
        | abrupt post =>
            change (Except.error (), post) ∈ (body state).results at matched
            change (Except.error (), post) ∈ (seq (guard test) body state).results
            unfold seq bindE
            exact ⟨Except.ok (), state, guardMember, matched⟩
        | fault label => exact matched
        | stuck => exact matched
    | guardFault notHolds => exact False.elim (notHolds holds)
  · intro check
    exact .guard holds (branch.2 check)

theorem L1Corres_spec (checkTermination : Bool) (env : Simpl.Body State Proc Fault)
    (relation : Simpl.StateRel State) :
    L1Corres checkTermination env (spec relation) (.Spec relation) := by
  intro state noFail
  have baseNoFail : Not (AutoCorres.spec relation state).failed := by
    intro failed
    apply noFail
    exact Or.inl failed
  have inhabited : ∃ post, relation (state, post) :=
    Classical.byContradiction fun empty =>
      baseNoFail ((AutoCorres.failed_spec (relation := relation) (state := state)).2 empty)
  constructor
  · intro result execution
    cases execution with
    | spec member =>
        simp only [Matches, spec, AutoCorres.mem_liftE, AutoCorres.mem_spec]
        exact ⟨member, True.intro⟩
    | specStuck empty => exact False.elim (empty inhabited.choose inhabited.choose_spec)
  · intro _
    exact .spec

private theorem liftE_no_error {program : Nondet State Value}
    {state post : State} {exception : Exception} :
    Not ((Except.error exception, post) ∈
      (liftE program state : Behavior State (Except Exception Value)).results) := by
  rintro ⟨value, middle, _, continuation⟩
  change (Except.error exception, post) = (Except.ok value, middle) at continuation
  cases continuation

@[simp] theorem mem_init_ok (update : (Value -> Value) -> State -> State) :
    (Except.ok (), post) ∈ (init update state).results ↔
      ∃ value, post = update (fun _ => value) state := by
  unfold init bindE
  constructor
  · rintro ⟨result, middle, member, continuation⟩
    cases result with
    | error exception => exact False.elim (liftE_no_error member)
    | ok value =>
        rw [mem_liftE, mem_select] at member
        rw [mem_liftE, mem_modify] at continuation
        rcases member with ⟨_, rfl⟩
        rcases continuation with ⟨_, rfl⟩
        exact ⟨value, rfl⟩
  · rintro ⟨value, rfl⟩
    refine ⟨Except.ok value, state, ?_, by simp⟩
    rw [mem_liftE, mem_select]
    exact ⟨True.intro, rfl⟩

@[simp] theorem init_no_error (update : (Value -> Value) -> State -> State) :
    Not ((Except.error exception, post) ∈ (init update state).results) := by
  unfold init bindE
  rintro ⟨result, middle, member, continuation⟩
  cases result with
  | error exception => exact liftE_no_error member
  | ok value => exact liftE_no_error continuation

@[simp] theorem init_not_failed (update : (Value -> Value) -> State -> State) :
    Not (init update state).failed := by
  intro failed
  unfold init bindE at failed
  rcases failed with failed | ⟨result, middle, member, failed⟩
  · simp [liftE, bind, select, returnOk, pure] at failed
  · cases result with
    | error exception => exact False.elim (liftE_no_error member)
    | ok value =>
        simp [liftE, bind, AutoCorres.modify, returnOk, pure] at failed

/-- `L1_init` returns normally at every state produced by an arbitrary value. -/
theorem init_behavior (update : (Value -> Value) -> State -> State) (state : State) :
    (∀ post, (Except.ok (), post) ∈ (init update state).results ↔
      ∃ value, post = update (fun _ => value) state) ∧
    (∀ exception post, Not ((Except.error exception, post) ∈
      (init update state).results)) ∧
    Not (init update state).failed := by
  exact ⟨fun _ => mem_init_ok update, fun _ _ => init_no_error update,
    init_not_failed update⟩

/-- Upstream `L1_init_alt_def`: initialization is its exact nondeterministic spec. -/
theorem init_alt_def [Nonempty Value]
    (update : (Value -> Value) -> State -> State) :
    init update = spec (fun pair =>
      ∃ value, pair.2 = update (fun _ => value) pair.1) := by
  funext state
  cases leftEq : init update state with
  | mk leftResults leftFailed =>
      cases rightEq : spec (fun pair =>
          ∃ value, pair.2 = update (fun _ => value) pair.1) state with
      | mk rightResults rightFailed =>
          congr
          · funext result
            rcases result with ⟨result, post⟩
            apply propext
            have leftResultsEq : (init update state).results = leftResults :=
              congrArg Behavior.results leftEq
            have rightResultsEq :
                (spec (fun pair => ∃ value,
                  pair.2 = update (fun _ => value) pair.1) state).results = rightResults :=
              congrArg Behavior.results rightEq
            rw [← leftResultsEq, ← rightResultsEq]
            cases result with
            | error exception =>
                constructor
                · intro member
                  exact False.elim (init_no_error update member)
                · intro member
                  apply False.elim
                  exact liftE_no_error (program := AutoCorres.spec fun pair =>
                    ∃ value, pair.2 = update (fun _ => value) pair.1) member
            | ok result =>
                cases result
                change ((Except.ok (), post) ∈ (init update state).results) ↔
                  (Except.ok (), post) ∈
                    (liftE (AutoCorres.spec fun pair => ∃ value,
                      pair.2 = update (fun _ => value) pair.1) state).results
                rw [mem_init_ok, mem_liftE, AutoCorres.mem_spec]
                constructor
                · rintro ⟨value, equality⟩
                  exact ⟨⟨value, equality⟩, rfl⟩
                · rintro ⟨⟨value, equality⟩, _⟩
                  exact ⟨value, equality⟩
          · apply propext
            have leftFailedEq : (init update state).failed = leftFailed :=
              congrArg Behavior.failed leftEq
            have rightFailedEq :
                (spec (fun pair => ∃ value,
                  pair.2 = update (fun _ => value) pair.1) state).failed = rightFailed :=
              congrArg Behavior.failed rightEq
            rw [← leftFailedEq, ← rightFailedEq]
            have leftNoFail := init_not_failed (state := state) update
            have rightNoFail : Not (spec (fun pair =>
                ∃ value, pair.2 = update (fun _ => value) pair.1) state).failed := by
              have value : Value := Classical.choice inferInstance
              simp [spec, liftE, bind, AutoCorres.spec, returnOk, pure]
              exact ⟨update (fun _ => value) state, value, rfl⟩
            exact iff_of_false leftNoFail rightNoFail

theorem L1Corres_init (checkTermination : Bool) (env : Simpl.Body State Proc Fault)
    [Nonempty Value]
    (update : (Value -> Value) -> State -> State) :
    L1Corres checkTermination env (init update)
      (.Spec fun pair => ∃ value, pair.2 = update (fun _ => value) pair.1) := by
  rw [init_alt_def]
  exact L1Corres_spec checkTermination env _

theorem L1Corres_fail (checkTermination : Bool) (env : Simpl.Body State Proc Fault)
    (source : Simpl.Com State Proc Fault) :
    L1Corres checkTermination env (fail : L1Program State) source := by
  intro state noFail
  exact False.elim (noFail True.intro)

theorem L1Corres_recguard {State : Type u} {Proc : Type v} {Fault : Type w}
    {checkTermination : Bool} {env : Simpl.Body State Proc Fault}
    {body : L1Program State} {source : Simpl.Com State Proc Fault} {measure : Nat}
    (bodyCorres : L1Corres checkTermination env body source) :
    L1Corres checkTermination env (recguard measure body) source := by
  by_cases zero : measure = 0
  · subst measure
    rw [show recguard 0 body = fail by
      funext state
      unfold recguard condition
      simp]
    exact L1Corres_fail checkTermination env source
  · rw [show recguard measure body = body by
      funext state
      unfold recguard condition
      simp [zero]]
    exact bodyCorres

theorem recguard_behavior (body : L1Program State) (state : State) :
    recguard 0 body state = fail state ∧
      ∀ measure, measure ≠ 0 -> recguard measure body state = body state := by
  constructor
  · simp [recguard, condition]
  · intro measure nonzero
    simp [recguard, condition, nonzero]

/-! ## Closed SSA bridge -/

/-- Package an L1 program as an exact closed call into an SSA `PrimFuncCtx`. -/
def toSSA (program : L1Program State) :
    SSABridge.ClosedProgram State (Except Unit Unit) :=
  ⟨program⟩

/-- The L1 package exposes the generic bridge's exact evaluation theorem. -/
theorem toSSA_eval (program : L1Program State) :
    cast (by simp only [SSABridge.outcomeTy_type])
      (Zag.Lang.SSA.SSAExpr.evalM? (toSSA program).ctx [] SSABridge.outcomeTy
        (toSSA program).expr) = some (SSABridge.suspend program) :=
  SSABridge.ClosedProgram.eval_exact (toSSA program)

/-- L1 skip evaluates through SSA as exactly its suspended shallow semantics. -/
theorem skip_toSSA_eval :
    cast (by simp only [SSABridge.outcomeTy_type])
      (Zag.Lang.SSA.SSAExpr.evalM? (toSSA (skip : L1Program State)).ctx []
        SSABridge.outcomeTy (toSSA (skip : L1Program State)).expr) =
        some (SSABridge.suspend (skip : L1Program State)) :=
  toSSA_eval skip

end Zag.Lang.AutoCorres.L1
