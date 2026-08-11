import Lang.AutoCorres.L2
import Lang.AutoCorres.Reader_Option_Monad
import Lang.AutoCorres.ExecConcrete

/-!
# Trusted type-strengthening kernel

This module contains the carrier model and the structural statement consumed
by the type-strengthening pass. It contains no search, diagnostics, or proof
construction.
-/

namespace Zag.Lang.AutoCorres.TypeStrengthen.Kernel

universe u v w

/-- The four monad carriers registered by the upstream type strengthening setup. -/
inductive Carrier where
  | pure
  | gets
  | option
  | nondet
  deriving DecidableEq, Repr

/-- The concrete type represented by a carrier for a state and result type. -/
abbrev Repr : Carrier -> Type u -> Type u -> Type u
  | .pure, _, Result => Result
  | .gets, State, Result => State -> Result
  | .option, State, Result => State -> Option Result
  | .nondet, State, Result => Nondet State Result

/-- Interpret a reader-option computation as failure or one unchanged-state result. -/
def optionNondet {State : Type u} {Result : Type v}
    (program : Lookup State Result) : Nondet State Result :=
  fun state =>
    match program state with
    | none => fail state
    | some value => pure value state

/-- The exception-free semantics represented by each registered carrier. -/
def denote {State Result : Type u} :
    (carrier : Carrier) -> Repr carrier State Result -> Nondet State Result
  | .pure, value => pure value
  | .gets, read => gets read
  | .option, program => optionNondet program
  | .nondet, program => program

/-- Typed replacement for the upstream carrier-specific lifting heads. -/
def embed {State Result : Type u} {Exception : Type v} (carrier : Carrier)
    (program : Repr carrier State Result) :
    L2.L2Program State Exception Result :=
  liftE (denote carrier program)

/-- Plain nondeterministic exception handling used by the second catch rule. -/
def nondetCatch {State : Type u} {Exception : Type v} {Result : Type w}
    (program : L2.L2Program State Exception Result)
    (handler : Exception -> Nondet State Result) : Nondet State Result :=
  bind program fun result =>
    match result with
    | .error exception => handler exception
    | .ok value => pure value

namespace Source

/--
Typed L2 source syntax. `Argument` is the explicit environment available to
closures. Every executable node is represented by a constructor.
-/
inductive Term : Type -> Type -> Type -> Type -> Type 1 where
  | pure {argument state exception result : Type}
      (value : argument -> result) (names : List String) :
      Term argument state exception result
  | gets {argument state exception result : Type}
      (read : argument -> state -> result) (names : List String) :
      Term argument state exception result
  | seq {argument state exception middle result : Type}
      (first : Term argument state exception middle)
      (next : Term (argument × middle) state exception result) :
      Term argument state exception result
  | conditionPure {argument state exception result : Type}
      (test : argument -> Bool)
      (thenBranch elseBranch : Term argument state exception result) :
      Term argument state exception result
  | condition {argument state exception result : Type}
      (test : argument -> state -> Bool)
      (thenBranch elseBranch : Term argument state exception result) :
      Term argument state exception result
  | modify {argument state exception : Type} (update : argument -> state -> state) :
      Term argument state exception Unit
  | guard {argument state exception : Type} (test : argument -> state -> Bool) :
      Term argument state exception Unit
  | exactGuard {argument state exception : Type}
      (test : argument -> state -> Prop) : Term argument state exception Unit
  | while {argument state exception result : Type}
      (test : argument -> result -> state -> Bool)
      (body : Term (argument × result) state exception result)
      (initial : argument -> result) (names : List String) :
      Term argument state exception result
  | catchBody {argument state exception caught result : Type}
      (body : Term argument state caught result)
      (handler : Term (argument × caught) state exception result) :
      Term argument state exception result
  | catchHandlers {argument state caught exception result : Type}
      (body : Term argument state caught result)
      (handler : Term (argument × caught) state exception result) :
      Term argument state exception result
  | spec {argument state exception result : Type}
      (relation : argument -> Set (state × state)) :
      Term argument state exception result
  | unknown {argument state exception result : Type} (names : List String) :
      Term argument state exception result
  | fail {argument state exception result : Type} : Term argument state exception result
  | recguard {argument state exception result : Type} (measure : argument -> Nat)
      (body : Term argument state exception result) :
      Term argument state exception result
  | throw {argument state exception result : Type}
      (value : argument -> exception) (names : List String) :
      Term argument state exception result

/-- A closed function body with an explicit inner exception type. -/
abbrev Closed (State InnerException Result : Type) :=
  Term Unit State InnerException Result

/-- Compatibility specialization for the original exception-free source API. -/
abbrev Syntax (State Result : Type) := Closed State Unit Result

/-- Interpret source syntax after the pure recognition and conversion phases. -/
noncomputable def Term.denote {Argument State Exception Result : Type}
    (argument : Argument) :
    Term Argument State Exception Result -> L2.L2Program State Exception Result
  | .pure value names => L2.gets (fun _ => value argument) names
  | .gets read names => L2.gets (read argument) names
  | .seq first next =>
      L2.seq (first.denote argument) fun value => next.denote (argument, value)
  | .conditionPure test thenBranch elseBranch =>
      L2.condition (fun _ => test argument = true)
        (thenBranch.denote argument) (elseBranch.denote argument)
  | .condition test thenBranch elseBranch =>
      L2.condition (fun state => test argument state = true)
        (thenBranch.denote argument) (elseBranch.denote argument)
  | .modify update => L2.modify (update argument)
  | .guard test => L2.guard fun state => test argument state = true
  | .exactGuard test => L2.guard (test argument)
  | .while test body initial names =>
      L2.while (fun value state => test argument value state = true)
        (fun value => body.denote (argument, value)) (initial argument) names
  | .catchBody body handler =>
      L2.catch (body.denote argument) fun exception =>
        handler.denote (argument, exception)
  | .catchHandlers body handler =>
      L2.catch (body.denote argument) fun exception =>
        handler.denote (argument, exception)
  | .spec relation => L2.spec (relation argument)
  | .unknown names => L2.unknown names
  | .fail => L2.fail
  | .recguard measure body => L2.recguard (measure argument) (body.denote argument)
  | .throw exception names => L2.throw (exception argument) names

/-- Stable constructor names used in explicit conversion diagnostics. -/
def Term.kind {Argument State Exception Result : Type} :
    Term Argument State Exception Result -> String
  | .pure _ _ => "pure"
  | .gets _ _ => "gets"
  | .seq _ _ => "seq"
  | .conditionPure _ _ _ => "conditionPure"
  | .condition _ _ _ => "condition"
  | .modify _ => "modify"
  | .guard _ => "guard"
  | .exactGuard _ => "exactGuard"
  | .while _ _ _ _ => "while"
  | .catchBody _ _ => "catchBody"
  | .catchHandlers _ _ => "catchHandlers"
  | .spec _ => "spec"
  | .unknown _ => "unknown"
  | .fail => "fail"
  | .recguard _ _ => "recguard"
  | .throw _ _ => "throw"

end Source

namespace Target

/-- Carrier-indexed target representation. Semantic monads are produced only by `denote`. -/
inductive Syntax : Carrier -> Type -> Type -> Type 1 where
  | atom {carrier : Carrier} {state result : Type}
      (program : Repr carrier state result) : Syntax carrier state result
  | seq {carrier : Carrier} {state middle result : Type}
      (first : Syntax carrier state middle)
      (next : middle -> Syntax carrier state result) : Syntax carrier state result
  | pureCondition {state result : Type} (test : Bool)
      (thenBranch elseBranch : Syntax .pure state result) : Syntax .pure state result
  | getsCondition {state result : Type} (test : state -> Bool)
      (thenBranch elseBranch : Syntax .gets state result) : Syntax .gets state result
  | optionCondition {state result : Type} (test : state -> Bool)
      (thenBranch elseBranch : Syntax .option state result) : Syntax .option state result
  | nondetCondition {state result : Type} (test : state -> Bool)
      (thenBranch elseBranch : Syntax .nondet state result) : Syntax .nondet state result
  | optionWhile {state result : Type} (test : result -> state -> Bool)
      (body : result -> Syntax .option state result) (initial : result) :
      Syntax .option state result
  | nondetWhile {state result : Type} (test : result -> state -> Bool)
      (body : result -> Syntax .nondet state result) (initial : result) :
      Syntax .nondet state result
  | optionRecguard {state result : Type} (measure : Nat)
      (body : Syntax .option state result) : Syntax .option state result
  | nondetRecguard {state result : Type} (measure : Nat)
      (body : Syntax .nondet state result) : Syntax .nondet state result
  | catchHandlers {argumentType state caught result : Type}
      (body : Source.Term argumentType state caught result) (argument : argumentType)
      (handler : caught -> Syntax .nondet state result) : Syntax .nondet state result

/-- Semantic interpretation is deliberately separate from pure target construction. -/
@[simp] noncomputable def Syntax.denote {carrier : Carrier} {State Result : Type} :
    Syntax carrier State Result -> Repr carrier State Result
  | .atom program => program
  | .seq (carrier := .pure) first next => (next first.denote).denote
  | .seq (carrier := .gets) first next =>
      fun state => (next (first.denote state)).denote state
  | .seq (carrier := .option) first next =>
      first.denote |>> fun value => (next value).denote
  | .seq (carrier := .nondet) first next =>
      bind first.denote fun value => (next value).denote
  | .pureCondition test thenBranch elseBranch =>
      if test then thenBranch.denote else elseBranch.denote
  | .getsCondition test thenBranch elseBranch =>
      fun state => if test state then thenBranch.denote state else elseBranch.denote state
  | .optionCondition test thenBranch elseBranch =>
      ocondition test thenBranch.denote elseBranch.denote
  | .nondetCondition test thenBranch elseBranch =>
      fun state => if test state then thenBranch.denote state else elseBranch.denote state
  | .optionWhile test body initial => owhile test (fun value => (body value).denote) initial
  | .nondetWhile test body initial =>
      whileLoop (fun value state => test value state = true)
        (fun value => (body value).denote) initial
  | .optionRecguard measure body =>
      ocondition (fun _ => decide (measure = 0)) ofail body.denote
  | .nondetRecguard measure body =>
      fun state => if decide (measure > 0) then body.denote state else fail state
  | .catchHandlers body argument handler =>
      nondetCatch (body.denote argument) fun exception => (handler exception).denote

end Target

/-- Carrier-indexed evidence for every recursively converted source node. -/
inductive Supported :
    (carrier : Carrier) ->
    {Argument State Exception Result : Type} ->
    Source.Term Argument State Exception Result -> Type 1 where
  | pureValue : Supported .pure (.pure value names)
  | pureSeq : Supported .pure first -> Supported .pure next ->
      Supported .pure (.seq first next)
  | pureCondition : Supported .pure thenBranch -> Supported .pure elseBranch ->
      Supported .pure (.conditionPure test thenBranch elseBranch)

  | getsValue : Supported .gets (.pure value names)
  | getsRead {argument state exception result : Type}
      {read : argument -> state -> result} {names : List String} :
      Supported .gets (Source.Term.gets (exception := exception) read names)
  | getsSeq : Supported .gets first -> Supported .gets next ->
      Supported .gets (.seq first next)
  | getsPureCondition : Supported .gets thenBranch -> Supported .gets elseBranch ->
      Supported .gets (.conditionPure test thenBranch elseBranch)
  | getsCondition : Supported .gets thenBranch -> Supported .gets elseBranch ->
      Supported .gets (.condition test thenBranch elseBranch)

  | optionValue : Supported .option (.pure value names)
  | optionRead {argument state exception result : Type}
      {read : argument -> state -> result} {names : List String} :
      Supported .option (Source.Term.gets (exception := exception) read names)
  | optionSeq : Supported .option first -> Supported .option next ->
      Supported .option (.seq first next)
  | optionPureCondition : Supported .option thenBranch -> Supported .option elseBranch ->
      Supported .option (.conditionPure test thenBranch elseBranch)
  | optionCondition : Supported .option thenBranch -> Supported .option elseBranch ->
      Supported .option (.condition test thenBranch elseBranch)
  | optionGuard : Supported .option (.guard test)
  | optionWhile : Supported .option body -> Supported .option (.while test body initial names)
  | optionFail : Supported .option .fail
  | optionRecguard {sourceMeasure : Argument -> Nat} : Supported .option body ->
      Supported .option (.recguard sourceMeasure body)

  | nondetValue : Supported .nondet (.pure value names)
  | nondetRead {argument state exception result : Type}
      {read : argument -> state -> result} {names : List String} :
      Supported .nondet (Source.Term.gets (exception := exception) read names)
  | nondetSeq : Supported .nondet first -> Supported .nondet next ->
      Supported .nondet (.seq first next)
  | nondetPureCondition : Supported .nondet thenBranch -> Supported .nondet elseBranch ->
      Supported .nondet (.conditionPure test thenBranch elseBranch)
  | nondetCondition : Supported .nondet thenBranch -> Supported .nondet elseBranch ->
      Supported .nondet (.condition test thenBranch elseBranch)
  | nondetModify : Supported .nondet (.modify update)
  | nondetGuard : Supported .nondet (.guard test)
  | nondetExactGuard : Supported .nondet (.exactGuard test)
  | nondetWhile : Supported .nondet body -> Supported .nondet (.while test body initial names)
  | nondetCatchBody : Supported .nondet body ->
      Supported .nondet (.catchBody body handler)
  | nondetCatchHandlers : Supported .nondet handler ->
      Supported .nondet (.catchHandlers body handler)
  | nondetSpec : Supported .nondet (.spec relation)
  | nondetUnknown : Supported .nondet (.unknown names)
  | nondetFail : Supported .nondet .fail
  | nondetRecguard {sourceMeasure : Argument -> Nat} : Supported .nondet body ->
      Supported .nondet (.recguard sourceMeasure body)

/-- Exact, exception-polymorphic result for an arbitrary closed source. -/
structure ClosedCertificate {State InnerException Result : Type} (carrier : Carrier)
    (source : Source.Closed State InnerException Result) where
  target : Target.Syntax carrier State Result
  exact : forall (Exception : Type),
    L2.call (Exception := Exception) (source.denote ()) =
      embed (Exception := Exception) carrier target.denote

/-- Compatibility specialization for the original `Unit` inner exception API. -/
abbrev Certificate {State Result : Type} (carrier : Carrier)
    (source : Source.Syntax State Result) := ClosedCertificate carrier source

end Zag.Lang.AutoCorres.TypeStrengthen.Kernel

/-! Compatibility names for clients of the former ML-owned carrier model. -/

namespace Zag.Lang.AutoCorres.ML.MonadTypes

universe u

abbrev Carrier := TypeStrengthen.Kernel.Carrier

abbrev Repr : Carrier -> Type u -> Type u -> Type u := TypeStrengthen.Kernel.Repr

end Zag.Lang.AutoCorres.ML.MonadTypes

/-!
# AutoCorres type strengthening

Corresponds only to [`tools/autocorres/TypeStrengthen.thy`](https://github.com/seL4/l4v/blob/bc2599a59c43e673dca021b10b9841e9b8da4430/tools/autocorres/TypeStrengthen.thy).

The rules below are semantic equalities.  `Exact` exposes both observations of
the nondeterministic monad, so a strengthening certificate cannot discard the
failure flag or merely relate successful results.
-/

namespace Zag.Lang.AutoCorres.TypeStrengthen

open Kernel

universe u v w x y

noncomputable section

variable {State : Type u} {Result : Type v}

private theorem behavior_ext {left right : Behavior State Result}
    (results : left.results = right.results)
    (failed : left.failed = right.failed) : left = right := by
  cases left
  cases right
  cases results
  cases failed
  rfl

/-- Extensional equality of result sets and failure observations. -/
structure Exact (left right : Nondet State Result) : Prop where
  results : ∀ state result,
    result ∈ (left state).results ↔ result ∈ (right state).results
  failed : ∀ state, (left state).failed ↔ (right state).failed

theorem Exact.eq (certificate : Exact left right) : left = right := by
  funext state
  apply behavior_ext
  · funext result
    exact propext (certificate.results state result)
  · exact propext (certificate.failed state)

theorem exact_iff_eq : Exact left right ↔ left = right := by
  constructor
  · exact Exact.eq
  · rintro rfl
    exact ⟨fun _ _ => Iff.rfl, fun _ => Iff.rfl⟩

private theorem exact_of_eq (equality : left = right) : Exact left right :=
  exact_iff_eq.mpr equality

@[simp] theorem mem_bindE_error
    {program : L2.L2Program State Exception α}
    {next : α → L2.L2Program State Exception β} :
    (Except.error exception, post) ∈ (bindE program next state).results ↔
      (Except.error exception, post) ∈ (program state).results ∨
        ∃ value middle, (Except.ok value, middle) ∈ (program state).results ∧
          (Except.error exception, post) ∈ (next value middle).results := by
  constructor
  · rintro ⟨source, middle, member, continuation⟩
    cases source with
    | error sourceException =>
        change (Except.error exception, post) =
          (Except.error sourceException, middle) at continuation
        cases continuation
        exact Or.inl member
    | ok value =>
        exact Or.inr ⟨value, middle, member, continuation⟩
  · rintro (member | ⟨value, middle, member, continuation⟩)
    · exact ⟨Except.error exception, post, member, rfl⟩
    · exact ⟨Except.ok value, middle, member, continuation⟩

@[simp] theorem failed_bindE
    {program : L2.L2Program State Exception α}
    {next : α → L2.L2Program State Exception β} :
    (bindE program next state).failed ↔
      (program state).failed ∨ ∃ value middle,
        (Except.ok value, middle) ∈ (program state).results ∧
          (next value middle).failed := by
  constructor
  · rintro (failed | ⟨source, middle, member, nextFailed⟩)
    · exact Or.inl failed
    · cases source with
      | error exception => exact False.elim nextFailed
      | ok value => exact Or.inr ⟨value, middle, member, nextFailed⟩
  · rintro (failed | ⟨value, middle, member, nextFailed⟩)
    · exact Or.inl failed
    · exact Or.inr ⟨Except.ok value, middle, member, nextFailed⟩

private theorem liftE_bind_eq (left : Nondet State α) (right : α → Nondet State β) :
    bindE (liftE (ε := Exception) left) (fun value => liftE (right value)) =
      liftE (bind left right) := by
  apply Exact.eq
  constructor
  · intro state result
    rcases result with ⟨outcome, post⟩
    cases outcome with
    | error exception => simp [L2.mem_liftE_iff]
    | ok value => simp
  · intro state
    simp

private theorem bind_pure_left (value : α) (next : α → Nondet State β) :
    bind (pure value) next = next value := by
  apply Exact.eq
  constructor
  · intro state result
    rcases result with ⟨outcome, post⟩
    constructor
    · rintro ⟨source, middle, equality, member⟩
      cases equality
      exact member
    · intro member
      exact ⟨value, state, rfl, member⟩
  · intro state
    constructor
    · rintro (failed | ⟨source, middle, equality, failed⟩)
      · exact False.elim failed
      · cases equality
        exact failed
    · intro failed
      exact Or.inr ⟨value, state, rfl, failed⟩

private theorem bind_gets_left (read : State → α) (next : α → Nondet State β) :
    bind (gets read) next = fun state => next (read state) state := by
  apply Exact.eq
  constructor
  · intro state result
    rcases result with ⟨outcome, post⟩
    constructor
    · rintro ⟨source, middle, equality, member⟩
      cases equality
      exact member
    · intro member
      exact ⟨read state, state, rfl, member⟩
  · intro state
    constructor
    · rintro (failed | ⟨source, middle, equality, failed⟩)
      · exact False.elim failed
      · cases equality
        exact failed
    · intro failed
      exact Or.inr ⟨read state, state, rfl, failed⟩

private theorem bind_fail_left (next : α → Nondet State β) :
    bind (fail : Nondet State α) next = fail := by
  apply Exact.eq
  constructor
  · intro state result
    constructor
    · rintro ⟨value, middle, member, _⟩
      exact False.elim (mem_fail member)
    · intro member
      exact False.elim (mem_fail member)
  · intro state
    constructor
    · intro _
      exact True.intro
    · intro _
      exact Or.inl True.intro

private theorem liftE_fail :
    (liftE (ε := Exception) (fail : Nondet State Result)) = fail := by
  apply Exact.eq
  constructor
  · intro state result
    constructor
    · rw [L2.mem_liftE_iff]
      rintro ⟨value, _, member⟩
      exact False.elim (mem_fail member)
    · intro member
      exact False.elim (mem_fail member)
  · intro state
    simp

private theorem liftE_congr_state {left right : Nondet State Result}
    (equality : left state = right state) :
    liftE (ε := Exception) left state = liftE right state := by
  unfold liftE bind
  rw [equality]

/-- Embed a pure value into L2. -/
def TS_return (value : Result) : L2.L2Program State Exception Result :=
  liftE (pure value)

/-- Embed a read-only state function into L2. -/
def TS_gets (read : State → Result) : L2.L2Program State Exception Result :=
  liftE (gets read)

/-- Interpret a reader-option computation as failure or one unchanged-state result. -/
def optionNondet (program : Lookup State Result) : Nondet State Result :=
  fun state =>
    match program state with
    | none => fail state
    | some value => pure value state

/-- Embed the reader-option monad into L2. -/
def gets_theE (program : Lookup State Result) : L2.L2Program State Exception Result :=
  liftE (optionNondet program)

/-- The exception-free semantics represented by each registered carrier. -/
def denote {State Result : Type u} :
    (carrier : Carrier) -> Kernel.Repr carrier State Result -> Nondet State Result
  | .pure, value => pure value
  | .gets, read => gets read
  | .option, program => optionNondet program
  | .nondet, program => program

/-- Typed replacement for the upstream carrier-specific lifting heads. -/
def embed {State Result : Type u} (carrier : Carrier)
    (program : Kernel.Repr carrier State Result) :
    L2.L2Program State Exception Result :=
  liftE (denote carrier program)

@[simp] theorem embed_pure {State Result : Type u} (value : Result) :
    embed (State := State) (Exception := Exception) .pure value =
      TS_return (State := State) value := rfl

@[simp] theorem embed_gets {State Result : Type u} (read : State → Result) :
    embed (Exception := Exception) .gets read = TS_gets read := rfl

@[simp] theorem embed_option {State Result : Type u} (program : Lookup State Result) :
    embed (Exception := Exception) .option program = gets_theE program := rfl

@[simp] theorem embed_nondet {State Result : Type u} (program : Nondet State Result) :
    embed (Exception := Exception) .nondet program = liftE program := rfl

/-! ## Call and exception polymorphism -/

@[simp] theorem mem_call_ok {program : L2.L2Program State InnerException Result} :
    (Except.ok value, post) ∈
        (L2.call (Exception := Exception) program state).results ↔
      (Except.ok value, post) ∈ (program state).results := by
  constructor
  · rintro ⟨source, middle, member, continuation⟩
    cases source with
    | error exception => exact False.elim (mem_fail continuation)
    | ok sourceValue =>
        change (Except.ok value, post) = (Except.ok sourceValue, middle) at continuation
        cases continuation
        exact member
  · intro member
    exact ⟨Except.ok value, post, member, rfl⟩

@[simp] theorem not_mem_call_error {program : L2.L2Program State InnerException Result} :
    ¬ (Except.error exception, post) ∈
      (L2.call (Exception := Exception) program state).results := by
  rintro ⟨source, middle, member, continuation⟩
  cases source with
  | error exception => exact mem_fail continuation
  | ok value =>
      change (Except.error exception, post) = (Except.ok value, middle) at continuation
      cases continuation

@[simp] theorem failed_call {program : L2.L2Program State InnerException Result} :
    (L2.call (Exception := Exception) program state).failed ↔
      (program state).failed ∨ ∃ exception post,
        (Except.error exception, post) ∈ (program state).results := by
  constructor
  · intro failed
    rcases failed with sourceFailed | ⟨source, middle, member, continuationFailed⟩
    · exact Or.inl sourceFailed
    · cases source with
      | error exception => exact Or.inr ⟨exception, middle, member⟩
      | ok value => exact False.elim continuationFailed
  · rintro (sourceFailed | ⟨exception, post, member⟩)
    · exact Or.inl sourceFailed
    · exact Or.inr ⟨Except.error exception, post, member, True.intro⟩

theorem L2_call_liftE (program : Nondet State Result) :
    L2.call (Exception := Exception) (liftE (ε := InnerException) program) =
      liftE (ε := Exception) program := by
  apply Exact.eq
  constructor
  · intro state result
    rcases result with ⟨outcome, post⟩
    cases outcome <;> simp
  · intro state
    simp

theorem L2_call_liftE_exact (program : Nondet State Result) :
    Exact (L2.call (Exception := Exception) (liftE (ε := InnerException) program))
      (liftE (ε := Exception) program) :=
  exact_of_eq (L2_call_liftE program)

theorem L2_call_embed_exact {State Result : Type u} (carrier : Carrier)
    (program : Kernel.Repr carrier State Result) :
    Exact
      (L2.call (Exception := Exception)
        (embed (Exception := InnerException) carrier program))
      (embed (Exception := Exception) carrier program) :=
  L2_call_liftE_exact (denote carrier program)

theorem L2_call_liftE_polymorphic
    {source : L2.L2Program State InnerException Result}
    {target : Nondet State Result}
    (equality : L2.call (Exception := Exception₁) source = liftE target) :
    L2.call (Exception := Exception₂) source = liftE target := by
  apply Exact.eq
  constructor
  · intro state result
    rcases result with ⟨outcome, post⟩
    cases outcome with
    | error exception => simp
    | ok value =>
        have pointwise := congrFun equality state
        have observed := congrArg
          (fun behavior => (Except.ok value, post) ∈ behavior.results) pointwise
        simpa using observed
  · intro state
    have pointwise := congrFun equality state
    have observed := congrArg Behavior.failed pointwise
    simpa using observed

theorem L2_call_TS_return (value : Result) :
    L2.call (Exception := Exception) (TS_return (State := State) (Exception := Unit) value) =
      L2.gets (fun _ : State => value) ["ret"] := by
  unfold TS_return
  rw [L2_call_liftE]
  apply Exact.eq
  constructor <;> simp [L2.gets, pure, gets]

theorem L2_call_TS_gets (read : State → Result) :
    L2.call (Exception := Exception) (TS_gets (Exception := Unit) read) =
      L2.gets read ["TS_internal_retval"] := by
  unfold TS_gets
  rw [L2_call_liftE]
  rfl

theorem L2_call_gets_theE (program : Lookup State Result) :
    L2.call (Exception := Exception) (gets_theE (Exception := Unit) program) =
      gets_theE (Exception := Exception) program :=
  L2_call_liftE _

theorem L2_call_L2_gets_polymorphic
    {source : L2.L2Program State InnerException Result}
    {read : State → Result} {names : List String}
    (equality : L2.call (Exception := Exception₁) source = L2.gets read names) :
    L2.call (Exception := Exception₂) source = L2.gets read names := by
  exact L2_call_liftE_polymorphic equality

theorem L2_call_gets_theE_polymorphic
    {source : L2.L2Program State InnerException Result}
    {program : Lookup State Result}
    (equality : L2.call (Exception := Exception₁) source = gets_theE program) :
    L2.call (Exception := Exception₂) source = gets_theE program := by
  exact L2_call_liftE_polymorphic equality

/-- A carrier-indexed exact strengthening certificate after `L2.call`. -/
structure Certificate {State Result : Type u} (carrier : Carrier)
    (source : L2.L2Program State InnerException Result)
    (target : Kernel.Repr carrier State Result)
    (Exception : Type x) : Prop where
  exact : Exact (L2.call (Exception := Exception) source) (embed carrier target)

theorem Certificate.equality
    (certificate : Certificate carrier source target Exception) :
    L2.call (Exception := Exception) source = embed carrier target :=
  certificate.exact.eq

theorem Certificate.polymorphicExact
    (certificate : Certificate carrier source target Exception₁) :
    Exact (L2.call (Exception := Exception₂) source) (embed carrier target) := by
  apply exact_of_eq
  exact L2_call_liftE_polymorphic certificate.equality

theorem Certificate.polymorphicEquality
    (certificate : Certificate carrier source target Exception₁) :
    L2.call (Exception := Exception₂) source = embed carrier target :=
  certificate.polymorphicExact.eq

theorem certificate_of_equality
    (equality : L2.call (Exception := Exception₁) source = embed carrier target) :
    Certificate carrier source target Exception₁ :=
  ⟨exact_of_eq equality⟩

/-! ## Pure carrier -/

theorem TS_return_L2_gets (value : Result) (names : List String) :
    L2.gets (Exception := Exception) (fun _ : State => value) names =
      TS_return value := by
  apply Exact.eq
  constructor <;> simp [L2.gets, TS_return, gets, pure]

theorem TS_return_L2_seq (left : α) (right : α → β) :
    L2.seq (TS_return (State := State) (Exception := Exception) left)
      (fun value => TS_return (right value)) = TS_return (right left) := by
  unfold L2.seq TS_return
  rw [liftE_bind_eq, bind_pure_left]

theorem TS_return_L2_condition (condition : Bool)
    (thenValue elseValue : Result) :
    L2.condition (State := State) (Exception := Exception) (fun _ => condition = true)
      (TS_return (State := State) thenValue) (TS_return elseValue) =
      TS_return (State := State) (if condition then thenValue else elseValue) := by
  funext state
  cases condition <;> simp [L2.condition]

/-! ## Reader carrier -/

theorem TS_gets_L2_gets (read : State → Result) (names : List String) :
    L2.gets (Exception := Exception) read names = TS_gets read := rfl

theorem TS_gets_L2_seq (left : State → α) (right : α → State → β) :
    L2.seq (TS_gets (Exception := Exception) left)
      (fun value => TS_gets (right value)) =
      TS_gets (fun state => right (left state) state) := by
  unfold L2.seq TS_gets
  rw [liftE_bind_eq]
  have equality := bind_gets_left left (fun value => gets (right value))
  apply congrArg (fun program : Nondet State β => liftE (ε := Exception) program)
  rw [equality]
  rfl

def readerCondition (condition : State → Bool)
    (thenRead elseRead : State → Result) : State → Result :=
  fun state => if condition state then thenRead state else elseRead state

theorem TS_gets_L2_condition (condition : State → Bool)
    (thenRead elseRead : State → Result) :
    L2.condition (fun state => condition state = true)
      (TS_gets (Exception := Exception) thenRead)
      (TS_gets elseRead) =
      TS_gets (readerCondition condition thenRead elseRead) := by
  funext state
  cases conditionEq : condition state <;>
    simp [L2.condition, TS_gets, readerCondition, conditionEq, liftE, bind,
      returnOk, pure, gets]

/-! ## Reader-option carrier -/

def optionRecguard (measure : Nat) (program : Lookup State Result) :
    Lookup State Result :=
  ocondition (fun _ => decide (measure = 0)) ofail program

theorem gets_theE_ofail :
    gets_theE (Exception := Exception) (ofail : Lookup State Result) = L2.fail := by
  unfold gets_theE optionNondet ofail L2.fail
  exact liftE_fail

theorem gets_theE_L2_gets (read : State → Result) (names : List String) :
    L2.gets (Exception := Exception) read names = gets_theE (ogets read) := by
  apply Exact.eq
  constructor <;> simp [L2.gets, gets_theE, optionNondet, ogets, gets, pure]

private theorem optionNondet_bind_eq (left : Lookup State α)
    (right : α → Lookup State β) :
    bind (optionNondet left) (fun value => optionNondet (right value)) =
      optionNondet (left |>> right) := by
  funext state
  cases leftEq : left state with
  | none =>
      apply behavior_ext
      · funext result
        apply propext
        constructor
        · rintro ⟨value, middle, member, _⟩
          rw [show optionNondet left state = fail state by
            simp [optionNondet, leftEq]] at member
          exact False.elim (mem_fail member)
        · intro member
          rw [show optionNondet (left |>> right) state = fail state by
            simp [optionNondet, obind, leftEq]] at member
          exact False.elim (mem_fail member)
      · apply propext
        constructor
        · intro _
          simp [optionNondet, obind, leftEq]
        · intro _
          exact Or.inl (by simp [optionNondet, leftEq])
  | some value =>
      have target : optionNondet (left |>> right) state =
          optionNondet (right value) state := by
        simp [optionNondet, obind, leftEq]
      apply behavior_ext
      · funext result
        apply propext
        constructor
        · rintro ⟨source, middle, member, continuation⟩
          rw [show optionNondet left state = pure value state by
            simp [optionNondet, leftEq]] at member
          rw [mem_pure] at member
          rcases member with ⟨rfl, rfl⟩
          rw [target]
          exact continuation
        · intro member
          rw [target] at member
          exact ⟨value, state, by simp [optionNondet, leftEq], member⟩
      · apply propext
        constructor
        · rintro (failed | ⟨source, middle, member, failed⟩)
          · rw [show optionNondet left state = pure value state by
              simp [optionNondet, leftEq]] at failed
            exact False.elim failed
          · rw [show optionNondet left state = pure value state by
              simp [optionNondet, leftEq]] at member
            rw [mem_pure] at member
            rcases member with ⟨rfl, rfl⟩
            simpa [target] using failed
        · intro failed
          rw [target] at failed
          exact Or.inr ⟨value, state, by simp [optionNondet, leftEq], failed⟩

theorem gets_theE_L2_seq (left : Lookup State α) (right : α → Lookup State β) :
    L2.seq (gets_theE (Exception := Exception) left)
      (fun value => gets_theE (right value)) = gets_theE (left |>> right) := by
  unfold L2.seq gets_theE
  rw [liftE_bind_eq, optionNondet_bind_eq]

theorem gets_theE_L2_guard (condition : State → Bool) :
    L2.guard (Exception := Exception) (fun state => condition state = true) =
      gets_theE (oguard condition) := by
  unfold L2.guard gets_theE
  congr 1
  funext state
  cases conditionEq : condition state
  · apply behavior_ext
    · funext result
      apply propext
      rcases result with ⟨result, post⟩
      constructor
      · rintro ⟨holds, _⟩
        simp [conditionEq] at holds
      · intro member
        rw [show optionNondet (oguard condition) state = fail state by
          simp [optionNondet, oguard, conditionEq]] at member
        exact False.elim (mem_fail member)
    · simp [AutoCorres.guard, optionNondet, oguard, conditionEq]
  · apply behavior_ext
    · funext result
      apply propext
      rcases result with ⟨result, post⟩
      rw [show optionNondet (oguard condition) state = pure () state by
        simp [optionNondet, oguard, conditionEq]]
      change (result, post) ∈
        (AutoCorres.guard (fun state => condition state = true) state).results ↔
        (result, post) ∈ (pure () state).results
      rw [mem_guard, mem_pure]
      simp [conditionEq]
    · rw [show optionNondet (oguard condition) state = pure () state by
        simp [optionNondet, oguard, conditionEq]]
      rw [failed_guard]
      simp [conditionEq, pure]

theorem gets_theE_L2_fail :
    (L2.fail : L2.L2Program State Exception Result) = gets_theE ofail :=
  gets_theE_ofail.symm

theorem gets_theE_L2_recguard (measure : Nat) (program : Lookup State Result) :
    L2.recguard measure (gets_theE (Exception := Exception) program) =
      gets_theE (optionRecguard measure program) := by
  by_cases zero : measure = 0
  · subst measure
    rw [L2.L2_recguard_zero, gets_theE_L2_fail]
    apply congrArg gets_theE
    funext state
    simp [optionRecguard, ocondition, ofail]
  · rw [show L2.recguard measure (gets_theE program) = gets_theE program by
      funext state
      simp [L2.recguard, L2.condition, zero]]
    apply congrArg gets_theE
    funext state
    simp [optionRecguard, ocondition, zero]

theorem gets_theE_L2_condition (condition : State → Bool)
    (thenProgram elseProgram : Lookup State Result) :
    L2.condition (fun state => condition state = true)
      (gets_theE (Exception := Exception) thenProgram)
      (gets_theE elseProgram) =
      gets_theE (ocondition condition thenProgram elseProgram) := by
  funext state
  cases conditionEq : condition state
  · rw [show L2.condition (fun state => condition state = true)
        (gets_theE thenProgram) (gets_theE elseProgram) state =
        gets_theE elseProgram state by simp [L2.condition, conditionEq]]
    unfold gets_theE
    apply liftE_congr_state
    simp [optionNondet, ocondition, conditionEq]
  · rw [show L2.condition (fun state => condition state = true)
        (gets_theE thenProgram) (gets_theE elseProgram) state =
        gets_theE thenProgram state by simp [L2.condition, conditionEq]]
    unfold gets_theE
    apply liftE_congr_state
    simp [optionNondet, ocondition, conditionEq]

private theorem optionWhile_to_whileResult
    {condition : Result → State → Bool} {body : Result → Lookup State Result}
    {value : Result} {state : State} {result : Option Result}
    (run : OptionWhile (fun value => condition value state)
      (fun value => body value state) (some value) result) :
    WhileResult (fun value currentState => condition value currentState = true)
      (fun value => optionNondet (body value)) (some (value, state))
      (result.map fun value => (value, state)) := by
  rw [show some (value, state) = (some value).map (fun value => (value, state)) by rfl]
  apply OptionWhile.rec
    (condition := fun value => condition value state)
    (body := fun value => body value state)
    (motive := fun input result _ => WhileResult
      (fun value currentState => condition value currentState = true)
      (fun value => optionNondet (body value))
      (input.map fun value => (value, state))
      (result.map fun value => (value, state)))
  · intro value stopped
    apply WhileResult.stop
    simp [stopped]
  · intro value continues failed
    apply WhileResult.bodyFailure (by simp [continues])
    simp [optionNondet, failed]
  · intro value next result continues nextValue rest induction
    apply WhileResult.step (by simp [continues])
      (next := next) (nextState := state)
    · simp [optionNondet, nextValue]
    · exact induction
  · exact run

private def optionWhileResult (condition : Result → State → Bool)
    (body : Result → Lookup State Result) (state : State) (value : Result) :
    Option (Result × State) → Prop
  | none => OptionWhile (fun value => condition value state)
      (fun value => body value state) (some value) none
  | some (result, post) => post = state ∧
      OptionWhile (fun value => condition value state)
        (fun value => body value state) (some value) (some result)

private theorem whileResult_to_optionWhile
    {condition : Result → State → Bool} {body : Result → Lookup State Result}
    {value : Result} {state : State} {final : Option (Result × State)}
    (run : WhileResult (fun value currentState => condition value currentState = true)
      (fun value => optionNondet (body value)) (some (value, state)) final) :
    optionWhileResult condition body state value final := by
  have general : ∀ {initial final},
      WhileResult (fun value currentState => condition value currentState = true)
        (fun value => optionNondet (body value)) initial final →
      ∀ value, initial = some (value, state) →
        optionWhileResult condition body state value final := by
    intro initial final execution
    apply WhileResult.rec
      (test := fun value currentState => condition value currentState = true)
      (body := fun value => optionNondet (body value))
      (motive := fun initial final _ => ∀ value, initial = some (value, state) →
        optionWhileResult condition body state value final)
    · intro current currentState stopped value initialEq
      have valueEq := congrArg Prod.fst (Option.some.inj initialEq)
      have stateEq := congrArg Prod.snd (Option.some.inj initialEq)
      cases valueEq
      cases stateEq
      unfold optionWhileResult
      exact ⟨rfl, .final (by
        cases conditionEq : condition current state
        · rfl
        · exact False.elim (stopped (by simp [conditionEq])))⟩
    · intro current currentState holds failed value initialEq
      have valueEq := congrArg Prod.fst (Option.some.inj initialEq)
      have stateEq := congrArg Prod.snd (Option.some.inj initialEq)
      cases valueEq
      cases stateEq
      unfold optionWhileResult
      cases bodyEq : body current state with
      | none => exact .fail (by simpa using holds) bodyEq
      | some next =>
          rw [show optionNondet (body current) state = pure next state by
            simp [optionNondet, bodyEq]] at failed
          exact False.elim failed
    · intro current currentState next nextState final holds member rest induction
      intro value initialEq
      have valueEq := congrArg Prod.fst (Option.some.inj initialEq)
      have stateEq := congrArg Prod.snd (Option.some.inj initialEq)
      cases valueEq
      cases stateEq
      unfold optionWhileResult
      cases bodyEq : body current state with
      | none =>
          rw [show optionNondet (body current) state = fail state by
            simp [optionNondet, bodyEq]] at member
          exact False.elim (mem_fail member)
      | some plainNext =>
          rw [show optionNondet (body current) state = pure plainNext state by
            simp [optionNondet, bodyEq]] at member
          rw [mem_pure] at member
          rcases member with ⟨rfl, rfl⟩
          cases final with
          | none => exact .step (by simpa using holds) bodyEq (induction next rfl)
          | some result =>
              rcases result with ⟨result, post⟩
              have tail := induction next rfl
              exact ⟨tail.1, .step (by simpa using holds) bodyEq tail.2⟩
    · exact execution
  exact general run value rfl

private theorem optionWhile_to_terminates
    {condition : Result → State → Bool} {body : Result → Lookup State Result}
    {value : Result} {state : State} {result : Option Result}
    (run : OptionWhile (fun value => condition value state)
      (fun value => body value state) (some value) result) :
    WhileTerminates (fun value currentState => condition value currentState = true)
      (fun value => optionNondet (body value)) value state := by
  have general : ∀ {input result},
      OptionWhile (fun value => condition value state)
        (fun value => body value state) input result →
      ∀ value, input = some value →
        WhileTerminates (fun value currentState => condition value currentState = true)
          (fun value => optionNondet (body value)) value state := by
    intro input result execution
    apply OptionWhile.rec
      (condition := fun value => condition value state)
      (body := fun value => body value state)
      (motive := fun input _ _ => ∀ value, input = some value →
        WhileTerminates (fun value currentState => condition value currentState = true)
          (fun value => optionNondet (body value)) value state)
    · intro current stopped value inputEq
      cases Option.some.inj inputEq
      apply WhileTerminates.stop
      simp [stopped]
    · intro current continues failed value inputEq
      cases Option.some.inj inputEq
      apply WhileTerminates.step (by simp [continues])
      intro next nextState member
      rw [show optionNondet (body current) state = fail state by
        simp [optionNondet, failed]] at member
      exact False.elim (mem_fail member)
    · intro current next result continues nextValue rest induction value inputEq
      cases Option.some.inj inputEq
      apply WhileTerminates.step (by simp [continues])
      intro next' nextState member
      rw [show optionNondet (body current) state = pure next state by
        simp [optionNondet, nextValue]] at member
      rw [mem_pure] at member
      rcases member with ⟨rfl, rfl⟩
      exact induction next' rfl
    · exact execution
  exact general run value rfl

private theorem terminates_to_optionWhile_exists
    {condition : Result → State → Bool} {body : Result → Lookup State Result}
    {value : Result} {state : State}
    (terminates : WhileTerminates
      (fun value currentState => condition value currentState = true)
      (fun value => optionNondet (body value)) value state) :
    ∃ result, OptionWhile (fun value => condition value state)
      (fun value => body value state) (some value) result := by
  apply WhileTerminates.rec
    (test := fun value (state : State) => condition value state = true)
    (body := fun value => optionNondet (body value))
    (motive := fun value state _ => ∃ result,
      OptionWhile (fun value => condition value state)
        (fun value => body value state) (some value) result)
  · intro value state stopped
    exact ⟨some value, .final (by
      cases conditionEq : condition value state
      · rfl
      · exact False.elim (stopped (by simp [conditionEq])))⟩
  · intro value state holds rest induction
    cases bodyEq : body value state with
    | none => exact ⟨none, .fail (by simpa using holds) bodyEq⟩
    | some next =>
        have member : (next, state) ∈ (optionNondet (body value) state).results := by
          simp [optionNondet, bodyEq]
        obtain ⟨result, run⟩ := induction next state member
        exact ⟨result, .step (by simpa using holds) bodyEq run⟩
  · exact terminates

private theorem whileLoop_optionNondet
    (condition : Result → State → Bool) (body : Result → Lookup State Result)
    (initial : Result) :
    whileLoop (fun value state => condition value state = true)
      (fun value => optionNondet (body value)) initial =
      optionNondet (owhile condition body initial) := by
  funext state
  let optionCondition := fun value => condition value state
  let optionBody := fun value => body value state
  by_cases existsRun : ∃ result, OptionWhile optionCondition optionBody
      (some initial) result
  · obtain ⟨result, run⟩ := existsRun
    have optionEq : optionWhile optionCondition optionBody initial = result :=
      optionWhile_eq_of_run run
    cases result with
    | none =>
        apply behavior_ext
        · funext outcome
          apply propext
          constructor
          · intro member
            have successful := whileResult_to_optionWhile member
            cases OptionWhile.deterministic successful.2 run
          · intro member
            rw [show optionNondet (owhile condition body initial) state = fail state by
              simp [optionNondet, owhile, optionCondition, optionBody, optionEq]] at member
            exact False.elim (mem_fail member)
        · apply propext
          constructor
          · intro _
            simp [optionNondet, owhile, optionCondition, optionBody, optionEq]
          · intro _
            exact Or.inl (optionWhile_to_whileResult run)
    | some final =>
        have terminates := optionWhile_to_terminates run
        apply behavior_ext
        · funext outcome
          rcases outcome with ⟨value, post⟩
          apply propext
          rw [show optionNondet (owhile condition body initial) state = pure final state by
            simp [optionNondet, owhile, optionCondition, optionBody, optionEq]]
          unfold whileLoop pure
          simp only [Prod.mk.injEq]
          constructor
          · intro member
            have successful := whileResult_to_optionWhile member
            have equality := OptionWhile.deterministic successful.2 run
            cases Option.some.inj equality
            exact ⟨rfl, successful.1⟩
          · rintro ⟨rfl, rfl⟩
            exact optionWhile_to_whileResult run
        · apply propext
          rw [show optionNondet (owhile condition body initial) state = pure final state by
            simp [optionNondet, owhile, optionCondition, optionBody, optionEq]]
          constructor
          · rintro (failedRun | doesNotTerminate)
            · have failed := whileResult_to_optionWhile failedRun
              cases OptionWhile.deterministic failed run
            · exact False.elim (doesNotTerminate terminates)
          · intro failed
            exact False.elim failed
  · have optionEq : optionWhile optionCondition optionBody initial = none := by
      simp [optionWhile, existsRun]
    apply behavior_ext
    · funext outcome
      apply propext
      constructor
      · intro member
        have successful := whileResult_to_optionWhile member
        exact False.elim (existsRun ⟨some outcome.1, successful.2⟩)
      · intro member
        rw [show optionNondet (owhile condition body initial) state = fail state by
          simp [optionNondet, owhile, optionCondition, optionBody, optionEq]] at member
        exact False.elim (mem_fail member)
    · apply propext
      constructor
      · intro _
        simp [optionNondet, owhile, optionCondition, optionBody, optionEq]
      · intro _
        exact Or.inr (fun terminates =>
          existsRun (terminates_to_optionWhile_exists terminates))
/-! ## Nondeterministic carrier -/

def nondetCondition (condition : State → Bool)
    (thenProgram elseProgram : Nondet State Result) : Nondet State Result :=
  fun state => if condition state then thenProgram state else elseProgram state

private def liftWhileFinal : Option (Result × State) →
    Option (Except Exception Result × State)
  | none => none
  | some (value, state) => some (Except.ok value, state)

private theorem whileResult_lift {State : Type u} {Result : Type v}
    {Exception : Type w} {test : Result → State → Prop}
    {body : Result → Nondet State Result} {value : Result} {state : State}
    {final : Option (Result × State)}
    (run : WhileResult test body (some (value, state)) final) :
    WhileResult
      (fun (result : Except Exception Result) state => match result with
        | .error _ => False
        | .ok value => test value state)
      (whileLoopEBody fun value => liftE (ε := Exception) (body value))
      (some (Except.ok value, state)) (liftWhileFinal final) := by
  let liftedTest : Except Exception Result → State → Prop :=
    fun result state => match result with
    | .error _ => False
    | .ok value => test value state
  let liftedBody : Except Exception Result → Nondet State (Except Exception Result) :=
    whileLoopEBody fun value => liftE (ε := Exception) (body value)
  rw [show some (Except.ok value, state) =
    liftWhileFinal (Exception := Exception) (some (value, state)) by rfl]
  apply WhileResult.rec (test := test) (body := body)
    (motive := fun initial final _ =>
      WhileResult liftedTest liftedBody (liftWhileFinal initial) (liftWhileFinal final))
  · intro value state stopped
    exact .stop stopped
  · intro value state holds failed
    exact .bodyFailure holds (L2.failed_liftE.mpr failed)
  · intro value state next nextState final holds member rest induction
    exact .step holds (mem_liftE.mpr member) induction
  · exact run

private theorem whileResult_unlift {State : Type u} {Result : Type v}
    {Exception : Type w} {test : Result → State → Prop}
    {body : Result → Nondet State Result} {value : Result} {state : State}
    {final : Option (Result × State)}
    (run : WhileResult
      (fun (result : Except Exception Result) state => match result with
        | .error _ => False
        | .ok value => test value state)
      (whileLoopEBody fun value => liftE (ε := Exception) (body value))
      (some (Except.ok value, state)) (liftWhileFinal final)) :
    WhileResult test body (some (value, state)) final := by
  let liftedTest : Except Exception Result → State → Prop :=
    fun result state => match result with
    | .error _ => False
    | .ok value => test value state
  let liftedBody : Except Exception Result → Nondet State (Except Exception Result) :=
    whileLoopEBody fun value => liftE (ε := Exception) (body value)
  have general : ∀ {initial liftedFinal},
      WhileResult liftedTest liftedBody initial liftedFinal →
      ∀ plainInitial plainFinal,
        initial = liftWhileFinal plainInitial →
        liftedFinal = liftWhileFinal plainFinal →
        WhileResult test body plainInitial plainFinal := by
    intro initial liftedFinal execution
    apply WhileResult.rec (test := liftedTest) (body := liftedBody)
      (motive := fun initial liftedFinal _ => ∀ plainInitial plainFinal,
        initial = liftWhileFinal plainInitial →
        liftedFinal = liftWhileFinal plainFinal →
        WhileResult test body plainInitial plainFinal)
    · intro liftedValue liftedState stopped plainInitial plainFinal initialEq finalEq
      cases liftedValue with
      | error exception =>
          cases plainInitial <;> simp [liftWhileFinal] at initialEq
      | ok sourceValue =>
          cases plainInitial with
          | none => simp [liftWhileFinal] at initialEq
          | some source =>
              rcases source with ⟨plainValue, plainState⟩
              simp [liftWhileFinal] at initialEq
              rcases initialEq with ⟨rfl, rfl⟩
              cases plainFinal with
              | none => simp [liftWhileFinal] at finalEq
              | some target =>
                  rcases target with ⟨targetValue, targetState⟩
                  simp [liftWhileFinal] at finalEq
                  rcases finalEq with ⟨rfl, rfl⟩
                  exact .stop stopped
    · intro liftedValue liftedState holds failed plainInitial plainFinal initialEq finalEq
      cases liftedValue with
      | error exception =>
          cases plainInitial <;> simp [liftWhileFinal] at initialEq
      | ok sourceValue =>
          cases plainInitial with
          | none => simp [liftWhileFinal] at initialEq
          | some source =>
              rcases source with ⟨plainValue, plainState⟩
              simp [liftWhileFinal] at initialEq
              rcases initialEq with ⟨rfl, rfl⟩
              cases plainFinal with
              | none => exact .bodyFailure holds (L2.failed_liftE.mp failed)
              | some target => simp [liftWhileFinal] at finalEq
    · intro liftedValue liftedState next nextState liftedFinal holds member rest induction
      intro plainInitial plainFinal initialEq finalEq
      cases liftedValue with
      | error exception =>
          cases plainInitial <;> simp [liftWhileFinal] at initialEq
      | ok sourceValue =>
          cases plainInitial with
          | none => simp [liftWhileFinal] at initialEq
          | some source =>
              rcases source with ⟨plainValue, plainState⟩
              simp [liftWhileFinal] at initialEq
              rcases initialEq with ⟨rfl, rfl⟩
              simp only [liftedBody, whileLoopEBody] at member
              rw [L2.mem_liftE_iff] at member
              rcases member with ⟨plainNext, rfl, member⟩
              exact .step holds member
                (induction (some (plainNext, nextState)) plainFinal rfl finalEq)
    · exact execution
  exact general run (some (value, state)) final rfl rfl

private theorem whileResult_no_error {State : Type u} {Result : Type v}
    {Exception : Type w} {test : Result → State → Prop}
    {body : Result → Nondet State Result} {value : Result} {state post : State}
    {exception : Exception}
    (run : WhileResult
      (fun (result : Except Exception Result) state => match result with
        | .error _ => False
        | .ok value => test value state)
      (whileLoopEBody fun value => liftE (ε := Exception) (body value))
      (some (Except.ok value, state)) (some (Except.error exception, post))) : False := by
  let liftedTest : Except Exception Result → State → Prop :=
    fun result state => match result with
    | .error _ => False
    | .ok value => test value state
  let liftedBody : Except Exception Result → Nondet State (Except Exception Result) :=
    whileLoopEBody fun value => liftE (ε := Exception) (body value)
  have noError : ∀ {initial final}, WhileResult liftedTest liftedBody initial final →
      (∀ value state, initial = some (Except.ok value, state) →
        ∀ exception post, final ≠ some (Except.error exception, post)) := by
    intro initial final execution
    apply WhileResult.rec (test := liftedTest) (body := liftedBody)
      (motive := fun initial final _ => ∀ value state,
        initial = some (Except.ok value, state) →
        ∀ exception post, final ≠ some (Except.error exception, post))
    · intro current currentState stopped value state initialEq exception post finalEq
      cases initialEq
      cases finalEq
    · intro current currentState holds failed value state initialEq exception post finalEq
      cases finalEq
    · intro current currentState next nextState final holds member rest induction
      intro value state initialEq exception post finalEq
      cases current with
      | error error => cases initialEq
      | ok currentValue =>
          simp only [liftedBody, whileLoopEBody] at member
          rw [L2.mem_liftE_iff] at member
          rcases member with ⟨plainNext, rfl, member⟩
          exact induction plainNext nextState rfl exception post finalEq
    · exact execution
  exact noError run value state rfl exception post rfl

private theorem whileTerminates_lift {State : Type u} {Result : Type v}
    {Exception : Type w} {test : Result → State → Prop}
    {body : Result → Nondet State Result} {value : Result} {state : State}
    (terminates : WhileTerminates test body value state) :
    WhileTerminates
      (fun (result : Except Exception Result) state => match result with
        | .error _ => False
        | .ok value => test value state)
      (whileLoopEBody fun value => liftE (ε := Exception) (body value))
      (Except.ok value) state := by
  let liftedTest : Except Exception Result → State → Prop :=
    fun result state => match result with
    | .error _ => False
    | .ok value => test value state
  let liftedBody : Except Exception Result → Nondet State (Except Exception Result) :=
    whileLoopEBody fun value => liftE (ε := Exception) (body value)
  change WhileTerminates liftedTest liftedBody (Except.ok value) state
  apply WhileTerminates.rec (test := test) (body := body)
    (motive := fun value state _ =>
      WhileTerminates liftedTest liftedBody (Except.ok value) state)
  · intro value state stopped
    exact .stop stopped
  · intro value state holds rest induction
    apply WhileTerminates.step (test := liftedTest) (body := liftedBody) holds
    intro next nextState member
    simp only [liftedBody, whileLoopEBody] at member
    rw [L2.mem_liftE_iff] at member
    rcases member with ⟨next, rfl, member⟩
    exact induction next nextState member
  · exact terminates

private theorem whileTerminates_unlift {State : Type u} {Result : Type v}
    {Exception : Type w} {test : Result → State → Prop}
    {body : Result → Nondet State Result} {value : Result} {state : State}
    (terminates : WhileTerminates
      (fun (result : Except Exception Result) state => match result with
        | .error _ => False
        | .ok value => test value state)
      (whileLoopEBody fun value => liftE (ε := Exception) (body value))
      (Except.ok value) state) :
    WhileTerminates test body value state := by
  let liftedTest : Except Exception Result → State → Prop :=
    fun result state => match result with
    | .error _ => False
    | .ok value => test value state
  let liftedBody : Except Exception Result → Nondet State (Except Exception Result) :=
    whileLoopEBody fun value => liftE (ε := Exception) (body value)
  have general : ∀ {liftedValue state},
      WhileTerminates liftedTest liftedBody liftedValue state →
      ∀ value, liftedValue = Except.ok value → WhileTerminates test body value state := by
    intro liftedValue state execution
    apply WhileTerminates.rec (test := liftedTest) (body := liftedBody)
      (motive := fun liftedValue state _ => ∀ value,
        liftedValue = Except.ok value → WhileTerminates test body value state)
    · intro current state stopped value equality
      cases current with
      | error exception => cases equality
      | ok currentValue =>
          cases equality
          exact .stop stopped
    · intro current state holds rest induction value equality
      cases current with
      | error exception => cases equality
      | ok currentValue =>
          cases equality
          apply WhileTerminates.step (test := test) (body := body) holds
          intro next nextState member
          exact induction (Except.ok next) nextState (mem_liftE.mpr member) next rfl
    · exact execution
  exact general terminates value rfl

theorem whileLoopE_liftE (test : Result → State → Prop)
    (body : Result → Nondet State Result) (initial : Result) :
    whileLoopE test (fun value => liftE (ε := Exception) (body value)) initial =
      liftE (whileLoop test body initial) := by
  apply Exact.eq
  constructor
  · intro state result
    rcases result with ⟨outcome, post⟩
    cases outcome with
    | error exception =>
        constructor
        · intro run
          exact False.elim (whileResult_no_error run)
        · intro member
          rw [L2.mem_liftE_iff] at member
          rcases member with ⟨value, equality, _⟩
          cases equality
    | ok value =>
        rw [mem_liftE]
        constructor
        · intro run
          exact whileResult_unlift (final := some (value, post)) run
        · intro run
          exact whileResult_lift run
  · intro state
    rw [L2.failed_liftE]
    constructor
    · rintro (run | doesNotTerminate)
      · exact Or.inl (whileResult_unlift (final := none) run)
      · exact Or.inr (fun terminates =>
          doesNotTerminate (whileTerminates_lift terminates))
    · rintro (run | doesNotTerminate)
      · exact Or.inl (whileResult_lift run)
      · exact Or.inr (fun terminates =>
          doesNotTerminate (whileTerminates_unlift terminates))

theorem gets_theE_L2_while (condition : Result → State → Bool)
    (body : Result → Lookup State Result) (initial : Result) (names : List String) :
    L2.while (fun value state => condition value state = true)
      (fun value => gets_theE (Exception := Exception) (body value)) initial names =
      gets_theE (owhile condition body initial) := by
  unfold L2.while gets_theE
  rw [whileLoopE_liftE, whileLoop_optionNondet]

theorem liftE_gets_theE (program : Lookup State Result) :
    gets_theE (Exception := Exception) program = liftE (optionNondet program) := rfl

theorem liftE_L2_seq (left : Nondet State α) (right : α → Nondet State β) :
    L2.seq (liftE (ε := Exception) left) (fun value => liftE (right value)) =
      liftE (bind left right) := by
  exact liftE_bind_eq left right

theorem liftE_L2_condition (condition : State → Bool)
    (thenProgram elseProgram : Nondet State Result) :
    L2.condition (fun state => condition state = true)
      (liftE (ε := Exception) thenProgram)
      (liftE elseProgram) =
      liftE (nondetCondition condition thenProgram elseProgram) := by
  funext state
  cases conditionEq : condition state
  · rw [show L2.condition (fun state => condition state = true)
        (liftE thenProgram) (liftE elseProgram) state = liftE elseProgram state by
      simp [L2.condition, conditionEq]]
    apply liftE_congr_state
    simp [nondetCondition, conditionEq]
  · rw [show L2.condition (fun state => condition state = true)
        (liftE thenProgram) (liftE elseProgram) state = liftE thenProgram state by
      simp [L2.condition, conditionEq]]
    apply liftE_congr_state
    simp [nondetCondition, conditionEq]

theorem liftE_L2_modify (update : State → State) :
    L2.modify (Exception := Exception) update = liftE (modify update) := rfl

theorem liftE_L2_gets (read : State → Result) (names : List String) :
    L2.gets (Exception := Exception) read names = liftE (gets read) := rfl

theorem liftE_L2_while (test : Result → State → Prop)
    (body : Result → Nondet State Result) (initial : Result) (names : List String) :
    L2.while test (fun value => liftE (ε := Exception) (body value)) initial names =
      liftE (whileLoop test body initial) := by
  exact whileLoopE_liftE test body initial

theorem liftE_L2_catch (program : Nondet State Result)
    (handler : Exception → L2.L2Program State NewException Result) :
    L2.catch (liftE program) handler = liftE program := by
  apply Exact.eq
  constructor
  · intro state result
    rcases result with ⟨outcome, post⟩
    constructor
    · rintro ⟨source, middle, sourceMember, continuation⟩
      rw [L2.mem_liftE_iff] at sourceMember ⊢
      rcases sourceMember with ⟨value, rfl, member⟩
      change (outcome, post) = (Except.ok value, middle) at continuation
      cases continuation
      exact ⟨value, rfl, member⟩
    · rw [L2.mem_liftE_iff]
      rintro ⟨value, rfl, member⟩
      exact ⟨Except.ok value, post,
        (L2.mem_liftE_iff.mpr ⟨value, rfl, member⟩), rfl⟩
  · intro state
    constructor
    · rintro (sourceFailed | ⟨source, middle, sourceMember, continuationFailed⟩)
      · have base : (program state).failed := by simpa using sourceFailed
        simpa using base
      · rw [L2.mem_liftE_iff] at sourceMember
        rcases sourceMember with ⟨value, rfl, member⟩
        exact False.elim continuationFailed
    · intro failed
      have base : (program state).failed := by simpa using failed
      exact Or.inl (by simpa using base)

/-- Plain nondeterministic exception handling used by the second catch rule. -/
def nondetCatch (program : L2.L2Program State Exception Result)
    (handler : Exception -> Nondet State Result) : Nondet State Result :=
  Kernel.nondetCatch program handler

theorem liftE_L2_catch' {NewException : Type}
    (program : L2.L2Program State Exception Result)
    (handler : Exception → Nondet State Result) :
    L2.catch program (fun exception => liftE (ε := NewException) (handler exception)) =
      liftE (ε := NewException) (nondetCatch program handler) := by
  apply Exact.eq
  constructor
  · intro state result
    rcases result with ⟨outcome, post⟩
    constructor
    · rintro ⟨source, middle, sourceMember, continuation⟩
      rw [L2.mem_liftE_iff]
      cases source with
      | error exception =>
          rw [L2.mem_liftE_iff] at continuation
          rcases continuation with ⟨value, equality, member⟩
          exact ⟨value, equality, Except.error exception, middle, sourceMember, member⟩
      | ok value =>
          change (outcome, post) = (Except.ok value, middle) at continuation
          cases continuation
          exact ⟨value, rfl, Except.ok value, post, sourceMember, rfl⟩
    · rw [L2.mem_liftE_iff]
      rintro ⟨value, rfl, source, middle, sourceMember, nextMember⟩
      cases source with
      | error exception =>
          exact ⟨Except.error exception, middle, sourceMember,
            L2.mem_liftE_iff.mpr ⟨value, rfl, nextMember⟩⟩
      | ok sourceValue =>
          rw [mem_pure] at nextMember
          rcases nextMember with ⟨rfl, rfl⟩
          exact ⟨Except.ok value, post, sourceMember, rfl⟩
  · intro state
    simp only [L2.catch, handle, nondetCatch, L2.failed_liftE]
    constructor
    · rintro (sourceFailed | ⟨source, middle, sourceMember, continuationFailed⟩)
      · exact Or.inl sourceFailed
      · cases source with
        | error exception =>
            exact Or.inr ⟨Except.error exception, middle, sourceMember,
              L2.failed_liftE.mp continuationFailed⟩
        | ok value => exact False.elim continuationFailed
    · rintro (sourceFailed | ⟨source, middle, sourceMember, nextFailed⟩)
      · exact Or.inl sourceFailed
      · cases source with
        | error exception =>
            exact Or.inr ⟨Except.error exception, middle, sourceMember,
              L2.failed_liftE.mpr nextFailed⟩
        | ok value => exact False.elim nextFailed

theorem liftE_L2_spec (relation : Set (State × State)) :
    (L2.spec relation : L2.L2Program State Exception Result) =
      liftE (bind (AutoCorres.spec relation) fun _ => select fun _ => True) := rfl

theorem liftE_L2_guard (condition : State → Prop) :
    L2.guard (Exception := Exception) condition = liftE (AutoCorres.guard condition) := rfl

theorem liftE_L2_unknown (names : List String) :
    (L2.unknown names : L2.L2Program State Exception Result) =
      liftE (select fun _ => True) := rfl

theorem liftE_L2_fail :
    (L2.fail : L2.L2Program State Exception Result) = liftE fail := by
  exact liftE_fail.symm

theorem liftE_L2_recguard (measure : Nat) (program : Nondet State Result) :
    L2.recguard measure (liftE (ε := Exception) program) =
      liftE (nondetCondition (fun _ => decide (measure > 0)) program fail) := by
  cases measure with
  | zero =>
      rw [L2.L2_recguard_zero, liftE_L2_fail]
      congr 1
  | succ measure =>
      rw [show L2.recguard (Nat.succ measure) (liftE program) = liftE program by
        funext state
        simp [L2.recguard, L2.condition]]
      congr 1

theorem liftE_exec_concrete (stateMap : ConcreteState → AbstractState)
    (program : Nondet ConcreteState Result) :
    exec_concrete stateMap (liftE (ε := Exception) program) =
      liftE (exec_concrete stateMap program) := by
  apply Exact.eq
  constructor
  · intro state result
    rcases result with ⟨outcome, post⟩
    cases outcome with
    | error exception =>
        constructor
        · rw [in_exec_concrete]
          rintro ⟨source, concretePost, _, _, member⟩
          rw [L2.mem_liftE_iff] at member
          rcases member with ⟨value, equality, _⟩
          cases equality
        · intro member
          rw [L2.mem_liftE_iff] at member
          rcases member with ⟨value, equality, _⟩
          cases equality
    | ok value =>
        constructor
        · rw [in_exec_concrete]
          rintro ⟨source, concretePost, initial, final, member⟩
          rw [mem_liftE] at member
          rw [mem_liftE]
          exact ⟨source, concretePost, initial.symm, final.symm, member⟩
        · rw [mem_liftE]
          rintro ⟨source, concretePost, initial, final, member⟩
          rw [in_exec_concrete]
          exact ⟨source, concretePost, initial.symm, final.symm,
            mem_liftE.mpr member⟩
  · intro state
    constructor
    · rw [snd_exec_concrete]
      rintro ⟨source, equality, failed⟩
      rw [L2.failed_liftE] at failed
      rw [L2.failed_liftE, snd_exec_concrete]
      exact ⟨source, equality, failed⟩
    · rw [L2.failed_liftE, snd_exec_concrete]
      rintro ⟨source, equality, failed⟩
      rw [snd_exec_concrete]
      exact ⟨source, equality, L2.failed_liftE.mpr failed⟩

theorem liftE_exec_abstract (stateMap : ConcreteState → AbstractState)
    (program : Nondet AbstractState Result) :
    exec_abstract stateMap (liftE (ε := Exception) program) =
      liftE (exec_abstract stateMap program) := by
  apply Exact.eq
  constructor
  · intro state result
    rcases result with ⟨outcome, post⟩
    cases outcome with
    | error exception =>
        constructor
        · rw [in_exec_abstract]
          rintro ⟨mappedPost, _, member⟩
          rw [L2.mem_liftE_iff] at member
          rcases member with ⟨value, equality, _⟩
          cases equality
        · intro member
          rw [L2.mem_liftE_iff] at member
          rcases member with ⟨value, equality, _⟩
          cases equality
    | ok value =>
        constructor
        · rw [in_exec_abstract]
          rintro ⟨mappedPost, equality, member⟩
          rw [mem_liftE] at member
          rw [mem_liftE, in_exec_abstract]
          exact ⟨mappedPost, equality, member⟩
        · rw [mem_liftE, in_exec_abstract]
          rintro ⟨mappedPost, equality, member⟩
          rw [in_exec_abstract]
          exact ⟨mappedPost, equality, mem_liftE.mpr member⟩
  · intro state
    constructor
    · rw [snd_exec_abstract, L2.failed_liftE]
      intro failed
      rw [L2.failed_liftE, snd_exec_abstract]
      exact failed
    · rw [L2.failed_liftE, snd_exec_abstract]
      intro failed
      rw [snd_exec_abstract, L2.failed_liftE]
      exact failed

end

end Zag.Lang.AutoCorres.TypeStrengthen
