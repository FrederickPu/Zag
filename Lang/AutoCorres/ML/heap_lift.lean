import Lang.AutoCorres.HeapLift
import Lang.AutoCorres.ExecConcrete
import Lang.AutoCorres.ML.heap_lift_base

/-!
# Certified heap-lift conversion kernel

Corresponds only to [`tools/autocorres/heap_lift.ML`](https://github.com/seL4/l4v/blob/bc2599a59c43e673dca021b10b9841e9b8da4430/tools/autocorres/heap_lift.ML).

This is a certified fragment of the upstream proof-producing conversion. It
reifies the L2 nodes for which `HeapLift.lean` currently provides faithful
rules, and makes every expression, update, guard, and specification premise an
indexed input. In particular, arbitrary functions are never inspected to
invent abstraction evidence.

The omitted upstream stages are parser and Isabelle-term inspection,
first-order application conversion, rule indexing and theorem search,
automatic heap-expression and structure-layout proof generation, function
eligibility analysis, recursive-call assumptions and recursive definition,
generated heap notation, tracing, parallel scheduling, and post-conversion
peephole simplification. `while`, direct calls, and `recguard` are deliberately
not constructors of `Supported`: the local `HeapLift.lean` has no corresponding
principal rules. Calls whose bodies already have certificates are adapted
separately below; loops and recursion remain typed obligations for a future
extension and are never translated to `L2.fail`.
-/

namespace Zag.Lang.AutoCorres.ML.HeapLift

open Zag.Lang.AutoCorres
open Zag.Lang.AutoCorres.HeapLift.Kernel

universe u v w x

variable {ConcreteState : Type u} {AbstractState : Type v}
variable {State : Type u} {Exception InnerException : Type w}
variable {Value Result First : Type}
variable {stateMap : ConcreteState -> AbstractState}

private theorem L2Tcorres_unknown (stateMap : ConcreteState -> AbstractState)
    (names : List String) :
    Zag.Lang.AutoCorres.HeapLift.L2Tcorres (Exception := Exception) stateMap
      (L2.unknown (Value := Value) names) (L2.unknown names) := by
  intro state _
  constructor
  · intro result post member
    change (result, post) ∈
      (liftE (select fun _ : Value => True) state).results at member
    rw [L2.mem_liftE_iff] at member
    rcases member with ⟨value, rfl, member⟩
    rw [mem_select] at member
    rcases member with ⟨_, rfl⟩
    change (Except.ok value, stateMap post) ∈
      (liftE (select fun _ : Value => True) (stateMap post)).results
    rw [L2.mem_liftE_iff]
    exact ⟨value, rfl, ⟨True.intro, rfl⟩⟩
  · simp [L2.unknown, select]

private theorem L2Tcorres_throw (stateMap : ConcreteState -> AbstractState)
    (exception : Exception) (names : List String) :
    Zag.Lang.AutoCorres.HeapLift.L2Tcorres stateMap
      (L2.throw (Value := Value) exception names) (L2.throw exception names) := by
  intro state _
  constructor
  · intro result post member
    cases result with
    | error actual =>
        change (Except.error actual, post) = (Except.error exception, state) at member
        cases member
        rfl
    | ok value =>
        change (Except.ok value, post) = (Except.error exception, state) at member
        cases member
  · simp [L2.throw, AutoCorres.throw, pure]

/--
The ordinary dependent conversion kernel. It only pattern matches on supplied
evidence and recursively assembles principal rules; it performs no theorem
search. Its target projection is computable even though denotation is not.
-/
def transform : Challenge (Exception := Exception) stateMap
  | _, _, .gets names evidence =>
      { target := .guardedGets evidence.abstractRewriteGuard
          evidence.abstractExpressionGuard evidence.abstract names
        correctness := by
          simpa only [Target.denote, Source.denote, L2.Syntax.denote] using
            Zag.Lang.AutoCorres.HeapLift.L2Tcorres_gets evidence.rewrite
              evidence.rewriteGuardAbstracts evidence.expressionAbstracts }
  | _, _, .modify evidence =>
      { target := .guardedModify evidence.abstractRewriteGuard
          evidence.abstractUpdateGuard evidence.abstract
        correctness := by
          simpa only [Target.denote, Source.denote, L2.Syntax.denote] using
            Zag.Lang.AutoCorres.HeapLift.L2Tcorres_modify evidence.rewrite
              evidence.rewriteGuardAbstracts evidence.updateAbstracts }
  | _, _, .guard evidence =>
      { target := .guard evidence.abstract
        correctness := by
          simpa only [Target.denote, Source.denote, L2.Syntax.denote] using
            Zag.Lang.AutoCorres.HeapLift.L2Tcorres_guard evidence.rewrite
              evidence.guardAbstracts }
  | _, _, .condition testEvidence thenSupported elseSupported =>
      let thenCertificate := transform thenSupported
      let elseCertificate := transform elseSupported
      { target := .guardedCondition testEvidence.abstractRewriteGuard
          testEvidence.abstractExpressionGuard testEvidence.abstract
          thenCertificate.target elseCertificate.target
        correctness := by
          simpa only [Target.denote, Source.denote, L2.Syntax.denote] using
            Zag.Lang.AutoCorres.HeapLift.L2Tcorres_condition
              thenCertificate.correctness elseCertificate.correctness
              testEvidence.rewrite testEvidence.rewriteGuardAbstracts
              testEvidence.expressionAbstracts }
  | _, _, .seq firstSupported nextSupported =>
      let firstCertificate := transform firstSupported
      { target := .seq firstCertificate.target fun value =>
          (transform (nextSupported value)).target
        correctness := by
          simpa only [Target.denote, Source.denote, L2.Syntax.denote] using
            Zag.Lang.AutoCorres.HeapLift.L2Tcorres_seq
              firstCertificate.correctness fun value =>
                (transform (nextSupported value)).correctness }
  | _, _, .catch bodySupported handlerSupported =>
      let bodyCertificate := transform bodySupported
      { target := .catch bodyCertificate.target fun exception =>
          (transform (handlerSupported exception)).target
        correctness := by
          simpa only [Target.denote, Source.denote, L2.Syntax.denote] using
            Zag.Lang.AutoCorres.HeapLift.L2Tcorres_catch
              bodyCertificate.correctness fun exception =>
                (transform (handlerSupported exception)).correctness }
  | _, _, .spec evidence =>
      { target := .guardedSpec evidence.precondition evidence.abstract
        correctness := by
          simpa only [Target.denote, Source.denote, L2.Syntax.denote] using
            Zag.Lang.AutoCorres.HeapLift.L2Tcorres_spec
              evidence.specificationAbstracts }
  | _, _, .unknown names =>
      { target := .unknown names
        correctness := by
          simpa only [Target.denote, Source.denote, L2.Syntax.denote] using
            L2Tcorres_unknown stateMap names }
  | _, _, .throw exception names =>
      { target := .throw exception names
        correctness := by
          simpa only [Target.denote, Source.denote, L2.Syntax.denote] using
            L2Tcorres_throw stateMap exception names }
  | _, _, .fail =>
      { target := .fail
        correctness := by
          simpa only [Target.denote, Source.denote, L2.Syntax.denote] using
            Zag.Lang.AutoCorres.HeapLift.L2Tcorres_fail stateMap L2.fail }

/-! ## Computable structural recognition -/

/-- Evidence that a source is one of the three purely structural identity leaves. -/
inductive IdentityLeaf {State : Type u} {Exception : Type v} :
    {Result : Type} -> Source State Exception Result -> Type (max (u + 1) (v + 1)) where
  | unknown {Result : Type} (names : List String) : IdentityLeaf (.unknown names)
  | throw {Result : Type} (exception : Exception) (names : List String) :
      IdentityLeaf (.throw exception names)
  | fail {Result : Type} : IdentityLeaf .fail

/-- Recognize only leaves that need no expression-abstraction inference. -/
def recognizeIdentityLeaf (source : Source State Exception Result) :
    Option (IdentityLeaf source) :=
  match source with
  | .unknown names => some (IdentityLeaf.unknown (Result := Result) names)
  | .throw exception names =>
      some (IdentityLeaf.throw (Result := Result) exception names)
  | .fail => some (IdentityLeaf.fail (Result := Result))
  | _ => none

/-! ## Mixed lifted and unlifted execution -/

/-- Syntax for selecting a lifted body or executing an unlifted concrete body. -/
inductive MixedTarget (ConcreteState : Type u) (AbstractState : Type v)
    (Exception : Type w) (Result : Type) where
  | lifted (target : Target AbstractState Exception Result)
  | unlifted (source : Source ConcreteState Exception Result)

noncomputable def MixedTarget.denote
    (stateMap : ConcreteState -> AbstractState) :
    MixedTarget ConcreteState AbstractState Exception Result ->
      L2.L2Program AbstractState Exception Result
  | .lifted target => target.denote
  | .unlifted source => exec_concrete stateMap source.denote

/-- A mixed execution choice with its correspondence theorem. -/
structure MixedCertificate (stateMap : ConcreteState -> AbstractState)
    (source : Source ConcreteState Exception Result) where
  target : MixedTarget ConcreteState AbstractState Exception Result
  correctness : Zag.Lang.AutoCorres.HeapLift.L2Tcorres stateMap
    (target.denote stateMap) source.denote

/--
An indexed mixed-execution choice. Only the lifted branch requires a prior
certificate; the unlifted branch carries the source it executes directly.
-/
inductive MixedExecutionChoice (stateMap : ConcreteState -> AbstractState) :
    {Result : Type} -> Source ConcreteState Exception Result ->
      Type (max (u + 1) (max (v + 1) (w + 1))) where
  | lifted {Result : Type} {source : Source ConcreteState Exception Result}
      (certificate : Certificate stateMap source) :
      MixedExecutionChoice stateMap source
  | unlifted {Result : Type} (source : Source ConcreteState Exception Result) :
      MixedExecutionChoice stateMap source

/-- Build the certificate selected by an indexed mixed-execution choice. -/
def mixedExecution : {Result : Type} ->
    {source : Source ConcreteState Exception Result} ->
    MixedExecutionChoice stateMap source -> MixedCertificate stateMap source
  | _, _, .lifted certificate =>
      { target := .lifted certificate.target
        correctness := certificate.correctness }
  | _, _, .unlifted source =>
      { target := .unlifted source
        correctness := corresXF_exec_concrete_self stateMap (fun _ => True)
          source.denote }

/-- Run a certified lifted target through the converse concrete-state adapter. -/
noncomputable def executeAbstractOnConcrete
    {source : Source ConcreteState Exception Result}
    (certificate : Certificate stateMap source) :
    L2.L2Program ConcreteState Exception Result :=
  exec_abstract stateMap certificate.target.denote

theorem executeAbstractOnConcrete_correct
    {source : Source ConcreteState Exception Result}
    (certificate : Certificate stateMap source) :
    Zag.Lang.AutoCorres.HeapLift.L2Tcorres id
      (executeAbstractOnConcrete certificate) source.denote := by
  exact corresXF_exec_abstract certificate.correctness

/-- A direct-call wrapper is only produced from an existing body certificate. -/
structure CallCertificate (stateMap : ConcreteState -> AbstractState)
    (source : Source ConcreteState InnerException Result)
    (OuterException : Type x) where
  abstractCall : L2.L2Program AbstractState OuterException Result
  concreteCall : L2.L2Program ConcreteState OuterException Result
  correctness : Zag.Lang.AutoCorres.HeapLift.L2Tcorres stateMap
    abstractCall concreteCall

/--
Adapt a certified body through `L2.call`. The current catch and fail rules close
this obligation; no unsupported call theorem is assumed.
-/
noncomputable def adaptCall
    {source : Source ConcreteState InnerException Result}
    (certificate : Certificate stateMap source)
    (OuterException : Type x) : CallCertificate stateMap source OuterException :=
  { abstractCall := L2.call certificate.target.denote
    concreteCall := L2.call source.denote
    correctness := by
      apply Zag.Lang.AutoCorres.HeapLift.L2Tcorres_catch certificate.correctness
      intro _
      exact Zag.Lang.AutoCorres.HeapLift.L2Tcorres_fail stateMap L2.fail }

/-! ## Reduction and correctness pins -/

theorem guardedGets_reduction_pin
    (Exception : Type w) {read : ConcreteState -> Result} (names : List String)
    (evidence : ExprEvidence stateMap read) :
    (transform (Supported.gets (Exception := Exception) names evidence)).target =
      Target.guardedGets (Exception := Exception) evidence.abstractRewriteGuard
        evidence.abstractExpressionGuard evidence.abstract names := by
  rfl

theorem guardedGets_correctness_pin
    (Exception : Type w) {read : ConcreteState -> Result} (names : List String)
    (evidence : ExprEvidence stateMap read) :
    Zag.Lang.AutoCorres.HeapLift.L2Tcorres (Exception := Exception) stateMap
      (transform (Supported.gets (Exception := Exception) names evidence)).target.denote
      (Source.gets (Exception := Exception) read names).denote :=
  (transform (Supported.gets (Exception := Exception) names evidence)).correctness

theorem guardedModify_reduction_pin
    (Exception : Type w) {update : ConcreteState -> ConcreteState}
    (evidence : UpdateEvidence stateMap update) :
    (transform (Supported.modify (Exception := Exception) evidence)).target =
      Target.guardedModify (Exception := Exception) evidence.abstractRewriteGuard
        evidence.abstractUpdateGuard evidence.abstract := by
  rfl

theorem guardedModify_correctness_pin
    (Exception : Type w) {update : ConcreteState -> ConcreteState}
    (evidence : UpdateEvidence stateMap update) :
    Zag.Lang.AutoCorres.HeapLift.L2Tcorres (Exception := Exception) stateMap
      (transform (Supported.modify (Exception := Exception) evidence)).target.denote
      (Source.modify (Exception := Exception) update).denote :=
  (transform (Supported.modify (Exception := Exception) evidence)).correctness

theorem sequence_reduction_pin
    (Exception : Type w) {read : ConcreteState -> First} (names : List String)
    (readEvidence : ExprEvidence stateMap read)
    {update : ConcreteState -> ConcreteState}
    (updateEvidence : UpdateEvidence stateMap update) :
    (transform (Supported.seq (Exception := Exception)
      (Supported.gets (Exception := Exception) names readEvidence)
      (fun _ => Supported.modify (Exception := Exception) updateEvidence))).target =
      Target.seq (Exception := Exception)
        (Target.guardedGets (Exception := Exception) readEvidence.abstractRewriteGuard
          readEvidence.abstractExpressionGuard readEvidence.abstract names)
        (fun _ => Target.guardedModify (Exception := Exception)
          updateEvidence.abstractRewriteGuard
          updateEvidence.abstractUpdateGuard updateEvidence.abstract) := by
  rfl

theorem sequence_correctness_pin
    (Exception : Type w) {read : ConcreteState -> First} (names : List String)
    (readEvidence : ExprEvidence stateMap read)
    {update : ConcreteState -> ConcreteState}
    (updateEvidence : UpdateEvidence stateMap update) :
    Zag.Lang.AutoCorres.HeapLift.L2Tcorres (Exception := Exception) stateMap
      (transform (Supported.seq (Exception := Exception)
        (Supported.gets (Exception := Exception) names readEvidence)
        (fun _ => Supported.modify (Exception := Exception) updateEvidence))).target.denote
      (Source.seq (Exception := Exception)
        (Source.gets (Exception := Exception) read names)
        (fun _ => Source.modify (Exception := Exception) update)).denote :=
  (transform (Supported.seq (Exception := Exception)
    (Supported.gets (Exception := Exception) names readEvidence)
    (fun _ => Supported.modify (Exception := Exception) updateEvidence))).correctness

theorem condition_reduction_pin
    {test : ConcreteState -> Prop} (testEvidence : ExprEvidence stateMap test)
    {thenSource elseSource : Source ConcreteState Exception Result}
    (thenSupported : Supported stateMap thenSource)
    (elseSupported : Supported stateMap elseSource) :
    (transform (Supported.condition testEvidence thenSupported elseSupported)).target =
      .guardedCondition testEvidence.abstractRewriteGuard
        testEvidence.abstractExpressionGuard testEvidence.abstract
        (transform thenSupported).target (transform elseSupported).target := by
  simp only [transform]

theorem condition_correctness_pin
    {test : ConcreteState -> Prop} (testEvidence : ExprEvidence stateMap test)
    {thenSource elseSource : Source ConcreteState Exception Result}
    (thenSupported : Supported stateMap thenSource)
    (elseSupported : Supported stateMap elseSource) :
    Zag.Lang.AutoCorres.HeapLift.L2Tcorres stateMap
      (transform (Supported.condition testEvidence thenSupported elseSupported)).target.denote
      (Source.condition test thenSource elseSource).denote :=
  (transform (Supported.condition testEvidence thenSupported elseSupported)).correctness

theorem mixedExecution_reduction_pin
    (source : Source ConcreteState Exception Result) :
    (mixedExecution (MixedExecutionChoice.unlifted (stateMap := stateMap)
      source)).target = .unlifted source := by
  rfl

theorem mixedExecution_correctness_pin
    (source : Source ConcreteState Exception Result) :
    Zag.Lang.AutoCorres.HeapLift.L2Tcorres stateMap
      ((mixedExecution (MixedExecutionChoice.unlifted (stateMap := stateMap)
        source)).target.denote stateMap) source.denote :=
  (mixedExecution (MixedExecutionChoice.unlifted (stateMap := stateMap)
    source)).correctness

end Zag.Lang.AutoCorres.ML.HeapLift
