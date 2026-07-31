import Lang.AutoCorres.LocalVarExtract
import Lang.AutoCorres.ML.prog
import Lang.AutoCorres.L2

/-!
# Proof-producing local-variable extraction implementation

Corresponds only to [`tools/autocorres/local_var_extract.ML`](https://github.com/seL4/l4v/blob/bc2599a59c43e673dca021b10b9841e9b8da4430/tools/autocorres/local_var_extract.ML).

This is a certified all-locals specialization of upstream `do_conv`: the complete aggregate of
locals is passed as an L2 value while globals remain as monadic state. It does
not yet parse arbitrary L1 terms or perform per-variable heterogeneous liveness
extraction. Its correspondence uses upstream's failure-conditional `L2Corres`;
it is not reverse simulation or denotational equality.

The certified fragment is skip, local update, global update, guard, throw,
sequence, condition, catch, and loop. Specs and source failure are recognized
but rejected. Calls, local initialization, recursion guards, per-variable
liveness, and upstream fallback behavior are not represented by this kernel.
L2 exceptions carry the locals projected from the exceptional L1 post-state;
this lets catch handlers receive updated locals despite L1's `Unit` exception
marker. In particular, `L2.fail` is never used as an untranslatable fallback.
-/

namespace Zag.Lang.AutoCorres.ML.LocalVarExtract

open Zag.Lang.AutoCorres

universe u v w

open Zag.Lang.AutoCorres.LocalVarExtract

export Kernel (StateModel)

namespace Source

export Kernel.Source (Syntax localTransform globalTransform)

namespace Syntax

export Kernel.Source.Syntax
  (skip localUpdate globalUpdate guard throw seq condition «catch» spec «loop» fail denote)

end Syntax

end Source

namespace Target

export Kernel.Target (Syntax)

namespace Syntax

export Kernel.Target.Syntax
  (skip localUpdate globalUpdate guard throw seq condition «catch» «loop» denote)

end Syntax

end Target

export Kernel (Extracts Certificate Supported)

namespace Supported

export Kernel.Supported
  (skip localUpdate globalUpdate guard throw seq condition «catch» «loop»)

end Supported

/-- Source constructors intentionally outside the current certified kernel. -/
inductive UnsupportedConstructor where
  | spec
  | fail
  deriving DecidableEq, Repr

/-- Explicit recognition failure; unsupported input is never translated to failure. -/
structure RecognitionError where
  sourceConstructor : UnsupportedConstructor
  reason : String
  deriving DecidableEq, Repr

def unsupportedSpec : RecognitionError :=
  { sourceConstructor := .spec
    reason := "specification extraction requires proving that its relation mentions only globals" }

def unsupportedFail : RecognitionError :=
  { sourceConstructor := .fail
    reason := "source failure is not used as an untranslatable fallback in this kernel" }

/-- Recognize the supported source shape, retaining the first unsupported child. -/
def recognizeSupported :
    (source : Source.Syntax Full Locals Globals) ->
      Except RecognitionError (Supported source)
  | .skip => .ok .skip
  | .localUpdate update => .ok (.localUpdate update)
  | .globalUpdate update => .ok (.globalUpdate update)
  | .guard test => .ok (.guard test)
  | .throw => .ok .throw
  | .seq first second =>
      match recognizeSupported first with
      | .error error => .error error
      | .ok firstSupported =>
          match recognizeSupported second with
          | .error error => .error error
          | .ok secondSupported => .ok (.seq firstSupported secondSupported)
  | .condition test thenBranch elseBranch =>
      match recognizeSupported thenBranch with
      | .error error => .error error
      | .ok thenSupported =>
          match recognizeSupported elseBranch with
          | .error error => .error error
          | .ok elseSupported => .ok (.condition test thenSupported elseSupported)
  | .catch body handler =>
      match recognizeSupported body with
      | .error error => .error error
      | .ok bodySupported =>
          match recognizeSupported handler with
          | .error error => .error error
          | .ok handlerSupported => .ok (.catch bodySupported handlerSupported)
  | .spec _ => .error unsupportedSpec
  | .loop test body =>
      match recognizeSupported body with
      | .error error => .error error
      | .ok bodySupported => .ok (.loop test bodySupported)
  | .fail => .error unsupportedFail

private theorem local_corres (model : StateModel Full Locals Globals)
    (update : Locals -> Globals -> Locals) :
    Extracts model (.localUpdate update) (.localUpdate update) := by
  intro locals
  apply L2.corres_gets_modify
  · intro state _
    exact (model.projectGlobals_assemble _ _).symm
  · intro state hypothesis
    rw [Source.localTransform, model.projectLocals_assemble, hypothesis]

private theorem global_corres (model : StateModel Full Locals Globals)
    (update : Locals -> Globals -> Globals) :
    Extracts model (.globalUpdate update) (.globalUpdate update) := by
  intro locals
  apply L2.L2corres_inject_return
    (injectedExtract := model.projectLocals) (inject := fun _ => locals)
    (required := fun state => model.projectLocals state = locals)
    (programCorres := L2.corres_modify (precondition := fun state =>
      model.projectLocals state = locals) (exceptionExtract := model.projectLocals)
      (returnExtract := fun _ => ())
      (abstractUpdate := update locals)
      (concreteUpdate := Source.globalTransform model update) (by
        intro state hypothesis
        rw [Source.globalTransform, model.projectGlobals_assemble, hypothesis]))
  · intro state hypothesis post member
    change (Except.ok (), post) ∈
      (L1.modify (Source.globalTransform model update) state).results at member
    unfold L1.modify at member
    rw [mem_liftE, mem_modify] at member
    rcases member with ⟨_, rfl⟩
    rw [Source.globalTransform, model.projectLocals_assemble, hypothesis]
  · intro _ hypothesis
    exact hypothesis

private theorem guard_corres (model : StateModel Full Locals Globals)
    (test : Locals -> Globals -> Prop) :
    Extracts model (.guard test) (.guard test) := by
  intro locals
  apply L2.L2corres_inject_return
    (injectedExtract := model.projectLocals) (inject := fun _ => locals)
    (required := fun state => model.projectLocals state = locals)
    (programCorres := L2.corres_guard (precondition := fun state =>
      model.projectLocals state = locals) (exceptionExtract := model.projectLocals)
      (returnExtract := fun _ => ()) (by
        intro state hypothesis
        rw [hypothesis]))
  · intro state hypothesis post member
    change (Except.ok (), post) ∈
      (L1.guard (fun state => test (model.projectLocals state)
        (model.projectGlobals state)) state).results at member
    unfold L1.guard at member
    rw [mem_liftE, mem_guard] at member
    rcases member with ⟨_, _, rfl⟩
    exact hypothesis.symm
  · intro _ hypothesis
    exact hypothesis

/--
The total pure local-conversion kernel corresponding to the structural core of
upstream `do_conv`. Support evidence makes every recursive case certifiable.
-/
def extract (model : StateModel Full Locals Globals) {source}
    (supported : Supported source) : Certificate model source :=
  match supported with
  | .skip =>
      { target := .skip
        corres := fun _locals => L2.corres_gets_skip (fun _ hypothesis => hypothesis) }
  | .localUpdate update =>
      { target := .localUpdate update
        corres := local_corres model update }
  | .globalUpdate update =>
      { target := .globalUpdate update
        corres := global_corres model update }
  | .guard test =>
      { target := .guard test
        corres := guard_corres model test }
  | .throw =>
      { target := .throw
        corres := fun _ => L2.corres_throw (fun _ hypothesis => hypothesis) }
  | .seq firstSupported secondSupported =>
      let firstCertificate := extract model firstSupported
      let secondCertificate := extract model secondSupported
      { target := .seq firstCertificate.target secondCertificate.target
        corres := fun locals => L2.L2corres_seq
          (firstCertificate.corres locals)
          (fun nextLocals => secondCertificate.corres nextLocals)
          (fun _ _ _ _ => rfl)
          (fun _ hypothesis => hypothesis) }
  | .condition test thenSupported elseSupported =>
      let thenCertificate := extract model thenSupported
      let elseCertificate := extract model elseSupported
      { target := .condition test thenCertificate.target elseCertificate.target
        corres := fun locals => L2.L2corres_cond
          (thenCertificate.corres locals)
          (elseCertificate.corres locals)
          (fun _ hypothesis => hypothesis)
          (fun _ hypothesis => hypothesis)
          (fun _ hypothesis => by rw [hypothesis]) }
  | .catch bodySupported handlerSupported =>
      let bodyCertificate := extract model bodySupported
      let handlerCertificate := extract model handlerSupported
      { target := .catch bodyCertificate.target handlerCertificate.target
        corres := fun locals => L2.L2corres_catch
          (bodyCertificate.corres locals)
          (fun exceptionalLocals => handlerCertificate.corres exceptionalLocals)
          (fun _ _ _ _ => rfl)
          (fun _ hypothesis => hypothesis) }
  | .loop test bodySupported =>
      let bodyCertificate := extract model bodySupported
      { target := .loop test bodyCertificate.target
        corres := fun locals => L2.L2corres_while
          (invariant := fun value state => model.projectLocals state = value)
          (bodyPrecondition := fun value state => model.projectLocals state = value)
          (required := fun value state => model.projectLocals state = value)
          (abstractTest := test)
          (concreteTest := fun state =>
            test (model.projectLocals state) (model.projectGlobals state))
          (abstractBody := bodyCertificate.target.denote)
          (initial := locals) (names := [])
          (bodyCertificate.corres)
          (fun _ _ _ _ => rfl)
          (fun _ _ => Iff.rfl)
          (fun _ _ hypothesis => hypothesis)
          (fun _ _ hypothesis => hypothesis)
          (fun _ hypothesis => hypothesis) }

/-- Recognize and run the proof-producing kernel without theorem search. -/
def run (model : StateModel Full Locals Globals)
    (source : Source.Syntax Full Locals Globals) :
    Except RecognitionError (Certificate model source) :=
  (recognizeSupported source).map (extract model)

/-! ## Reduction and correctness pins -/

theorem localTransform_preserves_globals (model : StateModel Full Locals Globals)
    (update : Locals -> Globals -> Locals) (state : Full) :
    model.projectGlobals (Source.localTransform model update state) =
      model.projectGlobals state := by
  exact model.projectGlobals_assemble _ _

theorem localTransform_returns_updated_locals (model : StateModel Full Locals Globals)
    (update : Locals -> Globals -> Locals) (state : Full) :
    model.projectLocals (Source.localTransform model update state) =
      update (model.projectLocals state) (model.projectGlobals state) := by
  exact model.projectLocals_assemble _ _

theorem extract_skip_target (model : StateModel Full Locals Globals) :
    (extract model Supported.skip).target = .skip := by
  rfl

theorem extract_localUpdate_target (model : StateModel Full Locals Globals)
    (update : Locals -> Globals -> Locals) :
    (extract model (Supported.localUpdate update)).target = .localUpdate update := by
  rfl

theorem extract_local_then_global_target (model : StateModel Full Locals Globals)
    (localUpdate : Locals -> Globals -> Locals)
    (globalUpdate : Locals -> Globals -> Globals) :
    (extract model (Supported.seq (Supported.localUpdate localUpdate)
      (Supported.globalUpdate globalUpdate))).target =
      .seq (.localUpdate localUpdate) (.globalUpdate globalUpdate) := by
  rfl

theorem extract_local_then_global_correct (model : StateModel Full Locals Globals)
    (localUpdate : Locals -> Globals -> Locals)
    (globalUpdate : Locals -> Globals -> Globals) :
    Extracts model (.seq (.localUpdate localUpdate) (.globalUpdate globalUpdate))
      (.seq (.localUpdate localUpdate) (.globalUpdate globalUpdate)) :=
  (extract model (Supported.seq (Supported.localUpdate localUpdate)
    (Supported.globalUpdate globalUpdate))).corres

theorem extract_guard_then_throw_target (model : StateModel Full Locals Globals)
    (test : Locals -> Globals -> Prop) :
    (extract model (Supported.seq (Supported.guard test) Supported.throw)).target =
      .seq (.guard test) .throw := by
  rfl

theorem extract_guard_then_throw_correct (model : StateModel Full Locals Globals)
    (test : Locals -> Globals -> Prop) :
    Extracts model (.seq (.guard test) .throw) (.seq (.guard test) .throw) :=
  (extract model (Supported.seq (Supported.guard test) Supported.throw)).corres

theorem extract_condition_target (model : StateModel Full Locals Globals)
    (test : Locals -> Globals -> Prop)
    (localUpdate : Locals -> Globals -> Locals)
    (globalUpdate : Locals -> Globals -> Globals) :
    (extract model (Supported.condition test (Supported.localUpdate localUpdate)
      (Supported.globalUpdate globalUpdate))).target =
      .condition test (.localUpdate localUpdate) (.globalUpdate globalUpdate) := by
  rfl

theorem extract_condition_correct (model : StateModel Full Locals Globals)
    (test : Locals -> Globals -> Prop)
    (localUpdate : Locals -> Globals -> Locals)
    (globalUpdate : Locals -> Globals -> Globals) :
    Extracts model
      (.condition test (.localUpdate localUpdate) (.globalUpdate globalUpdate))
      (.condition test (.localUpdate localUpdate) (.globalUpdate globalUpdate)) :=
  (extract model (Supported.condition test (Supported.localUpdate localUpdate)
    (Supported.globalUpdate globalUpdate))).corres

theorem extract_catch_target (model : StateModel Full Locals Globals)
    (localUpdate : Locals -> Globals -> Locals)
    (handlerUpdate : Locals -> Globals -> Globals) :
    (extract model (Supported.catch
      (Supported.seq (Supported.localUpdate localUpdate) Supported.throw)
      (Supported.globalUpdate handlerUpdate))).target =
      .catch (.seq (.localUpdate localUpdate) .throw)
        (.globalUpdate handlerUpdate) := by
  rfl

theorem extract_catch_correct (model : StateModel Full Locals Globals)
    (localUpdate : Locals -> Globals -> Locals)
    (handlerUpdate : Locals -> Globals -> Globals) :
    Extracts model
      (.catch (.seq (.localUpdate localUpdate) .throw) (.globalUpdate handlerUpdate))
      (.catch (.seq (.localUpdate localUpdate) .throw) (.globalUpdate handlerUpdate)) :=
  (extract model (Supported.catch
    (Supported.seq (Supported.localUpdate localUpdate) Supported.throw)
    (Supported.globalUpdate handlerUpdate))).corres

theorem extract_loop_target (model : StateModel Full Locals Globals)
    (test : Locals -> Globals -> Prop)
    (update : Locals -> Globals -> Locals) :
    (extract model (Supported.loop test (Supported.localUpdate update))).target =
      .loop test (.localUpdate update) := by
  rfl

theorem extract_loop_correct (model : StateModel Full Locals Globals)
    (test : Locals -> Globals -> Prop)
    (update : Locals -> Globals -> Locals) :
    Extracts model (.loop test (.localUpdate update))
      (.loop test (.localUpdate update)) :=
  (extract model (Supported.loop test (Supported.localUpdate update))).corres

theorem recognize_condition_supported (test : Locals -> Globals -> Prop) :
    recognizeSupported
      (Source.Syntax.condition test .skip .throw : Source.Syntax Full Locals Globals) =
      .ok (Supported.condition test Supported.skip Supported.throw) := by
  rfl

theorem recognize_catch_supported :
    recognizeSupported
      (Source.Syntax.catch .throw .skip : Source.Syntax Full Locals Globals) =
      .ok (Supported.catch Supported.throw Supported.skip) := by
  rfl

theorem recognize_loop_supported (test : Locals -> Globals -> Prop) :
    recognizeSupported
      (Source.Syntax.loop test .skip : Source.Syntax Full Locals Globals) =
      .ok (Supported.loop test Supported.skip) := by
  rfl

theorem recognize_spec_error (relation : Set (Full × Full)) :
    recognizeSupported
      (Source.Syntax.spec relation : Source.Syntax Full Locals Globals) =
      .error unsupportedSpec := by
  rfl

end Zag.Lang.AutoCorres.ML.LocalVarExtract
