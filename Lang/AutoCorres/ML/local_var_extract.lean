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
sequence, condition, catch, and loop. Specs and source failure remain in the
canonical syntax but have no support evidence. Calls, local initialization,
recursion guards, per-variable liveness, and upstream fallback behavior are not
represented by this kernel.
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

export Zag.Lang.AutoCorres.L1.Syntax
  (skip seq modify condition «catch» «while» throw spec guard fail «call»)
export Kernel.Source.Syntax (denote)

end Syntax

end Source

namespace Target

export Kernel.Target (Syntax)

namespace Syntax

export Kernel.Target.Syntax
  (skip localUpdate globalUpdate guard throw seq condition «catch» «loop» «call» fail denote)

end Syntax

end Target

namespace CanonicalTarget

export Kernel.CanonicalTarget (Syntax)

namespace Syntax

export Kernel.CanonicalTarget.Syntax (ofGeneric denote)

end Syntax

end CanonicalTarget

export Kernel (Extracts Certificate ClosedExtracts ClosedCertificate Supported)

namespace Supported

export Kernel.Supported
  (skip localUpdate globalUpdate guard throw seq condition «catch» «loop» «call» fail)

end Supported

private theorem local_corres (model : StateModel Full Locals Globals)
    (update : Locals -> Globals -> Locals) :
    Extracts model (Target.Syntax.localUpdate update)
      (.modify (Source.localTransform model update)) := by
  intro locals
  simp only [Target.Syntax.denote]
  apply L2.corres_gets_modify
  · intro state _
    exact (model.projectGlobals_assemble _ _).symm
  · intro state hypothesis
    rw [Source.localTransform, model.projectLocals_assemble, hypothesis]

private theorem global_corres (model : StateModel Full Locals Globals)
    (update : Locals -> Globals -> Globals) :
    Extracts model (Target.Syntax.globalUpdate update)
      (.modify (Source.globalTransform model update)) := by
  intro locals
  simp only [Target.Syntax.denote]
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
    Extracts model (Target.Syntax.guard test) (.guard fun state =>
      test (model.projectLocals state) (model.projectGlobals state)) := by
  intro locals
  simp only [Target.Syntax.denote]
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
    (supported : Supported model source) : Certificate model source :=
  match supported with
  | .skip =>
      { target := Target.Syntax.skip
        corres := fun _locals => by
          simpa only [Target.Syntax.denote,
            Source.Syntax.denote, L1.Syntax.denote, L1.skip]
            using L2.corres_gets_skip
              (stateProject := model.projectGlobals)
              (returnExtract := model.projectLocals)
              (exceptionExtract := model.projectLocals)
              (precondition := fun state => model.projectLocals state = _locals)
              (read := fun _ => _locals) (names := [])
              (fun _ hypothesis => hypothesis) }
  | .localUpdate update =>
      { target := Target.Syntax.localUpdate update
        corres := local_corres model update }
  | .globalUpdate update =>
      { target := Target.Syntax.globalUpdate update
        corres := global_corres model update }
  | .guard test =>
      { target := Target.Syntax.guard test
        corres := guard_corres model test }
  | .throw =>
      { target := Target.Syntax.throw
        corres := fun _ => by
          simpa only [Target.Syntax.denote,
            Source.Syntax.denote, L1.Syntax.denote, L1.throw]
            using L2.corres_throw (names := [])
              (fun _ hypothesis => hypothesis) }
  | .seq firstSupported secondSupported =>
      let firstCertificate := extract model firstSupported
      let secondCertificate := extract model secondSupported
      { target := Target.Syntax.seq firstCertificate.target secondCertificate.target
        corres := fun locals => L2.L2corres_seq
          (firstCertificate.corres locals)
          (fun nextLocals => secondCertificate.corres nextLocals)
          (fun _ _ _ _ => rfl)
          (fun _ hypothesis => hypothesis) }
  | .condition test thenSupported elseSupported =>
      let thenCertificate := extract model thenSupported
      let elseCertificate := extract model elseSupported
      { target := Target.Syntax.condition test thenCertificate.target
          elseCertificate.target
        corres := fun locals => L2.L2corres_cond
          (thenCertificate.corres locals)
          (elseCertificate.corres locals)
          (fun _ hypothesis => hypothesis)
          (fun _ hypothesis => hypothesis)
          (fun _ hypothesis => by rw [hypothesis]) }
  | .catch bodySupported handlerSupported =>
      let bodyCertificate := extract model bodySupported
      let handlerCertificate := extract model handlerSupported
      { target := Target.Syntax.catch bodyCertificate.target handlerCertificate.target
        corres := fun locals => L2.L2corres_catch
          (bodyCertificate.corres locals)
          (fun exceptionalLocals => handlerCertificate.corres exceptionalLocals)
          (fun _ _ _ _ => rfl)
          (fun _ hypothesis => hypothesis) }
  | .loop test bodySupported =>
      let bodyCertificate := extract model bodySupported
      { target := Target.Syntax.loop test bodyCertificate.target
        corres := fun locals => L2.L2corres_while
          (invariant := fun value state => model.projectLocals state = value)
          (bodyPrecondition := fun value state => model.projectLocals state = value)
          (required := fun value state => model.projectLocals state = value)
          (abstractTest := test)
          (concreteTest := fun state =>
            test (model.projectLocals state) (model.projectGlobals state))
          (abstractBody := Target.Syntax.denote bodyCertificate.target)
          (initial := locals) (names := [])
          (bodyCertificate.corres)
          (fun _ _ _ _ => rfl)
          (fun _ _ => Iff.rfl)
          (fun _ _ hypothesis => hypothesis)
          (fun _ _ hypothesis => hypothesis)
          (fun _ hypothesis => hypothesis) }
  | .call bodySupported =>
      let bodyCertificate := extract model bodySupported
      { target := Target.Syntax.call bodyCertificate.target
        corres := fun locals => by
          simpa only [Target.Syntax.denote, Source.Syntax.denote,
            L1.Syntax.denote] using bodyCertificate.corres locals }
  | .fail =>
      { target := Target.Syntax.fail
        corres := fun _ => by
          simpa only [Target.Syntax.denote, Source.Syntax.denote,
            L1.Syntax.denote] using
              (L2.corres_fail (stateProject := model.projectGlobals)
                (returnExtract := model.projectLocals)
                (exceptionExtract := model.projectLocals)) }

/--
Extract the same certified target into the explicitly closed Type0 canonical
syntax consumed by HeapLift. The correspondence is inherited from `extract`.
-/
def extractCanonical {Full : Type u} {Locals Globals : Type}
    (model : StateModel Full Locals Globals) {source}
    (supported : Supported model source) : ClosedCertificate model source :=
  (extract model supported).close

/-- Run the proof-producing kernel from narrow structural support evidence. -/
def run (model : StateModel Full Locals Globals) {source}
    (supported : Supported model source) : Certificate model source :=
  extract model supported

/-- Run the closed canonical extraction API used by the direct HeapLift path. -/
def runCanonical {Full : Type u} {Locals Globals : Type}
    (model : StateModel Full Locals Globals) {source}
    (supported : Supported model source) : ClosedCertificate model source :=
  extractCanonical model supported

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
      (.seq (.modify (Source.localTransform model localUpdate))
        (.modify (Source.globalTransform model globalUpdate))) :=
  (extract model (Supported.seq (Supported.localUpdate localUpdate)
    (Supported.globalUpdate globalUpdate))).corres

theorem extract_guard_then_throw_target (model : StateModel Full Locals Globals)
    (test : Locals -> Globals -> Prop) :
    (extract model (Supported.seq (Supported.guard test) Supported.throw)).target =
      .seq (.guard test) .throw := by
  rfl

theorem extract_guard_then_throw_correct (model : StateModel Full Locals Globals)
    (test : Locals -> Globals -> Prop) :
    Extracts model (.seq (.guard test) .throw)
      (.seq (.guard fun state =>
        test (model.projectLocals state) (model.projectGlobals state)) .throw) :=
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
      (.condition
        (fun state => test (model.projectLocals state) (model.projectGlobals state))
        (.modify (Source.localTransform model localUpdate))
        (.modify (Source.globalTransform model globalUpdate))) :=
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
      (.catch
        (.seq (.modify (Source.localTransform model localUpdate)) .throw)
        (.modify (Source.globalTransform model handlerUpdate))) :=
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
      (.while
        (fun state => test (model.projectLocals state) (model.projectGlobals state))
        (.modify (Source.localTransform model update))) :=
  (extract model (Supported.loop test (Supported.localUpdate update))).corres

theorem run_condition_target (model : StateModel Full Locals Globals)
    (test : Locals -> Globals -> Prop) :
    (run model (Supported.condition test Supported.skip Supported.throw)).target =
      .condition test .skip .throw := by
  rfl

end Zag.Lang.AutoCorres.ML.LocalVarExtract
