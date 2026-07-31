import Lang.AutoCorres.SimplConv

/-!
# Proof-producing SIMPL conversion

Corresponds only to [`tools/autocorres/simpl_conv.ML`](https://github.com/seL4/l4v/blob/bc2599a59c43e673dca021b10b9841e9b8da4430/tools/autocorres/simpl_conv.ML).

This is the structural SIMPL-to-L1 semantic conversion over the local command
core, corresponding to upstream `simpl_conv'`. The upstream procedure-table,
C-parser call pattern, definition, cleanup, and whole-program orchestration
machinery is not available in the local model.
-/

namespace Zag.Lang.AutoCorres.ML.SimplConv

universe u v w

open Zag.Lang.AutoCorres.SimplConv.Kernel

/-- SIMPL constructors for which the local converter has no sound L1 rule. -/
inductive UnsupportedConstructor where
  | Call
  | DynCom
  deriving DecidableEq, Repr

/-- A reviewable conversion failure, including its exact source constructor. -/
structure Unsupported where
  sourceConstructor : UnsupportedConstructor
  reason : String
  deriving DecidableEq, Repr

def unsupportedCall : Unsupported :=
  { sourceConstructor := .Call
    reason := "Call requires a proved callee correspondence and call-lowering rule" }

def unsupportedDynCom : Unsupported :=
  { sourceConstructor := .DynCom
    reason := "DynCom requires state-dependent command conversion" }

/--
The pure structural conversion corresponding to upstream `simpl_conv'`.
Its indexed input excludes unsupported source shapes before conversion begins.
-/
def simplConv (checkTermination : Bool)
    (env : Simpl.Body State Proc Fault) {source : Simpl.Com State Proc Fault}
    (supported : Supported source) : Certificate checkTermination env source :=
  match supported with
  | .skip =>
      { target := .skip
        corres := L1.L1Corres_skip checkTermination env }
  | .seq leftSupported rightSupported =>
      let leftCertificate := simplConv checkTermination env leftSupported
      let rightCertificate := simplConv checkTermination env rightSupported
      { target := .seq leftCertificate.target rightCertificate.target
        corres := L1.L1Corres_seq leftCertificate.corres rightCertificate.corres }
  | .basic transform =>
      { target := .modify transform
        corres := L1.L1Corres_modify checkTermination env transform }
  | .cond test thenSupported elseSupported =>
      let thenCertificate := simplConv checkTermination env thenSupported
      let elseCertificate := simplConv checkTermination env elseSupported
      { target := .condition test thenCertificate.target elseCertificate.target
        corres := L1.L1Corres_condition thenCertificate.corres elseCertificate.corres }
  | .catch bodySupported handlerSupported =>
      let bodyCertificate := simplConv checkTermination env bodySupported
      let handlerCertificate := simplConv checkTermination env handlerSupported
      { target := .catch bodyCertificate.target handlerCertificate.target
        corres := L1.L1Corres_catch bodyCertificate.corres handlerCertificate.corres }
  | .while test bodySupported =>
      let bodyCertificate := simplConv checkTermination env bodySupported
      { target := .while test bodyCertificate.target
        corres := L1.L1Corres_while bodyCertificate.corres }
  | .throw =>
      { target := .throw
        corres := L1.L1Corres_throw checkTermination env }
  | .guard fault test bodySupported =>
      let bodyCertificate := simplConv checkTermination env bodySupported
      { target := .seq (.guard test) bodyCertificate.target
        corres := L1.L1Corres_guard bodyCertificate.corres fault }
  | .spec relation =>
      { target := .spec relation
        corres := L1.L1Corres_spec checkTermination env relation }

/-- Recognize the supported input shape, retaining the first unsupported child. -/
def recognizeSupported :
    (source : Simpl.Com State Proc Fault) -> Except Unsupported (Supported source)
  | .Skip => .ok .skip
  | .Seq left right =>
      match recognizeSupported left with
      | .error unsupported => .error unsupported
      | .ok leftSupported =>
          match recognizeSupported right with
          | .error unsupported => .error unsupported
          | .ok rightSupported => .ok (.seq leftSupported rightSupported)
  | .Basic transform => .ok (.basic transform)
  | .Cond test thenCom elseCom =>
      match recognizeSupported thenCom with
      | .error unsupported => .error unsupported
      | .ok thenSupported =>
          match recognizeSupported elseCom with
          | .error unsupported => .error unsupported
          | .ok elseSupported => .ok (.cond test thenSupported elseSupported)
  | .Catch body handler =>
      match recognizeSupported body with
      | .error unsupported => .error unsupported
      | .ok bodySupported =>
          match recognizeSupported handler with
          | .error unsupported => .error unsupported
          | .ok handlerSupported => .ok (.catch bodySupported handlerSupported)
  | .While test body =>
      match recognizeSupported body with
      | .error unsupported => .error unsupported
      | .ok bodySupported => .ok (.while test bodySupported)
  | .Throw => .ok .throw
  | .Guard fault test body =>
      match recognizeSupported body with
      | .error unsupported => .error unsupported
      | .ok bodySupported => .ok (.guard fault test bodySupported)
  | .Spec relation => .ok (.spec relation)
  | .Call _ => .error unsupportedCall
  | .DynCom _ => .error unsupportedDynCom

/-- Recognize a command and run the proof-producing structural conversion. -/
def run (checkTermination : Bool) (env : Simpl.Body State Proc Fault)
    (source : Simpl.Com State Proc Fault) :
    Except Unsupported (Certificate checkTermination env source) :=
  (recognizeSupported source).map (simplConv checkTermination env)

/-!
Upstream `convert`, `define`, and top-level `translate` are later orchestration
stages and are not implemented by this local structural conversion.
-/

/-! ## Algorithm regression pins -/

theorem simplConv_skip_target (checkTermination : Bool)
    (env : Simpl.Body State Proc Fault) :
    (simplConv checkTermination env Supported.skip).target = (.skip : Target State) := by
  rfl

theorem simplConv_nested_target (checkTermination : Bool)
    (env : Simpl.Body State Proc Fault) (fault : Fault) (test : State -> Prop)
    (transform : State -> State) (relation : Simpl.StateRel State) :
    (simplConv checkTermination env
      (Supported.seq (Supported.guard fault test (Supported.basic transform))
        (Supported.catch Supported.throw (Supported.spec relation)))).target =
      .seq (.seq (.guard test) (.modify transform))
        (.catch .throw (.spec relation)) := by
  rfl

theorem recognizeSupported_nested (Proc : Type v) (fault : Fault) (test : State -> Prop)
    (transform : State -> State) (relation : Simpl.StateRel State) :
    let source : Simpl.Com State Proc Fault :=
      .Seq (.Guard fault test (.Basic transform)) (.Catch .Throw (.Spec relation))
    recognizeSupported source =
      .ok (Supported.seq (Supported.guard fault test (Supported.basic transform))
        (Supported.catch Supported.throw (Supported.spec relation))) := by
  rfl

theorem run_call_unsupported (checkTermination : Bool)
    (env : Simpl.Body State Proc Fault) (proc : Proc) :
    run checkTermination env (.Call proc) = .error unsupportedCall := by
  rfl

theorem run_dynCom_unsupported (checkTermination : Bool)
    (env : Simpl.Body State Proc Fault)
    (command : State -> Simpl.Com State Proc Fault) :
    run checkTermination env (.DynCom command) = .error unsupportedDynCom := by
  rfl

theorem recognizeSupported_first_unsupported (proc : Proc)
    (command : State -> Simpl.Com State Proc Fault) :
    recognizeSupported (Simpl.Com.Seq (.Call proc) (.DynCom command)) =
      .error unsupportedCall := by
  rfl

end Zag.Lang.AutoCorres.ML.SimplConv
