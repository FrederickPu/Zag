import Lang.AutoCorres.TypeStrengthen
import Lang.AutoCorres.ML.monad_types

/-!
# Pure type-strengthening kernel

Corresponds only to [`tools/autocorres/type_strengthen.ML`](https://github.com/seL4/l4v/blob/bc2599a59c43e673dca021b10b9841e9b8da4430/tools/autocorres/type_strengthen.ML).

The upstream proof search is represented by a typed source tree, recursively
indexed support evidence, and total conversion over that evidence. Bind, loop,
and handler bodies use an explicit environment, so there is no opaque program
leaf and candidate construction checks every converted closure.

The current kernel does not support a top-level throw, polishing, external
callee rewrites, or recursive function groups. In particular, it does not manufacture an SCC
translation: transferring recursive definitions also needs the upstream
monotonicity proof, which is not implied by a successful structural rewrite.
-/

namespace Zag.Lang.AutoCorres.ML.TypeStrengthen

open Zag.Lang.AutoCorres
open MonadTypes

namespace TS

export Zag.Lang.AutoCorres.TypeStrengthen
  (embed TS_return_L2_gets TS_return_L2_seq TS_return_L2_condition
   TS_gets_L2_gets TS_gets_L2_seq readerCondition TS_gets_L2_condition
   gets_theE_L2_gets gets_theE_L2_seq gets_theE_L2_condition
   gets_theE_L2_guard gets_theE_L2_while gets_theE_L2_fail
   optionRecguard gets_theE_L2_recguard liftE_L2_gets liftE_L2_seq
   nondetCondition liftE_L2_condition liftE_L2_modify liftE_L2_guard
   liftE_L2_while liftE_L2_catch nondetCatch liftE_L2_catch'
   liftE_L2_spec liftE_L2_unknown liftE_L2_fail liftE_L2_recguard
   L2_call_embed_exact)

end TS

namespace Source

export Zag.Lang.AutoCorres.TypeStrengthen.Kernel.Source (Term Closed Syntax)

namespace Term

export Zag.Lang.AutoCorres.TypeStrengthen.Kernel.Source.Term (denote kind)

end Term

end Source

namespace Target

export Zag.Lang.AutoCorres.TypeStrengthen.Kernel.Target (Syntax)

namespace Syntax

export Zag.Lang.AutoCorres.TypeStrengthen.Kernel.Target.Syntax (denote)

end Syntax

end Target

export Zag.Lang.AutoCorres.TypeStrengthen.Kernel (Supported)

/-- Internal raw rewrite used compositionally below `L2.call`. -/
structure RawCertificate {Argument State Exception Result : Type} (carrier : Carrier)
    (source : Source.Term Argument State Exception Result) (argument : Argument) where
  target : Target.Syntax carrier State Result
  equality : source.denote argument =
    TS.embed (Exception := Exception) carrier target.denote

export Zag.Lang.AutoCorres.TypeStrengthen.Kernel (ClosedCertificate Certificate)

/--
Total ordinary conversion over support evidence. The target is computed from
syntax and evidence; denotation occurs only in the erased equality field.
-/
def strengthenAt {Argument State Exception Result : Type} {carrier : Carrier}
    {source : Source.Term Argument State Exception Result}
    (supported : Supported carrier source) (argument : Argument) :
    RawCertificate carrier source argument :=
  match source, supported with
  | .pure value names, .pureValue =>
      { target := .atom (value argument)
        equality := by
          simpa [Source.Term.denote, Target.Syntax.denote] using
            (TS.TS_return_L2_gets (State := State) (Exception := Exception)
              (value argument) names) }
  | .seq _ nextSource, .pureSeq firstSupported nextSupported =>
      let first := strengthenAt firstSupported argument
      let next := fun value => strengthenAt nextSupported (argument, value)
      { target := .seq first.target (fun value => (next value).target)
        equality := by
          rw [Source.Term.denote, first.equality]
          have nextEquality :
              (fun value => Source.Term.denote (argument, value) nextSource) =
                (fun value => TS.embed .pure (next value).target.denote) := by
            funext value
            exact (next value).equality
          rw [nextEquality]
          exact TS.TS_return_L2_seq first.target.denote
            (fun value => (next value).target.denote) }
  | .conditionPure test _ _, .pureCondition thenSupported elseSupported =>
      let thenResult := strengthenAt thenSupported argument
      let elseResult := strengthenAt elseSupported argument
      { target := .pureCondition (test argument) thenResult.target elseResult.target
        equality := by
          rw [Source.Term.denote, thenResult.equality, elseResult.equality]
          exact TS.TS_return_L2_condition (test argument)
            thenResult.target.denote elseResult.target.denote }

  | .pure value names, .getsValue =>
      { target := .atom (fun _ => value argument)
        equality := by
          simpa [Source.Term.denote] using
            (TS.TS_gets_L2_gets (Exception := Exception)
              (fun _ : State => value argument) names) }
  | .gets read names, .getsRead =>
      { target := .atom (read argument)
        equality := by
          simpa [Source.Term.denote] using
            (TS.TS_gets_L2_gets (Exception := Exception) (read argument) names) }
  | .seq _ nextSource, .getsSeq firstSupported nextSupported =>
      let first := strengthenAt firstSupported argument
      let next := fun value => strengthenAt nextSupported (argument, value)
      { target := .seq first.target (fun value => (next value).target)
        equality := by
          rw [Source.Term.denote, first.equality]
          have nextEquality :
              (fun value => Source.Term.denote (argument, value) nextSource) =
                (fun value => TS.embed .gets (next value).target.denote) := by
            funext value
            exact (next value).equality
          rw [nextEquality]
          exact TS.TS_gets_L2_seq first.target.denote
            (fun value => (next value).target.denote) }
  | .conditionPure test _ _, .getsPureCondition thenSupported elseSupported =>
      let thenResult := strengthenAt thenSupported argument
      let elseResult := strengthenAt elseSupported argument
      { target := .getsCondition (fun _ => test argument)
          thenResult.target elseResult.target
        equality := by
          rw [Source.Term.denote, thenResult.equality, elseResult.equality]
          exact TS.TS_gets_L2_condition (fun _ => test argument)
            thenResult.target.denote elseResult.target.denote }
  | .condition test _ _, .getsCondition thenSupported elseSupported =>
      let thenResult := strengthenAt thenSupported argument
      let elseResult := strengthenAt elseSupported argument
      { target := .getsCondition (test argument)
          thenResult.target elseResult.target
        equality := by
          rw [Source.Term.denote, thenResult.equality, elseResult.equality]
          exact TS.TS_gets_L2_condition (test argument)
            thenResult.target.denote elseResult.target.denote }

  | .pure value names, .optionValue =>
      { target := .atom (ogets fun _ => value argument)
        equality := by
          simpa [Source.Term.denote] using
            (TS.gets_theE_L2_gets (Exception := Exception)
              (fun _ : State => value argument) names) }
  | .gets read names, .optionRead =>
      { target := .atom (ogets (read argument))
        equality := by
          simpa [Source.Term.denote] using
            (TS.gets_theE_L2_gets (Exception := Exception) (read argument) names) }
  | .seq _ nextSource, .optionSeq firstSupported nextSupported =>
      let first := strengthenAt firstSupported argument
      let next := fun value => strengthenAt nextSupported (argument, value)
      { target := .seq first.target (fun value => (next value).target)
        equality := by
          rw [Source.Term.denote, first.equality]
          have nextEquality :
              (fun value => Source.Term.denote (argument, value) nextSource) =
                (fun value => TS.embed .option (next value).target.denote) := by
            funext value
            exact (next value).equality
          rw [nextEquality]
          exact TS.gets_theE_L2_seq first.target.denote
            (fun value => (next value).target.denote) }
  | .conditionPure test _ _, .optionPureCondition thenSupported elseSupported =>
      let thenResult := strengthenAt thenSupported argument
      let elseResult := strengthenAt elseSupported argument
      { target := .optionCondition (fun _ => test argument)
          thenResult.target elseResult.target
        equality := by
          rw [Source.Term.denote, thenResult.equality, elseResult.equality]
          exact TS.gets_theE_L2_condition (fun _ => test argument)
            thenResult.target.denote elseResult.target.denote }
  | .condition test _ _, .optionCondition thenSupported elseSupported =>
      let thenResult := strengthenAt thenSupported argument
      let elseResult := strengthenAt elseSupported argument
      { target := .optionCondition (test argument)
          thenResult.target elseResult.target
        equality := by
          rw [Source.Term.denote, thenResult.equality, elseResult.equality]
          exact TS.gets_theE_L2_condition (test argument)
            thenResult.target.denote elseResult.target.denote }
  | .guard test, .optionGuard =>
      { target := .atom (oguard (test argument))
        equality := by
          simpa [Source.Term.denote] using
            (TS.gets_theE_L2_guard (Exception := Exception) (test argument)) }
  | .while test body initial names, .optionWhile bodySupported =>
      let bodyResult := fun value => strengthenAt bodySupported (argument, value)
      { target := .optionWhile (test argument)
          (fun value => (bodyResult value).target) (initial argument)
        equality := by
          rw [Source.Term.denote]
          have bodyEquality :
              (fun value => Source.Term.denote (argument, value) body) =
                (fun value => TS.embed .option (bodyResult value).target.denote) := by
            funext value
            exact (bodyResult value).equality
          rw [bodyEquality]
          exact TS.gets_theE_L2_while (test argument)
            (fun value => (bodyResult value).target.denote) (initial argument) names }
  | .fail, .optionFail =>
      { target := .atom ofail
        equality := by
          simpa [Source.Term.denote] using
            (TS.gets_theE_L2_fail (State := State) (Exception := Exception)
              (Result := Result)) }
  | .recguard sourceMeasure _, .optionRecguard bodySupported =>
      let bodyResult := strengthenAt bodySupported argument
      { target := .optionRecguard (sourceMeasure argument) bodyResult.target
        equality := by
          rw [Source.Term.denote, bodyResult.equality]
          exact TS.gets_theE_L2_recguard (sourceMeasure argument)
            bodyResult.target.denote }

  | .pure value names, .nondetValue =>
      { target := .atom (AutoCorres.gets fun _ => value argument)
        equality := by
          simpa [Source.Term.denote] using
            (TS.liftE_L2_gets (Exception := Exception)
              (fun _ : State => value argument) names) }
  | .gets read names, .nondetRead =>
      { target := .atom (AutoCorres.gets (read argument))
        equality := by
          simpa [Source.Term.denote] using
            (TS.liftE_L2_gets (Exception := Exception) (read argument) names) }
  | .seq _ nextSource, .nondetSeq firstSupported nextSupported =>
      let first := strengthenAt firstSupported argument
      let next := fun value => strengthenAt nextSupported (argument, value)
      { target := .seq first.target (fun value => (next value).target)
        equality := by
          rw [Source.Term.denote, first.equality]
          have nextEquality :
              (fun value => Source.Term.denote (argument, value) nextSource) =
                (fun value => TS.embed .nondet (next value).target.denote) := by
            funext value
            exact (next value).equality
          rw [nextEquality]
          exact TS.liftE_L2_seq first.target.denote
            (fun value => (next value).target.denote) }
  | .conditionPure test _ _, .nondetPureCondition thenSupported elseSupported =>
      let thenResult := strengthenAt thenSupported argument
      let elseResult := strengthenAt elseSupported argument
      { target := .nondetCondition (fun _ => test argument)
          thenResult.target elseResult.target
        equality := by
          rw [Source.Term.denote, thenResult.equality, elseResult.equality]
          exact TS.liftE_L2_condition (fun _ => test argument)
            thenResult.target.denote elseResult.target.denote }
  | .condition test _ _, .nondetCondition thenSupported elseSupported =>
      let thenResult := strengthenAt thenSupported argument
      let elseResult := strengthenAt elseSupported argument
      { target := .nondetCondition (test argument)
          thenResult.target elseResult.target
        equality := by
          rw [Source.Term.denote, thenResult.equality, elseResult.equality]
          exact TS.liftE_L2_condition (test argument)
            thenResult.target.denote elseResult.target.denote }
  | .modify update, .nondetModify =>
      { target := .atom (AutoCorres.modify (update argument))
        equality := by
          simpa [Source.Term.denote] using
            (TS.liftE_L2_modify (Exception := Exception) (update argument)) }
  | .guard test, .nondetGuard =>
      { target := .atom (AutoCorres.guard fun state => test argument state = true)
        equality := by
          simpa [Source.Term.denote] using
            (TS.liftE_L2_guard (Exception := Exception)
              (fun state => test argument state = true)) }
  | .exactGuard test, .nondetExactGuard =>
      { target := .atom (AutoCorres.guard (test argument))
        equality := by
          simpa [Source.Term.denote] using
            (TS.liftE_L2_guard (Exception := Exception) (test argument)) }
  | .while test body initial names, .nondetWhile bodySupported =>
      let bodyResult := fun value => strengthenAt bodySupported (argument, value)
      { target := .nondetWhile (test argument)
          (fun value => (bodyResult value).target) (initial argument)
        equality := by
          rw [Source.Term.denote]
          have bodyEquality :
              (fun value => Source.Term.denote (argument, value) body) =
                (fun value => TS.embed .nondet (bodyResult value).target.denote) := by
            funext value
            exact (bodyResult value).equality
          rw [bodyEquality]
          exact TS.liftE_L2_while
            (fun value state => test argument value state = true)
            (fun value => (bodyResult value).target.denote) (initial argument) names }
  | .catchBody _ handler, .nondetCatchBody bodySupported =>
      let bodyResult := strengthenAt bodySupported argument
      { target := bodyResult.target
        equality := by
          rw [Source.Term.denote, bodyResult.equality]
          exact TS.liftE_L2_catch bodyResult.target.denote
            (fun exception => handler.denote (argument, exception)) }
  | .catchHandlers body handler, .nondetCatchHandlers handlerSupported =>
      let handlerResult := fun exception =>
        strengthenAt handlerSupported (argument, exception)
      { target := .catchHandlers body argument
          (fun exception => (handlerResult exception).target)
        equality := by
          rw [Source.Term.denote]
          have handlerEquality :
              (fun exception => Source.Term.denote (argument, exception) handler) =
                (fun exception => TS.embed .nondet
                  (handlerResult exception).target.denote) := by
            funext exception
            exact (handlerResult exception).equality
          rw [handlerEquality]
          simpa only [Zag.Lang.AutoCorres.TypeStrengthen.embed,
            Zag.Lang.AutoCorres.TypeStrengthen.denote,
            Zag.Lang.AutoCorres.TypeStrengthen.nondetCatch,
            Zag.Lang.AutoCorres.TypeStrengthen.Kernel.Target.Syntax.denote,
            Zag.Lang.AutoCorres.TypeStrengthen.Kernel.nondetCatch] using
            TS.liftE_L2_catch' (body.denote argument)
              (fun exception => (handlerResult exception).target.denote) }
  | .spec relation, .nondetSpec =>
      { target := .atom (AutoCorres.bind (AutoCorres.spec (relation argument)) fun _ =>
          AutoCorres.select fun _ => True)
        equality := by
          simpa [Source.Term.denote] using
            (TS.liftE_L2_spec (Exception := Exception) (Result := Result)
              (relation argument)) }
  | .unknown names, .nondetUnknown =>
      { target := .atom (AutoCorres.select fun _ => True)
        equality := by
          simpa [Source.Term.denote] using
            (TS.liftE_L2_unknown (State := State) (Exception := Exception)
              (Result := Result) names) }
  | .fail, .nondetFail =>
      { target := .atom AutoCorres.fail
        equality := by
          simpa [Source.Term.denote] using
            (TS.liftE_L2_fail (State := State) (Exception := Exception)
              (Result := Result)) }
  | .recguard sourceMeasure _, .nondetRecguard bodySupported =>
      let bodyResult := strengthenAt bodySupported argument
      { target := .nondetRecguard (sourceMeasure argument) bodyResult.target
        equality := by
          rw [Source.Term.denote, bodyResult.equality]
          exact TS.liftE_L2_recguard (sourceMeasure argument)
            bodyResult.target.denote }

/-- Total strengthening of a supported closed source with any inner exception. -/
def strengthenClosed {State InnerException Result : Type} {carrier : Carrier}
    {source : Source.Closed State InnerException Result}
    (supported : Supported carrier source) : ClosedCertificate carrier source :=
  let raw := strengthenAt supported ()
  { target := raw.target
    exact := fun Exception => by
      rw [raw.equality]
      exact (TS.L2_call_embed_exact (InnerException := InnerException)
        (Exception := Exception) carrier raw.target.denote).eq }

/-- Compatibility specialization for the original `Unit` inner exception API. -/
def strengthen {State Result : Type} {carrier : Carrier}
    {source : Source.Syntax State Result}
    (supported : Supported carrier source) : Certificate carrier source :=
  strengthenClosed supported

theorem strengthenClosed_target_pin
    {State InnerException Result : Type} {carrier : Carrier}
    {source : Source.Closed State InnerException Result}
    (supported : Supported carrier source) :
    (strengthenClosed supported).target = (strengthenAt supported ()).target := by
  rfl

theorem strengthenClosed_correctness_pin
    {State InnerException Result : Type} {carrier : Carrier}
    {source : Source.Closed State InnerException Result}
    (supported : Supported carrier source) (OuterException : Type) :
    L2.call (Exception := OuterException) (source.denote ()) =
      TS.embed (Exception := OuterException) carrier
        (strengthenClosed supported).target.denote :=
  (strengthenClosed supported).exact OuterException

/--
Pointwise function certificate over the recursion measure and ordinary
arguments. This is the non-SCC precursor used by a future recursion phase.
-/
structure FunctionCertificate {Arguments State Result : Type} (carrier : Carrier)
    (source : Source.Term (Nat × Arguments) State Unit Result) where
  target : Nat -> Arguments -> Target.Syntax carrier State Result
  exact : forall measure arguments (Exception : Type),
    L2.call (Exception := Exception) (source.denote (measure, arguments)) =
      TS.embed (Exception := Exception) carrier (target measure arguments).denote

/-- Lift one uniformly reified function body pointwise in measure and arguments. -/
def strengthenFunction {Arguments State Result : Type} {carrier : Carrier}
    {source : Source.Term (Nat × Arguments) State Unit Result}
    (supported : Supported carrier source) : FunctionCertificate carrier source :=
  { target := fun measure arguments =>
      (strengthenAt supported (measure, arguments)).target
    exact := fun measure arguments Exception => by
      let raw := strengthenAt supported (measure, arguments)
      rw [raw.equality]
      exact (TS.L2_call_embed_exact (Exception := Exception) carrier raw.target.denote).eq }

/-! ## Structural candidate construction -/

/-- Explicit failure from one carrier-specific structural conversion. -/
structure Diagnostic where
  carrier : Carrier
  path : List String
  sourceConstructor : String
  reason : String

def Diagnostic.at (diagnostic : Diagnostic) (edge : String) : Diagnostic :=
  { diagnostic with path := edge :: diagnostic.path }

def unsupported (carrier : Carrier) (sourceConstructor : String) : Diagnostic :=
  { carrier
    path := []
    sourceConstructor
    reason := s!"{sourceConstructor} has no certified {carrier.name} conversion rule" }

/--
Computably construct all recursive support evidence for one carrier. Success
never follows from the source head alone when child conversions are required.
-/
def buildSupported (carrier : Carrier) {Argument State Exception Result : Type} :
    (source : Source.Term Argument State Exception Result) ->
      Except Diagnostic (Supported carrier source)
  | .pure value names => match carrier with
      | .pure => .ok .pureValue
      | .gets => .ok .getsValue
      | .option => .ok .optionValue
      | .nondet => .ok .nondetValue
  | .gets read names => match carrier with
      | .pure => .error (unsupported carrier "gets")
      | .gets => .ok .getsRead
      | .option => .ok .optionRead
      | .nondet => .ok .nondetRead
  | .seq first next =>
      match buildSupported carrier first with
      | .error diagnostic => .error (diagnostic.at "seq.first")
      | .ok firstSupported =>
          match buildSupported carrier next with
          | .error diagnostic => .error (diagnostic.at "seq.next")
          | .ok nextSupported => match carrier with
              | .pure => .ok (.pureSeq firstSupported nextSupported)
              | .gets => .ok (.getsSeq firstSupported nextSupported)
              | .option => .ok (.optionSeq firstSupported nextSupported)
              | .nondet => .ok (.nondetSeq firstSupported nextSupported)
  | .conditionPure _test thenBranch elseBranch =>
      match buildSupported carrier thenBranch with
      | .error diagnostic => .error (diagnostic.at "condition.then")
      | .ok thenSupported =>
          match buildSupported carrier elseBranch with
          | .error diagnostic => .error (diagnostic.at "condition.else")
          | .ok elseSupported => match carrier with
              | .pure => .ok (.pureCondition thenSupported elseSupported)
              | .gets => .ok (.getsPureCondition thenSupported elseSupported)
              | .option => .ok (.optionPureCondition thenSupported elseSupported)
              | .nondet => .ok (.nondetPureCondition thenSupported elseSupported)
  | .condition _test thenBranch elseBranch => match carrier with
      | .pure => .error (unsupported carrier "condition")
      | .gets =>
          match buildSupported .gets thenBranch with
          | .error diagnostic => .error (diagnostic.at "condition.then")
          | .ok thenSupported =>
              match buildSupported .gets elseBranch with
              | .error diagnostic => .error (diagnostic.at "condition.else")
              | .ok elseSupported => .ok (.getsCondition thenSupported elseSupported)
      | .option =>
          match buildSupported .option thenBranch with
          | .error diagnostic => .error (diagnostic.at "condition.then")
          | .ok thenSupported =>
              match buildSupported .option elseBranch with
              | .error diagnostic => .error (diagnostic.at "condition.else")
              | .ok elseSupported => .ok (.optionCondition thenSupported elseSupported)
      | .nondet =>
          match buildSupported .nondet thenBranch with
          | .error diagnostic => .error (diagnostic.at "condition.then")
          | .ok thenSupported =>
              match buildSupported .nondet elseBranch with
              | .error diagnostic => .error (diagnostic.at "condition.else")
              | .ok elseSupported => .ok (.nondetCondition thenSupported elseSupported)
  | .modify update => match carrier with
      | .nondet => .ok .nondetModify
      | carrier => .error (unsupported carrier "modify")
  | .guard test => match carrier with
      | .option => .ok .optionGuard
      | .nondet => .ok .nondetGuard
      | carrier => .error (unsupported carrier "guard")
  | .exactGuard test => match carrier with
      | .nondet => .ok .nondetExactGuard
      | carrier => .error (unsupported carrier "exactGuard")
  | .while _test body initial names => match carrier with
      | .option =>
          match buildSupported .option body with
          | .error diagnostic => .error (diagnostic.at "while.body")
          | .ok bodySupported => .ok (.optionWhile bodySupported)
      | .nondet =>
          match buildSupported .nondet body with
          | .error diagnostic => .error (diagnostic.at "while.body")
          | .ok bodySupported => .ok (.nondetWhile bodySupported)
      | carrier => .error (unsupported carrier "while")
  | .catchBody body handler => match carrier with
      | .nondet =>
          match buildSupported .nondet body with
          | .error diagnostic => .error (diagnostic.at "catch.body")
          | .ok bodySupported => .ok (.nondetCatchBody bodySupported)
      | carrier => .error (unsupported carrier "catchBody")
  | .catchHandlers body handler => match carrier with
      | .nondet =>
          match buildSupported .nondet handler with
          | .error diagnostic => .error (diagnostic.at "catch.handler")
          | .ok handlerSupported => .ok (.nondetCatchHandlers handlerSupported)
      | carrier => .error (unsupported carrier "catchHandlers")
  | .spec relation => match carrier with
      | .nondet => .ok .nondetSpec
      | carrier => .error (unsupported carrier "spec")
  | .unknown names => match carrier with
      | .nondet => .ok .nondetUnknown
      | carrier => .error (unsupported carrier "unknown")
  | .fail => match carrier with
      | .option => .ok .optionFail
      | .nondet => .ok .nondetFail
      | carrier => .error (unsupported carrier "fail")
  | .recguard measure body => match carrier with
      | .option =>
          match buildSupported .option body with
          | .error diagnostic => .error (diagnostic.at "recguard.body")
          | .ok bodySupported => .ok (.optionRecguard bodySupported)
      | .nondet =>
          match buildSupported .nondet body with
          | .error diagnostic => .error (diagnostic.at "recguard.body")
          | .ok bodySupported => .ok (.nondetRecguard bodySupported)
      | carrier => .error (unsupported carrier "recguard")
  | .throw _ _ => .error (unsupported carrier "throw")

/-- Build a certified candidate or retain its exact structural diagnostic. -/
def candidate {State Result : Type} (carrier : Carrier)
    (source : Source.Syntax State Result) :
    Except Diagnostic (MonadTypes.Candidate fun carrier => Certificate carrier source) :=
  match buildSupported carrier source with
  | .error diagnostic => .error diagnostic
  | .ok supported => .ok { carrier, certificate := strengthen supported }

structure Attempts {State Result : Type} (source : Source.Syntax State Result) where
  candidates : List (MonadTypes.Candidate fun carrier => Certificate carrier source)
  diagnostics : List Diagnostic

private def collectAttempts {State Result : Type} (source : Source.Syntax State Result) :
    List Carrier -> Attempts source
  | [] => { candidates := [], diagnostics := [] }
  | carrier :: rest =>
      let tail := collectAttempts source rest
      match candidate carrier source with
      | .ok successful => { tail with candidates := successful :: tail.candidates }
      | .error diagnostic => { tail with diagnostics := diagnostic :: tail.diagnostics }

/-- Try every carrier in the exact upstream precedence domain. -/
def attempts {State Result : Type} (source : Source.Syntax State Result) : Attempts source :=
  collectAttempts source [.pure, .gets, .option, .nondet]

structure SelectionError where
  diagnostics : List Diagnostic

/-- Existential carrier and exact certificate selected by `100, 80, 60, 0`. -/
def select {State Result : Type} (source : Source.Syntax State Result) : Except SelectionError
    (MonadTypes.Selected fun carrier => Certificate carrier source) :=
  let result := attempts source
  match MonadTypes.select result.candidates with
  | some selected => .ok selected
  | none => .error { diagnostics := result.diagnostics }

/-- Forced carrier selection fails unless that carrier's full certificate builds. -/
def force {State Result : Type} (carrier : Carrier) (source : Source.Syntax State Result) :
    Except Diagnostic (Certificate carrier source) :=
  match buildSupported carrier source with
  | .error diagnostic => .error diagnostic
  | .ok supported => .ok (strengthen supported)

/-! ## Computational reduction pins -/

private def purePin : Source.Syntax Nat Nat := .pure (fun _ => 7) []

private def getsPin : Source.Syntax Nat Nat :=
  .gets (fun _ state => state + 1) []

private def guardPin : Source.Syntax Nat Unit :=
  .guard (fun _ state => decide (state > 0))

private def modifyPin : Source.Syntax Nat Unit :=
  .modify (fun _ state => state + 1)

theorem pure_chosen_over_gets_pin :
    (select purePin).map (fun selected => selected.carrier) = .ok .pure := by
  rfl

theorem gets_chosen_over_option_pin :
    (select getsPin).map (fun selected => selected.carrier) = .ok .gets := by
  rfl

theorem guard_selects_option_pin :
    (select guardPin).map (fun selected => selected.carrier) = .ok .option := by
  rfl

theorem modify_selects_nondet_pin :
    (select modifyPin).map (fun selected => selected.carrier) = .ok .nondet := by
  rfl

theorem forced_incompatible_choice_errors_pin :
    (match force .pure modifyPin with
      | .error _ => true
      | .ok _ => false) = true := by
  rfl

end Zag.Lang.AutoCorres.ML.TypeStrengthen
