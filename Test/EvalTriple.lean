import Lib.Peano.Defs
import Meta.Eval.VC

namespace Zag.Test.EvalTriple

open Zag Zag.Lib.Peano
open scoped Std.Do

set_option linter.unusedSimpArgs false

/-- A pure Id term uses the generic monadic derivation, not the old evaluator relation. -/
theorem pureIdTerm :
    Zag.EvalTriple.IdEvaluatesTo natCtx ([] : OpCtx natCtx Id) .empty []
      (Term.nat 7) (Val.nat 7) := by
  apply Zag.EvaluatesFrom.step
    (nextState := ⟨.ret (Val.nat 7), [], []⟩)
    (I := Zag.EvalTriple.Singleton.idPre True)
  · simp [Std.Do.Triple.iff, Std.Do.wp, Zag.EvalTriple.StepPost,
      Zag.EvalTriple.At, Zag.EvalTriple.Stuck, Machine.step, Machine.evalTerm,
      Machine.evalTermImmediate, Machine.ofOption, Machine.start, Term.nat]
  exact Zag.EvaluatesFrom.done (by simp [Zag.EvalTriple.Singleton.idPost])

private def tickOp : Op natCtx (StateM Nat) :=
  Op.effectful 0 (fun _ => some NatTy) fun
  | [] => fun state => (some (Val.nat state), state + 1)
  | _ => pure none

private abbrev effectCtx : Ctx :=
  Machine.stateCtx natCtx ([("tick", tickOp)] : OpCtx natCtx (StateM Nat))

private def tickRef : Val natCtx :=
  .opRef "tick" [] [] NatTy

private def doneBody : Option (Val natCtx) → Op.Body natCtx
  | some value => .done value
  | none => .fail

private def tickStart : Machine.Config natCtx :=
  Machine.start [] (.op "tick" [])

private def tickApply : Machine.Config natCtx :=
  ⟨.apply tickRef [], [], [.opBody doneBody [] []]⟩

private def tickReturned (value : Val natCtx) : Machine.Config natCtx :=
  ⟨.ret value, [], [.opBody doneBody [] []]⟩

private def tickDone (value : Val natCtx) : Machine.Config natCtx :=
  ⟨.ret value, [], []⟩

private abbrev statePre (state : Nat) :=
  Zag.EvalTriple.Singleton.statePre state

private abbrev statePost (value : Val natCtx) (state : Nat) :=
  Zag.EvalTriple.Singleton.statePost fun result final =>
    result = value ∧ final = state

/-- One effectful surface term changes ambient state and returns the old state. -/
theorem oneStateMEffect :
    Zag.EvalTriple.State.EvaluatesTo natCtx
      ([("tick", tickOp)] : OpCtx natCtx (StateM Nat)) .empty []
      (.op "tick" []) 0 (Val.nat 0) 1 := by
  apply Zag.EvaluatesFrom.step (nextState := tickApply) (I := statePre 0)
  · simp [Std.Do.Triple.iff, Std.Do.wp, Zag.EvalTriple.StepPost,
      Zag.EvalTriple.At, Zag.EvalTriple.Stuck, tickStart, tickApply, tickRef,
       effectCtx, tickOp, Op.effectful, Op.Body.collect, Machine.step,
       Machine.evalTerm, Machine.driveSelectedOp, Machine.driveOp,
       Machine.ofOption, Machine.start, OpCtx.get?]
    funext result
    cases result <;> rfl
  apply Zag.EvaluatesFrom.step
    (nextState := tickReturned (Val.nat 0)) (I := statePre 1)
  · simp [Std.Do.Triple.iff, Std.Do.wp, Zag.EvalTriple.StepPost,
      Zag.EvalTriple.At, Zag.EvalTriple.Stuck, tickApply, tickReturned, tickRef,
       doneBody, effectCtx, tickOp, Op.effectful, Machine.step,
       Machine.applyValue, Machine.driveSelectedOp, Machine.driveOp,
       Machine.ofOption, Op.Body.collect, OpCtx.get?, OptionT.mk, OptionT.run,
      OptionT.lift, OptionT.bind, OptionT.pure, StateT.mk, StateT.run,
      StateT.bind, StateT.pure, StateT.run_pure, Id.run, Id.run_pure, Bind.bind,
      Pure.pure, monadLift, MonadLift.monadLift]
  apply Zag.EvaluatesFrom.step
    (nextState := tickDone (Val.nat 0)) (I := statePre 1)
  · simp [Std.Do.Triple.iff, Std.Do.wp, Zag.EvalTriple.StepPost,
      Zag.EvalTriple.At, Zag.EvalTriple.Stuck, tickReturned, tickDone,
       doneBody, effectCtx, Machine.step, Machine.ofOption, Machine.resumeFrame,
       Machine.driveOp]
  exact Zag.EvaluatesFrom.done (by simp [statePost])

private def secondTickBody : Option (Val natCtx) → Op.Body natCtx
  | some _ => .apply tickRef [] .done
  | none => .fail

private def secondTickFrame : Frame natCtx :=
  .opBody secondTickBody [] []

private def finalTickFrame : Frame natCtx :=
  .opBody doneBody [] []

private def sequenceStart : Machine.Config natCtx :=
  ⟨.apply tickRef [], [], [secondTickFrame]⟩

private def afterFirst (value : Val natCtx) : Machine.Config natCtx :=
  ⟨.ret value, [], [secondTickFrame]⟩

private def secondApply : Machine.Config natCtx :=
  ⟨.apply tickRef [], [], [finalTickFrame]⟩

private def afterSecond (value : Val natCtx) : Machine.Config natCtx :=
  ⟨.ret value, [], [finalTickFrame]⟩

private def sequenceDone : Machine.Config natCtx :=
  ⟨.ret (Val.nat 1), [], []⟩

private def firstPost : Val natCtx → Zag.EvalTriple.Assertion effectCtx :=
  fun value state => ULift.up (value = Val.nat 0 ∧ state = 1)

private theorem firstEffect :
    Zag.EvaluatesFrom effectCtx sequenceStart [secondTickFrame]
      (statePre 0)
      (firstPost, Std.Do.ExceptConds.false) := by
  apply Zag.EvaluatesFrom.step
    (nextState := afterFirst (Val.nat 0)) (I := statePre 1)
  · simp [Std.Do.Triple.iff, Std.Do.wp, Zag.EvalTriple.StepPost,
      Zag.EvalTriple.At, Zag.EvalTriple.Stuck, sequenceStart, afterFirst,
      secondTickFrame, tickRef, effectCtx, tickOp, Op.effectful,
       Machine.step, Machine.applyValue, Machine.driveSelectedOp,
       Machine.driveOp, Machine.ofOption, Op.Body.collect, OpCtx.get?,
      OptionT.mk, OptionT.run, OptionT.lift, OptionT.bind, OptionT.pure,
      StateT.mk, StateT.run, StateT.bind, StateT.pure, StateT.run_pure,
      Id.run, Id.run_pure, Bind.bind, Pure.pure, monadLift, MonadLift.monadLift]
  exact Zag.EvaluatesFrom.done (by simp [firstPost])

private theorem secondEffect (value : Val natCtx) (scope : Env natCtx) :
    Zag.EvaluatesFrom effectCtx
      ⟨.ret value, scope, [secondTickFrame]⟩ [] (firstPost value)
      (statePost (Val.nat 1) 2) := by
  apply Zag.EvaluatesFrom.step (nextState := secondApply) (I := statePre 1)
  · simp [Std.Do.Triple.iff, Std.Do.wp, Zag.EvalTriple.StepPost,
      Zag.EvalTriple.At, Zag.EvalTriple.Stuck, secondApply, secondTickFrame,
      finalTickFrame, secondTickBody, tickRef, effectCtx,
       Machine.step, Machine.ofOption, Machine.resumeFrame, Machine.driveOp,
      firstPost]
    intro _
    funext result
    cases result <;> rfl
  apply Zag.EvaluatesFrom.step
    (nextState := afterSecond (Val.nat 1)) (I := statePre 2)
  · simp [Std.Do.Triple.iff, Std.Do.wp, Zag.EvalTriple.StepPost,
      Zag.EvalTriple.At, Zag.EvalTriple.Stuck, secondApply, afterSecond,
      finalTickFrame, tickRef, effectCtx, tickOp, Op.effectful,
       Machine.step, Machine.applyValue, Machine.driveSelectedOp,
       Machine.driveOp, Machine.ofOption, Op.Body.collect, OpCtx.get?,
      OptionT.mk, OptionT.run, OptionT.lift, OptionT.bind, OptionT.pure,
      StateT.mk, StateT.run, StateT.bind, StateT.pure, StateT.run_pure,
      Id.run, Id.run_pure, Bind.bind, Pure.pure, monadLift, MonadLift.monadLift]
  apply Zag.EvaluatesFrom.step (nextState := sequenceDone) (I := statePre 2)
  · simp [Std.Do.Triple.iff, Std.Do.wp, Zag.EvalTriple.StepPost,
      Zag.EvalTriple.At, Zag.EvalTriple.Stuck, afterSecond, sequenceDone,
       finalTickFrame, doneBody, effectCtx, Machine.step, Machine.ofOption,
       Machine.resumeFrame, Machine.driveOp]
  exact Zag.EvaluatesFrom.done (by simp [statePost])

/-- The two effects occur in order: they return `0`, then `1`, and leave state `2`. -/
theorem sequentialEffectsInOrder :
    Zag.EvaluatesFrom effectCtx sequenceStart [] (statePre 0)
      (statePost (Val.nat 1) 2) :=
  Zag.EvaluatesFrom.bind firstEffect secondEffect

/-- The public bind rule is total-correctness composition of finite derivation trees. -/
theorem totalCorrectnessComposition :
    Zag.EvaluatesFrom effectCtx sequenceStart [] (statePre 0)
      (statePost (Val.nat 1) 2) := by
  exact Zag.EvaluatesFrom.bind firstEffect secondEffect

/-! The same judgments through the generic VC walker. -/

private def pureIdentityOp : Op natCtx (StateM Nat) :=
  Op.fixed 1 (fun _ => some NatTy)
    (Op.Body.collect (fun
      | [value] => .done value
      | _ => .fail) 1 [])

/-- Pure operand collection is stepped symbolically even in an effectful ambient monad. -/
theorem genericPureCollectedOperator :
    Zag.EvalTriple.State.EvaluatesTo natCtx
      ([("identity", pureIdentityOp)] : OpCtx natCtx (StateM Nat)) .empty []
      (.op "identity" [Term.nat 7]) 3 (Val.nat 7) 3 := by
  zvcgen [pureIdentityOp, Op.fixed, Op.Body.collect, OpCtx.get?,
    Op.Arg.ofTerms, Term.nat]

private def collectedEffectOp : Op natCtx (StateM Nat) :=
  Op.effectful 1 (fun _ => some NatTy) fun values state =>
    (values.head?, state + 1)

/-- Operand collection resumes to the effectful application without sampling the action. -/
theorem genericCollectedEffectOperator :
    Zag.EvalTriple.State.EvaluatesTo natCtx
      ([("collectedEffect", collectedEffectOp)] : OpCtx natCtx (StateM Nat)) .empty []
      (.op "collectedEffect" [Term.nat 7]) 3 (Val.nat 7) 4 := by
  zvcgen [collectedEffectOp, Op.effectful, Op.Body.collect, OpCtx.get?,
    Op.Arg.ofTerms, Term.nat]

example :
    Zag.EvalTriple.IdEvaluatesTo natCtx ([] : OpCtx natCtx Id) .empty []
      (Term.nat 7) (Val.nat 7) := by
  zvcgen

/-- The generic walker follows an effect result through its `opBody` continuation. -/
theorem genericEffectResultContinuation :
    Zag.EvaluatesFrom effectCtx tickApply [] (statePre 0)
      (statePost (Val.nat 0) 1) := by
  zvcgen [effectCtx, tickOp, Op.effectful, doneBody, statePost]

/-- Pure continuation steps preserve the ambient assertion inferred after an effect. -/
theorem genericPureContinuation (value : Val natCtx) :
    Zag.EvaluatesFrom effectCtx
      ⟨.ret value, [], [.opBody doneBody [] []]⟩ [] (firstPost value)
      (statePost (Val.nat 0) 1) := by
  zvcgen [doneBody, firstPost, statePost]

/-- The generic walker verifies the first effect and its value-dependent continuation. -/
private theorem genericFirstEffect :
    Zag.EvaluatesFrom effectCtx sequenceStart [secondTickFrame]
      (statePre 0) (firstPost, Std.Do.ExceptConds.false) := by
  zvcgen [effectCtx, tickOp, Op.effectful, sequenceStart, afterFirst,
    secondTickFrame, tickRef, firstPost]

/-- The generic walker verifies the second effect from the first effect's postcondition. -/
private theorem genericSecondEffect (value : Val natCtx) (scope : Env natCtx) :
    Zag.EvaluatesFrom effectCtx
      ⟨.ret value, scope, [secondTickFrame]⟩ [] (firstPost value)
      (statePost (Val.nat 1) 2) := by
  zvcgen [effectCtx, tickOp, Op.effectful, secondTickFrame, finalTickFrame,
    secondTickBody, doneBody, tickRef, firstPost, statePost]

/-- Two walker-generated effect segments compose in order without a fuel-bound adaptation. -/
theorem genericSequentialEffects :
    Zag.EvaluatesFrom effectCtx sequenceStart [] (statePre 0)
      (statePost (Val.nat 1) 2) :=
  Zag.EvaluatesFrom.bind genericFirstEffect genericSecondEffect

private opaque hiddenAction : StateM Nat (Option (Val natCtx)) :=
  fun state => (some (Val.nat state), state + 1)

private def hiddenOp : Op natCtx (StateM Nat) :=
  Op.effectful 0 (fun _ => some NatTy) fun
  | [] => hiddenAction
  | _ => pure none

private abbrev hiddenCtx : Ctx :=
  Machine.stateCtx natCtx ([("hidden", hiddenOp)] : OpCtx natCtx (StateM Nat))

private def hiddenRef : Val natCtx :=
  .opRef "hidden" [] [] NatTy

/-- `zvcgen?` leaves an opaque ambient action's public triple visible. -/
theorem genericMissingActionSpecVisible
    (hspec : Std.Do.Triple hiddenAction (statePre 0)
      (Zag.EvalTriple.ActionPost hiddenCtx
        (fun value => (statePost (Val.nat 0) 1).1 value)
        Std.Do.ExceptConds.false)) :
    Zag.EvaluatesFrom hiddenCtx
      ⟨.apply hiddenRef [], [], []⟩ [] (statePre 0)
      (statePost (Val.nat 0) 1) := by
  fail_if_success
    (clear hspec
     zvcgen? [hiddenCtx, hiddenOp, Op.effectful, hiddenRef, statePost] <;> done)
  zvcgen? [hiddenCtx, hiddenOp, Op.effectful, hiddenRef, statePost]

private abbrev identityBlocks : BlockCtx.Raw natCtx :=
  blocks% [
    identity(n : Nat) : Nat {
      ret n
    }
  ]

private def identityBlock : Block natCtx := identityBlocks[0].2

private abbrev identityCtx : Ctx :=
  Zag.EvalTriple.idCtx natCtx ([] : OpCtx natCtx Id)
    ⟨identityBlocks, by
      simp [BlockCtx.Valid, identityBlocks, Block.callNames, Term.callNames]⟩

/-- A generic application specification is proved directly for every caller stack. -/
theorem genericIdentityApply (n : Nat) :
    Zag.EvaluatesApply identityCtx
      (.blockRef "identity" [NatTy] NatTy) [Val.nat n]
      (Zag.EvalTriple.Singleton.idPre True)
      (Zag.EvalTriple.Singleton.idPost (· = Val.nat n)) := by
  zvcgen [identityCtx, identityBlocks, identityBlock, BlockCtx.get?,
    Machine.enterBlock]

/-- Generic value-call specifications use the same block-entry semantics. -/
theorem genericIdentityCallValues (n : Nat) :
    Zag.EvaluatesCallValues identityCtx "identity" [Val.nat n]
      (Zag.EvalTriple.Singleton.idPre True)
      (Zag.EvalTriple.Singleton.idPost (· = Val.nat n)) := by
  apply Zag.EvaluatesCallValues.of_body (block := identityBlock)
  · rfl
  · intro env base
    refine ⟨⟨.eval (.var "n"), [("n", Val.nat n)], .call "identity" env :: base⟩, ?_, ?_⟩
    · rfl
    · zvcgen [identityCtx, identityBlocks, identityBlock, BlockCtx.get?,
        Machine.enterBlock]

end Zag.Test.EvalTriple
