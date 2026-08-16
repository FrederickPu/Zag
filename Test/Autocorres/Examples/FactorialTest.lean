import Test.Autocorres.Examples.Common

namespace Zag.Test.Autocorres.Examples

open Zag Zag.Lib.PeanoHeap

abbrev factorialBlocks : BlockCtx.Raw heapCtx :=
  blocks% [
    factorial(n : Nat) : Nat {
      done := primEq n nat(0);
      ret if done { nat(1) } else { op "mul"[n, call factorial [op "sub"[n, nat(1)]]] }
    },
    callFactorial() : Nat {
      ret call factorial [nat(42)]
    }
  ]

theorem factorialBlocksValid : BlockCtx.Valid factorialBlocks := by
  valid_blocks [factorialBlocks]

abbrev factorialCtx : Ctx := mkCtx factorialBlocks factorialBlocksValid

theorem factorialCtx_wellTyped : Ctx.WellTyped factorialCtx := by typecheck_ctx

def factorialSpec : Nat → Nat
| 0 => 1
| n + 1 => (n + 1) * factorialSpec n

theorem factorial_eval (n : Nat) :
    EvaluatesCall factorialCtx "factorial" ([Val.nat n] : List (Val heapCtx))
      (Val.nat (factorialSpec n)) := by
  induction n with
  | zero => evaluates_call 300 [heapOpCtx, factorialBlocks, factorialSpec]
  | succ n ih =>
      refine EvaluatesCall.of_evaluatesFrom ?_
      intro env base
      let doneEnv : Env heapCtx := [("n", Val.nat (n + 1)), ("done", Val.bool false)]
      let mulResume : Option (Val heapCtx) → Op.Body heapCtx :=
        match (Op.natBinary (primCtx := heapCtx) Nat.mul).body with
        | .next _ resume =>
            match resume (some (Val.nat (n + 1))) with
            | .next _ resumeRhs => resumeRhs
            | _ => fun _ => Op.Body.fail
        | _ => fun _ => Op.Body.fail
      set_option linter.unusedSimpArgs false in
        simp +arith [EvalState.enterInstrs, EvalState.enterBlock, BlockCtx.get?,
          BlockCtx.Raw.get?, Scope.get?, Block.entryEnv, Term.nat, Term.bool, Term.ite,
          heapOpCtx, factorialBlocks]
      refine EvaluatesFrom.trans_stepN (fuel₀ := 12)
        (mid := {
          control := .eval (.call "factorial"
            [Term.op "sub" [Term.var "n", Term.nat 1]]),
          env := doneEnv,
          stack :=
            Frame.opBody mulResume [] doneEnv ::
            Frame.opBody (fun elseVal =>
              match elseVal with
              | some value => Op.Body.done value
              | none => Op.Body.fail) [] doneEnv ::
            Frame.call "factorial" env :: base }) ?_ ?_
      · set_option linter.unusedSimpArgs false in
          simp +arith [doneEnv, mulResume, EvalState.stepN, EvalState.step,
            EvalState.driveOp, EvalState.enterInstrs, EvalState.enterBlock, OpCtx.get?,
            BlockCtx.get?, BlockCtx.Raw.get?, Scope.get?, Block.entryEnv, Peano.opCtx,
            Op.natBinary, Op.natUnary, Op.compare, Op.eq, Op.ite, Op.ofVals,
            Op.Body.eager, Term.nat, Term.bool, Term.ite, heapOpCtx, factorialBlocks] <;>
            (first | rfl | funext z <;> cases z <;> rfl)
      refine EvaluatesFrom.call_then (block := factorialBlocks[0].2) (hcall := ih) ?_ ?_ ?_
      · set_option linter.unusedSimpArgs false in
          simp +arith [EvalState.step, EvalState.driveOp, EvalState.enterInstrs,
            EvalState.enterBlock, OpCtx.get?, BlockCtx.get?, BlockCtx.Raw.get?, Scope.get?,
            Block.entryEnv, Peano.opCtx, Op.natBinary, Op.natUnary, Op.compare,
            Op.eq, Op.ite, Op.ofVals, Op.Body.eager, Term.nat, Term.bool, Term.ite,
            heapOpCtx, factorialBlocks] <;> rfl
      · constructor
        · evaluates 20 [heapOpCtx, doneEnv]
        · exact EvaluatesToAll.nil
      · intro scope
        refine EvaluatesFrom.trans_stepN (fuel₀ := 3)
          (mid := {
            control := .ret (Val.nat (factorialSpec (n + 1))),
            env := env,
            stack := base }) ?_ ?_
        · set_option linter.unusedSimpArgs false in
            simp +arith [doneEnv, mulResume, EvalState.stepN, EvalState.step,
              EvalState.driveOp, EvalState.enterInstrs, EvalState.enterBlock, OpCtx.get?,
              BlockCtx.get?, BlockCtx.Raw.get?, Scope.get?, Block.entryEnv, Peano.opCtx,
              Op.natBinary, Op.natUnary, Op.compare, Op.eq, Op.ite, Op.ofVals,
              Op.Body.eager, Term.nat, Term.bool, Term.ite, heapOpCtx, factorialBlocks,
              factorialSpec] <;> rfl
        exact EvaluatesFrom.done

theorem callFactorial_eval :
    EvaluatesCall factorialCtx "callFactorial" [] (Val.nat (factorialSpec 42)) := by
  refine EvaluatesCall.of_evaluatesFrom ?_
  intro env base
  set_option linter.unusedSimpArgs false in
    simp +arith [EvalState.enterInstrs, EvalState.enterBlock, BlockCtx.get?,
      BlockCtx.Raw.get?, Scope.get?, Block.entryEnv, Term.nat, Term.bool, Term.ite,
      heapOpCtx, factorialBlocks]
  refine EvaluatesFrom.call_then (block := factorialBlocks[0].2)
    (hcall := factorial_eval 42) ?_ ?_ ?_
  · set_option linter.unusedSimpArgs false in
      simp +arith [EvalState.step, EvalState.driveOp, EvalState.enterInstrs,
        EvalState.enterBlock, OpCtx.get?, BlockCtx.get?, BlockCtx.Raw.get?, Scope.get?,
        Block.entryEnv, Peano.opCtx, Op.natBinary, Op.natUnary, Op.compare,
        Op.eq, Op.ite, Op.ofVals, Op.Body.eager, Term.nat, Term.bool, Term.ite,
        heapOpCtx, factorialBlocks] <;> rfl
  · evaluates_to_all 300 [heapOpCtx, factorialBlocks]
  · intro scope
    evaluates_from 300 [heapOpCtx, factorialBlocks]

/-- The same statement at the surface: calling `factorial` on a literal. -/
theorem factorial_eval_call (n : Nat) :
    EvaluatesTo factorialCtx [] (.call "factorial" [Term.nat n])
      (Val.nat (factorialSpec n)) := by
  obtain ⟨fuel, scope, hsteps⟩ :
      EvaluatesFrom factorialCtx (EvalState.start [] (.call "factorial" [Term.nat n]))
        (Val.nat (factorialSpec n)) [] := by
    unfold EvalState.start
    refine EvaluatesFrom.call_then (block := factorialBlocks[0].2)
      (hcall := factorial_eval n) ?_ ?_ ?_
    · set_option linter.unusedSimpArgs false in
        simp +arith [EvalState.step, EvalState.driveOp, EvalState.enterInstrs,
          EvalState.enterBlock, OpCtx.get?, BlockCtx.get?, BlockCtx.Raw.get?, Scope.get?,
          Block.entryEnv, Peano.opCtx, Op.natBinary, Op.natUnary, Op.compare,
          Op.eq, Op.ite, Op.ofVals, Op.Body.eager, Term.nat, Term.bool, Term.ite,
          heapOpCtx, factorialBlocks] <;> rfl
    · evaluates_to_all 300 [heapOpCtx, factorialBlocks]
    · intro scope
      exact EvaluatesFrom.done
  refine ⟨fuel, ?_⟩
  simpa [EvalState.result?] using congrArg EvalState.result? (EvalState.run_eq_of_stepN hsteps)

end Zag.Test.Autocorres.Examples
