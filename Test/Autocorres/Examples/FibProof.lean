import Test.Autocorres.Examples.Common

namespace Zag.Test.Autocorres.Examples

open Zag Zag.Lib.PeanoHeap

abbrev fibBlocks : BlockCtx.Raw heapCtx :=
  blocks% [
    fib(n : Nat) : Nat {
      small := op "lt"[n, nat(2)];
      ret if small { n } else { op "add"[call fib [op "sub"[n, nat(1)]], call fib [op "sub"[n, nat(2)]]] }
    },
    fibLinear(n : Nat) : Nat {
      ret call fibLinearLoop [n, nat(0), nat(1)]
    },
    fibLinearLoop(remaining : Nat, a : Nat, b : Nat) : Nat {
      done := primEq remaining nat(0);
      ret if done { a } else { call fibLinearLoop [op "sub"[remaining, nat(1)], b, op "add"[a, b]] }
    },
    callFib() : Nat {
      ignored := call fib [nat(42)];
      ret nat(0)
    }
  ]

theorem fibBlocksValid : BlockCtx.Valid fibBlocks := by valid_blocks [fibBlocks]

abbrev fibCtx : Ctx := mkCtx fibBlocks fibBlocksValid

theorem fibCtx_wellTyped : Ctx.WellTyped fibCtx := by typecheck_ctx

def fibLinearLoopSpec : Nat → Nat → Nat → Nat
| 0, a, _b => a
| n + 1, a, b => fibLinearLoopSpec n b (a + b)

theorem fibLinearLoop_eval (remaining a b : Nat) :
    EvaluatesCall fibCtx "fibLinearLoop"
        ([Val.nat remaining, Val.nat a, Val.nat b] : List (Val heapCtx))
      (Val.nat (fibLinearLoopSpec remaining a b)) := by
  induction remaining generalizing a b with
  | zero => evaluates_call 300 [heapOpCtx, fibBlocks, fibLinearLoopSpec]
  | succ remaining ih =>
      refine EvaluatesCall.of_evaluatesFrom ?_
      intro env base
      set_option linter.unusedSimpArgs false in
        simp +arith [EvalState.enterInstrs, EvalState.enterBlock, BlockCtx.get?,
          BlockCtx.Raw.get?, Scope.get?, Block.entryEnv, Term.nat, Term.bool, Term.ite,
          heapOpCtx, fibBlocks]
      refine EvaluatesFrom.trans_stepN (fuel₀ := 9)
        (mid := {
          control := .eval (.call "fibLinearLoop"
            [Term.op "sub" [Term.var "remaining", Term.nat 1],
             Term.var "b",
             Term.op "add" [Term.var "a", Term.var "b"]]),
          env := [("remaining", Val.nat (remaining + 1)), ("a", Val.nat a),
            ("b", Val.nat b), ("done", Val.bool false)],
          stack :=
            Frame.opBody (fun elseVal =>
              match elseVal with
              | some value => Op.Body.done value
              | none => Op.Body.fail) []
              [("remaining", Val.nat (remaining + 1)), ("a", Val.nat a),
                ("b", Val.nat b), ("done", Val.bool false)] ::
            Frame.call "fibLinearLoop" env :: base }) ?_ ?_
      · set_option linter.unusedSimpArgs false in
          simp +arith [EvalState.stepN, EvalState.step, EvalState.driveOp,
            EvalState.enterInstrs, EvalState.enterBlock, OpCtx.get?, BlockCtx.get?,
            BlockCtx.Raw.get?, Scope.get?, Block.entryEnv, Peano.opCtx, Op.natBinary,
            Op.natUnary, Op.compare, Op.eq, Op.ite, Op.ofVals, Op.Body.eager,
            Term.nat, Term.bool, Term.ite, heapOpCtx, fibBlocks] <;>
            (first | rfl | funext z <;> cases z <;> rfl)
      refine EvaluatesFrom.call_then (block := fibBlocks[2].2)
        (hcall := by simpa [fibLinearLoopSpec] using ih b (a + b)) ?_ ?_ ?_
      · set_option linter.unusedSimpArgs false in
          simp +arith [EvalState.step, EvalState.driveOp, EvalState.enterInstrs,
            EvalState.enterBlock, OpCtx.get?, BlockCtx.get?, BlockCtx.Raw.get?, Scope.get?,
            Block.entryEnv, Peano.opCtx, Op.natBinary, Op.natUnary, Op.compare,
            Op.eq, Op.ite, Op.ofVals, Op.Body.eager, Term.nat, Term.bool, Term.ite,
            heapOpCtx, fibBlocks] <;> rfl
      · evaluates_to_all 300 [heapOpCtx, fibBlocks]
      · intro scope
        refine EvaluatesFrom.trans_stepN (fuel₀ := 2)
          (mid := {
            control := .ret (Val.nat (fibLinearLoopSpec (remaining + 1) a b)),
            env := env,
            stack := base }) ?_ ?_
        · set_option linter.unusedSimpArgs false in
            simp +arith [EvalState.stepN, EvalState.step, EvalState.driveOp,
              EvalState.enterInstrs, EvalState.enterBlock, OpCtx.get?, BlockCtx.get?,
              BlockCtx.Raw.get?, Scope.get?, Block.entryEnv, Peano.opCtx, Op.natBinary,
              Op.natUnary, Op.compare, Op.eq, Op.ite, Op.ofVals, Op.Body.eager,
              Term.nat, Term.bool, Term.ite, heapOpCtx, fibBlocks, fibLinearLoopSpec] <;> rfl
        exact EvaluatesFrom.done

theorem fibLinear_eval (n : Nat) :
    EvaluatesCall fibCtx "fibLinear" ([Val.nat n] : List (Val heapCtx))
      (Val.nat (fibLinearLoopSpec n 0 1)) := by
  refine EvaluatesCall.of_evaluatesFrom ?_
  intro env base
  set_option linter.unusedSimpArgs false in
    simp +arith [EvalState.enterInstrs, EvalState.enterBlock, BlockCtx.get?,
      BlockCtx.Raw.get?, Scope.get?, Block.entryEnv, Term.nat, Term.bool, Term.ite,
      heapOpCtx, fibBlocks]
  refine EvaluatesFrom.call_then (block := fibBlocks[2].2)
    (hcall := fibLinearLoop_eval n 0 1) ?_ ?_ ?_
  · set_option linter.unusedSimpArgs false in
      simp +arith [EvalState.step, EvalState.driveOp, EvalState.enterInstrs,
        EvalState.enterBlock, OpCtx.get?, BlockCtx.get?, BlockCtx.Raw.get?, Scope.get?,
        Block.entryEnv, Peano.opCtx, Op.natBinary, Op.natUnary, Op.compare,
        Op.eq, Op.ite, Op.ofVals, Op.Body.eager, Term.nat, Term.bool, Term.ite,
        heapOpCtx, fibBlocks] <;> rfl
  · evaluates_to_all 300 [heapOpCtx, fibBlocks]
  · intro scope
    evaluates_from 300 [heapOpCtx, fibBlocks]

/-- The same statement at the surface: calling `fibLinear` on a literal. -/
theorem fibLinear_eval_call (n : Nat) :
    EvaluatesTo fibCtx [] (.call "fibLinear" [Term.nat n])
      (Val.nat (fibLinearLoopSpec n 0 1)) := by
  obtain ⟨fuel, scope, hsteps⟩ :
      EvaluatesFrom fibCtx (EvalState.start [] (.call "fibLinear" [Term.nat n]))
        (Val.nat (fibLinearLoopSpec n 0 1)) [] := by
    unfold EvalState.start
    refine EvaluatesFrom.call_then (block := fibBlocks[1].2)
      (hcall := fibLinear_eval n) ?_ ?_ ?_
    · set_option linter.unusedSimpArgs false in
        simp +arith [EvalState.step, EvalState.driveOp, EvalState.enterInstrs,
          EvalState.enterBlock, OpCtx.get?, BlockCtx.get?, BlockCtx.Raw.get?, Scope.get?,
          Block.entryEnv, Peano.opCtx, Op.natBinary, Op.natUnary, Op.compare,
          Op.eq, Op.ite, Op.ofVals, Op.Body.eager, Term.nat, Term.bool, Term.ite,
          heapOpCtx, fibBlocks] <;> rfl
    · evaluates_to_all 300 [heapOpCtx, fibBlocks]
    · intro scope
      exact EvaluatesFrom.done
  refine ⟨fuel, ?_⟩
  simpa [EvalState.result?] using congrArg EvalState.result? (EvalState.run_eq_of_stepN hsteps)

end Zag.Test.Autocorres.Examples
