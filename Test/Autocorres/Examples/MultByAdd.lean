import Test.Autocorres.Examples.Common

namespace Zag.Test.Autocorres.Examples

open Zag Zag.Lib.PeanoHeap

abbrev multByAddBlocks : BlockCtx.Raw heapCtx :=
  blocks% [
    multByAdd(x : Nat, y : Nat) : Nat {
      ret call multByAddLoop [x, y, nat(0)]
    },
    multByAddLoop(x : Nat, remaining : Nat, acc : Nat) : Nat {
      done := primEq remaining nat(0);
      ret if done { acc } else { call multByAddLoop [x, op "sub"[remaining, nat(1)], op "add"[acc, x]] }
    }
  ]

theorem multByAddBlocksValid : BlockCtx.Valid multByAddBlocks := by
  valid_blocks [multByAddBlocks]

abbrev multByAddCtx : Ctx := mkCtx multByAddBlocks multByAddBlocksValid

theorem multByAddCtx_wellTyped : Ctx.WellTyped multByAddCtx := by typecheck_ctx

/-- The loop accumulates one `x` per remaining step. -/
theorem multByAddLoop_eval (x remaining acc : Nat) :
    EvaluatesCall multByAddCtx "multByAddLoop"
        ([Val.nat x, Val.nat remaining, Val.nat acc] : List (Val heapCtx))
      (Val.nat (acc + remaining * x)) := by
  induction remaining generalizing acc with
  | zero => evaluates_call 300 [heapOpCtx, multByAddBlocks]
  | succ remaining ih =>
      refine EvaluatesCall.of_evaluatesFrom ?_
      intro env base
      set_option linter.unusedSimpArgs false in
        simp +arith [EvalState.enterInstrs, EvalState.enterBlock, BlockCtx.get?,
          BlockCtx.Raw.get?, Scope.get?, Block.entryEnv, Term.nat, Term.bool, Term.ite,
          heapOpCtx, multByAddBlocks]
      refine EvaluatesFrom.trans_stepN (fuel₀ := 9)
        (mid := {
          control := .eval (.call "multByAddLoop"
            [Term.var "x",
             Term.op "sub" [Term.var "remaining", Term.nat 1],
             Term.op "add" [Term.var "acc", Term.var "x"]]),
          env := [("x", Val.nat x), ("remaining", Val.nat (remaining + 1)),
            ("acc", Val.nat acc), ("done", Val.bool false)],
          stack :=
            Frame.opBody (fun elseVal =>
              match elseVal with
              | some value => Op.Body.done value
              | none => Op.Body.fail) []
              [("x", Val.nat x), ("remaining", Val.nat (remaining + 1)),
                ("acc", Val.nat acc), ("done", Val.bool false)] ::
            Frame.call "multByAddLoop" env :: base }) ?_ ?_
      · set_option linter.unusedSimpArgs false in
          simp +arith [EvalState.stepN, EvalState.step, EvalState.driveOp,
            EvalState.enterInstrs, EvalState.enterBlock, OpCtx.get?, BlockCtx.get?,
            BlockCtx.Raw.get?, Scope.get?, Block.entryEnv, Peano.opCtx, Op.natBinary,
            Op.natUnary, Op.compare, Op.eq, Op.ite, Op.ofVals, Op.Body.eager,
            Term.nat, Term.bool, Term.ite, heapOpCtx, multByAddBlocks] <;>
            (first | rfl | funext z <;> cases z <;> rfl)
      refine EvaluatesFrom.call_then (block := multByAddBlocks[1].2)
        (hcall := by
          show EvaluatesCall multByAddCtx "multByAddLoop"
            ([Val.nat x, Val.nat remaining, Val.nat (acc + x)] : List (Val heapCtx))
            (Val.nat (acc + (remaining + 1) * x))
          have hnat : (acc + x) + remaining * x = acc + (remaining + 1) * x := by
            rw [Nat.succ_mul]
            omega
          simpa [hnat] using ih (acc + x)) ?_ ?_ ?_
      · set_option linter.unusedSimpArgs false in
          simp +arith [EvalState.step, EvalState.driveOp, EvalState.enterInstrs,
            EvalState.enterBlock, OpCtx.get?, BlockCtx.get?, BlockCtx.Raw.get?, Scope.get?,
            Block.entryEnv, Peano.opCtx, Op.natBinary, Op.natUnary, Op.compare,
            Op.eq, Op.ite, Op.ofVals, Op.Body.eager, Term.nat, Term.bool, Term.ite,
            heapOpCtx, multByAddBlocks] <;> rfl
      · evaluates_to_all 300 [heapOpCtx, multByAddBlocks]
      · intro scope
        refine EvaluatesFrom.trans_stepN (fuel₀ := 2)
          (mid := {
            control := .ret (Val.nat (acc + (remaining + 1) * x)),
            env := env,
            stack := base }) ?_ ?_
        · set_option linter.unusedSimpArgs false in
            simp +arith [EvalState.stepN, EvalState.step, EvalState.driveOp,
              EvalState.enterInstrs, EvalState.enterBlock, OpCtx.get?, BlockCtx.get?,
              BlockCtx.Raw.get?, Scope.get?, Block.entryEnv, Peano.opCtx, Op.natBinary,
              Op.natUnary, Op.compare, Op.eq, Op.ite, Op.ofVals, Op.Body.eager,
              Term.nat, Term.bool, Term.ite, heapOpCtx, multByAddBlocks] <;> rfl
        exact EvaluatesFrom.done

theorem multByAdd_eval (x y : Nat) :
    EvaluatesCall multByAddCtx "multByAdd" ([Val.nat x, Val.nat y] : List (Val heapCtx))
      (Val.nat (x * y)) := by
  refine EvaluatesCall.of_evaluatesFrom ?_
  intro env base
  set_option linter.unusedSimpArgs false in
    simp +arith [EvalState.enterInstrs, EvalState.enterBlock, BlockCtx.get?,
      BlockCtx.Raw.get?, Scope.get?, Block.entryEnv, Term.nat, Term.bool, Term.ite,
      heapOpCtx, multByAddBlocks]
  refine EvaluatesFrom.call_then (block := multByAddBlocks[1].2)
    (hcall := by simpa [Nat.mul_comm] using multByAddLoop_eval x y 0) ?_ ?_ ?_
  · set_option linter.unusedSimpArgs false in
      simp +arith [EvalState.step, EvalState.driveOp, EvalState.enterInstrs,
        EvalState.enterBlock, OpCtx.get?, BlockCtx.get?, BlockCtx.Raw.get?, Scope.get?,
        Block.entryEnv, Peano.opCtx, Op.natBinary, Op.natUnary, Op.compare,
        Op.eq, Op.ite, Op.ofVals, Op.Body.eager, Term.nat, Term.bool, Term.ite,
        heapOpCtx, multByAddBlocks] <;> rfl
  · evaluates_to_all 300 [heapOpCtx, multByAddBlocks]
  · intro scope
    evaluates_from 300 [heapOpCtx, multByAddBlocks]

/-- The same statement at the surface: calling `multByAdd` on two literals. -/
theorem multByAdd_eval_call (x y : Nat) :
    EvaluatesTo multByAddCtx [] (.call "multByAdd" [Term.nat x, Term.nat y])
      (Val.nat (x * y)) := by
  obtain ⟨fuel, scope, hsteps⟩ :
      EvaluatesFrom multByAddCtx (EvalState.start [] (.call "multByAdd" [Term.nat x, Term.nat y]))
        (Val.nat (x * y)) [] := by
    unfold EvalState.start
    refine EvaluatesFrom.call_then (block := multByAddBlocks[0].2)
      (hcall := multByAdd_eval x y) ?_ ?_ ?_
    · set_option linter.unusedSimpArgs false in
        simp +arith [EvalState.step, EvalState.driveOp, EvalState.enterInstrs,
          EvalState.enterBlock, OpCtx.get?, BlockCtx.get?, BlockCtx.Raw.get?, Scope.get?,
          Block.entryEnv, Peano.opCtx, Op.natBinary, Op.natUnary, Op.compare,
          Op.eq, Op.ite, Op.ofVals, Op.Body.eager, Term.nat, Term.bool, Term.ite,
          heapOpCtx, multByAddBlocks] <;> rfl
    · evaluates_to_all 300 [heapOpCtx, multByAddBlocks]
    · intro scope
      exact EvaluatesFrom.done
  refine ⟨fuel, ?_⟩
  simpa [EvalState.result?] using congrArg EvalState.result? (EvalState.run_eq_of_stepN hsteps)

end Zag.Test.Autocorres.Examples
