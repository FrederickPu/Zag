import Test.Autocorres.Examples.Common

/-!
 Loops written as ordinary resumable operators rather than as self-recursive blocks.

As in `plusLoop` from `Plus.lean`, re-entry comes from an `opRef` passed to the CPS body: the
`while` operator applies the condition, then the body applies that continuation to its next state.

Recursive-block induction has nothing to say about such a loop -- there is no recursive call to
induct on. `Peano.Exact.while_evaluatesTo` handles it with an invariant indexed by the iteration,
plus the iteration count at which the condition goes false, supplied separately rather than
extracted from a decreasing measure.
-/

namespace Zag.Test.While

open Zag Zag.Lib.PeanoHeap
open Zag.EvalTriple.Exact

private abbrev heapOpCtx := Zag.Test.Autocorres.Examples.pureHeapOpCtx

/-! ### counting down

  `countDownCond` and `countDownBody` are ordinary blocks; neither mentions the other, and
  neither mentions `countDown`. The body only knows the continuation supplied by the operator. -/

abbrev whileBlocks : BlockCtx.Raw heapCtx :=
  blocks% [
    countDownCond(n : Nat) : Bool {
      ret primGt n nat(0)
    },
    countDownBody(n : Nat, loop : func[Nat] => Nat) : Nat {
      next := op "sub"[n, nat(1)];
      ret apply loop [next]
    },
    countDown(start : Nat) : Nat {
      final := while [countDownCond, countDownBody] (start);
      ret final
    }
  ]

theorem whileBlocksValid : BlockCtx.Valid whileBlocks := by valid_blocks [whileBlocks]

abbrev whileCtx : Ctx := Zag.Test.Autocorres.Examples.mkPureCtx whileBlocks whileBlocksValid

theorem whileCtx_wellTyped : Ctx.WellTyped whileCtx := by typecheck_ctx

/-- The same loop from a *symbolic* start, which no amount of running will settle. The invariant
  is `start - k` after `k` iterations; termination is `start` iterations. Nothing but `init` is
  left over, and no machine state is ever surfaced. -/
theorem countDown_eval_gen (s : Nat) :
    EvaluatesCallValues whileCtx "countDown" ([Val.nat s] : List (Val heapCtx)) (Val.nat 0) := by
  apply EvaluatesCallValues.of_evaluatesInstrs
  · rfl
  · rfl
  dsimp [whileBlocks, Block.entryEnv]
  apply EvaluatesInstrs.cons
  · apply Peano.Exact.while_evaluatesTo (hM := rfl)
      (I := fun k args => args = [Val.nat (s - k)]) (N := s)
      (initial := [Val.nat s]) (loopResult := Val.nat 0)
    auto_eval_refinement_goals [heapOpCtx, Op.fixed, whileBlocks]
    · exact EvaluatesList.cons (by
        exact EvaluatesTo.var_local (hM := rfl) (by rfl)) EvaluatesList.nil
    · intro k hk
      constructor
      · apply EvaluatesCallValues.of_evaluatesInstrs
        · rfl
        · rfl
        dsimp [whileBlocks, Block.entryEnv]
        apply EvaluatesInstrs.nil
        apply EvaluatesTo.of_eq
          (evaluates_gt_nat
            (EvaluatesTo.var_local (hM := rfl) (by rfl))
            (evaluates_nat (hM := rfl) _ 0))
        simp
        omega
      · intro hloop
        apply EvaluatesCallValues.of_evaluatesInstrs
        · rfl
        · rfl
        dsimp [whileBlocks, Block.entryEnv]
        refine EvaluatesInstrs.cons (instrValue := Val.nat (s - (k + 1))) ?_ ?_
        · apply EvaluatesTo.of_eq
            (evaluates_sub_nat
              (EvaluatesTo.var_local (hM := rfl) (by rfl))
              (evaluates_nat (hM := rfl) _ 1))
          simp [Nat.sub_sub]
        apply EvaluatesInstrs.nil
        exact EvaluatesTo.app
          (EvaluatesTo.var_local (hM := rfl) (by rfl))
          (EvaluatesList.cons (EvaluatesTo.var_local (hM := rfl) (by rfl)) EvaluatesList.nil)
          hloop
    · apply EvaluatesCallValues.of_evaluatesInstrs
      · rfl
      · rfl
      dsimp [whileBlocks, Block.entryEnv]
      apply EvaluatesInstrs.nil
      simpa using evaluates_gt_nat
        (ctx := whileCtx) (env := [("n", Val.nat 0)])
        (EvaluatesTo.var_local (ctx := whileCtx) (env := [("n", Val.nat 0)])
          (name := "n") (value := Val.nat 0) (hM := rfl) (by rfl))
        (evaluates_nat (ctx := whileCtx) (env := [("n", Val.nat 0)]) (hM := rfl) 0)
  · exact EvaluatesInstrs.nil (EvaluatesTo.var_local (by rfl))

/-- Counting `5` down to `0`, as a concrete specialization of the symbolic loop proof. -/
theorem countDown_eval :
    EvaluatesCallValues whileCtx "countDown" ([Val.nat 5] : List (Val heapCtx)) (Val.nat 0) := by
  exact countDown_eval_gen 5

/-- The symbolic exact proof packages all machine details behind the arithmetic invariant. -/
example (s : Nat) :
    EvaluatesCallValues whileCtx "countDown" ([Val.nat s] : List (Val heapCtx)) (Val.nat 0) := by
  exact countDown_eval_gen s

/-! ### an invariant that is not arithmetic

  Halving until the value reaches one. The loop state after `k` iterations is written as an
  iteration rather than as a closed-form expression, and termination is a hypothesis *about that
  iteration* -- exactly the shape a decreasing measure cannot express. -/

abbrev halveBlocks : BlockCtx.Raw heapCtx :=
  blocks% [
    halveCond(n : Nat) : Bool {
      ret primGt n nat(1)
    },
    halveBody(n : Nat, loop : func[Nat] => Nat) : Nat {
      next := op "div"[n, nat(2)];
      ret apply loop [next]
    },
    halve(start : Nat) : Nat {
      final := while [halveCond, halveBody] (start);
      ret final
    }
  ]

theorem halveBlocksValid : BlockCtx.Valid halveBlocks := by valid_blocks [halveBlocks]

abbrev halveCtx : Ctx := Zag.Test.Autocorres.Examples.mkPureCtx halveBlocks halveBlocksValid

theorem halveCtx_wellTyped : Ctx.WellTyped halveCtx := by typecheck_ctx

/-- The loop state after `k` iterations, written as an iteration rather than as a closed form. -/
def halveIter (start : Nat) : Nat → Nat
| 0 => start
| k + 1 => halveIter start k / 2

theorem halve_eval (s n : Nat)
    (running : ∀ k, k < n → 1 < halveIter s k)
    (stops : halveIter s n = 1) :
    EvaluatesCallValues halveCtx "halve" ([Val.nat s] : List (Val heapCtx)) (Val.nat 1) := by
  -- `stops` is picked up by arithmetic cleanup; the running fact and definitional preservation
  -- remain ordinary named premises.
  apply EvaluatesCallValues.of_evaluatesInstrs
  · rfl
  · rfl
  dsimp [halveBlocks, Block.entryEnv]
  apply EvaluatesInstrs.cons
  · apply Peano.Exact.while_evaluatesTo (hM := rfl)
      (I := fun k args => args = [Val.nat (halveIter s k)]) (N := n)
      (initial := [Val.nat s]) (loopResult := Val.nat 1)
    auto_eval_refinement_goals [heapOpCtx, Op.fixed, halveBlocks, halveIter]
    · exact EvaluatesList.cons (by
        exact EvaluatesTo.var_local (hM := rfl) (by rfl)) EvaluatesList.nil
    · intro k hk
      constructor
      · apply EvaluatesCallValues.of_evaluatesInstrs
        · rfl
        · rfl
        dsimp [halveBlocks, Block.entryEnv]
        apply EvaluatesInstrs.nil
        apply EvaluatesTo.of_eq
          (evaluates_gt_nat
            (EvaluatesTo.var_local (hM := rfl) (by rfl))
            (evaluates_nat (hM := rfl) _ 1))
        simp
        exact running k hk
      · intro hloop
        apply EvaluatesCallValues.of_evaluatesInstrs
        · rfl
        · rfl
        dsimp [halveBlocks, Block.entryEnv]
        refine EvaluatesInstrs.cons (instrValue := Val.nat (halveIter s (k + 1))) ?_ ?_
        · simpa [halveIter] using evaluates_div_nat
            (EvaluatesTo.var_local (hM := rfl) (by rfl))
            (evaluates_nat (hM := rfl) _ 2)
        apply EvaluatesInstrs.nil
        exact EvaluatesTo.app
          (EvaluatesTo.var_local (hM := rfl) (by rfl))
          (EvaluatesList.cons (EvaluatesTo.var_local (hM := rfl) (by rfl)) EvaluatesList.nil)
          hloop
    · apply EvaluatesCallValues.of_evaluatesInstrs
      · rfl
      · rfl
      dsimp [halveBlocks, Block.entryEnv]
      apply EvaluatesInstrs.nil
      simpa using evaluates_gt_nat
        (ctx := halveCtx) (env := [("n", Val.nat 1)])
        (EvaluatesTo.var_local (ctx := halveCtx) (env := [("n", Val.nat 1)])
          (name := "n") (value := Val.nat 1) (hM := rfl) (by rfl))
        (evaluates_nat (ctx := halveCtx) (env := [("n", Val.nat 1)]) (hM := rfl) 1)
  · exact EvaluatesInstrs.nil (EvaluatesTo.var_local (by rfl))

/-- Instantiated: from `100`, six halvings reach `1`. The hypotheses are ordinary `Nat` facts,
  decided here, and nothing about the machine appears in them. -/
example : EvaluatesCallValues halveCtx "halve" ([Val.nat 100] : List (Val heapCtx)) (Val.nat 1) :=
  halve_eval 100 6 (by decide) (by decide)

/-! ### what ordinary operator typing rejects

  `Term.hasType.op` checks both the first-class block operands and the loop state. These examples
  cover an undeclared operator, too few operands, mismatched state types, a missing block, and a
  body whose CPS signature does not match the state arity. -/

section Rejects

open Zag.Pr.TypeUnification

-- the block the rule is meant to accept
#guard (checkBlock? whileCtx whileBlocks[2].2).isSome = true

-- no such operator
#guard (checkBlock? whileCtx
  { params := [("start", Peano.NatTy)]
    instrs := [⟨"final", .op "forever"
      [Term.var "countDownCond", Term.var "countDownBody", Term.var "start"]⟩]
    outTy := Peano.NatTy
    result := Term.var "final" }).isSome = false

-- `while` requires condition, body, and at least one state operand
#guard (checkBlock? whileCtx
  { params := [("start", Peano.NatTy)]
    instrs := [⟨"final", .op "while" [Term.var "countDownCond", Term.var "start"]⟩]
    outTy := Peano.NatTy
    result := Term.var "final" }).isSome = false

-- the state is a `Bool`, but both driven blocks take a `Nat`
#guard (checkBlock? whileCtx
  { params := [("start", Peano.BoolTy)]
    instrs := [⟨"final", .op "while"
      [Term.var "countDownCond", Term.var "countDownBody", Term.var "start"]⟩]
    outTy := Peano.BoolTy
    result := Term.var "final" }).isSome = false

-- the body operand names a block that does not exist
#guard (checkBlock? whileCtx
  { params := [("start", Peano.NatTy)]
    instrs := [⟨"final", .op "while"
      [Term.var "countDownCond", Term.var "nope", Term.var "start"]⟩]
    outTy := Peano.NatTy
    result := Term.var "final" }).isSome = false

-- the one-state body does not accept two state values plus their continuation
#guard (checkBlock? whileCtx
  { params := [("a", Peano.NatTy), ("b", Peano.NatTy)]
    instrs := [⟨"final", .op "while" [Term.var "countDownCond", Term.var "countDownBody",
      Term.var "a", Term.var "b"]⟩]
    outTy := Peano.NatTy
    result := Term.var "final" }).isSome = false

end Rejects

end Zag.Test.While
