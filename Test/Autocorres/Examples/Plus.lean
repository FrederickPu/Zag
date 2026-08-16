import Test.Autocorres.Examples.Common

namespace Zag.Test.Autocorres.Examples

open Zag Zag.Lib.PeanoHeap
open Zag.Pr.Induction

abbrev plusBlocks : BlockCtx.Raw heapCtx :=
  blocks% [
    plus(x : Nat, y : Nat) : Nat {
      ret op "add"[x, y]
    },
    plusLoop(x : Nat, y : Nat) : Nat {
      done := primEq y nat(0);
      ret if done { x } else { call plusLoop [op "add"[x, nat(1)], op "sub"[y, nat(1)]] }
    },
    plusMain() : Nat {
      direct := call plus [nat(1), nat(2)];
      looped := call plusLoop [nat(1), nat(2)];
      same := primEq direct looped;
      ret if same { nat(0) } else { nat(1) }
    }
  ]

theorem plusBlocksValid : BlockCtx.Valid plusBlocks := by valid_blocks [plusBlocks]

abbrev plusCtx : Ctx := mkCtx plusBlocks plusBlocksValid

theorem plusCtx_wellTyped : Ctx.WellTyped plusCtx := by typecheck_ctx

/-! ### what the program computes -/

theorem plus_eval (x y : Nat) :
    EvaluatesCall plusCtx "plus" ([Val.nat x, Val.nat y] : List (Val heapCtx))
      (Val.nat (x + y)) := by
  evaluates_call 300 [heapOpCtx, plusBlocks]

theorem plusLoop_eval (x y : Nat) :
    EvaluatesCall plusCtx "plusLoop" ([Val.nat x, Val.nat y] : List (Val heapCtx))
      (Val.nat (x + y)) := by
  induction y generalizing x with
  | zero => evaluates_call 300 [heapOpCtx, plusBlocks]
  | succ y ih =>
      refine EvaluatesCall.of_evaluatesFrom ?_
      intro env base
      set_option linter.unusedSimpArgs false in
        simp +arith [EvalState.enterInstrs, EvalState.enterBlock, BlockCtx.get?,
          BlockCtx.Raw.get?, Scope.get?, Block.entryEnv, Term.nat, Term.bool, Term.ite,
          heapOpCtx, plusBlocks]
      refine EvaluatesFrom.trans_stepN (fuel₀ := 9)
        (mid := {
          control := .eval (.call "plusLoop"
            [Term.op "add" [Term.var "x", Term.nat 1],
             Term.op "sub" [Term.var "y", Term.nat 1]]),
          env := [("x", Val.nat x), ("y", Val.nat (y + 1)), ("done", Val.bool false)],
          stack :=
            Frame.opBody (fun elseVal =>
              match elseVal with
              | some value => Op.Body.done value
              | none => Op.Body.fail) []
              [("x", Val.nat x), ("y", Val.nat (y + 1)), ("done", Val.bool false)] ::
            Frame.call "plusLoop" env :: base }) ?_ ?_
      · set_option linter.unusedSimpArgs false in
          simp +arith [EvalState.stepN, EvalState.step, EvalState.driveOp,
            EvalState.enterInstrs, EvalState.enterBlock, OpCtx.get?, BlockCtx.get?,
            BlockCtx.Raw.get?, Scope.get?, Block.entryEnv, Peano.opCtx, Op.natBinary,
            Op.natUnary, Op.compare, Op.eq, Op.ite, Op.ofVals, Op.Body.eager,
            Term.nat, Term.bool, Term.ite, heapOpCtx, plusBlocks] <;>
            (first | rfl | funext z <;> cases z <;> rfl)
      refine EvaluatesFrom.call_then (block := plusBlocks[1].2) (hcall := ih (x + 1)) ?_ ?_ ?_
      · set_option linter.unusedSimpArgs false in
          simp +arith [EvalState.step, EvalState.driveOp, EvalState.enterInstrs,
            EvalState.enterBlock, OpCtx.get?, BlockCtx.get?, BlockCtx.Raw.get?, Scope.get?,
            Block.entryEnv, Peano.opCtx, Op.natBinary, Op.natUnary, Op.compare,
            Op.eq, Op.ite, Op.ofVals, Op.Body.eager, Term.nat, Term.bool, Term.ite,
            heapOpCtx, plusBlocks] <;> rfl
      · evaluates_to_all 300 [heapOpCtx, plusBlocks]
      · intro scope
        refine EvaluatesFrom.trans_stepN (fuel₀ := 2)
          (mid := { control := .ret (Val.nat (y + x + 1)), env := env, stack := base }) ?_ ?_
        · set_option linter.unusedSimpArgs false in
            simp +arith [EvalState.stepN, EvalState.step, EvalState.driveOp,
              EvalState.enterInstrs, EvalState.enterBlock, OpCtx.get?, BlockCtx.get?,
              BlockCtx.Raw.get?, Scope.get?, Block.entryEnv, Peano.opCtx, Op.natBinary,
              Op.natUnary, Op.compare, Op.eq, Op.ite, Op.ofVals, Op.Body.eager,
              Term.nat, Term.bool, Term.ite, heapOpCtx, plusBlocks] <;> rfl
        exact EvaluatesFrom.done

/-- The loop agrees with the one-shot version, which is what `plusMain` checks at runtime. -/
theorem plusMain_eval : EvaluatesCall plusCtx "plusMain" [] (Val.nat 0) := by
  refine EvaluatesCall.of_evaluatesFrom ?_
  intro env base
  set_option linter.unusedSimpArgs false in
    simp +arith [EvalState.enterInstrs, EvalState.enterBlock, BlockCtx.get?,
      BlockCtx.Raw.get?, Scope.get?, Block.entryEnv, Term.nat, Term.bool, Term.ite,
      heapOpCtx, plusBlocks]
  refine EvaluatesFrom.call_then (block := plusBlocks[0].2) (hcall := plus_eval 1 2) ?_ ?_ ?_
  · set_option linter.unusedSimpArgs false in
      simp +arith [EvalState.step, EvalState.driveOp, EvalState.enterInstrs,
        EvalState.enterBlock, OpCtx.get?, BlockCtx.get?, BlockCtx.Raw.get?, Scope.get?,
        Block.entryEnv, Peano.opCtx, Op.natBinary, Op.natUnary, Op.compare,
        Op.eq, Op.ite, Op.ofVals, Op.Body.eager, Term.nat, Term.bool, Term.ite,
        heapOpCtx, plusBlocks] <;> rfl
  · evaluates_to_all 600 [heapOpCtx, plusBlocks]
  · intro scope
    refine EvaluatesFrom.trans_stepN (fuel₀ := 1)
      (mid := {
        control := .eval (.call "plusLoop" [Term.nat 1, Term.nat 2]),
        env := [("direct", Val.nat 3)],
        stack :=
          Frame.instrs "looped"
            [{ name := "same", value := Term.op "eq" [Term.var "direct", Term.var "looped"] }]
            (Term.op "ite" [Term.var "same", Term.nat 0, Term.nat 1])
            [("direct", Val.nat 3)] ::
          Frame.call "plusMain" env :: base }) ?_ ?_
    · set_option linter.unusedSimpArgs false in
        simp +arith [EvalState.stepN, EvalState.step, EvalState.driveOp,
          EvalState.enterInstrs, EvalState.enterBlock, OpCtx.get?, BlockCtx.get?,
          BlockCtx.Raw.get?, Scope.get?, Block.entryEnv, Peano.opCtx, Op.natBinary,
          Op.natUnary, Op.compare, Op.eq, Op.ite, Op.ofVals, Op.Body.eager,
          Term.nat, Term.bool, Term.ite, heapOpCtx, plusBlocks] <;> rfl
    refine EvaluatesFrom.call_then (block := plusBlocks[1].2) (hcall := plusLoop_eval 1 2) ?_ ?_ ?_
    · set_option linter.unusedSimpArgs false in
        simp +arith [EvalState.step, EvalState.driveOp, EvalState.enterInstrs,
          EvalState.enterBlock, OpCtx.get?, BlockCtx.get?, BlockCtx.Raw.get?, Scope.get?,
          Block.entryEnv, Peano.opCtx, Op.natBinary, Op.natUnary, Op.compare,
          Op.eq, Op.ite, Op.ofVals, Op.Body.eager, Term.nat, Term.bool, Term.ite,
          heapOpCtx, plusBlocks] <;> rfl
    · evaluates_to_all 600 [heapOpCtx, plusBlocks]
    · intro scope
      evaluates_from 600 [heapOpCtx, plusBlocks]

/-! ### the same fact, proved inside Zag by induction

  Above, Lean evaluates the program. Here Zag states `plusLoop x n = x + n` as a proposition of
  its own and derives it from `Pr.Induction`'s rule; Lean only discharges the base and step. -/

theorem plusSuccSpec : SuccSpec plusCtx "succ" where
  hasType_op := fun _ _ ht => Term.hasType.unOp rfl ht
  eval_succ := fun _ _ _ ht => by
    simpa using (evaluates_natUnary (ctx := plusCtx) (name := "succ") (f := Nat.succ)
      (Peano.Model.succOp (ctx := plusCtx)) ht)

def plusLoopTerm (x : Nat) (t : Term heapCtx) : Term heapCtx := .call "plusLoop" [Term.nat x, t]

def plusAddTerm (x : Nat) (t : Term heapCtx) : Term heapCtx := .op "add" [Term.nat x, t]

def plusLoopStatement (x y : Nat) : Pr (Term heapCtx) :=
  .eq [] Peano.NatTy (plusLoopTerm x (Term.nat y)) (plusAddTerm x (Term.nat y))

def plusLoopPredicate (x : Nat) : Pr (Term heapCtx) :=
  .eq [] Peano.NatTy (plusLoopTerm x (.var "n")) (plusAddTerm x (.var "n"))

attribute [local simp] plusLoopTerm plusAddTerm plusLoopStatement plusLoopPredicate

theorem plusLoopStatement_eq (x y : Nat) :
    plusLoopStatement x y = Pr.Induction.instantiate "n" (Term.nat y) (plusLoopPredicate x) := rfl

theorem plusLoopTerm_hasType {varCtx : VarCtx} {x : Nat} {t : Term heapCtx}
    (ht : Term.hasType plusCtx varCtx t Peano.NatTy) :
    Term.hasType plusCtx varCtx (plusLoopTerm x t) Peano.NatTy :=
  Term.hasType.call (ctx := plusCtx) (varCtx := varCtx) (name := "plusLoop")
    (args := [Term.nat x, t]) (block := plusBlocks[1].2) rfl rfl (by
      intro idx
      cases idx using Fin.cases with
      | zero => exact Term.hasType.prim _
      | succ idx =>
          cases idx using Fin.cases with
          | zero => exact ht
          | succ idx => exact Fin.elim0 idx)

theorem plusAddTerm_hasType {varCtx : VarCtx} {x : Nat} {t : Term heapCtx}
    (ht : Term.hasType plusCtx varCtx t Peano.NatTy) :
    Term.hasType plusCtx varCtx (plusAddTerm x t) Peano.NatTy :=
  Term.hasType.binOp (argTy := Peano.NatTy) rfl (Term.hasType.prim _) ht

/-- The statement `plusLoop x t = x + t`, for any `t` that evaluates to a `Nat`. -/
theorem plusLoop_eq_of_arg_nat (x : Nat) {t : Term heapCtx}
    (ht : Term.hasType plusCtx [] t Peano.NatTy)
    (heval : ∀ env : Env heapCtx, env.Models [] → ∃ n : Nat,
      EvaluatesTo plusCtx env t (Val.nat n)) :
    Term.eq plusCtx [] Peano.NatTy (plusLoopTerm x t) (plusAddTerm x t) :=
  term_eq_nat_of_eval (plusLoopTerm_hasType ht) (plusAddTerm_hasType ht) fun env henv =>
    match heval env henv with
    | ⟨n, hn⟩ =>
        let hnatx : EvaluatesTo plusCtx env (Term.nat x) (Val.nat x) :=
          Pr.Induction.eval_natLit (ctx := plusCtx) env x
        let hblock : plusCtx.blockCtx.get? "plusLoop" = some plusBlocks[1].2 := by
          set_option linter.unusedSimpArgs false in
            simp [BlockCtx.get?, BlockCtx.Raw.get?, Scope.get?, plusCtx, plusBlocks]
        ⟨x + n,
          by
            unfold plusLoopTerm
            exact EvaluatesTo.call (block := plusBlocks[1].2)
              (hcall := plusLoop_eval x n) hblock
              (EvaluatesToAll.cons hnatx (EvaluatesToAll.cons hn EvaluatesToAll.nil)),
          by
            unfold plusAddTerm
            exact evaluates_natBinary (ctx := plusCtx) (name := "add") (f := Nat.add)
              (Peano.Model.addOp (ctx := plusCtx)) hnatx hn⟩

theorem plusLoopBaseProvable (x : Nat) :
    Pr.Provable plusCtx [] [] (Pr.Induction.instantiate "n" (Term.nat 0) (plusLoopPredicate x)) := by
  rw [← plusLoopStatement_eq x 0]
  refine Pr.Provable.ofProof ?_
  exact_reflected plusLoop_eq_of_arg_nat x (Term.hasType.prim _)
    (fun env _ => ⟨0, Pr.Induction.eval_natLit (ctx := plusCtx) env 0⟩)

theorem plusLoopStepProvable (x : Nat) :
    Pr.Provable plusCtx [] [] (Pr.Induction.natStepGoal "n" "n_next" "succ" (plusLoopPredicate x)) := by
  open_reflected_provable
  intro nTerm hn y hy hsucc _ih
  exact_reflected plusLoop_eq_of_arg_nat x hy
    (eval_nat_of_reflected_natUnary_eq (ctx := plusCtx) (name := "succ") (f := Nat.succ)
      rfl hsucc)

def plusLoopInductionProgram (x y : Nat) : Refinement plusCtx [] [] (plusLoopStatement x y) :=
  Pr.Induction.natInductionWithPredicate "succ" plusSuccSpec (plusLoopStatement x y)
    (plusLoopPredicate x) "n" "n_next" y (by decide) (by rfl)
    (by
      change ¬ ("n_next" ∈ (["n", "n"] : List String))
      decide)
    (plusLoopStatement_eq x y)

theorem plusLoopProvable (x y : Nat) : Pr.Provable plusCtx [] [] (plusLoopStatement x y) := by
  applyRefinement (plusLoopInductionProgram x y)
  · cases plusLoopBaseProvable x with | ofProof proof => exact proof
  · cases plusLoopStepProvable x with | ofProof proof => exact proof

example : Pr.Provable plusCtx [] [] (plusLoopStatement 7 100) := plusLoopProvable 7 100

end Zag.Test.Autocorres.Examples
