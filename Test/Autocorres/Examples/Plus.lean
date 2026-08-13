import Test.Autocorres.Examples.Correctness

namespace Zag.Test.Autocorres.Examples

open Zag Zag.Lib.PeanoHeap

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

theorem plusBlocksValid : BlockCtx.Valid plusBlocks := by
  constructor
  case left => decide
  case right =>
    set_option linter.unusedSimpArgs false in
      simp [plusBlocks, Block.callNames, Term.callNames, Term.nat, Term.bool, Term.ite,
        termHeap, termPtr, termArray]

abbrev plusCtx : Ctx := mkCtx plusBlocks plusBlocksValid

theorem plusCtx_wellTyped : Ctx.WellTyped plusCtx := by
  typecheck_ctx

theorem plus_eval (x y : Nat) :
    Term.eval plusCtx [] (.call "plus" [Term.nat x, Term.nat y]) = some (Val.nat (x + y)) := by
  have hblock : plusCtx.blockCtx.get? "plus" = some plusBlocks[0].2 := rfl
  have hargs : Term.evalListOutcome plusCtx [] [Term.nat x, Term.nat y] =
      some (.ok [Val.nat x, Val.nat y]) := evalListOutcome_two_nat [] x y
  have hlen : [Val.nat (primCtx := heapCtx) x, Val.nat y].length = plusBlocks[0].2.params.length :=
    rfl
  have hx : Term.eval plusCtx (plusBlocks[0].2.entryEnv [Val.nat x, Val.nat y]) (.var "x") =
      some (Val.nat x) := by
    simp [Term.eval, Term.evalGo_var, Block.entryEnv, Scope.get?]
  have hy : Term.eval plusCtx (plusBlocks[0].2.entryEnv [Val.nat x, Val.nat y]) (.var "y") =
      some (Val.nat y) := by
    simp [Term.eval, Term.evalGo_var, Block.entryEnv, Scope.get?]
  have hresult : Term.eval plusCtx (plusBlocks[0].2.entryEnv [Val.nat x, Val.nat y])
      (.op "add" [.var "x", .var "y"]) = some (Val.nat (x + y)) :=
    eval_nat_binary_op (ctx := plusCtx) (name := "add") (f := Nat.add) rfl hx hy
  have hbody : Term.evalBlock plusCtx "plus" (plusBlocks[0].2.entryEnv [Val.nat x, Val.nat y])
      plusBlocks[0].2 = some (.ok (Val.nat (x + y))) :=
    evalBlock_noInstr_eval hresult
  exact eval_call_ok hblock hargs hlen hbody

def plusLoopBlock : Block heapCtx := plusBlocks[1].2

theorem plusLoopBlock_eval (x y : Nat) :
    Term.evalBlock plusCtx "plusLoop" (plusLoopBlock.entryEnv [Val.nat x, Val.nat y])
      plusLoopBlock = some (.ok (Val.nat (x + y))) := by
  induction y generalizing x with
  | zero =>
      simpa using (by
        apply evalBlock_oneInstr_eval (instrValue := Val.bool true)
        case hinstr =>
          have hy : Term.eval plusCtx (plusLoopBlock.entryEnv [Val.nat x, Val.nat 0]) (.var "y") =
              some (Val.nat 0) := by
            simp [Term.eval, Term.evalGo_var, plusLoopBlock, Block.entryEnv, Scope.get?]
          have hzero : Term.eval plusCtx (plusLoopBlock.entryEnv [Val.nat x, Val.nat 0])
              (Term.nat 0) = some (Val.nat 0) := by
            simp [Term.eval, Term.nat]
          simpa using eval_nat_eq_op (ctx := plusCtx) hy hzero
        case hresult =>
          have hdone : Term.eval plusCtx
              (plusLoopBlock.entryEnv [Val.nat x, Val.nat 0] ++ [("done", Val.bool true)])
              (.var "done") = some (Val.bool true) := by
            simp [Term.eval, Term.evalGo_var, plusLoopBlock, Block.entryEnv, Scope.get?]
          rw [eval_ite_true hdone]
          simp [Term.eval, Term.evalGo_var, plusLoopBlock, Block.entryEnv, Scope.get?])
  | succ y ih =>
      apply evalBlock_oneInstr_eval (instrValue := Val.bool false)
      case hinstr =>
        have hy : Term.eval plusCtx (plusLoopBlock.entryEnv [Val.nat x, Val.nat (y + 1)])
            (.var "y") = some (Val.nat (y + 1)) := by
          simp [Term.eval, Term.evalGo_var, plusLoopBlock, Block.entryEnv, Scope.get?]
        have hzero : Term.eval plusCtx (plusLoopBlock.entryEnv [Val.nat x, Val.nat (y + 1)])
            (Term.nat 0) = some (Val.nat 0) := by
          simp [Term.eval, Term.nat]
        simpa using eval_nat_eq_op (ctx := plusCtx) hy hzero
      case hresult =>
        have hdone : Term.eval plusCtx
            (plusLoopBlock.entryEnv [Val.nat x, Val.nat (y + 1)] ++ [("done", Val.bool false)])
            (.var "done") = some (Val.bool false) := by
          simp [Term.eval, Term.evalGo_var, plusLoopBlock, Block.entryEnv, Scope.get?]
        rw [eval_ite_false hdone]
        have hx : Term.eval plusCtx
            (plusLoopBlock.entryEnv [Val.nat x, Val.nat (y + 1)] ++ [("done", Val.bool false)])
            (.var "x") = some (Val.nat x) := by
          simp [Term.eval, Term.evalGo_var, plusLoopBlock, Block.entryEnv, Scope.get?]
        have hy : Term.eval plusCtx
            (plusLoopBlock.entryEnv [Val.nat x, Val.nat (y + 1)] ++ [("done", Val.bool false)])
            (.var "y") = some (Val.nat (y + 1)) := by
          simp [Term.eval, Term.evalGo_var, plusLoopBlock, Block.entryEnv, Scope.get?]
        have hone : Term.eval plusCtx
            (plusLoopBlock.entryEnv [Val.nat x, Val.nat (y + 1)] ++ [("done", Val.bool false)])
            (Term.nat 1) = some (Val.nat 1) := by
          simp [Term.eval, Term.nat]
        have hnextX : Term.eval plusCtx
            (plusLoopBlock.entryEnv [Val.nat x, Val.nat (y + 1)] ++ [("done", Val.bool false)])
            (.op "add" [.var "x", Term.nat 1]) = some (Val.nat (x + 1)) :=
          eval_nat_binary_op (ctx := plusCtx) (name := "add") (f := Nat.add) rfl hx hone
        have hnextY : Term.eval plusCtx
            (plusLoopBlock.entryEnv [Val.nat x, Val.nat (y + 1)] ++ [("done", Val.bool false)])
            (.op "sub" [.var "y", Term.nat 1]) = some (Val.nat y) := by
          simpa using eval_nat_binary_op (ctx := plusCtx) (name := "sub") (f := Nat.sub) rfl hy hone
        have hargs : Term.evalListOutcome plusCtx
            (plusLoopBlock.entryEnv [Val.nat x, Val.nat (y + 1)] ++ [("done", Val.bool false)])
            [.op "add" [.var "x", Term.nat 1], .op "sub" [.var "y", Term.nat 1]] =
            some (.ok [Val.nat (x + 1), Val.nat y]) :=
          evalListOutcome_cons_ok (evalOutcome_ok_of_eval hnextX)
            (evalListOutcome_cons_ok (evalOutcome_ok_of_eval hnextY) (evalListOutcome_nil _))
        have hblock : plusCtx.blockCtx.get? "plusLoop" = some plusLoopBlock := rfl
        have hlen : [Val.nat (primCtx := heapCtx) (x + 1), Val.nat y].length =
            plusLoopBlock.params.length := rfl
        have hcall := eval_call_ok hblock hargs hlen (ih (x + 1))
        simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hcall

theorem plusLoop_eval (x y : Nat) :
    Term.eval plusCtx [] (.call "plusLoop" [Term.nat x, Term.nat y]) =
      some (Val.nat (x + y)) := by
  have hblock : plusCtx.blockCtx.get? "plusLoop" = some plusLoopBlock := rfl
  have hargs : Term.evalListOutcome plusCtx [] [Term.nat x, Term.nat y] =
      some (.ok [Val.nat x, Val.nat y]) := evalListOutcome_two_nat [] x y
  have hlen : [Val.nat (primCtx := heapCtx) x, Val.nat y].length = plusLoopBlock.params.length :=
    rfl
  exact eval_call_ok hblock hargs hlen (plusLoopBlock_eval x y)

end Zag.Test.Autocorres.Examples
