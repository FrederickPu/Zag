import Lib.Peano.Defs
import Zag.Machine
import Meta.UnifyType

/-!
Blocks are where Zag gets recursion: a block may call itself.

Note the placement of the recursive call. Instructions are evaluated eagerly, in order, so a
`call` in instruction position would recurse forever. An op instead chooses which of its
operands to evaluate (`Op.Body.next`), so putting the recursive call inside `ite`'s else operand
is what makes the recursion terminate -- that choice is the whole of Zag's control flow.
-/

namespace Zag.Test.Block

open Zag Zag.Lib.Peano

abbrev sumToBlocks : BlockCtx.Raw natCtx :=
  blocks% [
    sumTo(n : Nat) : Nat {
      isZero := primEq n nat(0);
      ret if isZero { nat(0) } else { op "add"[call sumTo [op "sub"[n, nat(1)]], n] }
    }
  ]

abbrev sumToCtx : Ctx where
  primCtx := natCtx
  opCtx := natOpCtx
  blockCtx := ⟨sumToBlocks, by
    refine ⟨by decide, ?_⟩
    simp [sumToBlocks, Block.callNames, Term.callNames, Term.nat, Term.ite]⟩

instance : Peano.Model sumToCtx where
  natType := by rfl
  boolType := by rfl
  eqOp := by rfl
  ltOp := by rfl
  gtOp := by rfl
  iteOp := by rfl
  addOp := by rfl
  subOp := by rfl
  mulOp := by rfl
  divOp := by rfl
  succOp := by rfl

def sumToBlock : Block natCtx := sumToBlocks[0].2

/- A recursive call is typed against the block's *declared* `outTy`, so `sumTo` is typeable
  without inferring its own result type. -/
theorem sumTo_hasType {varCtx : VarCtx} {arg : Term natCtx}
    (harg : Term.hasType sumToCtx varCtx arg Peano.NatTy) :
    Term.hasType sumToCtx varCtx (.call "sumTo" [arg]) Peano.NatTy := by
  have hget : sumToCtx.blockCtx.get? "sumTo" = some sumToBlock := rfl
  refine Term.hasType.call hget rfl ?_
  intro idx
  match idx with
  | ⟨0, _⟩ => simpa [sumToBlock] using harg
  | ⟨n + 1, h⟩ =>
      have : False := by
        change n + 1 < 1 at h
        omega
      contradiction

theorem sumToBlock_wellTyped : Block.WellTyped sumToCtx sumToBlock := by
  typecheck_block

theorem sumToCtx_wellTyped : Ctx.WellTyped sumToCtx := by
  typecheck_ctx

def runSumTo (n : Nat) : Option Nat :=
  (Machine.evalFuel sumToCtx 1000 [] (.call "sumTo" [Term.nat n])).run.bind Val.asNat?

/-- info: some 10 -/
#guard_msgs in
#eval runSumTo 4

/-- info: some 55 -/
#guard_msgs in
#eval runSumTo 10

end Zag.Test.Block
