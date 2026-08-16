import Lib.Peano.Defs
import Zag.EvalState
import Meta.UnifyType

/-!
Gauss's sum as a block program.

This is the SSA loop that used to live in `Test/Gauss/SSA.lean`, written against the block IR now
that it is part of Zag. The loop carried its two live variables in a `Ty.struct` state, packed by
`mkStruct` and read back by `structProj`, because `recurse` threaded exactly one state value.
A block takes named parameters, so `loop(i, acc)` needs no product type at all -- which is why
dropping `struct` from `Ty` costs this program nothing.

The back edge `yield nextI, nextAcc` is now the self-call `call loop [...]`, and it sits inside
the lazy `ite` operand so the loop actually terminates.
-/

namespace Zag.Test.Gauss

open Zag Zag.Lib.Peano

abbrev gaussBlocks : BlockCtx.Raw natCtx :=
  blocks% [
    gauss(n : Nat) : Nat {
      ret call loop [n, nat(0)]
    },
    loop(i : Nat, acc : Nat) : Nat {
      cond := primGt i nat(0);
      ret if cond { call loop [op "sub"[i, nat(1)], op "add"[acc, i]] } else { acc }
    }
  ]

abbrev gaussCtx : Ctx where
  primCtx := natCtx
  opCtx := natOpCtx
  blockCtx := ⟨gaussBlocks, by
    refine ⟨by decide, ?_⟩
    simp [gaussBlocks, Block.callNames, Term.callNames, Term.nat, Term.ite]⟩

instance : Peano.Model gaussCtx where
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

/-! ### the program computes Gauss's sum -/

def sumTo : Nat → Nat
| 0 => 0
| n + 1 => sumTo n + (n + 1)

def runGauss (n : Nat) : Option Nat :=
  (EvalState.run gaussCtx 2000 (EvalState.start [] (.call "gauss" [Term.nat n]))).result?.bind
    Val.asNat?

/-- info: [some 0, some 1, some 3, some 6, some 10, some 15, some 21, some 28] -/
#guard_msgs in
#eval (List.range 8).map runGauss

#guard (List.range 25).all (fun n => runGauss n == some (sumTo n))

/- the closed form `n * (n + 1) / 2` the original statement was compared against -/
#guard (List.range 25).all (fun n => runGauss n == some (n * (n + 1) / 2))

/-! ### typing -/

def gaussBlock : Block natCtx := gaussBlocks[0].2
def loopBlock : Block natCtx := gaussBlocks[1].2

theorem loop_hasType {varCtx : VarCtx} {i acc : Term natCtx}
    (hi : Term.hasType gaussCtx varCtx i Peano.NatTy)
    (hacc : Term.hasType gaussCtx varCtx acc Peano.NatTy) :
    Term.hasType gaussCtx varCtx (.call "loop" [i, acc]) Peano.NatTy := by
  have hget : gaussCtx.blockCtx.get? "loop" = some loopBlock := rfl
  refine Term.hasType.call hget rfl ?_
  intro idx
  match idx with
  | ⟨0, _⟩ => simpa [loopBlock] using hi
  | ⟨1, _⟩ => simpa [loopBlock] using hacc
  | ⟨n + 2, h⟩ =>
      have : False := by
        change n + 2 < 2 at h
        omega
      contradiction

theorem loopBlock_wellTyped : Block.WellTyped gaussCtx loopBlock := by
  typecheck_block

theorem gaussBlock_wellTyped : Block.WellTyped gaussCtx gaussBlock := by
  typecheck_block

theorem gaussCtx_wellTyped : Ctx.WellTyped gaussCtx := by
  typecheck_ctx

end Zag.Test.Gauss
