import Lang.Simple.ABI
import Lang.Simple.Lift.L2
import Lang.Simple.C0

/-!
  Word2 packing/eval facts for the C0.W2 locals convention.
-/

namespace Lang.Simple.Word2

open Zag
open Zag.Lang.SSA
open Lang.Simple
open Lang.Simple.ABI
open Lang.Simple.Lift.L2
open Lang.Simple.C0.W2 (ctx locals)

def envOfWords (x y : Word) : List (Val ctx.primCtx) :=
  [State.wordVal x, State.wordVal y]

def evalPackNats (x y : Nat) : Option (Nat × Nat) := do
  let v ← evalSSAWithLocals? (sc := ctx) locals
    (envOfWords (Word.ofNat x) (Word.ofNat y))
    (SSAExpr.ret locals.packCurrent)
  let tys := [WordTy, WordTy]
  let raw ← v.as? (.struct tys)
  let fields := cast (Ty.type.eq_5 ctx.primCtx tys) raw
  some (Word.toNat (State.toWord (fields ⟨0, by decide⟩)),
        Word.toNat (State.toWord (fields ⟨1, by decide⟩)))

theorem fromCom_skip_w2 :
    fromCom? (sc := ctx) (proc := Empty) (fault := Unit) locals Com.Skip =
      some (SSAExpr.ret locals.packCurrent) :=
  rfl

/-- Skip lift + packCurrent eval for Word2 (concrete, decidable). -/
theorem eval_pack_1_2 : evalPackNats 1 2 = some (1, 2) := by native_decide
theorem eval_pack_0_0 : evalPackNats 0 0 = some (0, 0) := by native_decide
theorem eval_pack_7_3 : evalPackNats 7 3 = some (7, 3) := by native_decide

end Lang.Simple.Word2
