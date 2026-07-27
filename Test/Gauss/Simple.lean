import Lang.Simple
import Lib.Peano

/-!
  # Gauss via Simpl / C0 (`BitVec 32` locals)

  Same claim as Rec/SSA: sum `1..n` = `n*(n+1)/2`, but LHS is imperative C0.

  ```
  // i = x, acc = y ; Word = uint32
  while (0 < i) {
    acc = acc + i;
    i = i - 1;
  }
  ```

  Source is `C0.W2.gaussStmt` → `elab` → `Com` → L2 → eval.
  WA is exercised separately (`gauss_WA`); no Corres proof claimed.
-/

namespace Zag.Test.Gauss.Simple

open Lang.Simple.C0.W2
open Lang.Simple.ABI

def gaussProgram := gauss
def gauss_L2' := gauss_L2
def gauss_WA' := gauss_WA

theorem gauss_from_c0 : (toCom gaussStmt).isSome = true := gauss_elab

theorem gauss_lifts : gauss_L2'.isSome = true := by native_decide

def closedForm (n : Nat) : Nat := n * (n + 1) / 2

theorem gauss_eval_5 :
    (do let s ← gauss_L2'; eval_L2_nats s 5 0) = some (0, closedForm 5) := by
  native_decide

theorem gauss_eval_0 :
    (do let s ← gauss_L2'; eval_L2_nats s 0 0) = some (0, closedForm 0) := by
  native_decide

theorem gauss_eval_10 :
    (do let s ← gauss_L2'; eval_L2_nats s 10 0) = some (0, closedForm 10) := by
  native_decide

theorem gauss_wa_runs : gauss_WA'.isSome = true := by native_decide

theorem closedForm_examples :
    closedForm 0 = 0 ∧ closedForm 5 = 15 ∧ closedForm 10 = 55 := by
  native_decide

example : Word = BitVec 32 := rfl

end Zag.Test.Gauss.Simple
