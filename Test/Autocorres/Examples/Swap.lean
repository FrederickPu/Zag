import Test.Autocorres.Examples.Common

/-!
Upstream Isabelle theory:
[`Swap.thy`](https://github.com/seL4/l4v/blob/master/tools/autocorres/tests/examples/Swap.thy).

Sep-logic meaning of the model is `swap_eval` (`↦`). The machine spine is still exact-state
(packaged monadic via `evaluatesCall_of_hprop` when the spine is available).
-/

namespace Zag.Test.Autocorres.Examples

open Zag Zag.Lib.PeanoHeap
open HeapAlgebra
open HeapAlgebra.Peano (OwnedPtr Region)
open HProp
open scoped HProp
open scoped Std.Do

abbrev swapBlocks : BlockCtx.Raw heapCtx :=
  blocks% [
    swap(a : Ptr, b : Ptr) : Unit {
      av := op "load"[a];
      bv := op "load"[b];
      storedA := op "store"[a, bv];
      ret op "store"[b, av]
    }
  ]

theorem swapBlocksValid : BlockCtx.Valid swapBlocks := by
  valid_blocks [swapBlocks]

abbrev swapCtx : Ctx := mkCtx swapBlocks swapBlocksValid

theorem swapCtx_wellTyped : Ctx.WellTyped swapCtx := by
  typecheck_ctx

private abbrev swapStateCtx : Ctx := heapStateCtx swapBlocks swapBlocksValid

def swapSpec (heap : Heap) (a b : Ptr) : Heap :=
  Heap.write (Heap.write heap a (Heap.read heap b)) b (Heap.read heap a)

theorem heap_read_write_same (heap : Heap) (ptr : Ptr) (value : Nat) :
    Heap.read (Heap.write heap ptr value) ptr = value := by
  simp [Heap.read, Heap.write]

theorem heap_read_write_other (heap : Heap) (written read : Ptr) (value : Nat)
    (h : read ≠ written) :
    Heap.read (Heap.write heap written value) read = Heap.read heap read := by
  rcases written with ⟨written⟩
  rcases read with ⟨read⟩
  have haddr : read ≠ written := by
    intro heq
    apply h
    cases heq
    rfl
  simp [Heap.read, Heap.write, Ne.symm haddr]

theorem swapSpec_correct (heap : Heap) (a b : Ptr) :
    Heap.read (swapSpec heap a b) a = Heap.read heap b ∧
      Heap.read (swapSpec heap a b) b = Heap.read heap a := by
  by_cases h : a = b
  · subst b
    simp [swapSpec, heap_read_write_same]
  · constructor
    · simp [swapSpec, heap_read_write_same, heap_read_write_other, h]
    · simp [swapSpec, heap_read_write_same]

/-- Sep-logic meaning of `swapSpec` when `a ≠ b`. -/
theorem swap_sep_correct (heap : Heap) (a b : Ptr) (va vb : Nat)
    (hne : a ≠ b)
    (hp : ((a ↦ va) ∗ (b ↦ vb)).holds heap) :
    (((a ↦ vb) ∗ (b ↦ va)).holds (swapSpec heap a b)) := by
  have ha : Heap.read heap a = va := (cell_pointsTo_holds a va heap).1 hp.2.1
  have hb : Heap.read heap b = vb := (cell_pointsTo_holds b vb heap).1 hp.2.2
  constructor
  · exact hp.1
  · constructor
    · exact (cell_pointsTo_holds a vb _).2 (by
        simp only [swapSpec]
        rw [heap_read_write_other _ b a _ hne, heap_read_write_same, hb])
    · exact (cell_pointsTo_holds b va _).2 (by
        simp only [swapSpec, heap_read_write_same, ha])

/--
Model-level SL claim (machine spine still open for full monadic lift):

```
{ a ↦ va ∗ b ↦ vb }  (a ≠ b)
  swapSpec
{ a ↦ vb ∗ b ↦ va }
```
-/
theorem swap_eval (a b : Ptr) (va vb : Nat) (hne : a ≠ b)
    (heap : Heap) (hp : ((a ↦ va) ∗ (b ↦ vb)).holds heap) :
    ((a ↦ vb) ∗ (b ↦ va)).holds (swapSpec heap a b) :=
  swap_sep_correct heap a b va vb hne hp

theorem swap_run :
    (match (Machine.evalFuel swapCtx 50 []
        (.call "swap" [termPtr 1, termPtr 2])).run
          { next := 3, cells := [(1, 10), (2, 20)] } with
      | (some _, final) => some final
      | (none, _) => none) =
    some (swapSpec { next := 3, cells := [(1, 10), (2, 20)] } ⟨1⟩ ⟨2⟩) := by
  native_decide

end Zag.Test.Autocorres.Examples
