import Meta.UnifyType
import Meta.Eval.VC
import Lib.PeanoHeap

/-!
Regression tests for the ambient Peano heap. Heap state is supplied only to `StateM`; block
parameters and results are ordinary object-language payloads.
-/

namespace Zag.Test.Heap

open Zag Zag.Lib.PeanoHeap

abbrev heapBlocks : BlockCtx.Raw heapCtx :=
  blocks% [
    storeThenRead(ptr : Ptr, value : Nat) : Nat {
      ignored := op "store"[ptr, value];
      ret op "load"[ptr]
    },
    allocStoreRead(size : Nat, value : Nat) : Nat {
      ptr := op "allocPtr"[size];
      ignored := op "store"[ptr, value];
      ret op "load"[ptr]
    }
  ]

theorem heapBlocksValid : BlockCtx.Valid heapBlocks := by
  valid_blocks [heapBlocks]

abbrev heapProgram : Ctx := mkCtx heapBlocks heapBlocksValid

theorem heapProgram_wellTyped : Ctx.WellTyped heapProgram := by
  typecheck_ctx

example : heapProgram.opCtx.outTy? "load" [PtrTy] = some NatTy := by rfl
example : heapProgram.opCtx.outTy? "store" [PtrTy, NatTy] = some UnitTy := by rfl
example : heapProgram.opCtx.outTy? "allocPtr" [NatTy] = some PtrTy := by rfl
example : heapProgram.opCtx.outTy? "load" [PtrTy, NatTy] = none := by rfl
example : heapProgram.opCtx.outTy? "store" [PtrTy] = none := by rfl

/-- The machine sequences allocation, write, and read through `OptionT.bind`. -/
private def allocStoreReadRun : Option (Val heapCtx) × Heap :=
  (Machine.evalFuel heapProgram 100 []
    (.call "allocStoreRead" [.nat 2, .nat 41])).run Heap.empty

theorem allocStoreReadRun_eq :
    (match allocStoreReadRun with
      | (some value, heap) => (value.asNat?, heap)
      | (none, heap) => (none, heap)) =
    (some 41, Heap.write (Heap.allocHeap Heap.empty 2) (Heap.allocPtr Heap.empty) 41) := by
  native_decide

private theorem allocStoreReadRun_raw :
    allocStoreReadRun =
      (some (Val.nat 41),
        Heap.write (Heap.allocHeap Heap.empty 2) (Heap.allocPtr Heap.empty) 41) := by
  have h := allocStoreReadRun_eq
  cases hrun : allocStoreReadRun with
  | mk value? heap =>
      cases value? with
      | none => simp [hrun] at h
      | some value =>
          simp [hrun] at h
          have hvalue : value.asNat? = some 41 := h.1
          have hheap : heap =
              Heap.write (Heap.allocHeap Heap.empty 2) (Heap.allocPtr Heap.empty) 41 := h.2
          rw [Val.eq_nat_of_asNat? hvalue, hheap]

/-- The bounded execution certifies an effectful surface call, including its final heap. -/
theorem allocStoreRead_evaluates :
    EvalTriple.State.EvaluatesCall heapCtx heapOpCtx
      (checkedBlocks heapBlocks heapBlocksValid)
      "allocStoreRead" [.nat 2, .nat 41] Heap.empty (Val.nat 41)
      (Heap.write (Heap.allocHeap Heap.empty 2) (Heap.allocPtr Heap.empty) 41) := by
  apply EvalTriple.State.EvaluatesFrom.of_evalConfigFuel
  change allocStoreReadRun = _
  exact allocStoreReadRun_raw

/-! ### Non-local exits -/

private abbrev exitBlocks : BlockCtx.Raw heapCtx :=
  blocks% [
    target() : Nat {
      ret nat(0)
    },
    matching() : Nat {
      ptr := op "allocPtr"[nat(1)];
      before := op "store"[ptr, nat(41)];
      escaped := exit matching (op "load"[ptr]);
      after := op "store"[ptr, nat(99)];
      ret nat(0)
    },
    escaping() : Nat {
      ptr := op "allocPtr"[nat(1)];
      before := op "store"[ptr, nat(7)];
      escaped := exit target (op "load"[ptr]);
      after := op "store"[ptr, nat(99)];
      ret nat(0)
    }
  ]

private theorem exitBlocksValid : BlockCtx.Valid exitBlocks := by
  valid_blocks [exitBlocks]

private abbrev exitProgram : Ctx := mkCtx exitBlocks exitBlocksValid

private def observeHeapRun (run : Option (Val heapCtx) × Heap) : Option Nat × Heap :=
  match run with
  | (some value, heap) => (value.asNat?, heap)
  | (none, heap) => (none, heap)

private abbrev matchingFinalHeap : Heap :=
  Heap.write (Heap.allocHeap Heap.empty 1) (Heap.allocPtr Heap.empty) 41

private abbrev escapingFinalHeap : Heap :=
  Heap.write (Heap.allocHeap Heap.empty 1) (Heap.allocPtr Heap.empty) 7

/-- A matching exit returns its evaluated payload and skips both the later store and block result. -/
theorem matchingExit_machine_run :
    observeHeapRun
      ((Machine.evalFuel exitProgram 100 [] (.call "matching" [])).run Heap.empty) =
      (some 41, matchingFinalHeap) := by
  native_decide

/-- A nonmatching exit reaches the public boundary as failure after retaining prior heap effects. -/
theorem nonmatchingExit_machine_failure_preserves_heap :
    observeHeapRun
      ((Machine.evalFuel exitProgram 100 [] (.call "escaping" [])).run Heap.empty) =
      (none, escapingFinalHeap) := by
  native_decide

/-- The same state transition stated without exposing any machine fuel. -/
private def heapSequence : StateM Heap Nat := do
  let ptr ← alloc 2
  store ptr 41
  load ptr

@[zspec] theorem heapSequence_spec :
    Std.Do.Triple heapSequence
      (fun heap => ULift.up (heap = Heap.empty))
      (Std.Do.PostCond.noThrow (ps := .arg Heap .pure) fun result finalHeap =>
        ULift.up (result = 41 ∧
          finalHeap = Heap.write (Heap.allocHeap Heap.empty 2) (Heap.allocPtr Heap.empty) 41)) := by
  zvcgen [heapSequence, alloc, store, load, Heap.read, Heap.write, Heap.allocPtr,
    Heap.allocHeap, Heap.zeroCells, Heap.empty]

end Zag.Test.Heap
