import Test.Autocorres.Examples.QuicksortModel
import Test.Autocorres.Examples.QuicksortProgram

namespace Zag.Test.Autocorres.Examples

open Zag Zag.Lib.PeanoHeap
open HeapAlgebra
open HeapAlgebra.Peano (OwnedPtr Region)
open HProp
open scoped HProp
open scoped Std.Do

local macro "quicksort_state_simp" extras:Lean.Parser.Tactic.simpLemma,* : tactic => `(tactic|
  set_option linter.unusedSimpArgs false in
    simp [quicksortCtx, mkCtx, quicksortBlocks, checkedBlocks,
      Machine.step, Machine.evalTerm, Machine.applyValue,
      Machine.driveSelectedOp, Machine.ofOption, Machine.evalTermImmediate,
      Machine.applyValueImmediate, Machine.resumeFrame, Machine.enterBlock,
      Machine.enterInstrs, Machine.driveOp, Machine.start,
      loadOp, storeOp, ptrAddOp, binaryNatBoolOp, Op.compare, Op.ite, Op.effectful,
      Op.Body.collect, Op.Arg.ofTerms, Op.Arg.ofVals, Op.ofVals,
      Op.Body.eager, Op.fixed, Op.natBinary, Block.entryEnv, Scope.get?, Term.nat,
      Term.ite, termPtr, valPtr, valUnit, asPtr?, $extras,*])

set_option maxHeartbeats 1000000 in
theorem partitionRotate_evaluates {heap : Heap} {base : Ptr} {n pivotIdx i : Nat}
    (_hpivotIdx : pivotIdx < i) (_hi : i < n)
    (hnext : EvalTriple.State.EvaluatesCallValues heapCtx heapOpCtx quicksortCtx.blockCtx
      "partitionLoop" [valPtr base, Val.nat n, Val.nat (pivotIdx + 1), Val.nat (i + 1)]
      (partitionHeapRotate heap base pivotIdx i) value final) :
    EvalTriple.State.EvaluatesCallValues heapCtx heapOpCtx quicksortCtx.blockCtx
      "partitionRotate"
      [valPtr base, Val.nat n, Val.nat pivotIdx, Val.nat i,
        Val.nat (Heap.read heap ⟨base.addr + pivotIdx⟩),
        Val.nat (Heap.read heap ⟨base.addr + i⟩)] heap value final := by
  let pivotPtr : Ptr := ⟨base.addr + pivotIdx⟩
  let currentPtr : Ptr := ⟨base.addr + i⟩
  let pivot := Heap.read heap pivotPtr
  let current := Heap.read heap currentPtr
  let movedCurrent := Heap.write heap pivotPtr current
  let nextPivotPtr : Ptr := ⟨base.addr + pivotIdx + 1⟩
  let shifted := Heap.read movedCurrent nextPivotPtr
  let movedShifted := Heap.write movedCurrent currentPtr shifted
  let rotated := Heap.write movedShifted nextPivotPtr pivot
  have hload : heapOpCtx.get? "load" = some loadOp := by simp
  have hstore : heapOpCtx.get? "store" = some storeOp := by simp
  have hptrAdd : heapOpCtx.get? "ptrAdd" = some ptrAddOp := by rfl
  have hadd : heapOpCtx.get? "add" = some (Op.natBinary Nat.add) := by rfl
  intro env stack
  refine ⟨_, _, by rfl, by rfl, ?_⟩
  change EvalTriple.State.EvaluatesFrom heapCtx heapOpCtx quicksortCtx.blockCtx _ heap value final stack
  repeat
    first
    | apply EvalTriple.State.EvaluatesFrom.step (middle := movedCurrent)
      · change Id.run ((Machine.step
          (Machine.stateCtx heapCtx heapOpCtx quicksortCtx.blockCtx) _).run heap) = _
        simpa [movedCurrent, pivotPtr, current] using
          storeOp_step quicksortCtx.blockCtx _ _ heap pivotPtr current
    | apply EvalTriple.State.EvaluatesFrom.step (middle := movedShifted)
      · change Id.run ((Machine.step
          (Machine.stateCtx heapCtx heapOpCtx quicksortCtx.blockCtx) _).run movedCurrent) = _
        simpa [movedShifted, currentPtr, shifted] using
          storeOp_step quicksortCtx.blockCtx _ _ movedCurrent currentPtr shifted
    | apply EvalTriple.State.EvaluatesFrom.step (middle := rotated)
      · change Id.run ((Machine.step
          (Machine.stateCtx heapCtx heapOpCtx quicksortCtx.blockCtx) _).run movedShifted) = _
        simpa [rotated, nextPivotPtr, pivot] using
          storeOp_step quicksortCtx.blockCtx _ _ movedShifted nextPivotPtr pivot
    | apply EvalTriple.State.EvaluatesFrom.step (middle := movedCurrent)
      · change Id.run ((Machine.step
          (Machine.stateCtx heapCtx heapOpCtx quicksortCtx.blockCtx) _).run movedCurrent) = _
        simpa [nextPivotPtr, shifted] using
          loadOp_step quicksortCtx.blockCtx _ _ movedCurrent nextPivotPtr
    | apply EvalTriple.State.EvaluatesFrom.call_then hnext
      intro scope
      exact EvalTriple.State.EvaluatesFrom.return_to_call
    | apply EvalTriple.State.EvaluatesFrom.step (middle := heap)
      · quicksort_state_simp hload, hstore, hptrAdd, hadd, pivotPtr, currentPtr, pivot, current,
          movedCurrent, nextPivotPtr, shifted, movedShifted, rotated
        rfl
    | apply EvalTriple.State.EvaluatesFrom.step (middle := movedCurrent)
      · quicksort_state_simp hload, hstore, hptrAdd, hadd, pivotPtr, currentPtr, pivot, current,
          movedCurrent, nextPivotPtr, shifted, movedShifted, rotated
        rfl
    | apply EvalTriple.State.EvaluatesFrom.step (middle := movedShifted)
      · quicksort_state_simp hload, hstore, hptrAdd, hadd, pivotPtr, currentPtr, pivot, current,
          movedCurrent, nextPivotPtr, shifted, movedShifted, rotated
        rfl
    | apply EvalTriple.State.EvaluatesFrom.step (middle := rotated)
      · quicksort_state_simp hload, hstore, hptrAdd, hadd, pivotPtr, currentPtr, pivot, current,
          movedCurrent, nextPivotPtr, shifted, movedShifted, rotated
        rfl

set_option maxRecDepth 10000 in
theorem partitionHeapLoopSpec_evaluates (heap : Heap) (base : Ptr)
    (n pivotIdx i : Nat) (hpivotIdx : pivotIdx < i) (hi : i ≤ n) :
    EvalTriple.State.EvaluatesCallValues heapCtx heapOpCtx quicksortCtx.blockCtx
      "partitionLoop" [valPtr base, Val.nat n, Val.nat pivotIdx, Val.nat i] heap
      (Val.nat (partitionHeapLoopSpec heap base n pivotIdx i).2)
      (partitionHeapLoopSpec heap base n pivotIdx i).1 := by
  induction hmeasure : n - i using Nat.strongRecOn generalizing heap pivotIdx i with
  | ind measure ih =>
      rw [partitionHeapLoopSpec]
      split <;> rename_i hdone
      · have hle : heapOpCtx.get? "le" =
            some (binaryNatBoolOp fun a b => decide (a ≤ b)) := by rfl
        have hite : heapOpCtx.get? "ite" = some Op.ite := by rfl
        intro env stack
        refine ⟨_, _, by rfl, by rfl, ?_⟩
        repeat
          first
          | exact EvalTriple.State.EvaluatesFrom.return_to_call
          | exact EvalTriple.State.EvaluatesFrom.done
          | apply EvalTriple.State.EvaluatesFrom.step (middle := heap)
            · quicksort_state_simp hle, hite, hdone
              rfl
      · have hin : i < n := by omega
        by_cases hlt : Heap.read heap ⟨base.addr + i⟩ <
            Heap.read heap ⟨base.addr + pivotIdx⟩
        · rw [if_pos hlt]
          have hrec := ih (n - (i + 1)) (by omega)
            (partitionHeapRotate heap base pivotIdx i) (pivotIdx + 1) (i + 1)
            (by omega) (by omega) rfl
          have hrotate := partitionRotate_evaluates (by omega) hin hrec
          have hload : heapOpCtx.get? "load" = some loadOp := by simp
          have hptrAdd : heapOpCtx.get? "ptrAdd" = some ptrAddOp := by rfl
          have hltOp : heapOpCtx.get? "lt" = some (Op.compare Val.primLt?) := by rfl
          have hite : heapOpCtx.get? "ite" = some Op.ite := by rfl
          have hstep : EvalTriple.State.EvaluatesCallValues heapCtx heapOpCtx
              quicksortCtx.blockCtx "partitionLoopStep"
              [valPtr base, Val.nat n, Val.nat pivotIdx, Val.nat i] heap
              (Val.nat (partitionHeapLoopSpec
                (partitionHeapRotate heap base pivotIdx i) base n
                (pivotIdx + 1) (i + 1)).2)
              (partitionHeapLoopSpec (partitionHeapRotate heap base pivotIdx i)
                base n (pivotIdx + 1) (i + 1)).1 := by
            intro env stack
            refine ⟨_, _, by rfl, by rfl, ?_⟩
            repeat
              first
              | apply EvalTriple.State.EvaluatesFrom.step (middle := heap)
                · change Id.run ((Machine.step
                    (Machine.stateCtx heapCtx heapOpCtx quicksortCtx.blockCtx) _).run heap) = _
                  simpa using loadOp_step quicksortCtx.blockCtx _ _ heap
                    ⟨base.addr + pivotIdx⟩
              | apply EvalTriple.State.EvaluatesFrom.step (middle := heap)
                · change Id.run ((Machine.step
                    (Machine.stateCtx heapCtx heapOpCtx quicksortCtx.blockCtx) _).run heap) = _
                  simpa using loadOp_step quicksortCtx.blockCtx _ _ heap ⟨base.addr + i⟩
              | apply EvalTriple.State.EvaluatesFrom.call_then hrotate
                intro scope
                apply EvalTriple.State.EvaluatesFrom.step (middle :=
                  (partitionHeapLoopSpec (partitionHeapRotate heap base pivotIdx i)
                    base n (pivotIdx + 1) (i + 1)).1)
                · simp [Machine.step, Machine.ofOption, Machine.resumeFrame,
                    Machine.driveOp]
                  rfl
                exact EvalTriple.State.EvaluatesFrom.return_to_call
              | apply EvalTriple.State.EvaluatesFrom.step (middle := heap)
                · quicksort_state_simp hload, hptrAdd, hltOp, hite, hlt
                  rfl
          have hle : heapOpCtx.get? "le" =
              some (binaryNatBoolOp fun a b => decide (a ≤ b)) := by rfl
          have houterIte : heapOpCtx.get? "ite" = some Op.ite := by rfl
          intro env stack
          refine ⟨_, _, by rfl, by rfl, ?_⟩
          repeat
            first
            | apply EvalTriple.State.EvaluatesFrom.call_then hstep
              intro scope
              apply EvalTriple.State.EvaluatesFrom.step (middle :=
                (partitionHeapLoopSpec (partitionHeapRotate heap base pivotIdx i)
                  base n (pivotIdx + 1) (i + 1)).1)
              · simp [Machine.step, Machine.ofOption, Machine.resumeFrame,
                  Machine.driveOp]
                rfl
              exact EvalTriple.State.EvaluatesFrom.return_to_call
            | apply EvalTriple.State.EvaluatesFrom.step (middle := heap)
              · quicksort_state_simp hle, houterIte, hdone
                rfl
        · rw [if_neg hlt]
          have hrec := ih (n - (i + 1)) (by omega) heap pivotIdx (i + 1)
            (by omega) (by omega) rfl
          have hload : heapOpCtx.get? "load" = some loadOp := by simp
          have hptrAdd : heapOpCtx.get? "ptrAdd" = some ptrAddOp := by rfl
          have hltOp : heapOpCtx.get? "lt" = some (Op.compare Val.primLt?) := by rfl
          have hite : heapOpCtx.get? "ite" = some Op.ite := by rfl
          have hadd : heapOpCtx.get? "add" = some (Op.natBinary Nat.add) := by rfl
          have hstep : EvalTriple.State.EvaluatesCallValues heapCtx heapOpCtx
              quicksortCtx.blockCtx "partitionLoopStep"
              [valPtr base, Val.nat n, Val.nat pivotIdx, Val.nat i] heap
              (Val.nat (partitionHeapLoopSpec heap base n pivotIdx (i + 1)).2)
              (partitionHeapLoopSpec heap base n pivotIdx (i + 1)).1 := by
            intro env stack
            refine ⟨_, _, by rfl, by rfl, ?_⟩
            repeat
              first
              | apply EvalTriple.State.EvaluatesFrom.step (middle := heap)
                · change Id.run ((Machine.step
                    (Machine.stateCtx heapCtx heapOpCtx quicksortCtx.blockCtx) _).run heap) = _
                  simpa using loadOp_step quicksortCtx.blockCtx _ _ heap
                    ⟨base.addr + pivotIdx⟩
              | apply EvalTriple.State.EvaluatesFrom.step (middle := heap)
                · change Id.run ((Machine.step
                    (Machine.stateCtx heapCtx heapOpCtx quicksortCtx.blockCtx) _).run heap) = _
                  simpa using loadOp_step quicksortCtx.blockCtx _ _ heap ⟨base.addr + i⟩
              | apply EvalTriple.State.EvaluatesFrom.call_then hrec
                intro scope
                repeat
                  first
                  | exact EvalTriple.State.EvaluatesFrom.return_through_done_call
                  | exact EvalTriple.State.EvaluatesFrom.return_to_call
                  | apply EvalTriple.State.EvaluatesFrom.step (middle :=
                      (partitionHeapLoopSpec heap base n pivotIdx (i + 1)).1)
                    · simp [Machine.step, Machine.ofOption, Machine.resumeFrame,
                        Machine.driveOp, Op.Body.resume?]
                      rfl
              | apply EvalTriple.State.EvaluatesFrom.step (middle := heap)
                · quicksort_state_simp hload, hptrAdd, hltOp, hite, hadd, hlt
                  rfl
          have hle : heapOpCtx.get? "le" =
              some (binaryNatBoolOp fun a b => decide (a ≤ b)) := by rfl
          have houterIte : heapOpCtx.get? "ite" = some Op.ite := by rfl
          intro env stack
          refine ⟨_, _, by rfl, by rfl, ?_⟩
          repeat
            first
            | apply EvalTriple.State.EvaluatesFrom.call_then hstep
              intro scope
              repeat
                first
                | exact EvalTriple.State.EvaluatesFrom.return_through_done_call
                | exact EvalTriple.State.EvaluatesFrom.return_to_call
                | apply EvalTriple.State.EvaluatesFrom.step (middle :=
                    (partitionHeapLoopSpec heap base n pivotIdx (i + 1)).1)
                  · simp [Machine.step, Machine.ofOption, Machine.resumeFrame,
                      Machine.driveOp, Op.Body.resume?]
                    rfl
            | apply EvalTriple.State.EvaluatesFrom.step (middle := heap)
              · quicksort_state_simp hle, houterIte, hdone
                rfl

theorem partitionHeapSpec_evaluates (heap : Heap) (base : Ptr) (n : Nat) (hn : 0 < n) :
    EvalTriple.State.EvaluatesCallValues heapCtx heapOpCtx quicksortCtx.blockCtx
      "partition" [valPtr base, Val.nat n] heap
      (Val.nat (partitionHeapSpec heap base n).2) (partitionHeapSpec heap base n).1 := by
  have hloop := partitionHeapLoopSpec_evaluates heap base n 0 1 (by omega) (by omega)
  have hzero : heapOpCtx.get? "add" = some (Op.natBinary Nat.add) := by rfl
  intro env stack
  refine ⟨_, _, by rfl, by rfl, ?_⟩
  repeat
    first
    | apply EvalTriple.State.EvaluatesFrom.call_then hloop
      intro scope
      exact EvalTriple.State.EvaluatesFrom.return_to_call
    | apply EvalTriple.State.EvaluatesFrom.step (middle := heap)
      · quicksort_state_simp hzero, partitionHeapSpec
        rfl

set_option maxRecDepth 10000 in
theorem quicksortHeapSpec_evaluates (heap : Heap) (base : Ptr) (n : Nat) :
    EvalTriple.State.EvaluatesCallValues heapCtx heapOpCtx quicksortCtx.blockCtx
      "quicksort" [valPtr base, Val.nat n] heap valUnit (quicksortHeapSpec heap base n) := by
  induction n using Nat.strongRecOn generalizing heap base with
  | ind n ih =>
      rw [quicksortHeapSpec]
      split <;> rename_i hactive
      · let part := partitionHeapSpec heap base n
        have hpartition := partitionHeapSpec_evaluates heap base n (by omega)
        change EvalTriple.State.EvaluatesCallValues heapCtx heapOpCtx quicksortCtx.blockCtx
          "partition" [valPtr base, Val.nat n] heap (Val.nat part.2) part.1 at hpartition
        have hp : part.2 < n :=
          (partitionHeapLoopSpec_index heap base n 0 1 (by omega) (by omega)).2
        let left := quicksortHeapSpec part.1 base part.2
        have hleft := ih part.2 hp part.1 base
        change EvalTriple.State.EvaluatesCallValues heapCtx heapOpCtx quicksortCtx.blockCtx
          "quicksort" [valPtr base, Val.nat part.2] part.1 valUnit left at hleft
        let rightBase : Ptr := ⟨base.addr + (part.2 + 1)⟩
        let rightLen := n - part.2 - 1
        have hright := ih rightLen (by omega) left rightBase
        have hrightBaseEq : (⟨base.addr + part.2 + 1⟩ : Ptr) = rightBase := by
          simp [rightBase, Nat.add_assoc]
        change EvalTriple.State.EvaluatesCallValues heapCtx heapOpCtx quicksortCtx.blockCtx
          "quicksort" [valPtr base, Val.nat n] heap valUnit
          (quicksortHeapSpec left ⟨base.addr + part.2 + 1⟩ rightLen)
        rw [hrightBaseEq]
        have hactiveCall : EvalTriple.State.EvaluatesCallValues heapCtx heapOpCtx
            quicksortCtx.blockCtx "quicksortActive" [valPtr base, Val.nat n] heap valUnit
            (quicksortHeapSpec left rightBase rightLen) := by
          have hptrAdd : heapOpCtx.get? "ptrAdd" = some ptrAddOp := by rfl
          have hadd : heapOpCtx.get? "add" = some (Op.natBinary Nat.add) := by rfl
          have hsub : heapOpCtx.get? "sub" = some (Op.natBinary Nat.sub) := by rfl
          intro env stack
          refine ⟨_, _, by rfl, by rfl, ?_⟩
          repeat
            first
            | apply EvalTriple.State.EvaluatesFrom.call_then hpartition
              intro scope
            | apply EvalTriple.State.EvaluatesFrom.call_then hleft
              intro scope
            | apply EvalTriple.State.EvaluatesFrom.call_then hright
              intro scope
              exact EvalTriple.State.EvaluatesFrom.return_to_call
            | apply EvalTriple.State.EvaluatesFrom.step (middle := heap)
              · quicksort_state_simp hptrAdd, hadd, hsub, part, left, rightBase, rightLen
                rfl
            | apply EvalTriple.State.EvaluatesFrom.step (middle := part.1)
              · quicksort_state_simp hptrAdd, hadd, hsub, part, left, rightBase, rightLen
                rfl
            | apply EvalTriple.State.EvaluatesFrom.step (middle := left)
              · quicksort_state_simp hptrAdd, hadd, hsub, part, left, rightBase, rightLen
                rfl
        have hltOp : heapOpCtx.get? "lt" = some (Op.compare Val.primLt?) := by rfl
        have hite : heapOpCtx.get? "ite" = some Op.ite := by rfl
        intro env stack
        refine ⟨_, _, by rfl, by rfl, ?_⟩
        repeat
          first
          | apply EvalTriple.State.EvaluatesFrom.call_then hactiveCall
            intro scope
            apply EvalTriple.State.EvaluatesFrom.step (middle :=
              quicksortHeapSpec left rightBase rightLen)
            · simp [Machine.step, Machine.ofOption, Machine.resumeFrame,
                Machine.driveOp]
              rfl
            exact EvalTriple.State.EvaluatesFrom.return_to_call
          | apply EvalTriple.State.EvaluatesFrom.step (middle := heap)
            · quicksort_state_simp hltOp, hite, hactive
              rfl
      · have hltOp : heapOpCtx.get? "lt" = some (Op.compare Val.primLt?) := by rfl
        have hite : heapOpCtx.get? "ite" = some Op.ite := by rfl
        intro env stack
        refine ⟨_, _, by rfl, by rfl, ?_⟩
        repeat
          first
          | exact EvalTriple.State.EvaluatesFrom.return_to_call
          | exact EvalTriple.State.EvaluatesFrom.done
          | apply EvalTriple.State.EvaluatesFrom.step (middle := heap)
            · quicksort_state_simp hltOp, hite, hactive
              rfl

theorem quicksort_evaluates (heap : Heap) (base : Ptr) (n : Nat) :
    EvalTriple.State.EvaluatesCall heapCtx heapOpCtx quicksortCtx.blockCtx
      "quicksort" [termPtr base.addr, .nat n] heap valUnit (quicksortHeapSpec heap base n) := by
  unfold EvalTriple.State.EvaluatesCall
  apply EvalTriple.State.EvaluatesTo.of_evaluatesFrom
  have hcall := quicksortHeapSpec_evaluates heap base n
  repeat
    first
    | apply EvalTriple.State.EvaluatesFrom.call_then hcall
      intro scope
      exact EvalTriple.State.EvaluatesFrom.done
    | apply EvalTriple.State.EvaluatesFrom.step (middle := heap)
      · set_option linter.unusedSimpArgs false in
          simp [quicksortCtx, mkCtx, quicksortBlocks, checkedBlocks,
            Machine.step, Machine.evalTerm, Machine.applyValue,
            Machine.driveSelectedOp, Machine.ofOption, Machine.evalTermImmediate,
            Machine.applyValueImmediate, Machine.resumeFrame, Machine.enterBlock,
            Machine.enterInstrs, Machine.driveOp, Machine.start,
            Op.effectful, Op.Body.collect, Op.Arg.ofTerms, Op.Arg.ofVals,
            Op.ofVals, Op.Body.eager, Op.fixed, Block.entryEnv, Scope.get?,
            Term.nat, termPtr, valPtr, valUnit, asPtr?]
        rfl

def QuicksortRangeValid (heap : Heap) (base : Ptr) (n : Nat) : Prop :=
  0 < base.addr ∧ base.addr + n ≤ heap.next

private abbrev quicksortStateCtx : Ctx :=
  heapStateCtx quicksortBlocks quicksortBlocksValid

private theorem heapRange_eq_of_segment (heap : Heap) (base : Ptr) (n : Nat)
    (contents : Nat → Nat)
    (hp : (segment base.addr n contents).holds heap) :
    heapRange heap base n = (List.range n).map contents := by
  simpa [heapRange, segment] using hp

private theorem heapRange_segment (heap : Heap) (base : Ptr) (n : Nat) :
    (segment base.addr n (fun i => HeapArray.get (heapRange heap base n) i)).holds heap := by
  intro i hi
  exact (heapRange_get heap base hi).symm

/-
```
{ segment base n contents }
  quicksort(base, n)
{ r = unit ∧ final segment is a sorted permutation of contents, with outside cells framed }
```

`QuicksortRangeValid` mentions `Heap.next`, but Peano `HProp` support tracks observable cells, not
allocator metadata; the public footprint therefore specifies the actual sorted range cells.
-/
@[zspec] theorem quicksort_correct (base : Ptr) (n : Nat) (contents : Nat → Nat) :
    Zag.EvaluatesCall quicksortStateCtx
      "quicksort" [termPtr base.addr, .nat n]
      (HProp.toAssertion (segment base.addr n contents))
      (Std.Do.PostCond.noThrow fun result final =>
        ⌜result = valUnit ∧
          List.Perm (heapRange final base n) ((List.range n).map contents) ∧
          (heapRange final base n).Pairwise (· ≤ ·) ∧
          (segment base.addr n (fun i => HeapArray.get (heapRange final base n) i)).holds final ∧
          ∃ h0 : Heap, (segment base.addr n contents).holds h0 ∧
            ∀ ptr, ptr.addr < base.addr ∨ base.addr + n ≤ ptr.addr →
              Heap.read final ptr = Heap.read h0 ptr⌝) := by
  let PreHeap := { heap : Heap // (segment base.addr n contents).holds heap }
  change EvalTriple.EvaluatesFrom quicksortStateCtx
    (Machine.start [] (.call "quicksort" [termPtr base.addr, .nat n])) [] _ _
  apply EvalTriple.Steps.split (cases := fun hh : PreHeap => EvalTriple.Singleton.statePre hh.1)
  · intro s hs
    refine ⟨⟨s, by simpa [HProp.toAssertion] using hs⟩, ?_⟩
    simp [EvalTriple.Singleton.statePre]
  · intro hh
    have hcorrect := quicksortHeapSpec_correct hh.1 base n
    have hinitRange := heapRange_eq_of_segment hh.1 base n contents hh.2
    have hex := quicksort_evaluates hh.1 base n
    refine EvalTriple.EvaluatesFrom.consequence hex .rfl ?_
    simp [EvalTriple.Singleton.statePost, Std.Do.PostCond.entails]
    refine ⟨?_, hcorrect.2.1, heapRange_segment (quicksortHeapSpec hh.1 base n) base n, ?_⟩
    · simpa [hinitRange] using hcorrect.1
    · exact ⟨hh.1, hh.2, hcorrect.2.2⟩

def quicksortTestHeap (base : Ptr) (xs : HeapArray) : Heap :=
  { next := base.addr + xs.length + 1
    cells := (List.range xs.length).zipWith (fun offset value => (base.addr + offset, value)) xs }

def runQuicksort (heap : Heap) (base : Ptr) (n : Nat) : Option (HeapArray × Heap) :=
  match (Machine.evalFuel quicksortCtx 100000 []
      (.call "quicksort" [termPtr base.addr, .nat n])).run heap with
  | (some _, final) => some (heapRange final base n, final)
  | (none, _) => none

def runQuicksortValues (base : Ptr) (xs : HeapArray) : Option HeapArray :=
  (runQuicksort (quicksortTestHeap base xs) base xs.length).map Prod.fst

#guard runQuicksortValues ⟨3⟩ [4, 1, 3, 2] == some [1, 2, 3, 4]
#guard runQuicksortValues ⟨5⟩ [3, 1, 2, 1, 3] == some [1, 1, 2, 3, 3]
#guard runQuicksortValues ⟨2⟩ (List.range 20) == some (List.range 20)
#guard (runQuicksort
    { next := 7, cells := [(1, 99), (2, 4), (3, 1), (4, 3), (5, 2), (6, 88)] }
    ⟨2⟩ 4).map (fun result =>
      (result.1, Heap.read result.2 ⟨1⟩, Heap.read result.2 ⟨6⟩)) ==
  some ([1, 2, 3, 4], 99, 88)

end Zag.Test.Autocorres.Examples
