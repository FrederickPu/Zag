import Test.Autocorres.Examples.Common

/-!
Upstream Isabelle theory:
[`Quicksort.thy`](https://github.com/seL4/l4v/blob/master/tools/autocorres/tests/examples/Quicksort.thy).

The executable program uses an ambient `PeanoHeap`: its array argument is a base pointer, loads and
stores address `base + i`, and recursive calls advance that pointer exactly as the C program does.
Lengths, indices, addresses, and values are unbounded `Nat`; the explicit bounds below ensure the
source subtractions do not underflow and all addressed offsets belong to the input range. This model
does not claim fixed-width, alignment, allocation, or typed-memory fidelity.
-/

namespace Zag.Test.Autocorres.Examples

open Zag Zag.Lib.PeanoHeap

/-! # Quicksort, first-element pivot

   ```
  partition(A, n):                 -- pivot starts at A[0]
    p := 0
    for i := 1 to n-1:
      if A[i] < A[p]:
        pivot := A[p]; A[p] := A[i]; p++
        A[i] := A[p]; A[p] := pivot
    return p

  quicksort(A, n):
    if 1 < n:
      p := partition(A, n)
      quicksort(A, p); quicksort(A+p+1, n-p-1)
  ```

  There are no primitive `for` loops, so the source loop is tail recursion carrying `p` and `i`.
  Its three assignments are ambient stores in source order. Partition mutates the heap once and
  returns only its pivot index; quicksort mutates the same heap and returns unit. -/
abbrev quicksortBlocks : BlockCtx.Raw heapCtx :=
  blocks% [
    partitionLoop(base : Ptr, n : Nat, pivotIdx : Nat, i : Nat) : Nat {
      done := op "le"[n, i];
      ret if done { pivotIdx }
        else { call partitionLoopStep [base, n, pivotIdx, i] }
    },
    partitionLoopStep(base : Ptr, n : Nat, pivotIdx : Nat, i : Nat) : Nat {
      pivotPtr := op "ptrAdd"[base, pivotIdx];
      pivot := op "load"[pivotPtr];
      currentPtr := op "ptrAdd"[base, i];
      current := op "load"[currentPtr];
      ret if op "lt"[current, pivot] {
        call partitionRotate [base, n, pivotIdx, i, pivot, current]
      } else {
        call partitionLoop [base, n, pivotIdx, op "add"[i, nat(1)]]
      }
    },
    partitionRotate(base : Ptr, n : Nat, pivotIdx : Nat, i : Nat,
        pivot : Nat, current : Nat) : Nat {
      pivotPtr := op "ptrAdd"[base, pivotIdx];
      storedCurrent := op "store"[pivotPtr, current];
      nextPivotIdx := op "add"[pivotIdx, nat(1)];
      nextPivotPtr := op "ptrAdd"[base, nextPivotIdx];
      shifted := op "load"[nextPivotPtr];
      currentPtr := op "ptrAdd"[base, i];
      storedShifted := op "store"[currentPtr, shifted];
      storedPivot := op "store"[nextPivotPtr, pivot];
      ret call partitionLoop [base, n, nextPivotIdx, op "add"[i, nat(1)]]
    },
    partition(base : Ptr, n : Nat) : Nat {
      ret call partitionLoop [base, n, nat(0), nat(1)]
    },
    quicksort(base : Ptr, n : Nat) : Unit {
      active := op "lt"[nat(1), n];
      ret if active { call quicksortActive [base, n] } else { raw(termUnit) }
    },
    quicksortActive(base : Ptr, n : Nat) : Unit {
      p := call partition [base, n];
      left := call quicksort [base, p];
      rightOffset := op "add"[p, nat(1)];
      rightBase := op "ptrAdd"[base, rightOffset];
      rightLen := op "sub"[op "sub"[n, p], nat(1)];
      ret call quicksort [rightBase, rightLen]
    }
  ]

theorem quicksortBlocksValid : BlockCtx.Valid quicksortBlocks := by
  valid_blocks [quicksortBlocks]
  intro name h
  simp [termUnit, Term.callNames] at h

abbrev quicksortCtx : Ctx := mkCtx quicksortBlocks quicksortBlocksValid

theorem quicksortCtx_wellTyped : Ctx.WellTyped quicksortCtx := by
  typecheck_ctx

end Zag.Test.Autocorres.Examples
