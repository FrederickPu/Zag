import Test.Autocorres.Examples.Common

namespace Zag.Test.Autocorres.Examples

open Zag Zag.Lib.PeanoHeap

/-! # Quicksort, Lomuto partitioning

  ```
  quicksort(A, lo, hi):
    if lo < hi:
      p := partition(A, lo, hi)
      quicksort(A, lo, p-1); quicksort(A, p+1, hi)

  partition(A, lo, hi):            -- pivot = A[hi]
    i := lo
    for j := lo to hi-1:
      if A[j] <= pivot: swap A[i], A[j]; i := i+1
    swap A[i], A[hi]
    return i
  ```

  Two things about the IR shape it into what is below.

  A block returns a single value, and partition produces *two* results -- the reordered array and
  the pivot's final index. `State` pairs a `Heap` with a payload, not two arbitrary values, and
  there is no tuple primitive, so the pair cannot be returned. The loop is therefore written twice
  under the same recursion, once projecting the array and once projecting the index. Both walk
  identical states, so `partitionIdx` names the index that `partitionArray` puts the pivot at.

  There are also no loops, so `for j` is the tail-recursive `partitionLoop*`, carrying `i` and `j`
  as parameters. Array ops are functional (`arraySwap` returns a new array), so the array is
  threaded through the recursion rather than mutated. -/
abbrev quicksortBlocks : BlockCtx.Raw heapCtx :=
  blocks% [
    partitionLoopArray(xs : Array, lo : Nat, hi : Nat, i : Nat, j : Nat) : Array {
      pivot := op "arrayGet"[xs, hi];
      cur := op "arrayGet"[xs, j];
      keep := op "le"[cur, pivot];
      ret if op "lt"[j, hi] {
            if keep {
              call partitionLoopArray
                [op "arraySwap"[xs, i, j], lo, hi, op "add"[i, nat(1)], op "add"[j, nat(1)]]
            } else {
              call partitionLoopArray [xs, lo, hi, i, op "add"[j, nat(1)]]
            }
          } else {
            op "arraySwap"[xs, i, hi]
          }
    },
    partitionLoopIdx(xs : Array, lo : Nat, hi : Nat, i : Nat, j : Nat) : Nat {
      pivot := op "arrayGet"[xs, hi];
      cur := op "arrayGet"[xs, j];
      keep := op "le"[cur, pivot];
      ret if op "lt"[j, hi] {
            if keep {
              call partitionLoopIdx
                [op "arraySwap"[xs, i, j], lo, hi, op "add"[i, nat(1)], op "add"[j, nat(1)]]
            } else {
              call partitionLoopIdx [xs, lo, hi, i, op "add"[j, nat(1)]]
            }
          } else {
            i
          }
    },
    partitionArray(xs : Array, lo : Nat, hi : Nat) : Array {
      ret call partitionLoopArray [xs, lo, hi, lo, lo]
    },
    partitionIdx(xs : Array, lo : Nat, hi : Nat) : Nat {
      ret call partitionLoopIdx [xs, lo, hi, lo, lo]
    },
    quicksort(xs : Array, lo : Nat, hi : Nat) : Array {
      split := call partitionArray [xs, lo, hi];
      p := call partitionIdx [xs, lo, hi];
      ret if op "lt"[lo, hi] {
            call quicksort
              [call quicksort [split, lo, op "sub"[p, nat(1)]], op "add"[p, nat(1)], hi]
          } else {
            xs
          }
    },
    quicksortAll(xs : Array) : Array {
      len := op "arrayLen"[xs];
      ret call quicksort [xs, nat(0), op "sub"[len, nat(1)]]
    }
  ]

theorem quicksortBlocksValid : BlockCtx.Valid quicksortBlocks := by
  valid_blocks [quicksortBlocks]
  -- every name called is declared; `valid_blocks` reduces this to a propositional residue
  intro name h
  rcases h with (h | h) | h <;> simp [h]

abbrev quicksortCtx : Ctx := mkCtx quicksortBlocks quicksortBlocksValid

def runQuicksort (xs : HeapArray) : Option HeapArray :=
  (EvalState.run quicksortCtx 10000
    (EvalState.start [] (.call "quicksortAll" [termArray xs]))).result?.bind asArray?

#guard runQuicksort [4, 1, 3, 2] == some [1, 2, 3, 4]

theorem quicksortCtx_wellTyped : Ctx.WellTyped quicksortCtx := by
  typecheck_ctx

end Zag.Test.Autocorres.Examples
