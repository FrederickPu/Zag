import Meta.UnifyType
import Meta.Eval
import Lib.PeanoHeap

/-!
`State(a)` is one arity-1 primitive, not a family of hand-rolled result types. What that buys is
checked here: a single `mkState`/`stateHeap`/`stateValue` triple types at every payload,
including payloads (`Bool`, `Array`, a nested `State`) that no program in the tree returns and
for which no operator was ever written.

These are typing checks. Evaluating the state operators is not checked, here or anywhere: their
`Op.Signature` decodes the payload from the operand type, so running one goes through a `cast`
across `Ty.type`, which is `Type`-valued and well-founded and therefore does not reduce. The
nine operators these three replaced had no evaluation tests either.
-/

namespace Zag.Test.Heap

open Zag Zag.Lib.PeanoHeap

abbrev heapProgram : Ctx := mkCtx [] (by decide)

/-! ### the payload is decoded from the operand type -/

example : heapProgram.opCtx.outTy? "mkState" [HeapTy, NatTy] = some (StateTy NatTy) := by rfl
example : heapProgram.opCtx.outTy? "mkState" [HeapTy, BoolTy] = some (StateTy BoolTy) := by rfl
example : heapProgram.opCtx.outTy? "mkState" [HeapTy, PtrTy] = some (StateTy PtrTy) := by rfl
example : heapProgram.opCtx.outTy? "mkState" [HeapTy, ArrayTy] = some (StateTy ArrayTy) := by rfl

/-- Nothing about the payload is special-cased, so a `State` may carry a `State`. -/
example : heapProgram.opCtx.outTy? "mkState" [HeapTy, StateTy BoolTy] =
    some (StateTy (StateTy BoolTy)) := by rfl

example : heapProgram.opCtx.outTy? "stateHeap" [StateTy NatTy] = some HeapTy := by rfl
example : heapProgram.opCtx.outTy? "stateHeap" [StateTy ArrayTy] = some HeapTy := by rfl
example : heapProgram.opCtx.outTy? "stateValue" [StateTy NatTy] = some NatTy := by rfl
example : heapProgram.opCtx.outTy? "stateValue" [StateTy PtrTy] = some PtrTy := by rfl
example : heapProgram.opCtx.outTy? "stateValue" [StateTy (StateTy PtrTy)] =
    some (StateTy PtrTy) := by rfl

/-! ### and it is still a real constraint -/

/-- The first operand of `mkState` must be a heap. -/
example : heapProgram.opCtx.outTy? "mkState" [NatTy, NatTy] = none := by rfl

/-- A projection's operand must be a `State`, not merely anything. -/
example : heapProgram.opCtx.outTy? "stateValue" [NatTy] = none := by rfl
example : heapProgram.opCtx.outTy? "stateHeap" [HeapTy] = none := by rfl

/-- Arity is still checked. -/
example : heapProgram.opCtx.outTy? "mkState" [HeapTy] = none := by rfl
example : heapProgram.opCtx.outTy? "stateValue" [StateTy NatTy, NatTy] = none := by rfl

/-! ### a block returning `State(a)` type-checks at more than one payload -/

abbrev stateBlocks : BlockCtx.Raw heapCtx :=
  blocks% [
    storeThenRead(heap : Heap, ptr : Ptr, value : Nat) : State[Nat] {
      written := op "store"[heap, ptr, value];
      readBack := op "load"[written, ptr];
      ret op "mkState"[written, readBack]
    },
    allocThenReturn(heap : Heap, size : Nat) : State[Ptr] {
      ptr := op "allocPtr"[heap, size];
      grown := op "allocHeap"[heap, size];
      ret op "mkState"[grown, ptr]
    },
    unwrap(state : State[Nat]) : Nat {
      ret op "stateValue"[state]
    },
    rewrap(state : State[Nat]) : State[Nat] {
      heap := op "stateHeap"[state];
      value := op "stateValue"[state];
      ret op "mkState"[heap, op "add"[value, nat(1)]]
    }
  ]

theorem stateBlocksValid : BlockCtx.Valid stateBlocks := by valid_blocks [stateBlocks]

abbrev stateCtx : Ctx := mkCtx stateBlocks stateBlocksValid

theorem stateCtx_wellTyped : Ctx.WellTyped stateCtx := by typecheck_ctx

end Zag.Test.Heap
