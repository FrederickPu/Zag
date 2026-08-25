import Test.Autocorres.Examples.Common

/-!
Current-model analogue of upstream
[`ConditionGuard.thy`](https://github.com/seL4/l4v/blob/master/tools/autocorres/tests/examples/ConditionGuard.thy).

Each dereference occurs only inside the non-null branch that guards it. `arith` recurses without a
result when C division's divisor is zero, rather than assigning an unrelated total value to
undefined execution. PeanoHeap has no allocation provenance, so non-null but invalid C pointers
remain unsupported. Signed C arithmetic is represented by the nonnegative `Nat` fragment.
-/

namespace Zag.Test.Autocorres.Examples

open Zag Zag.Lib.PeanoHeap
open Zag.EvalTriple.Exact

abbrev conditionGuardBlocks : BlockCtx.Raw heapCtx :=
  blocks% [
    f1(ptr : Ptr) : Unit {
      isNull := op "ptrIsNull"[ptr];
      ret if isNull { raw(termUnit) } else {
        if primEq (op "load"[ptr]) nat(0)
          { op "store"[ptr, nat(1)] } else { raw(termUnit) }
      }
    },
    f2(ptr : Ptr) : Unit {
      isNull := op "ptrIsNull"[ptr];
      ret if isNull { raw(termUnit) } else {
        if primEq (op "load"[ptr]) nat(0)
          { op "store"[ptr, nat(1)] } else { raw(termUnit) }
      }
    },
    fancy(ptr : Ptr) : Unit {
      isNull := op "ptrIsNull"[ptr];
      ret if isNull { raw(termUnit) } else {
        if primEq (op "load"[ptr]) nat(0) {
          op "store"[ptr, op "load"[op "ptrAdd"[ptr, nat(1)]]]
        } else {
          if primEq (op "load"[op "ptrAdd"[ptr, nat(1)]]) nat(0) {
            op "store"[ptr, op "load"[op "ptrAdd"[ptr, nat(1)]]]
          } else { raw(termUnit) }
        }
      }
    },
    loop(ptr : Ptr) : Unit {
      isNull := op "ptrIsNull"[ptr];
      ret if isNull { raw(termUnit) } else {
        if primEq (op "load"[ptr]) nat(0)
          { call loop [op "ptrAdd"[ptr, nat(1)]] } else { raw(termUnit) }
      }
    },
    arith(x : Nat, y : Nat) : Nat {
      zeroDivisor := primEq y nat(0);
      ret if zeroDivisor { call arith [x, y] } else {
        if primEq (op "div"[x, y]) nat(0) { nat(1) } else {
          if primEq (op "div"[y, x]) nat(0) { nat(1) } else { nat(0) }
        }
      }
    }
  ]

theorem conditionGuardBlocksValid : BlockCtx.Valid conditionGuardBlocks := by
  valid_blocks [conditionGuardBlocks, termUnit]

abbrev conditionGuardCtx : Ctx := mkCtx conditionGuardBlocks conditionGuardBlocksValid

theorem conditionGuardCtx_wellTyped : Ctx.WellTyped conditionGuardCtx := by
  typecheck_ctx

/-- The two source loops are represented by genuine recursive call edges. -/
theorem conditionGuard_partialCallEdges :
    conditionGuardBlocks[3].2.callNames = ["loop"] ∧
    conditionGuardBlocks[4].2.callNames = ["arith"] := by
  simp [conditionGuardBlocks, termUnit, Block.callNames, Term.callNames, Term.ite, Term.nat]

def conditionGuardHeap : Heap :=
  { next := 7, cells := [(1, 0), (2, 0), (3, 7), (4, 0), (5, 9), (6, 8)] }

def runConditionHeap (name : String) (heap : Heap) (ptr : Ptr)
    (fuel : Nat := 1000) : Option Heap :=
  match (Machine.evalFuel conditionGuardCtx fuel [] (.call name [termPtr ptr.addr])).run heap with
  | (some _, final) => some final
  | (none, _) => none

def runConditionArith (x y : Nat) (fuel : Nat := 1000) : Option Nat :=
  let (result, _) :=
    (Machine.evalFuel conditionGuardCtx fuel [] (.call "arith" [Term.nat x, Term.nat y])).run
      conditionGuardHeap
  result.bind Val.asNat?

/- Null short-circuiting and the guarded write are both observable. -/
#guard runConditionHeap "f1" conditionGuardHeap null = some conditionGuardHeap
#guard runConditionHeap "f1" conditionGuardHeap ⟨1⟩ =
  some (Heap.write conditionGuardHeap ⟨1⟩ 1)

/- The struct-field projection uses the same offset-zero cell in this PeanoHeap layout. -/
#guard runConditionHeap "f2" conditionGuardHeap ⟨4⟩ =
  some (Heap.write conditionGuardHeap ⟨4⟩ 1)
#guard runConditionHeap "f2" conditionGuardHeap ⟨3⟩ = some conditionGuardHeap

/- `fancy` exercises both sides of the short-circuiting disjunction and its no-write path. -/
#guard runConditionHeap "fancy" conditionGuardHeap ⟨1⟩ =
  some (Heap.write conditionGuardHeap ⟨1⟩ 0)
#guard runConditionHeap "fancy" conditionGuardHeap ⟨3⟩ =
  some (Heap.write conditionGuardHeap ⟨3⟩ 0)
#guard runConditionHeap "fancy" conditionGuardHeap ⟨5⟩ = some conditionGuardHeap

def firstConditionLoopFuel (heap : Heap) (ptr : Ptr) : Option Nat :=
  (List.range 1000).find? fun fuel => (runConditionHeap "loop" heap ptr fuel).isSome

/- Crossing two zero cells takes strictly more machine steps than stopping at a nonzero cell. -/
#guard (firstConditionLoopFuel conditionGuardHeap ⟨3⟩).getD 1000 <
  (firstConditionLoopFuel conditionGuardHeap ⟨1⟩).getD 1000
#guard runConditionHeap "loop" conditionGuardHeap null = some conditionGuardHeap

/- Both defined short-circuit outcomes and the explicit non-returning zero-divisor path. -/
#guard runConditionArith 0 5 = some 1
#guard runConditionArith 2 2 = some 0
#guard runConditionArith 10 0 1000 = none

end Zag.Test.Autocorres.Examples
