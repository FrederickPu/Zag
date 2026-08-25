import Test.Autocorres.Examples.Common

/-!
Current-model analogue of upstream
[`TraceDemo.thy`](https://github.com/seL4/l4v/blob/master/tools/autocorres/tests/examples/TraceDemo.thy).

Zag does not have heap-lift/word-abstraction phases, stored rule traces, simplifier traces, or trace
file export. `Zag.eval.sym` emits proof-time diagnostics but does not produce a stable trace artifact
that this module can query and assert. It is therefore explicitly not presented as an AutoCorres
trace analogue. The separate executable smoke test below checks only the C body's PeanoHeap/`Nat`
behavior; null dereference is represented by a non-returning call, and pointer provenance remains
unsupported.
-/

namespace Zag.Test.Autocorres.Examples

open Zag Zag.Lib.PeanoHeap

abbrev traceDemoBlocks : BlockCtx.Raw heapCtx :=
  blocks% [
    incr(ptr : Ptr) : Unit {
      isNull := op "ptrIsNull"[ptr];
      ret if isNull { call incr [ptr] } else {
        op "store"[ptr, op "add"[op "load"[ptr], nat(1)]]
      }
    }
  ]

theorem traceDemoBlocksValid : BlockCtx.Valid traceDemoBlocks := by
  valid_blocks [traceDemoBlocks]

abbrev traceDemoCtx : Ctx := mkCtx traceDemoBlocks traceDemoBlocksValid

theorem traceDemoCtx_wellTyped : Ctx.WellTyped traceDemoCtx := by
  typecheck_ctx

def traceDemoHeap : Heap := { next := 2, cells := [(1, 41)] }

def runTraceIncrBody (heap : Heap) (ptr : Ptr) : Option Heap :=
  match (Machine.evalFuel traceDemoCtx 1000 [] (.call "incr" [termPtr ptr.addr])).run heap with
  | (some _, final) => some final
  | (none, _) => none

/- This is C-body execution coverage, not translation-phase trace correspondence. -/
#guard runTraceIncrBody traceDemoHeap ⟨1⟩ =
  some (Heap.write traceDemoHeap ⟨1⟩ 42)
#guard runTraceIncrBody traceDemoHeap null = none

end Zag.Test.Autocorres.Examples
