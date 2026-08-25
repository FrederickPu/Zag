import Test.Autocorres.Examples.Common

/-!
Current-model analogue of upstream
[`FunctionInfoDemo.thy`](https://github.com/seL4/l4v/blob/master/tools/autocorres/tests/examples/FunctionInfoDemo.thy).

Zag exposes block definitions through `BlockCtx.get?` and direct calls through `Block.callNames`;
the checks below query both through the installed context. The source functions return `void`, but
because both calls are non-returning, the local `Nat` result type is an unobservable unit stand-in.
Zag has no translation-unit/phase function-info table, intermediate
correctness metadata, heap-info cache, or stored final correspondence theorem, so those upstream
queries are unsupported rather than approximated by well-typing.
-/

namespace Zag.Test.Autocorres.Examples

open Zag Zag.Lib.PeanoHeap

abbrev functionInfoBlocks : BlockCtx.Raw heapCtx :=
  blocks% [
    rec() : Nat {
      ret call rec []
    },
    f() : Nat {
      ret call rec []
    }
  ]

theorem functionInfoBlocksValid : BlockCtx.Valid functionInfoBlocks := by
  valid_blocks [functionInfoBlocks]

abbrev functionInfoCtx : Ctx := mkCtx functionInfoBlocks functionInfoBlocksValid

theorem functionInfoCtx_wellTyped : Ctx.WellTyped functionInfoCtx := by
  typecheck_ctx

/-- Definitions are retrievable by function name in the current program context. -/
theorem functionInfoCtx_definitions :
    functionInfoCtx.blockCtx.get? "rec" = some functionInfoBlocks[0].2 ∧
    functionInfoCtx.blockCtx.get? "f" = some functionInfoBlocks[1].2 := by
  constructor <;> rfl

/-- Retrieved definitions expose the direct recursive/caller edges as local call metadata. -/
theorem functionInfoCtx_callGraph :
    (functionInfoCtx.blockCtx.get? "rec").map Block.callNames = some ["rec"] ∧
    (functionInfoCtx.blockCtx.get? "f").map Block.callNames = some ["rec"] := by
  constructor
  · rw [functionInfoCtx_definitions.1]
    simp [functionInfoBlocks, Block.callNames, Term.callNames]
  · rw [functionInfoCtx_definitions.2]
    simp [functionInfoBlocks, Block.callNames, Term.callNames]

end Zag.Test.Autocorres.Examples
