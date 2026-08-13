import Test.Autocorres.Examples.Str2Long

/-! Block analogue of upstream `type_strengthen_tricks.thy`. -/

namespace Zag.Test.Autocorres.Examples

open Zag Zag.Lib.PeanoHeap

abbrev typeStrengthenBlocks : BlockCtx.Raw heapCtx :=
  blocks% [
    pureInc(x : Nat) : Nat {
      ret op "add"[x, nat(1)]
    },
    globalRead(heap : Heap, ptr : Ptr) : Nat {
      ret op "load"[heap, ptr]
    },
    stateUpdate(heap : Heap, ptr : Ptr, value : Nat) : Heap {
      ret op "store"[heap, ptr, value]
    },
    exceptionParse(chars : Array, len : Nat) : StateNat {
      ret call str2long [chars, len]
    }
  ]

abbrev typeStrengthenProgramBlocks : BlockCtx.Raw heapCtx :=
  str2longBlocks ++ typeStrengthenBlocks

theorem typeStrengthenProgramBlocksValid : BlockCtx.Valid typeStrengthenProgramBlocks := by
  constructor
  case left => decide
  case right =>
    set_option linter.unusedSimpArgs false in
      simp [typeStrengthenProgramBlocks, str2longBlocks, typeStrengthenBlocks,
        Block.callNames, Term.callNames, Term.nat, Term.bool, Term.ite, termHeap, termPtr,
        termArray]

abbrev typeStrengthenCtx : Ctx :=
  mkCtx typeStrengthenProgramBlocks typeStrengthenProgramBlocksValid

theorem typeStrengthenCtx_wellTyped : Ctx.WellTyped typeStrengthenCtx := by
  typecheck_ctx

end Zag.Test.Autocorres.Examples
