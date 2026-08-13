import Test.Autocorres.Examples.Common

namespace Zag.Test.Autocorres.Examples

open Zag Zag.Lib.PeanoHeap

abbrev str2longBlocks : BlockCtx.Raw heapCtx :=
  blocks% [
    str2long(chars : Array, len : Nat) : StateNat {
      ret call str2longLoop [chars, len, nat(0), nat(0), bool(false)]
    },
    str2longLoop(chars : Array, len : Nat, idx : Nat, acc : Nat, error : Bool) : StateNat {
      done := op "le"[len, idx];
      ch := op "arrayGet"[chars, idx];
      digitOk := op "isDigit"[ch];
      digit := op "digit"[ch];
      nextAcc := op "add"[op "mul"[acc, nat(10)], digit];
      nextError := op "ite"[digitOk, error, bool(true)];
      ret if done { op "mkStateNat"[raw(termHeap Heap.empty), acc] }
        else { call str2longLoop [chars, len, op "add"[idx, nat(1)], nextAcc, nextError] }
    }
  ]

theorem str2longBlocksValid : BlockCtx.Valid str2longBlocks := by
  constructor
  case left => decide
  case right =>
    set_option linter.unusedSimpArgs false in
      simp [str2longBlocks, Block.callNames, Term.callNames, Term.nat, Term.bool,
        Term.ite, termHeap, termPtr, termArray]

abbrev str2longCtx : Ctx := mkCtx str2longBlocks str2longBlocksValid

theorem str2longCtx_wellTyped : Ctx.WellTyped str2longCtx := by
  typecheck_ctx

end Zag.Test.Autocorres.Examples
