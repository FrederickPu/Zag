import Lib.Peano.Defs
import Zag.EvalState

/-!
Non-local exit.

A call is the frame an unwind can target. `exit b v` unwinds to the *nearest enclosing call*
of the block named `b` and makes `v` that call's value:

* naming the current block is an **early return** -- every later instruction, and the block's
  `ret` term, are skipped;
* naming an enclosing block **breaks out of it**, which is what the old recursor stack allowed
  by calling an outer motive from an inner loop body.

An exit that escapes every enclosing call is stuck, so `Machine.result?` is `none`.
-/

namespace Zag.Test.Exit

open Zag Zag.Lib.Peano

/-! ### early return -/

/- `clamp n = if n > 10 then 10 else n`, written as a guard that returns out of the block
  before `ret n` is ever reached. -/
abbrev clampBlocks : BlockCtx.Raw natCtx :=
  blocks% [
    clamp(n : Nat) : Nat {
      tooBig := primGt n nat(10);
      guard := if tooBig { exit clamp nat(10) } else { nat(0) };
      ret n
    }
  ]

abbrev clampCtx : Ctx where
  primCtx := natCtx
  opCtx := natOpCtx
  blockCtx := ⟨clampBlocks, by
    refine ⟨by decide, ?_⟩
    simp [clampBlocks, Block.callNames, Term.callNames, Term.nat, Term.ite]⟩

def runClamp (n : Nat) : Option Nat :=
  (Machine.evalFuel clampCtx 500 [] (.call "clamp" [Term.nat n])).run.bind Val.asNat?

/-- info: [some 0, some 3, some 9, some 10, some 10, some 10] -/
#guard_msgs in
#eval [0, 3, 9, 10, 11, 50].map runClamp

#guard (List.range 20).all (fun n => runClamp n == some (min n 10))

/-! ### breaking out of an enclosing block -/

/- `inner` unwinds past its own frame to `outer`, so the `add 100` in `outer` never runs. -/
abbrev breakBlocks : BlockCtx.Raw natCtx :=
  blocks% [
    outer(n : Nat) : Nat {
      r := call inner [n];
      ret op "add"[r, nat(100)]
    },
    inner(n : Nat) : Nat {
      big := primGt n nat(5);
      guard := if big { exit outer nat(0) } else { nat(0) };
      ret n
    }
  ]

abbrev breakCtx : Ctx where
  primCtx := natCtx
  opCtx := natOpCtx
  blockCtx := ⟨breakBlocks, by
    refine ⟨by decide, ?_⟩
    simp [breakBlocks, Block.callNames, Term.callNames, Term.nat, Term.ite]⟩

def runOuter (n : Nat) : Option Nat :=
  (Machine.evalFuel breakCtx 500 [] (.call "outer" [Term.nat n])).run.bind Val.asNat?

/-- info: [some 100, some 103, some 105, some 0, some 0] -/
#guard_msgs in
#eval [0, 3, 5, 6, 40].map runOuter

/- calling `inner` directly leaves the exit with no enclosing `outer` frame, so it escapes and
  evaluation is stuck -/
/-- info: none -/
#guard_msgs in
#eval (Machine.evalFuel breakCtx 500 [] (.call "inner" [Term.nat 9])).run.bind Val.asNat?

end Zag.Test.Exit
