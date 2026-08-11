import Test.AutoCorres.CParser.ScalarSimpl.Plus2Resolution

namespace Zag.Test.AutoCorres.CParser.ScalarSimpl

open Zag.Lang.AutoCorres.CParser.ScalarSimpl
open FixtureHelpers

def plus2Condition : Expr :=
  .binary s32 u32 .greater (.variable u32 2) (.literal s32 0)

def plus2Increment : Expr :=
  .binary u32 u32 .add (.variable u32 1) (.literal s32 1)

def plus2Decrement : Expr :=
  .binary u32 u32 .subtract (.variable u32 2) (.literal s32 1)

def plus2LoopBody : Stmt :=
  .seq (.seq (.assign 1 u32 plus2Increment)
    (.seq (.assign 2 u32 plus2Decrement) .skip)) .skip

def plus2Loop : Stmt := .while plus2Condition plus2LoopBody

def expectedPlus2 : Function :=
  { name := "plus2"
    returnType := u32
    parameters := [(1, u32), (2, u32)]
    locals := []
    body := .seq plus2Loop (.seq (.return u32 (.variable u32 1)) .skip) }

set_option maxRecDepth 100000 in
set_option maxHeartbeats 500000 in
theorem plus2_is_resolved_while_body : plus2 = expectedPlus2 := by native_decide

theorem plus2_body_is_actual_loop :
    plus2.body = .seq plus2Loop (.seq (.return u32 (.variable u32 1)) .skip) := by
  rw [plus2_is_resolved_while_body]
  rfl

end Zag.Test.AutoCorres.CParser.ScalarSimpl
