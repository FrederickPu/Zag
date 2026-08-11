import Test.AutoCorres.CParser.ScalarSimpl.MultByAddResolution

namespace Zag.Test.AutoCorres.CParser.ScalarSimpl

open Zag.Lang.AutoCorres.CParser.ScalarSimpl
open FixtureHelpers

def multByAddCondition : Expr :=
  .binary s32 u32 .greater (.variable u32 1) (.literal s32 0)

def multByAddResultIncrement : Expr :=
  .binary u32 u32 .add (.variable u32 3) (.variable u32 2)

def multByAddDecrement : Expr :=
  .binary u32 u32 .subtract (.variable u32 1) (.literal s32 1)

def multByAddLoopBody : Stmt :=
  .seq (.seq (.assign 3 u32 multByAddResultIncrement)
    (.seq (.assign 1 u32 multByAddDecrement) .skip)) .skip

def multByAddLoop : Stmt := .while multByAddCondition multByAddLoopBody

def expectedMultByAdd : Function :=
  { name := "mult_by_add"
    returnType := u32
    parameters := [(1, u32), (2, u32)]
    locals := [3]
    body := .seq (.declare 3 u32 (some (.literal s32 0)))
      (.seq multByAddLoop (.seq (.return u32 (.variable u32 3)) .skip)) }

set_option maxRecDepth 100000 in
set_option maxHeartbeats 500000 in
theorem mult_by_add_is_resolved_body : multByAdd = expectedMultByAdd := by native_decide

theorem mult_by_add_body_is_actual_initialized_loop :
    multByAdd.body = .seq (.declare 3 u32 (some (.literal s32 0)))
      (.seq multByAddLoop (.seq (.return u32 (.variable u32 3)) .skip)) := by
  rw [mult_by_add_is_resolved_body]
  rfl

theorem mult_by_add_loop_body_has_actual_post_decrement :
    multByAddLoopBody =
      .seq (.seq (.assign 3 u32 multByAddResultIncrement)
        (.seq (.assign 1 u32
          (.binary u32 u32 .subtract (.variable u32 1) (.literal s32 1))) .skip)) .skip := by
  rfl

end Zag.Test.AutoCorres.CParser.ScalarSimpl
