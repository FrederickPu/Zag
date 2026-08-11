import Test.AutoCorres.CParser.ScalarSimpl.GcdFunction

namespace Zag.Test.AutoCorres.CParser.ScalarSimpl

open Zag.Lang.AutoCorres.CParser
open Zag.Lang.AutoCorres.CParser.ScalarSimpl
open FixtureHelpers

def gcdCondition : Zag.Lang.AutoCorres.CParser.ScalarSimpl.Expr :=
  .binary s32 u32 .notEqual (.variable u32 1) (.literal s32 0)

def gcdRemainder : Zag.Lang.AutoCorres.CParser.ScalarSimpl.Expr :=
  .binary u32 u32 .modulus (.variable u32 2) (.variable u32 1)

def gcdLoopBody : Stmt :=
  .seq
    (.seq (.assign 3 u32 (.variable u32 1))
      (.seq (.assign 1 u32 gcdRemainder)
        (.seq (.assign 2 u32 (.variable u32 3)) .skip)))
    .skip

def gcdLoop : Stmt := .while gcdCondition gcdLoopBody

def expectedGcd : Function :=
  { name := "gcd"
    returnType := u32
    parameters := [(1, u32), (2, u32)]
    locals := [3]
    body := .seq (.declare 3 u32 none)
      (.seq gcdLoop (.seq (.return u32 (.variable u32 2)) .skip)) }

set_option maxRecDepth 100000 in
set_option maxHeartbeats 500000 in
theorem gcd_is_exact_resolved_function : gcdFunction = expectedGcd := by native_decide

theorem gcd_body_has_uninitialized_c_loop_mod_assignments_and_return :
    gcdFunction.body = expectedGcd.body :=
  congrArg Function.body gcd_is_exact_resolved_function

def gcdEmitsSupported :
    Zag.Lang.AutoCorres.SimplConv.Kernel.Supported gcdFunction.command :=
  gcdCertificate.supported

theorem gcd_finite_execution_iff (state : State) (outcome : Raw.FunctionOutcome) :
    Raw.FunctionExec gcdCertificate.program "gcd" gcdCertificate.functionInfo
        gcdCertificate.rawBody gcdFunction.returnType state outcome ↔
      Zag.Lang.AutoCorres.Simpl.Exec emptyEnvironment gcdFunction.command (.normal state)
        (Raw.embedOutcome outcome) :=
  gcdCertificate.finite_iff state outcome

end Zag.Test.AutoCorres.CParser.ScalarSimpl
