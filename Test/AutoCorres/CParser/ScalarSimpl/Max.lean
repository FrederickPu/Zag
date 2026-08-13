import Test.AutoCorres.CParser.ScalarSimpl.MaxResolution
import Lang.AutoCorres.ML.simpl_conv
import Lang.AutoCorres.ML.type_strengthen

namespace Zag.Test.AutoCorres.CParser.ScalarSimpl

open Zag.Lang.AutoCorres.CParser
open Zag.Lang.AutoCorres.CParser.ScalarSimpl
open FixtureHelpers

private def expectedMax : Function :=
  { name := "max"
    returnType := u32
    parameters := [(1, u32), (2, u32)]
    locals := []
    body := .seq
      (.cond (.binary s32 u32 .lessEqual (.variable u32 1) (.variable u32 2))
        (.seq (.seq (.return u32 (.variable u32 2)) .skip) .skip) .skip)
      (.seq (.return u32 (.variable u32 1)) .skip) }

set_option maxRecDepth 100000 in
set_option maxHeartbeats 500000 in
theorem max_is_resolved_by_symbol_id : maxFunction = expectedMax := by
  native_decide

private def maxInitial (a b : Int) : State :=
  match maxFunction.enter [a, b] with
  | .ok state => state
  | .error _ => {}

private def maxResult (a b : Int) : State :=
  (maxInitial a b).resetReturn.returnValue u32
    (if u32.cast a ≤ u32.cast b then u32.cast b else u32.cast a)

private theorem max_read_one (a b : Int) :
    (maxInitial a b).resetReturn.read? 1 = some (u32.cast a) := by
  simp [maxInitial, max_is_resolved_by_symbol_id, expectedMax, Function.enter,
    State.resetReturn, State.read?, State.write]

private theorem max_read_two (a b : Int) :
    (maxInitial a b).resetReturn.read? 2 = some (u32.cast b) := by
  simp [maxInitial, max_is_resolved_by_symbol_id, expectedMax, Function.enter,
    State.resetReturn, State.read?, State.write]

theorem max_resolved_executes (a b : Int) :
    maxFunction.Exec (maxInitial a b) (.normal (maxResult a b)) := by
  apply Function.Exec.returned
  rw [max_is_resolved_by_symbol_id]
  by_cases ordered : u32.cast a ≤ u32.cast b
  · apply Stmt.Exec.seqReturned
    apply Stmt.Exec.condTrue (value := 1)
    · simp [Expr.eval, max_read_one, max_read_two, u32_cast_idempotent, ordered]
    · decide
    · apply Stmt.Exec.seqReturned
      apply Stmt.Exec.seqReturned
      apply Stmt.Exec.ret
      simpa [Expr.eval, maxResult, ordered] using max_read_two a b
  · apply Stmt.Exec.seqNormal
    · apply Stmt.Exec.condFalse
      · simp [Expr.eval, max_read_one, max_read_two, u32_cast_idempotent, ordered]
      · exact .skip
    · apply Stmt.Exec.seqReturned
      apply Stmt.Exec.ret
      simpa [Expr.eval, maxResult, ordered] using max_read_one a b

theorem max_generated_simpl_executes (a b : Int) :
    Zag.Lang.AutoCorres.Simpl.Exec emptyEnvironment maxFunction.command
      (.normal (maxInitial a b)) (.normal (maxResult a b)) :=
  maxFunction.command_correct _ _ (max_resolved_executes a b)

def maxEmitsSupported :
    Zag.Lang.AutoCorres.SimplConv.Kernel.Supported maxFunction.command :=
  maxCertificate.supported

theorem max_finite_execution_equivalence :
    Raw.Equivalent maxCertificate.program "max" maxCertificate.functionInfo
      maxCertificate.rawBody maxFunction.returnType maxFunction.command :=
  maxCertificate.resolution.compose

theorem max_finite_execution_iff (state : State) (outcome : Raw.FunctionOutcome) :
    Raw.FunctionExec maxCertificate.program "max" maxCertificate.functionInfo
        maxCertificate.rawBody maxFunction.returnType state outcome ↔
      Zag.Lang.AutoCorres.Simpl.Exec emptyEnvironment maxFunction.command (.normal state)
        (Raw.embedOutcome outcome) :=
  maxCertificate.finite_iff state outcome

theorem max_raw_fixture_executes_then_branch :
    Raw.FunctionExec maxCertificate.program "max" maxCertificate.functionInfo
      maxCertificate.rawBody maxFunction.returnType (maxInitial 4 9)
        (.success (maxResult 4 9)) :=
  (max_finite_execution_iff (maxInitial 4 9) (.success (maxResult 4 9))).2 (by
    simpa [Raw.embedOutcome] using max_generated_simpl_executes 4 9)

theorem max_raw_then_branch_executes_in_simpl :
    Zag.Lang.AutoCorres.Simpl.Exec emptyEnvironment maxFunction.command
      (.normal (maxInitial 4 9)) (.normal (maxResult 4 9)) := by
  simpa [Raw.embedOutcome] using
    (max_finite_execution_iff (maxInitial 4 9) (.success (maxResult 4 9))).1
      max_raw_fixture_executes_then_branch

theorem max_raw_fixture_executes_else_branch :
    Raw.FunctionExec maxCertificate.program "max" maxCertificate.functionInfo
      maxCertificate.rawBody maxFunction.returnType (maxInitial 9 4)
        (.success (maxResult 9 4)) :=
  (max_finite_execution_iff (maxInitial 9 4) (.success (maxResult 9 4))).2 (by
    simpa [Raw.embedOutcome] using max_generated_simpl_executes 9 4)

theorem max_raw_else_branch_executes_in_simpl :
    Zag.Lang.AutoCorres.Simpl.Exec emptyEnvironment maxFunction.command
      (.normal (maxInitial 9 4)) (.normal (maxResult 9 4)) := by
  simpa [Raw.embedOutcome] using
    (max_finite_execution_iff (maxInitial 9 4) (.success (maxResult 9 4))).1
      max_raw_fixture_executes_else_branch

/-! Phase-local regressions. These are exact for their stated manual models, but
are not claimed to be generated from `maxFunction`. -/

namespace MaxManual

open Zag.Lang.AutoCorres

abbrev Word32 := BitVec 32
private def w32 (value : Nat) : Word32 := BitVec.ofNat 32 value

structure State where
  a : Word32
  b : Word32
  result : Word32
  deriving DecidableEq

def env : Simpl.Body State Unit Unit := fun _ => none

def source : Simpl.Com State Unit Unit :=
  .Cond (fun state => state.a.toNat <= state.b.toNat)
    (.Basic fun state => { state with result := state.b })
    (.Basic fun state => { state with result := state.a })

def supported : Zag.Lang.AutoCorres.SimplConv.Kernel.Supported source :=
  .cond (fun state : State => state.a.toNat <= state.b.toNat)
    (.basic fun state : State => { state with result := state.b })
    (.basic fun state : State => { state with result := state.a })

def certificate := ML.SimplConv.simplConv false env supported

theorem keeps_condition :
    match certificate.target with
    | .condition _ (.modify _) (.modify _) => True
    | _ => False := by
  trivial

theorem manual_source_corres : L1.L1Corres false env certificate.target.denote source :=
  certificate.corres

def initial : State := { a := w32 3, b := w32 5, result := 0 }

theorem chooses_larger_argument :
    (Except.ok (), { initial with result := w32 5 }) ∈
      (certificate.target.denote initial).results := by
  simp [certificate, supported, ML.SimplConv.simplConv,
    Zag.Lang.AutoCorres.SimplConv.Kernel.Target.denote, L1.condition,
    L1.modify, initial, w32]

namespace TypeStrengthen

open Zag.Lang.AutoCorres.TypeStrengthen.Kernel

abbrev Arguments := Word32 × Word32

def source : Source.Term Arguments Unit Unit Word32 :=
  .conditionPure (fun arguments => decide (arguments.1 <= arguments.2))
    (.pure Prod.snd ["ret"]) (.pure Prod.fst ["ret"])

def supported : Supported .pure source :=
  .pureCondition .pureValue .pureValue

def certificate (arguments : Arguments) :=
  ML.TypeStrengthen.strengthenAt supported arguments

theorem target_is_max (arguments : Arguments) :
    (certificate arguments).target.denote =
      if decide (arguments.1 <= arguments.2) then arguments.2 else arguments.1 := by
  rfl

theorem manual_phase_exact (arguments : Arguments) :
    source.denote arguments =
      Zag.Lang.AutoCorres.TypeStrengthen.embed .pure
        (certificate arguments).target.denote :=
  (certificate arguments).equality

end TypeStrengthen

end MaxManual

end Zag.Test.AutoCorres.CParser.ScalarSimpl
