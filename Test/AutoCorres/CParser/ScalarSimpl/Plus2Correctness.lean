import Test.AutoCorres.CParser.ScalarSimpl.Plus2Invariant
import Test.AutoCorres.CParser.ScalarSimpl.Plus

namespace Zag.Test.AutoCorres.CParser.ScalarSimpl

open Zag.Lang.AutoCorres.CParser.ScalarSimpl
open FixtureHelpers

abbrev Word32 := BitVec 32

def plus2Initial (a b : Word32) : State :=
  match plus2.enter [Int.ofNat a.toNat, Int.ofNat b.toNat] with
  | .ok state => state
  | .error _ => {}

def plus2Result (a b : Word32) : State :=
  (plus2State (Int.ofNat a.toNat + Int.ofNat b.toNat) 0).returnValue u32
    (u32.cast (Int.ofNat a.toNat + Int.ofNat b.toNat))

theorem plus2_initial_eq_state (a b : Word32) :
    plus2Initial a b = plus2State (Int.ofNat a.toNat) b.toNat := by
  simp [plus2Initial, plus2_is_resolved_while_body, expectedPlus2, Function.enter,
    plus2State, State.write]

theorem plus2_resolved_executes (a b : Word32) :
    plus2.Exec (plus2Initial a b) (.normal (plus2Result a b)) := by
  apply Function.Exec.returned
  rw [plus2_is_resolved_while_body, plus2_initial_eq_state]
  apply Stmt.Exec.seqNormal
  · exact plus2Loop_exec (Int.ofNat a.toNat) b.toNat b.isLt
  · apply Stmt.Exec.seqReturned
    apply Stmt.Exec.ret
    simp [Expr.eval, plus2State_read_a]

theorem plus2_generated_simpl_executes (a b : Word32) :
    Zag.Lang.AutoCorres.Simpl.Exec emptyEnvironment plus2.command
      (.normal (plus2Initial a b)) (.normal (plus2Result a b)) :=
  plus2.command_correct _ _ (plus2_resolved_executes a b)

def plus2EmitsSupported :
    Zag.Lang.AutoCorres.SimplConv.Kernel.Supported plus2.command :=
  plus2Certificate.supported

theorem plus2_finite_execution_equivalence :
    Raw.Equivalent plus2Certificate.program "plus2" plus2Certificate.functionInfo
      plus2Certificate.rawBody plus2.returnType plus2.command :=
  plus2Certificate.resolution.compose

theorem plus2_finite_execution_iff (state : State) (outcome : Raw.FunctionOutcome) :
    Raw.FunctionExec plus2Certificate.program "plus2" plus2Certificate.functionInfo
        plus2Certificate.rawBody plus2.returnType state outcome ↔
      Zag.Lang.AutoCorres.Simpl.Exec emptyEnvironment plus2.command (.normal state)
        (Raw.embedOutcome outcome) :=
  plus2Certificate.finite_iff state outcome

theorem plus2_raw_fixture_executes (a b : Word32) :
    Raw.FunctionExec plus2Certificate.program "plus2" plus2Certificate.functionInfo
      plus2Certificate.rawBody plus2.returnType (plus2Initial a b)
        (.success (plus2Result a b)) :=
  (plus2_finite_execution_iff (plus2Initial a b) (.success (plus2Result a b))).2 (by
    simpa [Raw.embedOutcome] using plus2_generated_simpl_executes a b)

theorem plus2_success_is_wrapping_add (a b : Word32) :
    BitVec.ofInt 32 (plus2Result a b).result = a + b := by
  change BitVec.ofInt 32
      (u32.cast (u32.cast (Int.ofNat a.toNat + Int.ofNat b.toNat))) = a + b
  rw [u32_cast_idempotent, bitvec_of_u32_cast, BitVec.ofInt_add,
    Int.ofNat_eq_natCast, Int.ofNat_eq_natCast, BitVec.ofInt_natCast,
    BitVec.ofInt_natCast]
  simp

theorem certified_plus_executes (a b : Word32) :
    plus.Exec (plusInitial (Int.ofNat a.toNat) (Int.ofNat b.toNat))
      (.normal (plusResult (Int.ofNat a.toNat) (Int.ofNat b.toNat))) :=
  plus_resolved_executes (Int.ofNat a.toNat) (Int.ofNat b.toNat)

theorem plus2_is_plus (a b : Word32) :
    BitVec.ofInt 32 (plus2Result a b).result =
      BitVec.ofInt 32
        (plusResult (Int.ofNat a.toNat) (Int.ofNat b.toNat)).result := by
  rw [plus2_success_is_wrapping_add]
  change a + b = BitVec.ofInt 32
    (u32.cast (u32.cast (u32.cast (Int.ofNat a.toNat) +
      u32.cast (Int.ofNat b.toNat))))
  rw [u32_cast_idempotent, bitvec_of_u32_cast, BitVec.ofInt_add,
    bitvec_of_u32_cast, bitvec_of_u32_cast, Int.ofNat_eq_natCast,
    Int.ofNat_eq_natCast, BitVec.ofInt_natCast, BitVec.ofInt_natCast]
  simp

end Zag.Test.AutoCorres.CParser.ScalarSimpl
