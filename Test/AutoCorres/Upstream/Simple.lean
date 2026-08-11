import Lang.AutoCorres.ML.simpl_conv
import Lang.AutoCorres.ML.type_strengthen
import Test.AutoCorres.CParser.ScalarSimpl.GcdCoreObstruction
import Test.AutoCorres.CParser.ScalarSimpl.GcdExecution
import Test.AutoCorres.CParser.ScalarSimpl.GcdPipelineFinal

/-!
# `Simple` upstream example

Sources:

* [`simple.c`](https://github.com/seL4/l4v/blob/bc2599a59c43e673dca021b10b9841e9b8da4430/tools/autocorres/tests/examples/simple.c)
* [`Simple.thy`](https://github.com/seL4/l4v/blob/bc2599a59c43e673dca021b10b9841e9b8da4430/tools/autocorres/tests/examples/Simple.thy)

This file retains the `max` pins and links the exact `gcd` fixture, Euclidean
proofs, generated five-phase chain, and arbitrary-input final correctness.
-/

namespace Zag.Test.AutoCorres.Upstream.Simple

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

namespace Gcd

open Zag.Test.AutoCorres.CParser.ScalarSimpl

def fixture_shape := gcd_body_has_uninitialized_c_loop_mod_assignments_and_return
def finite_c_simpl_correspondence := gcd_finite_execution_iff
def invariant_initial := gcd_invariant_initial
def invariant_preserved := gcd_invariant_preserved
def variant_decreases := gcd_variant_strictly_decreases
def final_result := gcd_invariant_final
def recursive_result := gcdWord_toNat
def word_abstract_guarded_map := kernel_unsigned_int_guard
def simpl_endpoint := GcdPipeline.fixture_simpl_endpoint
def lve_endpoint := GcdPipeline.lve_consumes_fixture_endpoint
def heap_lift_endpoint := GcdPipeline.heapLiftCorres
def word_abstract_endpoint := GcdPipeline.word_consumes_heap_endpoint
def type_strengthen_endpoint := GcdPipeline.type_strengthen_consumes_word_endpoint
noncomputable def generated_chain := GcdPipeline.finalChain
def generated_correspondence := GcdPipeline.finalAcCorres
def generated_exact := GcdPipeline.final_target_exact
def generated_pure_return := GcdPipeline.final_target_pure_return
def generated_no_failure := GcdPipeline.final_target_no_failure
def generated_correct := GcdPipeline.final_target_returns_only_gcd
def generated_valid := GcdPipeline.final_target_valid

end Gcd

end Zag.Test.AutoCorres.Upstream.Simple
