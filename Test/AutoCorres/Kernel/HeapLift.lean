import Lang.AutoCorres.ML.heap_lift

/-!
# HeapLift kernel test

This is a synthetic kernel test, not an upstream test-suite port. Its rules are
derived from:

* [`HeapLift.thy`](https://github.com/seL4/l4v/blob/bc2599a59c43e673dca021b10b9841e9b8da4430/tools/autocorres/HeapLift.thy)
* [`heap_lift.ML`](https://github.com/seL4/l4v/blob/bc2599a59c43e673dca021b10b9841e9b8da4430/tools/autocorres/heap_lift.ML)

The test supplies abstraction evidence explicitly. It changes state
representations, drops concrete audit data, and enforces a nontrivial validity
guard, but does not claim parser, layout, or evidence discovery.
-/

namespace Zag.Test.AutoCorres.Kernel.HeapLift

open Zag.Lang.AutoCorres
open Zag.Lang.AutoCorres.HeapLift
open Zag.Lang.AutoCorres.HeapLift.Kernel

structure ConcreteState where
  rawCell : Nat
  valid : Bool
  audit : Nat
  deriving DecidableEq

structure AbstractState where
  cell : Nat
  valid : Bool
  deriving DecidableEq

def stateMap (state : ConcreteState) : AbstractState :=
  { cell := state.rawCell, valid := state.valid }

def readConcrete (state : ConcreteState) : Nat := state.rawCell
def readAbstract (state : AbstractState) : Nat := state.cell

def writeConcrete (value : Nat) (state : ConcreteState) : ConcreteState :=
  { state with rawCell := value, audit := state.audit + 1 }

def writeAbstract (value : Nat) (state : AbstractState) : AbstractState :=
  { state with cell := value }

def isValid (state : AbstractState) : Prop := state.valid = true

def readEvidence :
    ExprEvidence stateMap readConcrete where
  rewritePrecondition := fun _ => True
  rewritten := readConcrete
  abstractRewriteGuard := fun _ => True
  abstractExpressionGuard := isValid
  abstract := readAbstract
  rewrite := struct_rewrite_expr_id readConcrete
  rewriteGuardAbstracts := abs_guard_constant True
  expressionAbstracts := by
    simp [abs_expr, stateMap, readConcrete, readAbstract]

def writeEvidence (value : Nat) :
    UpdateEvidence stateMap (writeConcrete value) where
  rewritePrecondition := fun _ => True
  rewritten := writeConcrete value
  abstractRewriteGuard := fun _ => True
  abstractUpdateGuard := isValid
  abstract := writeAbstract value
  rewrite := struct_rewrite_modifies_id (writeConcrete value)
  rewriteGuardAbstracts := abs_guard_constant True
  updateAbstracts := by
    simp [abs_modifies, stateMap, writeConcrete, writeAbstract]

def source : Source ConcreteState Unit Unit :=
  .seq (.gets readConcrete ["cell"]) fun value =>
    .modify (writeConcrete (value + 1))

theorem source_alias_is_canonical_l2_syntax :
    (source : L2.Syntax ConcreteState Unit Unit) =
      .seq (.gets readConcrete ["cell"]) fun value =>
        .modify (writeConcrete (value + 1)) := by
  rfl

theorem source_alias_has_canonical_l2_denotation :
    Source.denote source =
      L2.Syntax.denote (source : L2.Syntax ConcreteState Unit Unit) := by
  rfl

def supported : Supported stateMap source :=
  .seq (.gets ["cell"] readEvidence) fun value =>
    .modify (writeEvidence (value + 1))

def certificate := ML.HeapLift.transform supported

local macro "simp_certificate" : tactic => `(tactic|
  simp [certificate, supported, ML.HeapLift.transform, readEvidence,
    writeEvidence, isValid])

theorem exact_target :
    certificate.target =
      Target.seq
        (.guardedGets (fun _ => True) isValid readAbstract ["cell"])
        (fun value => .guardedModify (fun _ => True) isValid
          (writeAbstract (value + 1))) := by
  rfl

theorem read_guard_accepts_valid :
    match certificate.target with
    | .seq (.guardedGets rewriteGuard expressionGuard _ _) _ =>
        rewriteGuard { cell := 7, valid := true } ∧
          expressionGuard { cell := 7, valid := true }
    | _ => False := by
  simp_certificate

theorem read_guard_rejects_invalid :
    match certificate.target with
    | .seq (.guardedGets _ expressionGuard _ _) _ =>
        ¬expressionGuard { cell := 7, valid := false }
    | _ => False := by
  simp_certificate

theorem update_guard_rejects_invalid :
    ¬(writeEvidence 8).abstractUpdateGuard { cell := 7, valid := false } := by
  simp [writeEvidence, isValid]

theorem certified :
    L2Tcorres stateMap certificate.target.denote source.denote :=
  certificate.correctness

theorem target_runs_when_valid :
    (Except.ok (), { cell := 8, valid := true }) ∈
      (certificate.target.denote { cell := 7, valid := true }).results := by
  simp [exact_target, Target.denote, readAbstract, writeAbstract, isValid,
    L2.seq, L2.guard, L2.gets, L2.modify]
  exact ⟨7, { cell := 7, valid := true }, ⟨rfl, rfl⟩,
    { cell := 7, valid := true }, ⟨rfl, rfl⟩, rfl, rfl⟩

theorem valid_target_does_not_fail :
    ¬(certificate.target.denote { cell := 7, valid := true }).failed := by
  simp [exact_target, Target.denote, isValid, L2.seq, L2.guard, bindE,
    L2.failed_liftE, Zag.Lang.AutoCorres.guard]
  constructor
  · intro x x1 x2 hx hfirst
    cases hx
    change (x2, x1) = ((), { cell := 7, valid := true }) at hfirst
    cases hfirst
    simp [L2.gets, L2.failed_liftE, Zag.Lang.AutoCorres.gets]
  · intro x x1 x2 x3 x4 hx2 hfirst hread
    cases hx2
    cases x4
    change ((), x3) = ((), { cell := 7, valid := true }) at hfirst
    cases hfirst
    rcases x with error | value
    · simp [L2.gets] at hread
    · simp [L2.gets] at hread
      rcases hread with ⟨rfl, rfl⟩
      simp [L2.modify,
        Zag.Lang.AutoCorres.bind, Zag.Lang.AutoCorres.liftE,
        Zag.Lang.AutoCorres.guard, returnOk, Zag.Lang.AutoCorres.pure]
      intro x x1 member
      rcases member with ⟨value, middle, _, returned⟩
      change (x, x1) = (Except.ok value, middle) at returned
      cases returned
      simp [Zag.Lang.AutoCorres.bind,
        Zag.Lang.AutoCorres.modify, Zag.Lang.AutoCorres.pure]

theorem target_fails_when_invalid :
    (certificate.target.denote { cell := 7, valid := false }).failed := by
  simp [exact_target, Target.denote, isValid, L2.seq, L2.guard, bindE,
    L2.failed_liftE, Zag.Lang.AutoCorres.guard]

theorem invalid_target_has_no_results
    (result : Except Unit Unit × AbstractState) :
    result ∉ (certificate.target.denote { cell := 7, valid := false }).results := by
  rw [exact_target]
  rcases result with ⟨outcome, post⟩
  simp [Target.denote, isValid, L2.seq, L2.guard, bindE,
    Zag.Lang.AutoCorres.bind,
    Zag.Lang.AutoCorres.liftE, Zag.Lang.AutoCorres.guard]
  rintro ⟨_, _, ⟨_, _, ⟨_, _, impossible, _⟩, _⟩, _⟩
  exact impossible

end Zag.Test.AutoCorres.Kernel.HeapLift
