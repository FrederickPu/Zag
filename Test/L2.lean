import Lang.Simple
import Lib.Peano

/-!
  L2 = AC LocalVarExtract (`L2Defs.thy` / `local_var_extract.ML`).

  **Not L1.** L1 keeps packed `FullState` + exception flags.
  L2 turns `state.get.i` / `state.set.i` into SSA locals `x`,`y`,…
  (see experimental `Lift/L2.fusedFromCom?` + `stateTermFields?`).
-/

namespace Zag.Test.L2

open Zag
open Zag.Lang.SSA
open Lang.Simple
open Lang.Simple.ABI
open Lang.Simple.Lift.L2
open Lang.Simple.C0.W2

def w (n : Nat) : Word := Word.ofNat n

/-! ## LocalContext = lifted locals (AC L2_gets names) -/

theorem locals_named_xy :
    locals.vars.map (·.name) = ["x", "y"] := by
  native_decide

/-! ## The fused helper rewrites Skip to the pack of SSA locals -/

theorem fromCom_skip_shape :
    fusedFromCom? (sc := ctx) (proc := Proc) (fault := Fault) locals .Skip =
      some (.ret locals.packCurrent) :=
  fromCom_skip locals

/-- Eval under **local env** `[Word, Word]`, not packed `State`. -/
theorem skip_eval_from_local_env :
    (do
      let e ← fusedFromCom? (sc := ctx) (proc := Proc) (fault := Fault) locals .Skip
      eval_L2 e (w 1) (w 2)) = some (w 1, w 2) := by
  native_decide

/-! ## Basic assignment: Simpl state.get/set → SSA locals -/

/-- C0 `x = x + y` lifts and evals on local env. -/
theorem add_l2_eval :
    (do let s ← add_fusedL2; eval_L2 s (w 10) (w 20)) = some (w 30, w 20) := by
  native_decide

theorem max_l2_eval :
    (do let s ← max_fusedL2; eval_L2 s (w 1) (w 9)) = some (w 9, w 9) := by
  native_decide

theorem add_fused_l2_isSome : add_fusedL2.isSome = true := by native_decide

/--
  L2 add does not take a single packed State as the only input —
  `eval_L2` feeds two Word locals (the lift).
-/
theorem add_l2_two_word_env :
    (do
      let ssa ← add_fusedL2
      evalSSAWithLocals? (sc := ctx) locals
        [State.wordVal (w 3), State.wordVal (w 4)] ssa).isSome = true := by
  native_decide

/-! ## Dialect whitelist = post-extract (no local ABI) -/

theorem drops_state_get :
    ¬ (targetDialect locals).primFns.contains "state.get.0" := by
  native_decide

theorem drops_state_set :
    ¬ (targetDialect locals).primFns.contains "state.set.0" := by
  native_decide

theorem drops_state_pack :
    ¬ (targetDialect locals).primFns.contains "state.pack.2" := by
  native_decide

theorem keeps_word_add :
    (targetDialect locals).primFns.contains "word.add" = true := by
  native_decide

theorem keeps_heap :
    (targetDialect locals).primFns.contains "heap.load" = true := by
  native_decide

/-- Ambient residual after lift = Globals (heap), not FullState. -/
theorem l2_ambient_is_globals :
    (targetDialect locals).State = Globals := rfl

/-! ## Contrast with L1: L1 still threads packed `st` -/

open Lang.Simple.Lift.L1 (toSSA? evalL1? packFlagged falseB)

theorem l1_skip_uses_packed_st :
    toSSA? (ctx := ctx) (proc := Proc) (fault := Fault) .Skip =
      some (.ret (packFlagged ctx.stateTy falseB falseB (.var "st"))) := rfl

theorem l1_eval_needs_full_state :
    (evalL1? (ctx := ctx)
      ((toSSA? (ctx := ctx) (proc := Proc) (fault := Fault) .Skip).get
        (by native_decide))
      (State.val [w 5, w 6])).isSome = true := by
  native_decide

end Zag.Test.L2
