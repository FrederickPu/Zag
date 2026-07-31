import Lang.Simple
import Lib.Peano

/-!
  L1 exception ladder on Word2 — AutoCorres L1 outcomes.

  Proves by execution that L1 encodes:
  Normal / Abrupt / Fault and Seq/Catch short-circuit correctly.
-/

namespace Zag.Test.L1

open Zag
open Lang.Simple
open Lang.Simple.ABI
open Lang.Simple.Lift.L1
open Lang.Simple.C0.W2 (ctx)

/-- Empty proc env (no Call). -/
def Γ : ProcEnv ctx Empty Unit := fun _ => none
def uf : Unit := ()

abbrev Proc := Empty
abbrev Fault := Unit

def w (n : Nat) : Word := Word.ofNat n
def stVal (x y : Word) : Val ctx.primCtx := State.val [x, y]

def boolFalse : BExp ctx :=
  ⟨Term.bool (primCtx := ctx.primCtx) false, Term.hasType.prim _⟩
def boolTrue : BExp ctx :=
  ⟨Term.bool (primCtx := ctx.primCtx) true, Term.hasType.prim _⟩

def decode? (v : Val ctx.primCtx) : Option (Bool × Bool × Nat × Nat) := do
  let tys := [boolTy, boolTy, StateTy]
  let raw ← v.as? (.struct tys)
  let f := cast (Ty.type.eq_5 ctx.primCtx tys) raw
  let fault := Ty.toBool ctx.primCtx (f ⟨0, by decide⟩)
  let abrupt := Ty.toBool ctx.primCtx (f ⟨1, by decide⟩)
  let st := State.toWords (f ⟨2, by decide⟩)
  match st with
  | [x, y] => some (fault, abrupt, Word.toNat x, Word.toNat y)
  | _ => none

def run (cmd : Com ctx Proc Fault) (x y : Nat) : Option (Bool × Bool × Nat × Nat) := do
  let e ← toSSA? (ctx := ctx) (proc := Proc) (fault := Fault) cmd
  let v ← evalL1? e (stVal (w x) (w y))
  decode? v

theorem skip_normal : run .Skip 3 4 = some (false, false, 3, 4) := by native_decide
theorem throw_abrupt : run .Throw 3 4 = some (false, true, 3, 4) := by native_decide
theorem catch_throw_skip :
    run (.Catch .Throw .Skip) 3 4 = some (false, false, 3, 4) := by native_decide
theorem seq_throw_skip :
    run (.Seq .Throw .Skip) 3 4 = some (false, true, 3, 4) := by native_decide
theorem guard_false_fault :
    run (.Guard boolFalse .Skip) 3 4 = none := by native_decide
theorem guard_true_skip :
    run (.Guard boolTrue .Skip) 3 4 = some (false, false, 3, 4) := by native_decide
theorem seq_skip_skip :
    run (.Seq .Skip .Skip) 1 2 = some (false, false, 1, 2) := by native_decide
theorem cond_true_skip :
    run (.Cond boolTrue .Skip .Throw) 5 6 = some (false, false, 5, 6) := by native_decide
theorem cond_false_throw :
    run (.Cond boolFalse .Skip .Throw) 5 6 = some (false, true, 5, 6) := by native_decide

theorem exception_ladder :
    run .Skip 0 0 = some (false, false, 0, 0) ∧
    run .Throw 0 0 = some (false, true, 0, 0) ∧
    run (.Catch .Throw .Skip) 0 0 = some (false, false, 0, 0) ∧
    run (.Seq .Throw .Skip) 0 0 = some (false, true, 0, 0) ∧
    run (.Guard boolFalse .Skip) 0 0 = none := by
  native_decide

/--
  L1corres-style execution pins (AC L1Defs.thy:54–65):
  each BigStep outcome class is matched by `evalL1?` encoding.
  Full ∀-quantified `SimplExceptionFaithful` remains open; these are the
  concrete obligations for Skip/Throw/Catch/Guard on Word2.
-/
theorem l1corres_skip_exec :
    run .Skip 3 4 = some (false, false, 3, 4) := skip_normal

theorem l1corres_throw_exec :
    run .Throw 3 4 = some (false, true, 3, 4) := throw_abrupt

theorem l1corres_catch_exec :
    run (.Catch .Throw .Skip) 3 4 = some (false, false, 3, 4) :=
  catch_throw_skip

theorem l1corres_guard_fault_exec :
    run (.Guard boolFalse .Skip) 3 4 = none :=
  guard_false_fault

/-- FullState is the L1 ambient carrier (not bare list). -/
theorem l1_state_is_fullstate :
    (State.asFull? (stVal (w 1) (w 2))).isSome = true := by
  native_decide

theorem l1_state_locals :
    (State.asFull? (stVal (w 1) (w 2))).map (·.locals) =
      some [w 1, w 2] := by
  native_decide

theorem l1_project_globals_empty_heap :
    ((State.asFull? (stVal (w 1) (w 2))).map projectGlobals).map (·.heap) =
      some [] := by
  native_decide

/-- While lowers via `loopBody`→`recurse` (`partial_fixpoint`); no fuel. -/
theorem while_lowers :
    (toSSA? (ctx := ctx) (proc := Proc) (fault := Fault)
      (.While boolFalse .Skip)).isSome = true := by
  native_decide

/-- False condition: exit immediately, state preserved (AC L1_while). -/
theorem while_false_skip :
    run (.While boolFalse .Skip) 3 4 = some (false, false, 3, 4) := by
  native_decide

theorem while_false_ignores_body :
    run (.While boolFalse (.Seq .Throw .Skip)) 1 2 = some (false, false, 1, 2) := by
  native_decide

/-- One iteration then exit: cond true once via constant, body Skip, then false — need
    stateful cond; constant-true would diverge. Body Throw exits abrupt (AC while+throw). -/
theorem while_true_throw_abrupt :
    run (.While boolTrue .Throw) 5 6 = some (false, true, 5, 6) := by
  native_decide

/-- Seq of Basic-free programs: L1 matches BigStep outcome classes. -/
theorem l1_matches_bigstep_classes :
    run .Skip 0 0 = some (false, false, 0, 0) ∧
    run .Throw 0 0 = some (false, true, 0, 0) ∧
    run (.Guard boolFalse .Skip) 0 0 = none ∧
    run (.While boolFalse .Skip) 0 0 = some (false, false, 0, 0) ∧
    run (.While boolTrue .Throw) 0 0 = some (false, true, 0, 0) := by
  native_decide

/-- Catch+While: abrupt from body is handled (AC L1_catch / L1_while). -/
theorem while_throw_catch :
    run (.Catch (.While boolTrue .Throw) .Skip) 2 3 = some (false, false, 2, 3) := by
  native_decide

/-- Cond inside Seq preserves short-circuit. -/
theorem seq_cond_throw :
    run (.Seq (.Cond boolFalse .Skip .Throw) .Skip) 1 1 = some (false, true, 1, 1) := by
  native_decide

/-! ### BigStep ↔ L1 exec (AC L1corres direction on Word2) -/

theorem bigstep_skip_word2 (x y : Word) :
    BigStep (ctx := ctx) (proc := Empty) (fault := Unit) Γ uf
      .Skip (.normal (stVal x y)) (.normal (stVal x y)) :=
  bigStep_skip_normal (ctx := ctx) (proc := Empty) (fault := Unit) Γ uf _

theorem bigstep_throw_word2 (x y : Word) :
    BigStep (ctx := ctx) (proc := Empty) (fault := Unit) Γ uf
      .Throw (.normal (stVal x y)) (.abrupt (stVal x y)) :=
  bigStep_throw_abrupt (ctx := ctx) (proc := Empty) (fault := Unit) Γ uf _

/-- L1corres-style: BigStep Normal Skip is matched by L1 Normal encoding. -/
theorem l1corres_skip_word2 :
    BigStep (ctx := ctx) (proc := Empty) (fault := Unit) Γ uf
      .Skip (.normal (stVal (w 3) (w 4))) (.normal (stVal (w 3) (w 4))) ∧
    run .Skip 3 4 = some (false, false, 3, 4) :=
  ⟨bigstep_skip_word2 _ _, skip_normal⟩

theorem l1corres_throw_word2 :
    BigStep (ctx := ctx) (proc := Empty) (fault := Unit) Γ uf
      .Throw (.normal (stVal (w 3) (w 4))) (.abrupt (stVal (w 3) (w 4))) ∧
    run .Throw 3 4 = some (false, true, 3, 4) :=
  ⟨bigstep_throw_word2 _ _, throw_abrupt⟩

theorem l1corres_guard_false_word2 :
    BigStep (ctx := ctx) (proc := Empty) (fault := Unit) Γ uf
      (.Guard boolFalse .Skip)
       (.normal (stVal (w 3) (w 4))) (.fault uf (stVal (w 3) (w 4))) ∧
    run (.Guard boolFalse .Skip) 3 4 = none := by
  refine ⟨BigStep.guardFalse (ctx := ctx) (proc := Empty) (fault := Unit) ?_,
    guard_false_fault⟩
  native_decide

theorem fault_retains_state :
    Outcome.state? (.fault uf (stVal (w 3) (w 4))) = some (stVal (w 3) (w 4)) := rfl

theorem fault_seq_retains_state :
    BigStep (ctx := ctx) (proc := Empty) (fault := Unit) Γ uf
      (.Seq (.Guard boolFalse .Skip) .Skip)
      (.normal (stVal (w 3) (w 4)))
      (.fault uf (stVal (w 3) (w 4))) := by
  apply BigStep.seqFault
  exact BigStep.guardFalse (by native_decide)

theorem fault_catch_retains_state :
    BigStep (ctx := ctx) (proc := Empty) (fault := Unit) Γ uf
      (.Catch (.Guard boolFalse .Skip) .Skip)
      (.normal (stVal (w 3) (w 4)))
      (.fault uf (stVal (w 3) (w 4))) := by
  apply BigStep.catchFault
  exact BigStep.guardFalse (by native_decide)

/-- L1 is exception rewrite only — still uses packed FullState (not local lift). -/
theorem l1_skip_still_packed_state :
    toSSA_exnCore? (ctx := ctx) (proc := Empty) (fault := Unit) .Skip =
      some (.ret (packFlagged ctx.stateTy falseB falseB (.var "st"))) := rfl

theorem faithful_exnCore_word2_shape :
    toSSA_exnCore? (ctx := ctx) (proc := Empty) (fault := Unit) .Throw =
      some (.ret (packFlagged ctx.stateTy falseB trueB (.var "st"))) ∧
    BigStep Γ uf .Skip (.normal (stVal (w 0) (w 0))) (.normal (stVal (w 0) (w 0))) ∧
    BigStep Γ uf .Throw (.normal (stVal (w 0) (w 0))) (.abrupt (stVal (w 0) (w 0))) :=
  ⟨rfl, bigstep_skip_word2 _ _, bigstep_throw_word2 _ _⟩

end Zag.Test.L1
