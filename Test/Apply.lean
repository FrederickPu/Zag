import Test.Autocorres.Examples.Common
import Meta.Eval.VC

/-!
Blocks are values, and there is one calling convention.

`Term.call` and `Term.app` used to be different mechanisms: `call` looked a name up in
`ctx.blockCtx` and entered the block, while `app` evaluated a term to a `Val` of `func` type and
applied it. They were separate because a block cannot inhabit `Ty.type (.func …)` -- that type is
a *pure* Lean function into `Option`, and running a block needs the machine.

`Val.blockRef` closes the gap. A name with no local binding evaluates to the block of that name,
and `Machine.applyValue` either applies a primitive function value or enters a block. So
`call f [x]` and `app (var f) [x]` are the same computation, and a block can be passed to another
block as an argument.

A block reference captures nothing: Zag blocks are top level and closed, since `enterBlock` builds
the callee's environment out of its parameters alone.
-/

namespace Zag.Test.Apply

open Zag Zag.Lib.PeanoHeap
open Zag.Test.Autocorres.Examples
open Zag.EvalTriple.Exact

private abbrev heapOpCtx := pureHeapOpCtx

abbrev applyBlocks : BlockCtx.Raw heapCtx :=
  blocks% [
    double(n : Nat) : Nat {
      ret op "add"[n, n]
    },
    increment(n : Nat) : Nat {
      ret op "add"[n, nat(1)]
    },
    twice(f : func[Nat] => Nat, x : Nat) : Nat {
      once := apply f [x];
      ret apply f [once]
    },
    doubleTwice(x : Nat) : Nat {
      ret call twice [double, x]
    },
    incrementTwice(x : Nat) : Nat {
      ret call twice [increment, x]
    }
  ]

theorem applyBlocksValid : BlockCtx.Valid applyBlocks := by valid_blocks [applyBlocks]

abbrev applyCtx : Ctx := mkPureCtx applyBlocks applyBlocksValid

theorem applyCtx_wellTyped : Ctx.WellTyped applyCtx := by typecheck_ctx

/-! ### the two calling conventions agree -/

theorem double_call (x : Nat) :
    EvaluatesCallValues applyCtx "double" ([Val.nat x] : List (Val heapCtx)) (Val.nat (x + x)) := by
  apply EvaluatesCallValues.of_evaluatesInstrs
  · rfl
  · rfl
  apply EvaluatesInstrs.nil
  exact evaluates_add_nat
    (EvaluatesTo.var_local (name := "n") (by rfl))
    (EvaluatesTo.var_local (name := "n") (by rfl))

theorem increment_call (x : Nat) :
    EvaluatesCallValues applyCtx "increment" ([Val.nat x] : List (Val heapCtx)) (Val.nat (x + 1)) := by
  apply EvaluatesCallValues.of_evaluatesInstrs
  · rfl
  · rfl
  apply EvaluatesInstrs.nil
  exact evaluates_add_nat
    (EvaluatesTo.var_local (name := "n") (by rfl))
    (evaluates_nat _ 1)

/-- `call double [3]`. -/
example : EvaluatesTo applyCtx [] (.call "double" [Term.nat 3]) (Val.nat 6) := by
  exact EvaluatesTo.call (double_call 3) (by rfl)
    (EvaluatesList.cons (evaluates_nat [] 3) EvaluatesList.nil)

/-- `apply double [3]` -- the same computation, reached through `Val.blockRef`. -/
example : EvaluatesTo applyCtx [] (.app (.var "double") [Term.nat 3]) (Val.nat 6) := by
  exact EvaluatesTo.app
    (EvaluatesTo.var_block (ctx := applyCtx) (env := []) (name := "double")
      (block := applyBlocks[0].2) (by rfl) (by rfl))
    (EvaluatesList.cons (evaluates_nat [] 3) EvaluatesList.nil)
    (EvaluatesApply.blockRef (double_call 3))

/-- A name with no local binding *is* the block, as a value. -/
example : EvaluatesTo applyCtx [] (.var "double")
    (Val.blockRef "double" [Peano.NatTy] Peano.NatTy) := by
  exact EvaluatesTo.var_block (ctx := applyCtx) (env := []) (name := "double")
    (block := applyBlocks[0].2) (by rfl) (by rfl)

/-! ### where the two conventions differ

  They reach the same state -- `enterBlock name block vargs env stack` -- but only when the name
  is not shadowed. `call f` looks `f` up in `ctx.blockCtx` and ignores the environment; `app
  (var f)` checks the environment first. So `call` means "the block, definitely" and `app (var f)`
  means "whatever `f` is here", and `Term.call` is *not* redundant. -/

/-- A local binding shadows a block of the same name. -/
example : EvaluatesTo applyCtx [("double", Val.nat 9)] (.var "double") (Val.nat 9) := by
  exact EvaluatesTo.var_local (by rfl)

/-- Under that binding `call` still reaches the block. -/
example : EvaluatesTo applyCtx [("double", Val.nat 9)] (.call "double" [Term.nat 3])
    (Val.nat 6) := by
  exact EvaluatesTo.call (double_call 3) (by rfl)
    (EvaluatesList.cons (evaluates_nat _ 3) EvaluatesList.nil)

/-- `app (var "double")` does not: it picks up the local `Val.nat 9`, and applying a value whose
  type is not a `func` fails, so the machine gets stuck rather than calling the block. -/
example : Term.evalApp (Val.nat 9 : Val heapCtx) [Val.nat 3] = none := rfl

/-- The dual half of `applyValue`: a block reference is not applied by `Term.evalApp` either.
  Running a block is the machine's job, so `Machine.applyValue` intercepts it first. -/
example : Term.evalApp (Val.blockRef (primCtx := heapCtx) "double" [Peano.NatTy] Peano.NatTy)
    [Val.nat 3] = none := rfl

/-! ### passing a block to a block

  `twice` takes a function and applies it twice. Nothing in the language knew how to do this
  before: `call` needs a statically known name, so a block-valued *parameter* was inexpressible. -/

/-- A specification of `twice` at a *block-valued* argument. -/
theorem twiceDouble_eval (x : Nat) :
    EvaluatesCallValues applyCtx "twice"
      ([Val.blockRef "double" [Peano.NatTy] Peano.NatTy, Val.nat x] : List (Val heapCtx))
      (Val.nat (x + x + (x + x))) := by
  apply EvaluatesCallValues.of_evaluatesInstrs
  · rfl
  · rfl
  dsimp [applyBlocks, Block.entryEnv]
  apply EvaluatesInstrs.cons
  · exact EvaluatesTo.app
      (EvaluatesTo.var_local (by rfl))
      (EvaluatesList.cons (EvaluatesTo.var_local (by rfl)) EvaluatesList.nil)
      (EvaluatesApply.blockRef (double_call x))
  apply EvaluatesInstrs.nil
  exact EvaluatesTo.app
    (EvaluatesTo.var_local (by rfl))
    (EvaluatesList.cons (EvaluatesTo.var_local (by rfl)) EvaluatesList.nil)
    (EvaluatesApply.blockRef (double_call (x + x)))

theorem twiceIncrement_eval (x : Nat) :
    EvaluatesCallValues applyCtx "twice"
      ([Val.blockRef "increment" [Peano.NatTy] Peano.NatTy, Val.nat x] : List (Val heapCtx))
      (Val.nat (x + 1 + 1)) := by
  apply EvaluatesCallValues.of_evaluatesInstrs
  · rfl
  · rfl
  dsimp [applyBlocks, Block.entryEnv]
  apply EvaluatesInstrs.cons
  · exact EvaluatesTo.app
      (EvaluatesTo.var_local (by rfl))
      (EvaluatesList.cons (EvaluatesTo.var_local (by rfl)) EvaluatesList.nil)
      (EvaluatesApply.blockRef (increment_call x))
  apply EvaluatesInstrs.nil
  exact EvaluatesTo.app
    (EvaluatesTo.var_local (by rfl))
    (EvaluatesList.cons (EvaluatesTo.var_local (by rfl)) EvaluatesList.nil)
    (EvaluatesApply.blockRef (increment_call (x + 1)))

/-- The block reference travels through exact argument evaluation as an ordinary value. -/
theorem doubleTwice_eval : EvaluatesCallValues applyCtx "doubleTwice"
    ([Val.nat 5] : List (Val heapCtx)) (Val.nat 20) := by
  apply EvaluatesCallValues.of_evaluatesInstrs
  · rfl
  · rfl
  apply EvaluatesInstrs.nil
  exact EvaluatesTo.call (twiceDouble_eval 5) (by rfl)
    (EvaluatesList.cons
      (EvaluatesTo.var_block (ctx := applyCtx) (name := "double")
        (block := applyBlocks[0].2) (by rfl) (by rfl))
      (EvaluatesList.cons (EvaluatesTo.var_local (by rfl)) EvaluatesList.nil))

theorem incrementTwice_eval : EvaluatesCallValues applyCtx "incrementTwice"
    ([Val.nat 5] : List (Val heapCtx)) (Val.nat 7) := by
  apply EvaluatesCallValues.of_evaluatesInstrs
  · rfl
  · rfl
  apply EvaluatesInstrs.nil
  exact EvaluatesTo.call (twiceIncrement_eval 5) (by rfl)
    (EvaluatesList.cons
      (EvaluatesTo.var_block (ctx := applyCtx) (name := "increment")
        (block := applyBlocks[1].2) (by rfl) (by rfl))
      (EvaluatesList.cons (EvaluatesTo.var_local (by rfl)) EvaluatesList.nil))

private abbrev vcFallbackBlocks : BlockCtx.Raw heapCtx :=
  blocks% [
    choose() : Nat {
      ret exit choose nat(1)
    },
    chooseCaller() : Nat {
      ret call choose []
    }
  ]

private theorem vcFallbackBlocksValid : BlockCtx.Valid vcFallbackBlocks := by
  valid_blocks [vcFallbackBlocks]

private abbrev vcFallbackCtx : Ctx := mkPureCtx vcFallbackBlocks vcFallbackBlocksValid

/-- Self-exit blocks close by `of_exit` without treating the goal as its own call rule. -/
private theorem zvcgen_noSelfReference :
    EvaluatesCallValues (hM := rfl) vcFallbackCtx "choose" [] (Val.nat 1) := by
  zvcgen? 0 [heapOpCtx, Op.fixed, vcFallbackBlocks]

/-- Calls without direct semantic rules retain the machine evaluator fallback. -/
private theorem zvcgen_machineFallback (_n : Nat) :
    EvaluatesCallValues (hM := rfl) vcFallbackCtx "choose" [] (Val.nat 1) := by
  zvcgen? 100 [heapOpCtx, Op.fixed, vcFallbackBlocks]

/-- A named local call specification composes with a caller whose result is that call. -/
private theorem zvcgen_localCallSpec :
    EvaluatesCallValues (hM := rfl) vcFallbackCtx "chooseCaller" [] (Val.nat 1) := by
  have hchoose : EvaluatesCallValues (hM := rfl) vcFallbackCtx "choose" [] (Val.nat 1) := by
    evaluates_call 100 [heapOpCtx, Op.fixed, vcFallbackBlocks]
  apply EvaluatesCallValues.of_evaluatesInstrs
  · rfl
  · rfl
  dsimp [vcFallbackBlocks, Block.entryEnv]
  apply EvaluatesInstrs.nil
  exact EvaluatesTo.call hchoose (by rfl) EvaluatesList.nil

/-! ### instruction-sequence composition -/

/-- A call specification fixes the instruction result before the dependent tail is processed. -/
example (x : Nat) : EvaluatesInstrs applyCtx
    [Instr.ofTerm "once" (.call "double" [Term.nat x]),
      Instr.ofTerm "answer" (.op "add" [.var "once", Term.nat 1])]
    (.var "answer") [] (Val.nat (x + x + 1)) := by
  apply EvaluatesInstrs.cons
  · exact EvaluatesTo.call (double_call x) (by rfl)
      (EvaluatesList.cons (evaluates_nat [] x) EvaluatesList.nil)
  apply EvaluatesInstrs.cons
  · exact evaluates_add_nat
      (EvaluatesTo.var_local (by rfl))
      (evaluates_nat _ 1)
  exact EvaluatesInstrs.nil (EvaluatesTo.var_local (by rfl))

/-- The same sequencing rule works when the instruction reaches the block through `Term.app`. -/
example (x : Nat) : EvaluatesInstrs applyCtx
    [Instr.ofTerm "once" (.app (.var "double") [Term.nat x]),
      Instr.ofTerm "answer" (.op "add" [.var "once", Term.nat 1])]
    (.var "answer") [] (Val.nat (x + x + 1)) := by
  apply EvaluatesInstrs.cons
  · exact EvaluatesTo.app
      (EvaluatesTo.var_block (ctx := applyCtx) (env := []) (name := "double")
        (block := applyBlocks[0].2) (by rfl) (by rfl))
      (EvaluatesList.cons (evaluates_nat [] x) EvaluatesList.nil)
      (EvaluatesApply.blockRef (double_call x))
  apply EvaluatesInstrs.cons
  · exact evaluates_add_nat
      (EvaluatesTo.var_local (by rfl))
      (evaluates_nat _ 1)
  exact EvaluatesInstrs.nil (EvaluatesTo.var_local (by rfl))

/-- The same `twice` block, driven by two different arguments. -/
example : EvaluatesTo applyCtx [] (.call "twice" [.var "double", Term.nat 3]) (Val.nat 12) := by
  exact EvaluatesTo.call (twiceDouble_eval 3) (by rfl)
    (EvaluatesList.cons
      (EvaluatesTo.var_block (ctx := applyCtx) (env := []) (name := "double")
        (block := applyBlocks[0].2) (by rfl) (by rfl))
      (EvaluatesList.cons (evaluates_nat [] 3) EvaluatesList.nil))

example : EvaluatesTo applyCtx [] (.call "twice" [.var "increment", Term.nat 3]) (Val.nat 5) := by
  exact EvaluatesTo.call (twiceIncrement_eval 3) (by rfl)
    (EvaluatesList.cons
      (EvaluatesTo.var_block (ctx := applyCtx) (env := []) (name := "increment")
        (block := applyBlocks[1].2) (by rfl) (by rfl))
      (EvaluatesList.cons (evaluates_nat [] 3) EvaluatesList.nil))

end Zag.Test.Apply
