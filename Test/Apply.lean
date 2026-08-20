import Test.Autocorres.Examples.Common

/-!
Blocks are values, and there is one calling convention.

`Term.call` and `Term.app` used to be different mechanisms: `call` looked a name up in
`ctx.blockCtx` and entered the block, while `app` evaluated a term to a `Val` of `func` type and
applied it. They were separate because a block cannot inhabit `Ty.type (.func …)` -- that type is
a *pure* Lean function into `Option`, and running a block needs the machine.

`Val.blockRef` closes the gap. A name with no local binding evaluates to the block of that name,
and `EvalState.applyValue` either applies a primitive function value or enters a block. So
`call f [x]` and `app (var f) [x]` are the same computation, and a block can be passed to another
block as an argument.

A block reference captures nothing: Zag blocks are top level and closed, since `enterBlock` builds
the callee's environment out of its parameters alone.
-/

namespace Zag.Test.Apply

open Zag Zag.Lib.PeanoHeap

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

abbrev applyCtx : Ctx := mkCtx applyBlocks applyBlocksValid

theorem applyCtx_wellTyped : Ctx.WellTyped applyCtx := by typecheck_ctx

/-! ### the two calling conventions agree -/

theorem double_call (x : Nat) :
    EvaluatesCall applyCtx "double" ([Val.nat x] : List (Val heapCtx)) (Val.nat (x + x)) := by
  evaluates_call 300 [heapOpCtx, Op.fixed, applyBlocks]

theorem increment_call (x : Nat) :
    EvaluatesCall applyCtx "increment" ([Val.nat x] : List (Val heapCtx)) (Val.nat (x + 1)) := by
  evaluates_call 300 [heapOpCtx, Op.fixed, applyBlocks]

/-- `call double [3]`. -/
example : EvaluatesTo applyCtx [] (.call "double" [Term.nat 3]) (Val.nat 6) := by
  evaluates 300 [heapOpCtx, Op.fixed, applyBlocks]

/-- `apply double [3]` -- the same computation, reached through `Val.blockRef`. -/
example : EvaluatesTo applyCtx [] (.app (.var "double") [Term.nat 3]) (Val.nat 6) := by
  evaluates 300 [heapOpCtx, Op.fixed, applyBlocks]

/-- A name with no local binding *is* the block, as a value. -/
example : EvaluatesTo applyCtx [] (.var "double")
    (Val.blockRef "double" [Peano.NatTy] Peano.NatTy) := by
  evaluates 300 [heapOpCtx, Op.fixed, applyBlocks]

/-! ### where the two conventions differ

  They reach the same state -- `enterBlock name block vargs env stack` -- but only when the name
  is not shadowed. `call f` looks `f` up in `ctx.blockCtx` and ignores the environment; `app
  (var f)` checks the environment first. So `call` means "the block, definitely" and `app (var f)`
  means "whatever `f` is here", and `Term.call` is *not* redundant. -/

/-- A local binding shadows a block of the same name. -/
example : EvaluatesTo applyCtx [("double", Val.nat 9)] (.var "double") (Val.nat 9) := by
  evaluates 300 [heapOpCtx, Op.fixed, applyBlocks]

/-- Under that binding `call` still reaches the block. -/
example : EvaluatesTo applyCtx [("double", Val.nat 9)] (.call "double" [Term.nat 3])
    (Val.nat 6) := by
  evaluates 300 [heapOpCtx, Op.fixed, applyBlocks]

/-- `app (var "double")` does not: it picks up the local `Val.nat 9`, and applying a value whose
  type is not a `func` fails, so the machine gets stuck rather than calling the block. -/
example : Term.evalApp (Val.nat 9 : Val heapCtx) [Val.nat 3] = none := rfl

/-- The dual half of `applyValue`: a block reference is not applied by `Term.evalApp` either.
  Running a block is the machine's job, so `EvalState.applyValue` intercepts it first. -/
example : Term.evalApp (Val.blockRef (primCtx := heapCtx) "double" [Peano.NatTy] Peano.NatTy)
    [Val.nat 3] = none := rfl

/-! ### passing a block to a block

  `twice` takes a function and applies it twice. Nothing in the language knew how to do this
  before: `call` needs a statically known name, so a block-valued *parameter* was inexpressible. -/

/-- A specification of `twice` at a *block-valued* argument. -/
theorem twiceDouble_eval (x : Nat) :
    EvaluatesCall applyCtx "twice"
      ([Val.blockRef "double" [Peano.NatTy] Peano.NatTy, Val.nat x] : List (Val heapCtx))
      (Val.nat (x + x + (x + x))) := by
  have double_twice :
      EvaluatesCall applyCtx "double" ([Val.nat (2 * x)] : List (Val heapCtx))
        (Val.nat (4 * x)) := by
    simpa only [← Nat.add_mul] using double_call (2 * x)
  evaluates_call_wp 300 [heapOpCtx, Op.fixed, applyBlocks]
  use_apply 300 [heapOpCtx, Op.fixed, applyBlocks]
    (EvaluatesApply.blockRef (argTys := [Peano.NatTy]) (outTy := Peano.NatTy)
      (double_call x))
  use_apply 300 [heapOpCtx, Op.fixed, applyBlocks]
    (EvaluatesApply.blockRef (argTys := [Peano.NatTy]) (outTy := Peano.NatTy)
      double_twice)

theorem twiceIncrement_eval (x : Nat) :
    EvaluatesCall applyCtx "twice"
      ([Val.blockRef "increment" [Peano.NatTy] Peano.NatTy, Val.nat x] : List (Val heapCtx))
      (Val.nat (x + 1 + 1)) := by
  evaluates_call_wp 300 [heapOpCtx, Op.fixed, applyBlocks]
  use_apply 300 [heapOpCtx, Op.fixed, applyBlocks]
    (EvaluatesApply.blockRef (argTys := [Peano.NatTy]) (outTy := Peano.NatTy)
      (increment_call x))
  use_apply 300 [heapOpCtx, Op.fixed, applyBlocks]
    (EvaluatesApply.blockRef (argTys := [Peano.NatTy]) (outTy := Peano.NatTy)
      (increment_call (x + 1)))

/-- `use_call` discharges the call to `twice` from that specification, with the block reference
  travelling through `evaluates_to_all` as an ordinary argument value. -/
theorem doubleTwice_eval : EvaluatesCall applyCtx "doubleTwice"
    ([Val.nat 5] : List (Val heapCtx)) (Val.nat 20) := by
  evaluates_call_wp 300 [heapOpCtx, Op.fixed, applyBlocks]
  use_call 300 [heapOpCtx, Op.fixed, applyBlocks] twiceDouble_eval

theorem incrementTwice_eval : EvaluatesCall applyCtx "incrementTwice"
    ([Val.nat 5] : List (Val heapCtx)) (Val.nat 7) := by
  evaluates_call_wp 300 [heapOpCtx, Op.fixed, applyBlocks]
  use_call 300 [heapOpCtx, Op.fixed, applyBlocks] twiceIncrement_eval

private abbrev wpFallbackBlocks : BlockCtx.Raw heapCtx :=
  blocks% [
    choose() : Nat {
      ret exit choose nat(1)
    },
    chooseCaller() : Nat {
      ret call choose []
    }
  ]

private theorem wpFallbackBlocksValid : BlockCtx.Valid wpFallbackBlocks := by
  valid_blocks [wpFallbackBlocks]

private abbrev wpFallbackCtx : Ctx := mkCtx wpFallbackBlocks wpFallbackBlocksValid

/-- The WP processor must not use the declaration under construction as its own call rule. -/
private theorem processEvalWPGoals_noSelfReference :
    EvaluatesCall wpFallbackCtx "choose" [] (Val.nat 1) := by
  fail_if_success (process_eval_wp_goals 0 [heapOpCtx, Op.fixed, wpFallbackBlocks] <;> done)
  evaluates_call 100 [heapOpCtx, Op.fixed, wpFallbackBlocks]

/-- Calls without direct semantic rules retain the machine evaluator fallback. -/
private theorem processEvalWPGoals_machineFallback (_n : Nat) :
    EvaluatesCall wpFallbackCtx "choose" [] (Val.nat 1) := by
  process_eval_wp_goals 100 [heapOpCtx, Op.fixed, wpFallbackBlocks]

/-- A named local call specification is collected before goal preprocessing can prune it. -/
private theorem processEvalWPGoals_localCallSpec :
    EvaluatesCall wpFallbackCtx "chooseCaller" [] (Val.nat 1) := by
  have hchoose : EvaluatesCall wpFallbackCtx "choose" [] (Val.nat 1) := by
    evaluates_call 100 [heapOpCtx, Op.fixed, wpFallbackBlocks]
  process_eval_wp_goals 0 [heapOpCtx, Op.fixed, wpFallbackBlocks]

/-! ### instruction-sequence composition -/

/-- A call specification fixes the instruction result before the dependent tail is processed. -/
example (x : Nat) : EvaluatesInstrs applyCtx
    [Instr.ofTerm "once" (.call "double" [Term.nat x]),
      Instr.ofTerm "answer" (.op "add" [.var "once", Term.nat 1])]
    (.var "answer") [] (Val.nat (x + x + 1)) := by
  use_call 300 [heapOpCtx, Op.fixed, applyBlocks] (double_call x)

/-- The same sequencing rule works when the instruction reaches the block through `Term.app`. -/
example (x : Nat) : EvaluatesInstrs applyCtx
    [Instr.ofTerm "once" (.app (.var "double") [Term.nat x]),
      Instr.ofTerm "answer" (.op "add" [.var "once", Term.nat 1])]
    (.var "answer") [] (Val.nat (x + x + 1)) := by
  use_apply 300 [heapOpCtx, Op.fixed, applyBlocks]
    (EvaluatesApply.blockRef (argTys := [Peano.NatTy]) (outTy := Peano.NatTy)
      (double_call x))

/-- The same `twice` block, driven by two different arguments. -/
example : EvaluatesTo applyCtx [] (.call "twice" [.var "double", Term.nat 3]) (Val.nat 12) := by
  evaluates 300 [heapOpCtx, Op.fixed, applyBlocks]

example : EvaluatesTo applyCtx [] (.call "twice" [.var "increment", Term.nat 3]) (Val.nat 5) := by
  evaluates 300 [heapOpCtx, Op.fixed, applyBlocks]

end Zag.Test.Apply
