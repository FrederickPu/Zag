import Zag.Theory

/-!
# Concretizing a term against an environment

`Term.eval` is a `partial_fixpoint`, so a term is never evaluated by `rfl` or `decide`. What
takes their place is a *calculus*: one equation per term former rewriting `Term.eval ctx env t`
into the evaluations of `t`'s operands. Because the equations are unconditional they compose
under `simp`, so concretizing a whole term against an environment -- "what value does each bound
variable stand for" -- is a single rewrite pass rather than a hand-built chain of `have`s.

The environment is the concretization context: `env` binds each name in scope to a `Val`, which
may mention Lean variables. Evaluation is therefore symbolic in those variables, and the result
is an ordinary Lean expression built from them.

Everything here is generic in `Ctx`. Operator semantics come from `Op.ofVals`, which is the
shape every eager operator has, so one equation (`Term.eval_op_ofVals`) covers all of them.
Lazy operators -- the ones that choose which operands to evaluate -- need their own equation;
see `Lib/Peano/Eval.lean` for `ite`.
-/

namespace Zag

namespace Term

variable {ctx : Ctx}

/-! ### term formers -/

@[simp] theorem eval_prim (env : Env ctx.primCtx) (ty : Ty) (val : Ty.type ctx.primCtx ty) :
    Term.eval ctx env (no_index (Term.prim ty val)) = some (Val.mk ty val) :=
  Term.evalGo_prim ctx env ty val

@[simp] theorem eval_var (env : Env ctx.primCtx) (name : String) :
    Term.eval ctx env (no_index (Term.var name)) = Scope.get? env name :=
  Term.evalGo_var ctx env name

@[simp] theorem eval_exit (env : Env ctx.primCtx) (name : String) (value : Term ctx.primCtx) :
    Term.eval ctx env (no_index (Term.exit name value)) = none :=
  Term.evalGo_exit ctx env name value

@[simp] theorem evalList_nil (env : Env ctx.primCtx) :
    Term.evalList ctx env (no_index ([] : List (Term ctx.primCtx))) = some [] := by
  rw [Term.evalList, Term.evalListOutcome.eq_def]
  rfl

@[simp] theorem evalList_cons (env : Env ctx.primCtx) (term : Term ctx.primCtx)
    (terms : List (Term ctx.primCtx)) :
    Term.evalList ctx env (no_index (term :: terms)) = (do
      let value ← Term.eval ctx env term
      let values ← Term.evalList ctx env terms
      some (value :: values)) := by
  rw [Term.evalList, Term.evalListOutcome.eq_def, Term.eval, Term.evalGo, Term.evalList]
  cases hterm : Term.evalOutcome ctx env term with
  | none => simp [hterm]
  | some outcome =>
      cases outcome with
      | exit block value => simp [hterm, Outcome.ok?]
      | ok value =>
          cases hterms : Term.evalListOutcome ctx env terms with
          | none => simp [hterm, hterms, Outcome.ok?]
          | some rest => cases rest <;> simp [hterm, hterms, Outcome.ok?]

end Term

/-- What it means to call a named block on argument *values*.

  This is the normal form a `call` reduces to, and so it is the shape in which a block's
  specification is stated: `Term.evalCall ctx "plusLoop" [Val.nat x, Val.nat y] = some ..`.
  Stating it this way is what lets an induction hypothesis discharge the recursive call --
  the arguments at the call site are arbitrary terms, but once evaluated they are the same
  values the hypothesis speaks about. -/
def Term.evalCall (ctx : Ctx) (name : String) (vargs : List (Val ctx.primCtx)) :
    Option (Val ctx.primCtx) :=
  match ctx.blockCtx.get? name with
  | none => none
  | some block =>
      if vargs.length = block.params.length then
        (Term.evalBlock ctx name (block.entryEnv vargs) block).bind Outcome.ok?
      else none

namespace Term

variable {ctx : Ctx}

/-- An unwind that escapes the enclosing call is stuck at the level of values, so a call reads
  as: evaluate the arguments, then call the block on the resulting values. -/
@[simp] theorem eval_call_eq (env : Env ctx.primCtx) (name : String)
    (args : List (Term ctx.primCtx)) :
    Term.eval ctx env (no_index (Term.call name args)) =
      (Term.evalList ctx env args).bind (Term.evalCall ctx name) := by
  rw [Term.eval, Term.evalGo, Term.evalOutcome.eq_def, Term.evalList]
  cases hargs : Term.evalListOutcome ctx env args with
  | none => cases hblock : ctx.blockCtx.get? name <;> simp [hblock, hargs]
  | some outcome =>
      cases outcome with
      | exit b v => cases hblock : ctx.blockCtx.get? name <;> simp [hblock, hargs, Outcome.ok?]
      | ok vargs =>
          simp only [hargs, Option.bind_some, Outcome.ok?, Term.evalCall.eq_def]
          cases hblock : ctx.blockCtx.get? name with
          | none => simp
          | some block =>
              by_cases hlen : vargs.length = block.params.length <;> simp [hlen]

theorem evalOutcome_ok_of_eval {env : Env ctx.primCtx} {term : Term ctx.primCtx}
    {value : Val ctx.primCtx} (h : Term.eval ctx env term = some value) :
    Term.evalOutcome ctx env term = some (.ok value) := by
  rw [Term.eval, Term.evalGo] at h
  cases hterm : Term.evalOutcome ctx env term with
  | none => rw [hterm] at h; simp at h
  | some outcome =>
      cases outcome with
      | exit b v => rw [hterm] at h; simp [Outcome.ok?] at h
      | ok v =>
          rw [hterm] at h
          simp only [Option.bind_some, Outcome.ok?, Option.some.injEq] at h
          rw [h]

end Term

/-! ### running a block body

  `Block.run` is the value-level view of a block: instructions in order, each extending the
  environment with its own name, then the returned term. It says nothing about non-local exit,
  which is exactly why it is usable -- a `some` answer certifies that nothing unwound, and
  `Term.evalBlock_ok_of_run` turns it into the `Outcome`-level statement a call consumes. -/
def Block.run (ctx : Ctx) : Env ctx.primCtx → List (Instr ctx.primCtx) → Term ctx.primCtx →
    Option (Val ctx.primCtx)
| env, [], result => Term.eval ctx env result
| env, instr :: instrs, result => do
    let value ← Term.eval ctx env instr.value
    Block.run ctx (env ++ [(instr.name, value)]) instrs result

namespace Block

variable {ctx : Ctx}

@[simp] theorem run_nil (env : Env ctx.primCtx) (result : Term ctx.primCtx) :
    Block.run ctx env (no_index ([] : List (Instr ctx.primCtx))) result =
      Term.eval ctx env result := rfl

@[simp] theorem run_cons (env : Env ctx.primCtx) (instr : Instr ctx.primCtx)
    (instrs : List (Instr ctx.primCtx)) (result : Term ctx.primCtx) :
    Block.run ctx env (no_index (instr :: instrs)) result = (do
      let value ← Term.eval ctx env instr.value
      Block.run ctx (env ++ [(instr.name, value)]) instrs result) := rfl

end Block

namespace Term

variable {ctx : Ctx}

private theorem evalInstrs_of_run :
    ∀ (instrs : List (Instr ctx.primCtx)) (env : Env ctx.primCtx) (result : Term ctx.primCtx)
      (value : Val ctx.primCtx), Block.run ctx env instrs result = some value →
      ∃ scope, Term.evalInstrs ctx env instrs = some (.ok scope) ∧
        Term.eval ctx scope result = some value
| [], env, result, value, hrun =>
    ⟨env, by rw [Term.evalInstrs.eq_def], hrun⟩
| instr :: instrs, env, result, value, hrun => by
    rw [Block.run_cons] at hrun
    cases hinstr : Term.eval ctx env instr.value with
    | none => rw [hinstr] at hrun; simp at hrun
    | some instrValue =>
        rw [hinstr] at hrun
        have hrest : Block.run ctx (env ++ [(instr.name, instrValue)]) instrs result =
          some value := hrun
        obtain ⟨scope, hscope, hresult⟩ := evalInstrs_of_run instrs _ result value hrest
        refine ⟨scope, ?_, hresult⟩
        rw [Term.evalInstrs.eq_def]
        simp [evalOutcome_ok_of_eval hinstr, hscope]

/-- A block whose body runs to a value returns that value from any call of it. -/
theorem evalBlock_ok_of_run {name : String} {env : Env ctx.primCtx} {block : Block ctx.primCtx}
    {value : Val ctx.primCtx} (hrun : Block.run ctx env block.instrs block.result = some value) :
    Term.evalBlock ctx name env block = some (.ok value) := by
  obtain ⟨scope, hscope, hresult⟩ := evalInstrs_of_run block.instrs env block.result value hrun
  rw [Term.evalBlock.eq_def, hscope]
  simp [evalOutcome_ok_of_eval hresult]

/-- Stepping into a callee: a call returns what the block's body runs to. This is the one step
  `simp` cannot take on its own, because it is where a recursive program would unfold forever. -/
theorem evalCall_of_run {name : String} {vargs : List (Val ctx.primCtx)}
    {block : Block ctx.primCtx} {value : Val ctx.primCtx}
    (hblock : ctx.blockCtx.get? name = some block)
    (hlen : vargs.length = block.params.length)
    (hrun : Block.run ctx (block.entryEnv vargs) block.instrs block.result = some value) :
    Term.evalCall ctx name vargs = some value := by
  rw [Term.evalCall.eq_def, hblock]
  simp [hlen, evalBlock_ok_of_run hrun, Outcome.ok?]

/-! ### operators

  An operator's `body` decides, one operand at a time, whether that operand is evaluated.
  `Op.Body.eager` is the "evaluate everything, then apply" shape, and `Op.ofVals` -- the shape
  of every fixed-signature operator -- is built from it. -/

theorem _root_.Zag.Op.Body.eager_zero {primCtx : PrimitiveCtx}
    (run : List (Val primCtx) → Option (Val primCtx)) (vals : List (Val primCtx)) :
    Op.Body.eager run 0 vals =
      match run vals with
      | some value => .done value
      | none => .fail := rfl

theorem _root_.Zag.Op.Body.eager_succ {primCtx : PrimitiveCtx}
    (run : List (Val primCtx) → Option (Val primCtx)) (remaining : Nat)
    (vals : List (Val primCtx)) :
    Op.Body.eager run (remaining + 1) vals = .next true (fun
      | some value => Op.Body.eager run remaining (vals ++ [value])
      | none => .fail) := rfl

theorem evalBody_eager {env : Env ctx.primCtx}
    (run : List (Val ctx.primCtx) → Option (Val ctx.primCtx)) :
    ∀ (args : List (Term ctx.primCtx)) (acc : List (Val ctx.primCtx)),
      Term.evalBody ctx env args (Op.Body.eager run args.length acc) = (do
        let vals ← Term.evalList ctx env args
        run (acc ++ vals))
| [], acc => by
    rw [show ([] : List (Term ctx.primCtx)).length = 0 from rfl, Op.Body.eager_zero]
    cases hrun : run acc <;> simp [hrun]
| arg :: args, acc => by
    rw [show (arg :: args).length = args.length + 1 from rfl, Op.Body.eager_succ,
      Term.evalBody_next_true]
    cases harg : Term.evalGo ctx env arg with
    | none =>
        have hval : Term.eval ctx env arg = none := harg
        simp [hval]
    | some value =>
        have hval : Term.eval ctx env arg = some value := harg
        show Term.evalBody ctx env args (Op.Body.eager run args.length (acc ++ [value])) = _
        rw [evalBody_eager run args (acc ++ [value])]
        simp only [hval, Term.evalList_cons, List.append_assoc, List.cons_append, List.nil_append]
        cases hlist : Term.evalList ctx env args <;> simp

theorem eval_op_ofVals {env : Env ctx.primCtx} {name : String} {argTys : List Ty} {outTy : Ty}
    {interp : List (Val ctx.primCtx) → Option (Val ctx.primCtx)} {args : List (Term ctx.primCtx)}
    (hop : ctx.opCtx.get? name = some (Op.ofVals argTys outTy interp))
    (hlen : args.length = argTys.length) :
    Term.eval ctx env (.op name args) = (do
      let vals ← Term.evalList ctx env args
      if vals.map Val.ty = argTys then do
        let raw ← (← interp vals).as? outTy
        some (Val.mk outTy raw)
      else none) := by
  have hbody : (Op.ofVals argTys outTy interp).body =
      Op.Body.eager (fun vals =>
        if vals.map Val.ty = argTys then do
          let raw ← (← interp vals).as? outTy
          some (Val.mk outTy raw)
        else none) args.length [] := by
    rw [hlen]; rfl
  rw [Term.eval, Term.evalGo_op, hop]
  show (if args.length = (Op.ofVals argTys outTy interp).arity then
      Term.evalBody ctx env args (Op.ofVals argTys outTy interp).body else none) = _
  rw [if_pos (show args.length = (Op.ofVals argTys outTy interp).arity from hlen), hbody,
    evalBody_eager]
  cases hvals : Term.evalList ctx env args <;> simp

end Term

end Zag
