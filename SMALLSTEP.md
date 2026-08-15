# Small-step migration — implementation plan

Replace the big-step evaluator with the small-step machine in `Zag/EvalState.lean`, then add
instruction-level control flow and put the heap in a monad.

**Verify with `LEAN_NUM_THREADS=2 lake build Zag Lib Meta Test`.** Without the thread limit the
full-parallel build exhausts memory on this machine and reports spurious "failed to read file
… .olean" and `std::bad_alloc` errors that look like real failures and are not.

---

## Why big-step has to go

`partial_fixpoint` cannot be parameterised over the context's monad. It needs
`Lean.Order.MonoBind` on whatever monad the recursion sits under, which needs a `CCPO`, and the
*pure* instance is exactly the one that has none: `MonoBind Id` requires
`(α : Type) → PartialOrder (Id α)`, which cannot exist because `Id Empty = Empty` has no least
element.

Note the obstruction is about **which `bind` the recursion is under**, not about the result type.
`Option α` works and `Id (Option α)` does not, even though the two types are definitionally
equal. Today's `Term.evalOutcome` is fine only because it recurses under `Option.bind`.

Small-step has no fixpoint — `step` is structural, `run` recurses on fuel — so the obligation
disappears and `M` can be any `Monad`. Verified: a fuel driver over an abstract `Monad M`
compiles with **zero** axioms.

---

## Current state (all green, 55 targets)

`Zag/EvalState.lean` holds the machine, alongside the untouched big-step evaluator:

| | |
|---|---|
| `Focus` | `eval t` / `ret v` / `exit b v` — what the machine is doing |
| `Frame` | `exitValue`, `opBody`, `callArgs`, `appFn`, `appArgs`, `instrs`, `call` |
| `EvalState` | `focus`, `env`, `stack` (head = **top** of stack) |
| `step` | structural, `Option`-valued; `none` = stuck |
| `run` | fuel-driven, **halts early** when stuck — so over-estimating fuel is free |
| `stepN` | exact step count, no early stop; use this in proofs, `run` in tactics |
| `EvaluatesTo` | `∃ fuel, (run ctx fuel (start env t)).result? = some value` |
| `EvaluatesCall` | spec form, on argument **values** — see below |

Weakening layer, all proved, all `propext, Quot.sound` only (no `Classical.choice`):
`driveOp_weaken`, `enterBlock_weaken`, `step_weaken`, `stepN_weaken`, `EvaluatesTo.weaken`,
`EvaluatesTo.unique`, plus `stepN_add`, `exists_stepN_run`, `run_eq_of_stepN`, `run_le`.

`Ctx` already carries the monad, defaulted so every existing literal still compiles:

```lean
structure Ctx where
  primCtx : PrimitiveCtx
  M : Type → Type := Id
  [monad : Monad M]
  opCtx : OpCtx primCtx
  blockCtx : BlockCtx primCtx := .empty
```

`Meta/Eval.lean` has the `evaluates` tactic (generalised off Peano — pass the program's op
context and blocks). Working today, in both Peano and heap contexts, including recursion:

```lean
example : EvaluatesTo gaussCtx [] (.call "gauss" [Term.nat 5]) (Val.nat 15) := by
  evaluates 600 [natOpCtx, gaussBlocks]

example : EvaluatesTo simpleCtx [] (.call "gcd" [Term.nat 12, Term.nat 18]) (Val.nat 6) := by
  evaluates 800 [heapOpCtx, simpleBlocks, binaryNatOp]

example : EvaluatesTo clampCtx [] (.call "clamp" [Term.nat 42]) (Val.nat 10) := by
  evaluates 200 [natOpCtx, clampBlocks]        -- exercises `exit`
```

---

## Target design

`Term.eval` does **not** survive. `Zag/Eval.lean` and `concretize` are deleted, not ported,
along with `Term.evalList`, `Term.evalCall`, `Block.run` and `Outcome`. `evaluates` becomes the
only tactic and `EvaluatesTo`/`EvaluatesCall` the only semantics.

`Term.eq` restates relationally — equivalent to today's function equality by
`EvaluatesTo.unique`, and it still equates divergence:

```lean
eq : ∀ env, env.Models varCtx → ∀ v, EvaluatesTo ctx env t₁ v ↔ EvaluatesTo ctx env t₂ v
```

### Why specs are stated on values

An induction hypothesis has to match the machine *part-way through a run*. At the recursive call
the machine sits at `enterBlock "plusLoop" block [Val.nat (x+1), Val.nat y] …`, while the surface
term still reads `.call "plusLoop" [op "add" .., op "sub" ..]`. Those coincide only once the
arguments are evaluated, so the spec must speak about values:

```lean
def EvaluatesCall (ctx) (name) (vargs) (value) : Prop :=
  ∀ (env : Env ctx.primCtx) (base : List (Frame ctx.primCtx)),
    ∃ block st fuel scope,
      ctx.blockCtx.get? name = some block ∧
      EvalState.enterBlock name block vargs env base = some st ∧
      EvalState.stepN ctx fuel st = some ⟨.ret value, scope, base⟩
```

Quantifying over `env` and `base` is load-bearing: `enterBlock` bakes the caller's environment
into the `Frame.call` it pushes, so a spec fixed at `[] []` would not transport to a call site.

This is the same role `Term.evalCall` plays in the big-step tree, arrived at independently in
both ports.

---

## Steps

Everything through step 3 is **additive** — the tree stays green. Step 4 is the one that must
land in a single pass.

### 1. `stepN_call` — DONE

Landed in `Zag/EvalState.lean` as `EvalState.stepN_call`, with `EvalState.stepN_callArgs` and
`EvaluatesToAll` underneath. `propext, Quot.sound` only.

```lean
theorem stepN_call (hblock : ctx.blockCtx.get? name = some block)
    (hargs : EvaluatesToAll ctx env args vargs) :
    ∃ n, stepN ctx n ⟨.eval (.call name args), env, S⟩ = enterBlock name block vargs env S
```

Stated as an *equation*, not `∃ st, … = some st` — an arity mismatch makes `enterBlock` `none`,
and the machine gets stuck there, so both sides are `none` and the equation still holds.

Applying it needs all implicits given explicitly (`ctx`, `name`, `block`, `env`, `S`, `args`,
`vargs`); elaboration will not infer them from the goal.

### 2. `evaluates_call` tactic

Today `concretize [ih]` works only because `ih` is an equation `simp` rewrites with. Under the
machine the proof is **run → apply hypothesis → run**, glued by `stepN_add`. The tactic must:

1. step until the state is an `enterBlock` matching an available hypothesis,
2. apply it,
3. continue stepping.

This is real metaprogramming, not a larger simp set. It is the second-riskiest item after (1).

### 3. Port `Plus.lean`

The shape is unchanged from today's proofs:

```lean
theorem plusLoop_eval (x y : Nat) :
    EvaluatesCall plusCtx "plusLoop" [Val.nat x, Val.nat y] (Val.nat (x + y)) := by
  induction y generalizing x with
  | zero      => evaluates_call 300 [heapOpCtx, plusBlocks]
  | succ y ih => evaluates_call 300 [heapOpCtx, plusBlocks, ih]
```

`plus_eval` and the `zero` case already pass with the existing `evaluates`. `succ` is the real
test and is exactly what (1) and (2) unblock. Then do one heap example — `Suzuki` is simplest
(one block, no recursion, and its heap is threaded explicitly so it is a *pure* program today).

### 4. Delete big-step — single pass

Remove `Term.eval`, `Term.evalGo`, `Term.evalOutcome`, `Term.evalBlock`, `Term.evalInstrs`,
`Term.evalListOutcome`, `Term.evalBodyOutcome`, the five `partial_fixpoint`s, `Outcome`,
`Zag/Eval.lean`, `Lib/Peano/Eval.lean`'s eval rules, and `concretize`. Restate `Term.eq`,
`Term.Terminates`, `Pr.interp`, `Meta/Induction.lean`'s `SuccSpec`, and all four example files
on `EvaluatesTo`/`EvaluatesCall`.

`#eval` / `#guard` in `Test/Block.lean`, `Test/Gauss.lean`, `Test/Exit.lean`, `Test/Monad.lean`
move onto `EvalState.run` with explicit fuel.

### 5. `Op.Body` cleanup

```lean
inductive Op.Body (primCtx) where
| done (value : Option (Val primCtx))      -- none = UB in a well-typed program
| next (evaluate : Bool) (resume : Option (Val primCtx) → Op.Body primCtx)
```

`fail` and `done none` are the same shape, so this is a semantic cleanup: every current `fail`
is a type check (`Op.ofVals`'s `vals.map Val.ty = argTys`, `Op.compare`'s `lhs.ty = rhs.ty`,
`Op.ite`'s `as? BoolTy`), and typing now carries that weight. Nothing in PeanoHeap needs
`done none` yet — `Nat.div _ 0 = 0`, `HeapArray.get` and `Heap.read` are all total with
defaults — but it is the hook for making those UB instead.

Ops keep `next` and **cannot loop**: each operand is offered once.

### 6. Instruction-level control flow

Separate from term ops. Ops do short-circuit; only `Control` loops.

```lean
inductive Instr.Source (primCtx) where
| term    (value : Term primCtx)
| control (control : String) (blocks : List String) (args : List (Term primCtx))

structure Instr (primCtx) where
  name   : String                  -- unchanged, so instr.name keeps working
  source : Instr.Source primCtx

structure Control.Call (primCtx) where
  block : String
  args  : List (Val primCtx)

inductive Control.Result (primCtx) where
| ret  (value : Val primCtx)
| exit (blockName : String) (value : Val primCtx)     -- break / continue

inductive Control.Yield (primCtx) where
| done   (value : Val primCtx)
| call   (target : Control.Call primCtx) (state : Val primCtx)
| unwind (blockName : String) (value : Val primCtx)   -- not mine, keep unwinding

structure Control (primCtx) (M : Type → Type) where
  accepts : List (VarCtx × Ty) → List Ty → Option Ty
  init    : List (Val primCtx) → M (Control.Yield primCtx)
  step    : Val primCtx → Control.Result primCtx → M (Control.Yield primCtx)
```

`ControlCtx` on `Ctx`; `while`/`for`/`switch` are entries in it. Needs a `Frame.control` holding
the control, its threaded state, and the block names, plus a `control` case in
`Block.instrsHaveType` and surface syntax.

`step` is total — ill-typed input is not evaluation's problem — so `accepts` must be strong
enough that `Ctx.WellTyped` really implies every `step` call is well-fed. If it is too
permissive the guarantee is vacuous.

Closest analogue is MLIR `scf.while`/`scf.for` (ops taking regions with block arguments).
Difference: our blocks are flat and named, so `break`/`continue` are `exit <name> v` — a
labelled break — rather than structured branch targets.

**Blocks do not become values.** `Ty.type` (Data.lean:158) is defined before `Term` (:430), and
`Term.prim` depends on `Ty.type`, so a `Block` primitive could only ever carry a *name*. Naming
blocks in the instruction is simpler and avoids the question.

`ite` stays a term op — its condition arrives as an operand value, so it never needs a
heap read to decide which branch to take.

### 7. `OptionT` and the heap

```lean
step : EvalState ctx.primCtx → OptionT ctx.M (EvalState ctx.primCtx)
```

`OptionT M`, **not** `StateT σ Option`. Effects performed before a stuck state must survive:

```
OptionT (StateM Heap) α  =  Heap → Option α × Heap     -- store then stuck: store stands
StateT Heap Option α     =  Heap → Option (α × Heap)   -- store then stuck: store lost
```

`OptionT Id α = Option α` by `rfl`, so pure contexts are untouched.

Failure means UB or *no rule applies*, never a type error. The one well-typed case that needs it
is an `exit` with no enclosing frame — `Test/Exit.lean` tests exactly that. Everything else it
currently catches (name not found, arity mismatch, wrong operand type) is ruled out by
`Ctx.WellTyped`.

`run` is the single place that *catches* failure:

```lean
def run : Nat → EvalState ctx.primCtx → ctx.M (EvalState ctx.primCtx)
  | 0, s => pure s
  | fuel + 1, s => do
      match ← (step ctx s).run with
      | none => pure s                 -- stuck: stop, don't propagate
      | some next => run fuel next
```

Note `step_weaken`'s current proof inverts `some` on its hypothesis. Under `OptionT M` that
becomes `pure`, which is **not** injective for an abstract monad. Restate it around a structural
"not stuck" predicate rather than an inversion, or factor `step` into a pure structural part
plus the one monadic case (operator application) and prove weakening about the pure part.

Then heap into `M`: `statePrim` and the `mkState`/`stateHeap`/`stateValue` triple come out of
`Lib/PeanoHeap.lean`, and the seven heap programs (`Alloc`, `CList`, `Kmalloc`, `ListRev`,
`Str2Long`, `Suzuki`, `TypeStrengthenTricks`) lose their `heap` parameter and their manual
threading.

---

## Landmines

Each of these cost real time in the previous session.

**`Ty.type` does not reduce definitionally.** It is `Type`-valued and well-founded, so the
`cast`s inside `Val` are stuck. `rfl` and `decide` cannot run the machine even though `step` is
structural — the tactic must be `simp`-driven. `#eval` works only because `partial_fixpoint`
compiles to a real program; after step 4 it needs explicit fuel.

**`(f :: rest) ++ base` is not syntactically a `cons`.** Match arms on the stack will not reduce
without `List.cons_append` in the simp set. This was 4 of the 5 stubborn cases in `step_weaken`.

**`simp only [Option.bind_some]` fails on `do` notation.** `do` elaborates to `>>=`, not
`Option.bind`. Use `show` to strip the bind, or plain `simp`.

**`obtain ⟨rfl, rfl, rfl⟩ := by simpa using h` silently proves the wrong goal.** The `by` block
elaborates against a metavariable and closes the main goal instead. Use
`simp only [Option.some.injEq, EvalState.mk.injEq] at h` then `obtain ⟨rfl, rfl, rfl⟩ := h`.

**`step_weaken` is 25 cases; 20 close with one uniform script.** The three that resist are the
ones calling out to `Term.evalApp`, `enterInstrs`, and the exit-name test — i.e. everything that
is not pure stack manipulation.

**DiscrTree and reducible contexts.** A reducible `Ctx` unfolds to a literal before `simp` looks
up its rules, giving a 2773-key path and no matches. `mkCtx` must stay an `abbrev` so
`ctx.primCtx` reduces to `heapCtx`, and the calculus rules need `no_index` on their indexed
argument. Specs must also be stated at the `heapCtx` flavour —
`([Val.nat x, Val.nat y] : List (Val heapCtx))` — because a call inside a block body carries
arguments elaborated in the context the program text lives in. This bit repeatedly.

**`Peano.Model` has ten fields.** Adding a context means `natType, boolType, eqOp, ltOp, gtOp,
iteOp, addOp, subOp, mulOp, divOp, succOp`, all `by rfl`.

**`ret` is a keyword token** (block syntax), so it cannot be a Lean identifier in any file
importing `Zag.Syntax`. Same care for any new control-flow keyword.

**Names, never indices.** `Scope`/`BlockCtx`/`VarCtx` are all name-keyed; there are no de Bruijn
indices anywhere in the current tree.

---

## Open

`Term.eq` becomes equality of `M`-computations, so two terms are equal only if they have the
same effects. At `M = Id` that is today's meaning exactly, so `Plus.lean`'s reflected induction
proof is unaffected. It only bites once a context has a heap — confirm before step 7.
