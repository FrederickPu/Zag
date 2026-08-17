# Handoff

## State

`LEAN_NUM_THREADS=1 lake build Zag Lib Meta Test` is green, no `sorry`, no new axioms.

Use `LEAN_NUM_THREADS=1`. Higher parallelism OOMs and reports *fake* errors — "failed to read
`.olean`", `std::bad_alloc`. Rerun single-threaded before believing them.

| file | contents |
|---|---|
| `Zag/Machine.lean` | `Action`, `Sink`, `Frame`, `EvalState`, the drivers, `step`, `run`, `stepN`. No proofs. |
| `Zag/Weakening.lean` | `*_weaken`, `*_append_eq_none`, stuck-state analysis |
| `Zag/EvalState.lean` | `EvaluatesTo` / `EvaluatesCall` / `EvaluatesFrom` and the calculus |
| `Zag/Loop.lean` | `BodySweep`, `sweep_run`, `control_loop` |
| `Lib/Peano/Eval.lean` | `whileControl`, `whileControlCtx`, `while_invariant` |
| `Meta/Eval.lean` | `evaluates_call`, `tail_induction`, `while_induction` |

---

# Next task: continuation-passing `while`

## Why

Today's `whileControl n` runs **one body block per loop variable** and sweeps them in sequence,
because a block returns a single value. That forces `while` / `while2` / `while3` as separate
`ControlCtx` entries, forces `BodySweep` into the proof rule, and makes a simultaneous update
like `(x, y) := (y, x % y)` inexpressible at any ordering.

Blocks are values now (`Val.blockRef`), so the body can take a **continuation** as a parameter
and call it with the whole next state at once. That deletes all three workarounds.

## Shape

```
while [cond, body, a₁, …, aₙ]
```

One argument list — the blocks are ordinary terms that evaluate to block references, so
`Instr.Source.control` loses its separate `blocks : List String` field. `Control.roles`, the
role-index lookups in `driveControl`, `blockNames[0]?` / `hcondRole` in the loop rule, and
`checkRoleBlocks?` in the typechecker all go with it.

`body` takes the loop variables **plus a continuation** as its last parameter:

```
gcdBody(x : Nat, y : Nat, k : func[Nat, Nat] => Nat) : Nat {
  ret apply k [y, op "mod"[x, y]]
}
```

Both continuation arguments are evaluated in the body's scope, so this is simultaneous
assignment. A body that *doesn't* call its continuation returns the loop's answer directly —
which is early exit, for free.

## Typing

`consControl` already infers the types of every instruction argument and calls `ctrl.out argTys`,
so the whole coherence check is `whileControl.out` — the control stating its own typing rule.
With `Ts = [T₁ … Tₙ]` the init-arg types:

```
R  = T₁                      the loop answers with its first variable, unchanged
K  = func Ts R               the continuation
cond : func Ts Bool
body : func (Ts ++ [K]) R
──────────────────────────────
while [cond, body, a₁…aₙ] : R
```

`out` receives `[condTy, bodyTy, T₁ … Tₙ]` and requires `condArgs = Ts`, `boolTy = Peano.BoolTy`,
`bodyArgs = Ts ++ [.func Ts R]`, and `initTys.head? = some R`. `Ty` has `DecidableEq`, so
`typecheck_ctx` still discharges by `decide`.

`R = T₁` is what makes an immediate exit well-typed: the condition failing on the first test is
not a special case, the loop just answers with its state. So order the state to put the answer
first — `gcd` is `(x, y)`, `fibLinear` is `(a, remaining, b)`. That constraint already exists;
`whileControl` exits with `args.head?` today.

## The two genuinely new pieces

```lean
| loopRef (control : String) (captured : List (Val primCtx))
          (argTys : List Ty) (outTy : Ty)
```

The continuation. It cannot be a `blockRef` (the loop is not a block) or a `Ty.func` value (that
is a pure Lean function). `captured` is `[condRef, bodyRef]`, which makes **`Val` recursive** — a
nested inductive Lean accepts, but it touches `Val.ty`, `Val.as?`, `Val.raw` and every `cases v`.
`applyValue` grows a third branch that restarts the control.

`Control.Yield.call role args` becomes `Yield.apply (fn : Val) (args : List Val)`, which hands
off to `applyValue`.

## Consequence: it returns, it does not jump

```
loop(args) = if cond(args) then body(args, loop) else args.head
```

Applying the continuation **returns**, so the answer travels back out through every iteration and
the stack grows one turn per iteration. Correct, and fine in a total fuel-based model — but
`Frame.control` stops being a fixed point an invariant sits at. `control_loop` becomes an
induction where each turn *wraps* the next rather than replacing it; `BodySweep` and `sweep_run`
are deleted.

A genuine jump would need an unwinding `Action`. That was rejected: `EvalState.step` reads only
the top frame, and any rule that makes a step depend on a frame further down makes `step_weaken`
false.

## Order of work

1. `Instr.Source.control` reshape + `blocks%` syntax.
2. `Val.loopRef`, the `applyValue` branch, `Yield.apply`.
3. `whileControl` — one definition, no arity — and `whileControl.out`.
4. `control_loop` as a wrapping induction; delete `BodySweep`, `sweep_run`, `while_bodies`, and
   the `while2` / `while3` entries.
5. Reconvert, then extend.

## What step 5 unblocks

Already loops, to be reconverted: `plusLoop`, `multByAddLoop`, Gauss's `loop`,
`Test/While.lean`'s `countDown` and `halve`.

Currently recursive, blocked only by the sweep, and expressible under the new design:

| loop | file | was blocked by |
|---|---|---|
| `gcdLoop(x, y)` | `Simple.lean` | simultaneous swap `(x, y) := (y, x % y)` |
| `fibLinearLoop(remaining, a, b)` | `FibProof.lean` | simultaneous `(a, b) := (b, a + b)` |
| `markLoop(heap, current)` | `SchorrWaite.lean` | `current'` must read the pre-`store` heap |
| `isPrimeLoop(n, div)` | `IsPrime.lean` | early exit carrying a value |
| `binarySearchLoop(xs, needle, low, high)` | `BinarySearch.lean` | early exit carrying a value |

Keep at least one recursive loop so `tail_induction` stays exercised — `factorial` and `fib` are
not loops at all (they operate after the call / recurse twice), so they cover it.

---

# Also outstanding

- **`Term.Terminates`, `Term.eq`, `Pr.interp`, `Pr.Provable` are misfiled** in
  `Zag/EvalState.lean`. They are proposition semantics, not evaluation. They cannot fold into
  `Zag/Theory.lean` because `Term.eq` needs `EvaluatesTo`, so a `Zag/Pr.lean` has to sit *after*
  `Zag/EvalState.lean`; `Zag.lean`, `Meta/Induction.lean` and `Meta/UnifyType.lean` need the
  import. ~40 lines.
- **Decide whether `Term.call` survives.** `call f args` and `app (var f) args` reach the same
  state when `f` is not locally bound, but `call` ignores the environment and `app` does not, so
  they are different intents (`Test/Apply.lean` pins both). Dropping `call` means
  `Block.callNames` / `BlockCtx.Valid` can no longer check that referenced blocks exist — a
  `.var` is indistinguishable from a local variable — and that check moves entirely into
  `Ctx.WellTyped`.
- **A block handed to a higher-order operator fails.** `Op` bodies are pure, so `Val.raw` of a
  block reference is the function that always declines. Fixing it needs an `Op.Body` outcome that
  asks the machine to apply a value and resume — the coroutine shape `Op.Body.next` already has.
  Prerequisite for `Test/Monad.lean`'s `bind` taking a block.
- **The control typing rule does not constrain driven blocks' result types.** `Control` carries no
  per-role signature; `out` is its only typing field. The new design fixes this for `while`,
  since `out` sees the block types directly.
- **`Ctx.M` is unused.** Controls are pure. Effects were meant to live there, arriving with moving
  the heap out of values and into the monad.
- **`Action.stuck`** exists only so `enterInstrs` can be total. Removing it means `enterInstrs`
  returns `Option`, which pushes partiality into `enterInstrs_stack` and every proof using it —
  worse metatheory to save one constructor.

---

# Landmines

- **`do` on `Option` does not reduce under `simp`.** `Option.bind_some` is `x >>= some = x`, not
  what you want, and `Option.some_bind` does not exist. Write explicit `match`es in anything the
  evaluation tactics must compute through. Do not "tidy" `driveControl`, the control `step` cases,
  or `whileControl.next` back into `do`.
- **`EvalState.step` only ever reads the *top* frame.** That is what makes `step_weaken` true and
  the whole compositional layer possible. Any rule that makes a step depend on a frame further
  down makes weakening false, because appending `base` could introduce the matching frame.
  Unwinding is fine: it consumes one top frame per step.
- **Never tag `Val.nat` / `Val.bool` with `@[eval_step]`.** `Val.mk_ofNat` / `mk_ofBool` are
  `@[simp]` and fold *into* them, so an unfolding tag makes `simp [eval_step, …]` loop. Symptom is
  `maximum recursion depth` in an unrelated file. Same for passing an op context explicitly
  alongside the tagged `Peano.opCtx`.
- **`eval_step` and `eval_fold` must stay separate simp sets.** A fold rule and its unfold rule in
  one `simp` call loop.
- **Unfolding `step` in a proof means unfolding `evalStep`, `resumeFrame` and `unwindFrame` too.**
  All are `@[eval_step]`, so the tactics are fine; explicit `simp only [step, …]` sites are not.
- **A reducible `Ctx` unfolds to a literal before `simp` looks up rules** (2773 DiscrTree keys, no
  matches). `mkCtx` must stay an `abbrev`; specs are stated at the `heapCtx` flavour.
- **`omega` reads the local context.** A leftover-goal count smaller than expected is usually
  this, not a bug.
- **`while`, `for` and `switch` are Lean keywords.** `blocks%`'s control name is `rawIdent`,
  matched with an *untyped* antiquotation (`$control`, not `$control:rawIdent`).
- **Two adjacent `term`s in a tactic syntax parse as an application.** Hence
  `while_induction [..] I stopping_at N`.
- **`(f :: rest) ++ base` is not syntactically a `cons`** — match arms need `List.cons_append`.
- **`obtain ⟨rfl, rfl, rfl⟩ := by simpa using h` silently closes the main goal.** Use
  `simp only [Option.some.injEq, EvalState.mk.injEq] at h` first.
- **Doc comments cannot attach to `attribute` or `#guard`.** Use `/- … -/` or `--`.
- **Declaring `theorem EvaluatesFrom.foo` opens that namespace inside the proof**, so `step`
  resolves to `EvaluatesFrom.step` and silently makes no progress. Qualify as `EvalState.step`.
- **The sweep's leftover goal has no stable case tag.** `case init` is reliable; close the
  invariant step with `all_goals`. (Moot once `BodySweep` is deleted.)
- `Zag/Data.lean` and `Zag/Theory.lean` are deliberately import-free; their `@[eval_step]` tags
  live in `Zag/Machine.lean`. Do not add `import Lean` to them.
