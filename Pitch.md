# why program verification

Program verification is a much stronger alternative to testing. When you test a piece of code you sample from a distribution of expected inputs and check correctness on those samples. But many programs have arbitrary or even non-deterministic behavior (multithreading, for instance), and others take inputs of unbounded size, where no sampling distribution is obviously the right one — what *is* the correct probability distribution over lists? Testing can only ever cover the cases you thought to sample. Formal verification instead proves correctness for *all* inputs at once, and its cost is paid once up front rather than growing with the space of behaviors you are trying to cover.

# tldr

Zag lets you take a low-level program — C, LLVM IR, Zig — embed its language once, write programs and propositions in it, and prove them in Lean. The distinctive part is *what you have to trust*. Every proof step is represented by a `Refinement`: proof automation packaged with a machine-checked certificate that its subgoals imply its goal. An unsound refinement does not typecheck. The hand-written trust boundary is the target language's semantic specification: its primitive types and operations, and its lowering to Zag's core language. Everything above that boundary is checked by Lean.

```
┌───────────────────────────────────────────────────────────┐
│                  what you trust by hand                   │
│                                                           │
│  ┌──────────────┐  ┌──────────────┐  ┌──────────────┐     │
│  │ PrimitiveCtx │  │ PrimFuncCtx  │  │   toTerm?    │     │
│  │              │  │              │  │              │     │
│  │ types and    │  │ operations   │  │ source AST → │     │
│  │ their Lean   │  │ and how they │  │ Zag's core   │     │
│  │ meaning      │  │ evaluate     │  │ Term type    │     │
│  └──────┬───────┘  └──────┬───────┘  └──────┬───────┘     │
│         │                 │                 │             │
│         └────────┬────────┘                 │             │
│                  │                          │             │
│          semantic spec              structural rule       │
│       (what the language            (source→Term,         │
│        means in Lean)                one clause per       │
│                                      constructor)         │
└──────────────────────┬────────────────────────────────────┘
                       │
                       ▼
          ┌────────────────────────┐
          │   Zag's shared kernel  │
          │                        │
          │  • Term.eval           │  ← one evaluator for everything
          │  • Term.hasType        │
          │  • Pr.interp           │  ← propositions are data
          │  • Refinement          │  ← automations certify themselves
          └────────────────────────┘
                       │
                       ▼
              every proof is checked
```

# why lean

Lean is a dependently-typed programming language and proof assistant: you write ordinary programs and mathematical proofs in the same language, and the compiler checks the proofs. It has one of the fastest-growing formal mathematics libraries, and — because of recent "AI for math" efforts — a large amount of pretraining and RL has been directed at Lean code, making it ergonomic for both humans and AI agents to write proofs in.

# why not the existing approaches

To prove properties about programs, existing tools generally do one of two things:

1. **Transpile the source language into Lean** with an unverified translator (e.g. [Aeneas](https://github.com/AeneasVerif/aeneas)). This is convenient, but the translator itself is trusted code — a bug in it silently invalidates every proof built on its output.

```
source language             Lean
┌──────────┐    ┌───────────┐    ┌──────────┐
│  program │───>│translator │───>│  program │───> proofs
└──────────┘    └───────────┘    └──────────┘
                      ▲
                 trusted: a bug here
                 silently invalidates
                 every proof
```

2. **Embed the program faithfully and use proof automation** to break goals into subgoals. This keeps the trusted base small, and Lean's kernel checks every finished proof, so no tactic can ever establish a false statement. But the automation *itself* has no guarantees: a tactic can loop forever, fail outright, or reduce your goal to subgoals that don't actually suffice — and extending it without quietly breaking those reductions is hard (cf. [AutoCorres](https://isa-afp.org/entries/AutoCorres2.html)).

```
source language                Lean
┌──────────┐   ┌───────────┐   ┌─────────────────┐
│  program │──>│ embed into│──>│proof automation │──> proofs
└──────────┘   │ Lean      │   └─────────────────┘
               └───────────┘           ▲
                                 unverified: can
                                 loop, fail, or
                                 emit subgoals
                                 that don't suffice
```

Zag avoids both failure modes. Against #1, lowering is part of the language specification rather than an opaque external translation step: primitive semantics and structural lowering into Zag's core `Term` are stated explicitly, and Zag supplies the shared evaluator used by every proof. Against #2, the trust base stays small, but every automation is *total and self-certifying*. Propositions are reified as `Pr` values and proof reductions as `Refinement` values ([`Zag/Meta.lean`](Zag/Meta.lean)) carrying a proof that their subgoals suffice:

```
source language          ┌──────────────────────────────────────┐
┌──────────┐             │            Zag                       │
│  program │──toTerm?──> │                                      │
└──────────┘             │  ┌────────────┐  ┌───────────────┐   │
                         │  │ Term.eval  │  │ Refinement    │   │
                         │  │            │  │               │   │
                         │  │ one shared │  │ total, self-  │   │
                         │  │ evaluator  │  │ certifying:   │   │
                         │  │ for every  │  │ prove is a    │   │
                         │  │ proof      │  │ checked proof │   │
                         │  └────────────┘  └───────────────┘   │
                         │         ▲                 ▲          │
                         │    language spec    automation layer │
                         │   (trusted once)   (trusted never)   │
                         └──────────────────────────────────────┘
                                   │
                                   ▼
                          Lean checks every proof
                          (no false theorems, ever)
```

```lean
structure Refinement ctx ctxTy ctxTerm {E} [Language ctx.primCtx E] (goal : Pr E) where
  goals : List (Pr E)
  prove : (∀ subgoal, subgoal ∈ goals →
    Language.Provable ... subgoal) → Language.Provable ... goal

abbrev Tactic ctx ctxTy ctxTerm E [Language ctx.primCtx E] :=
  (goal : Pr E) → Refinement ctx ctxTy ctxTerm goal

abbrev Tactic? ctx ctxTy ctxTerm E [Language ctx.primCtx E] :=
  (goal : Pr E) → Option (Refinement ctx ctxTy ctxTerm goal)
```

A `Refinement` for a `goal` produces a list of sub`goals` together with `prove`: a proof that provability of all the subgoals implies provability of the goal. `ctxTy` and `ctxTerm` are the ambient variable context, while `E` identifies the language in which the goal is written. Because `prove` is checked, a refinement whose subgoals do not imply its goal cannot be constructed. Lean's kernel already prevents false theorems; `Refinement` additionally makes each reduction valid by construction and each tactic an ordinary terminating Lean function.

A `Tactic` is a total function from every goal in language `E` to a certified refinement of that same goal. It may close the goal, reduce it to new subgoals, or leave it unchanged with `Refinement.stuck`. A `Tactic?` can instead return `none` to say that it does not apply. `Tactic?.orElse` can then try another tactic without comparing goals for equality, while `Tactic?.toTactic` turns a final `none` into a stuck refinement containing the original goal.

Refinements and tactics compose. Given a refinement that emits subgoals, `refine` ([`Zag/Meta.lean`](Zag/Meta.lean)) replaces each subgoal with another refinement; `Tactic.andThen` performs that operation with a tactic, and `Tactic.iterate` applies a tactic under bounded fuel. `Tactic.raise` and `Tactic?.raise` reuse core `Term` tactics for reflecting surface languages. This builds a tree whose leaves are closed by Lean proofs, with the certificate threaded through automatically. Concretely, `iterate n step goal` unfolds as:

```
iterate n step goal  =
  if n = 0 then  step goal                          -- emit subgoals as-is
  else           (step goal).refine                 -- replace each subgoal:
                   fun g _ => iterate (n-1) step g  --   recurse with less fuel
```

So for `n = 3`, expanding one branch:

```
                  iterate 3 step goal
                          |
                     step goal
                   goals: [g₁, g₂, g₃]
                          |
              refine: replace each subgoal with iterate 2
                 /                   |                   \
        iterate 2 step g₁      (closed)           iterate 2 step g₃
         goals: [g₁₁]          goals: []           goals: [g₃₁, g₃₂]
              |                                       /              \
        refine g₁₁                              refine g₃₁       refine g₃₂
              |                                     |                |
      iterate 1 step g₁₁                   iterate 1 step g₃₁  iterate 1 step g₃₂
        goals: [g₁₁₁]                       goals: []           goals: []
              |                                 |                  |
           refine                            (leaf)             (leaf)
              |
      iterate 0 step g₁₁₁
        goals: output of the final step application
```

After all branches close, the final program's `.goals` is `[] ++ [] ++ [] = []`. Then `toProvable program hempty` ([`Zag/Meta.lean`](Zag/Meta.lean)) (where `hempty : program.goals = []`) collapses the tree:

```
toProvable program hempty :
  (∀ subgoal ∈ program.goals, Provable subgoal) → Provable goal
     ↑                                ↑
  trivially true               each leaf's prove
  (no subgoals)                threads upward through
                               refine's composition
```

Each `refine` composes the `prove` fields: the outer refinement's `prove` says "if my subgoals hold, I hold," and each inner refinement's `prove` says the same for its own subgoals. Fuel `n` permits `n` recursive refinements after the initial step, so a branch sees at most `n + 1` step applications. `toProvable` checks that the resulting goal list is empty and converts the tree into one proof.

# embedding a language

Zag is a *deep embedding*: programs and types are **data** — values of inductive `Term` and `Ty` types, syntax trees rather than Lean code ([`Zag/Data.lean`](Zag/Data.lean)):

```lean
inductive Ty where
  | prim   : String → Ty        -- "Nat", "Bool", ...
  | struct : List Ty → Ty       -- tuples / records
  | func   : List Ty → Ty → Ty  -- function types
  -- also: var, option, union

inductive Term (primCtx : PrimitiveCtx) where
  | prim (ty : Ty) : Ty.type primCtx ty → Term primCtx  -- literal value
  | var : Nat → Term primCtx                            -- de Bruijn variable
  | app : Term primCtx → List (Term primCtx) → Term primCtx
  | ite : Term → Term → Term → Term
  | recurse (resultTy : Ty) (initState body : Term) : Term  -- bounded loop
  -- also: primFunc, primEq/primLt/primGt, mkStruct, structProj
```

Because a program is inert data, we can write Lean functions that take it apart — an evaluator `Term.eval` ([`Zag/Theory.lean`](Zag/Theory.lean)), a typing relation `hasType` ([`Zag/Data.lean`](Zag/Data.lean)), and automations that pattern-match on its structure. (In a *shallow* embedding the program dissolves into Lean and you can only reason about its translation, never about the program itself.)

To bring in a new language you supply three things. Take a small SSA language (similar to LLVM IR), in [`Lang/SSA.lean`](Lang/SSA.lean):

**1. The raw syntax** — the AST (`SSAExpr`/`SSAValue`) with `let_`, `ite`, loops and `yield`:

```lean
mutual
inductive SSAExpr primCtx where
  | ret (value : SSAValue primCtx)
  | let_ (name : String) (value : SSAValue primCtx) (next : SSAExpr primCtx)
  | ite (cond : SSAValue primCtx) (thenExpr elseExpr : SSAExpr primCtx)
  | yield (next : List (SSAValue primCtx))
end
```

**2. The primitive semantics** — the built-in types ([`PrimitiveCtx`](Zag/Data.lean)) and how operations evaluate ([`PrimFuncCtx`](Zag/Data.lean)):

```lean
abbrev natCtx : PrimitiveCtx := [("Nat", Nat), ("Bool", Bool)]
abbrev natFuncCtx : PrimFuncCtx natCtx :=
  [ ("add", natBinaryFunc Nat.add), ("sub", natBinaryFunc Nat.sub)
  , ("mul", natBinaryFunc Nat.mul), ("div", natBinaryFunc Nat.div) ]
```
([`Test/Gauss/SSA.lean`](Test/Gauss/SSA.lean))

**3. A `Language` instance** ([`Zag/Meta/Language.lean`](Zag/Meta/Language.lean)) — `toTerm?` lowers the AST into Zag's core `Term`. Most clauses are direct: a source `ite` becomes a `Term.ite`, while the interesting clauses encode control flow: a loop lowers to `Term.recurse`, a `let_` extends the variable context, and a `yield` becomes a recursive call to the enclosing loop's motive. The result is an `Option`, so malformed control flow is rejected rather than assigned an arbitrary core meaning. A reflecting language also supplies `ofTerm`, allowing core tactic subgoals to be quoted back into source propositions:

```lean
instance : Language.Reflects natCtx (SSAExpr natCtx) where
  toTerm? expr := SSAExpr.toTerm? expr {}
  ofTerm term := .ret (.raw term)
  toTerm?_ofTerm _ := rfl
```

Programs can then be written with the custom `ssa%` syntax while retaining their SSA type:

```lean
def lhsSSA (n : Nat) : SSAExpr natCtx :=
  ssa% {
    zero := prim(0 : Nat);
    one := prim(1 : Nat);
    start := prim(n : Nat);
    acc0 := prim(0 : Nat);
    loop (i : Nat := start, acc : Nat := acc0) : Nat {
      cond := gt i zero;
      if cond {
        nextI := call sub [i, one];
        nextAcc := call add [acc, i];
        yield nextI, nextAcc
      } else {
        acc
      }
    }
  }

theorem lhsSSA_lowers (n : Nat) :
    Language.toTerm? (lhsSSA n) = some (loopTerm n 0) := rfl
```
([`Test/Gauss/SSA.lean`](Test/Gauss/SSA.lean))

The `ssa%` block remains surface syntax until `toTerm?` succeeds. For symbolic `n`, the resulting core term is the following, writing `NatTy` for `.prim "Nat"`, `stateTys` for the loop-state type `[NatTy, NatTy]`, and `Term.nat k` for a `Nat` literal:

```lean
.recurse NatTy
  (.app (.mkStruct stateTys) [Term.nat n, Term.nat 0])                 -- init state (i := n, acc := 0)
  (.ite (.primGt (.app (.structProj stateTys 0) [.var 0]) (Term.nat 0)) -- cond: i > 0
    (.app (.var 1)                                                      -- yield: recurse on new state
      [.app (.mkStruct stateTys)
        [ .app (.primFunc "sub") [.app (.structProj stateTys 0) [.var 0], Term.nat 1]   -- i - 1
        , .app (.primFunc "add") [.app (.structProj stateTys 1) [.var 0],                -- acc + i
                                  .app (.structProj stateTys 0) [.var 0]] ]])
    (.app (.structProj stateTys 1) [.var 0]))                           -- else: acc
```

The whole loop is one `recurse` over a struct-packed state `(i, acc)`; `.var 0` is the current state, `.var 1` the recursive continuation (the loop's motive), and `structProj 0`/`1` project out `i`/`acc`. The comfortable surface syntax and this inert tree are *the same object* — which is exactly what lets Zag evaluate it and prove things about it.

# propositions, and what it means to prove one

So far `Pr` has just been "the type of propositions." Its parameter records the expression type used at proposition leaves, which lets goals retain their source-language syntax.

`Pr` is an *inductive datatype* of propositions ([`Zag/Data.lean`](Zag/Data.lean)) — not an arbitrary Lean `Prop`, but a small fixed grammar:

```lean
inductive Pr (E : Type) where
  | eq (ctx : List Ty) (ty : Ty) : E → E → Pr E
  | hasType (ctx : List Ty) : E → Ty → Pr E
  | and : Pr E → Pr E → Pr E
  | forallTy   : Pr E → Pr E
  | forallTerm : Pr E → Pr E
```

Core goals use `Pr (Term primCtx)`; an SSA-native goal uses `Pr (SSAExpr primCtx)`. Because a `Pr` is *data* with finitely many shapes, a tactic can pattern-match on it and take it apart — peel a `forallTerm`, split an `and`, or lower its leaves and invoke a core tactic. You cannot case-analyse an arbitrary Lean `Prop` like that. Restricting propositions to this grammar is the price that buys structural automation.

A `Pr` is only syntax. Its *meaning* is a genuine Lean proposition, assigned by `Pr.interp` ([`Zag/Theory.lean`](Zag/Theory.lean)), which just reads each shape off as the corresponding logical connective:

```lean
Pr.interp ... (.eq ctx ty x y)  =  «x and y are typed-equal at ty»
Pr.interp ... (.and p q)        =  Pr.interp ... p ∧ Pr.interp ... q
Pr.interp ... (.forallTerm p)   =  ∀ x, Pr.interp ... p
```

`Pr.Provable p` ([`Zag/Theory.lean`](Zag/Theory.lean)) is nothing more than *holding a Lean proof of `Pr.interp p`* for a core proposition:

```lean
inductive Pr.Provable ... (p : Pr (Term primCtx)) : Prop
  | ofProof (proof : Pr.interp ... p)
```

`Language.Provable` extends this to a surface proposition: it contains a successful `Pr.toTerm?` result and a `Pr.Provable` proof of that core proposition. Thus a surface goal has no separate semantics. A refinement never proves anything unavailable by hand; it only reduces one checked proposition to smaller checked propositions.

**The Gauss example.** The theorem "the loop summing `1 + 2 + ... + n` returns `n * (n + 1) / 2`" is the `Pr` that equates two programs — the loop `lhsProgram n` and the closed form `rhsTerm n`, at type `Nat` ([`Test/Gauss/Rec.lean`](Test/Gauss/Rec.lean)):

```lean
def gaussStatement (n : Nat) : Pr (Term natCtx) :=
  .eq [] NatTy (lhsProgram n) (rhsTerm n)
```

The same theorem can remain in SSA syntax ([`Test/Gauss/SSA.lean`](Test/Gauss/SSA.lean)):

```lean
def gaussGoalSSA (n : Nat) : Pr (SSAExpr natCtx) :=
  .eq [] NatTy (lhsSSA n) (.ret (.raw (rhsTerm n)))

theorem gaussGoalSSA_toTerm (n : Nat) :
    (gaussGoalSSA n).toTerm? = some (gaussStatement n) := rfl
```

`Tactic.raise` applies a core tactic after successful lowering and quotes its generated subgoals
back through `ofTerm`. Partial tactics use `Tactic?.raise`; if one does not apply, `toTactic`
retains the original SSA goal instead of replacing it with raw quoted core syntax. The test suite
runs raised structural decomposition and induction and checks this no-op behavior.

Its interpretation `Pr.interp ... (gaussStatement n)` unfolds to two familiar demands: that both programs are well-typed, and that they evaluate to the same `Nat`. The Gauss proof establishes the typing lemmas directly. Zag also provides `Pr.TypeUnification.unifyType` ([`Meta/UnifyType.lean`](Meta/UnifyType.lean)), a core tactic that decomposes `hasType` goals by term structure. For example, `hasType ctx (ite c t e) ty` reduces to typing obligations for the condition and both branches.

```lean
let refinement := Tactic.iterate 20
  (Pr.TypeUnification.unifyType (ctx := peanoCtx) (ctxTy := []) (ctxTerm := []))
  (.hasType bodyCtx bodyTerm NatTy)
```

Here is the goal tree that `iterate` builds for `bodyTerm` — the loop body, an `ite` on a comparison:

```
            hasType bodyCtx bodyTerm NatTy
                        |
                   unifyType
                        |
          ┌─────────────┼─────────────┐
          |             |             |
  hasType cond    hasType yield   hasType acc
   : Bool          : NatTy         : NatTy
          |             |             |
       unifyType     unifyType     unifyType
          |             |             |
    ┌─────┴─────┐  (app recurse)  (app structProj)
    |           |       |             |
  hasType    hasType   ...           ...
  lhs :Nat  rhs :Nat
    |           |
 (app proj)  (nat 0)
    |           |
  ┌─┴──┐       ok
  |    |
hasType hasType
var 0  structProj
 :Σ    :Nat→Σ
  |      |
  ok      ok
```

Each leaf marked ok can be resolved by `unifyType` matching against `primFuncMatch?`, `varMatch?`, or a known constructor type. Once a refinement has no goals, `Refinement.toProvable` collapses it into a single proof. The evaluation demand is the real mathematics: an ordinary Lean proof that the loop computes the closed form and, crucially, a proof about the loop's executable semantics rather than an unverified translation.

Under the hood, `gaussStatement n` is obtained by instantiating a *predicate* ([`Test/Gauss/Rec.lean`](Test/Gauss/Rec.lean)) — a `Pr` with a hole for the input:

```lean
def gaussPredicate : Pr (Term natCtx) :=
  .eq [] NatTy
    (.recurse NatTy (.var 0) bodyTerm)           -- loop with input as var 0
    (.app (.primFunc "div")                       -- closed form with var 0
      [(.app (.primFunc "mul")
        [(.var 0), (.app (.primFunc "add") [(.var 0), Term.nat 1])]),
       Term.nat 2])

-- gaussStatement n = substitute nat(n) for var 0:
theorem gaussStatement_eq (n : Nat) :
    gaussStatement n = Pr.Induction.instantiateTermAt 0 gaussPredicate (Term.nat n)
```

So `gaussStatement n` is literally `gaussPredicate` with `Term.nat n` plugged in for `var 0`. The proof proceeds by *natural-number induction on the predicate itself*: first prove the predicate holds at `0`, then prove it lifts from any `k` to `k + 1`. The full proof tree:

```
 gaussStatement n
 = .eq [] NatTy (lhsProgram n) (rhsTerm n)
      which is:  instantiateTermAt 0 gaussPredicate (nat n)
           |
 gaussInductionProgram n                    ← natInductionWithPredicate
           |                                    instantiates at (nat n)
      ┌────┴────────────────────────────────┐
      |                                     |
 BASE: gaussStatement 0               STEP: natStepGoal 0 gaussPredicate
 = .eq [] NatTy                          = .forallNat 0 (.forallNat 1
     (lhsProgram 0)                          (.implies (isSuccPr 0)
     (rhsTerm 0))                              (.implies P[1] P[0])))
      |                                     |
      |  Pr.interp gives:                 Pr.interp gives:
      |  1. hasType (lhsProgram 0) NatTy    ∀ x y : Nat,
      |  2. hasType (rhsTerm 0) NatTy       isSuccPr(x,y) →
      |  3. lhsProgram 0 ⟶ Val.nat 0        P[x] → P[y]
      |     rhsTerm 0 ⟶ Val.nat 0           where P[k] = gaussPredicate[k]
      |                                     |
      |  (loop with init=0 never enters     natStepGoal_of_literal_step
      |   the body; closed form 0*1/2=0)         |
      |                                     ┌────┴────────────┐
      ok                                    |                 |
                                    for each literal k:   gaussPredicate_congr
                                    gaussStatement k →    (swap well-typed term
                                    gaussStatement(k+1)   for the literal it
                                         |                evaluates to)
                                    gaussLiteralStep            |
                                      [unfold loop body   term.eval = k → P[k]
                                       one iteration,     term.eval = k+1 → P[k+1]
                                       show it matches         |
                                        the closed form]       ok  ok
                                         |
                                          ok
```
([`Meta/Induction.lean`](Meta/Induction.lean))

At the base, both sides of `.eq` evaluate to `Val.nat 0` — the loop with `init=0` never enters the body (the condition `0 > 0` is false), and the closed form `0 * 1 / 2 = 0`. At each induction step, `gaussLiteralStep` ([`Test/Gauss/Rec.lean`](Test/Gauss/Rec.lean)) unfolds exactly one loop iteration: given that `lhsProgram k` evaluates to `k*(k+1)/2` (extracted from the inductive hypothesis via `rhsTerm_eval_rhs`), it shows that `lhsProgram (k+1)` evaluates to `(k+1)*(k+2)/2` by chaining `cond_eval_succ` (the condition is true when `i = k+1`) and `step_eval_succ` (the body adds `k+1` to the accumulator). `gaussPredicate_congr` handles the bookkeeping of swapping a well-typed term `t` for the concrete `nat k` it evaluates to, so the step proved at the literal level lifts back to the term-quantified `natStepGoal`. Every edge carries a `prove` certificate; the whole tree collapses into a single `Pr.Provable natCtx natFuncCtx [] [] (gaussStatement n)`.

# what you trust

That closes the loop on the opening promise. The trust base is the language specification: `PrimitiveCtx`, `PrimFuncCtx`, and the partial lowering that connects surface syntax to core `Term`. The `Refinement` layer above it, including `unifyType` and induction, is *total and self-certifying*: each `prove` field is a reduction Lean checks, so a broken reduction is a compile-time type error. Soundness is guaranteed by Lean's kernel; refinements additionally make automation compositional and valid by construction. What remains for a human is the genuine mathematical content, with the surrounding framework ensuring it concerns the actual program semantics.
