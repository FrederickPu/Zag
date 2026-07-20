# why program verification

Program verification is a much stronger alternative to testing. When you test a piece of code you sample from a distribution of expected inputs and check correctness on those samples. But many programs have arbitrary or even non-deterministic behavior (multithreading, for instance), and others take inputs of unbounded size, where no sampling distribution is obviously the right one — what *is* the correct probability distribution over lists? Testing can only ever cover the cases you thought to sample. Formal verification instead proves correctness for *all* inputs at once, and its cost is paid once up front rather than growing with the space of behaviors you are trying to cover.

# tldr

Zag lets you take a low-level program — C, LLVM IR, Zig — embed its language once, write programs in it, and prove properties about those programs in Lean. The distinctive part is *what you have to trust*. Every proof step is carried out by a `MetaProgram`: a piece of proof automation that comes packaged with a machine-checked proof of its own soundness. An unsound automation simply does not typecheck. So the only thing you trust by hand is the semantic specification of your target language — the meaning of its primitive types and operations. Everything built on top of that is checked by Lean.

# why lean

Lean is a dependently-typed programming language and proof assistant: you write ordinary programs and mathematical proofs in the same language, and the compiler checks the proofs. It has one of the fastest-growing formal mathematics libraries, and — because of recent "AI for math" efforts — a large amount of pretraining and RL has been directed at Lean code, making it ergonomic for both humans and AI agents to write proofs in.

# why not the existing approaches

To prove properties about programs, existing tools generally do one of two things:

1. **Transpile the source language into Lean** with an unverified translator (e.g. Aeneas). This is convenient, but the translator itself is trusted code — a bug in it silently invalidates every proof built on its output.

2. **Embed the program faithfully and use proof automation** to break goals into subgoals. This keeps the trusted base small, and Lean's kernel checks every finished proof, so no tactic can ever establish a false statement. But the automation *itself* has no guarantees: a tactic can loop forever, fail outright, or reduce your goal to subgoals that don't actually suffice — and extending it without quietly breaking those reductions is hard.

Zag avoids both failure modes. Against #1, you never hand-write a translator at all: you *declaratively specify* your language's semantics — its primitive types and operations, plus a structural lowering into Zag's core `Term` — and Zag supplies the single, shared evaluator that every proof runs against. There is no bespoke transpiler to get wrong, because the semantics *is* the specification. Against #2, the trust base stays just as small, but every automation is *total and self-certifying*. Instead of open-ended metacode, we reify propositions as a datatype `Pr` and automations as values of a type `MetaProgram` that carries, in its type, a proof that its reduction is valid:

```lean
structure MetaProgram primCtx primFuncCtx ctxTy ctxTerm goal where
  goals : List (Pr primCtx)
  prove : (∀ subgoal, subgoal ∈ goals →
    Pr.Provable ... subgoal) → Pr.Provable ... goal
```

A `MetaProgram` for a `goal` produces a list of sub`goals` together with `prove`: a proof that provability of all the subgoals implies provability of the goal. (`primCtx`/`primFuncCtx` are the language's primitive types and operations; `ctxTy`/`ctxTerm` are the ambient variable context.) Because `prove` is a *checked proof* the automation carries with it, you cannot construct a `MetaProgram` whose subgoals fail to imply its goal — it would not typecheck — and, being a plain total function, it always terminates. Lean's kernel already stops any tactic from proving something false; what `MetaProgram` adds is that every reduction is valid *by construction* and every automation is total, so the layer composes and extends without anyone re-auditing it by hand.

`MetaProgram`s compose. Given a program that emits subgoals, `refine` replaces each subgoal with another `MetaProgram`, and `iterate` applies a step under bounded fuel — building a tree whose leaves are closed by hand-written Lean proofs, with the soundness certificate threaded through automatically.

# embedding a language

Zag is a *deep embedding*: a program is **data** — a value of an inductive `Term` type, i.e. a syntax tree — rather than Lean code. Types are data too, a value of `Ty`:

```lean
inductive Ty where
  | prim   : String → Ty        -- named primitive: "Nat", "Bool", ...
  | struct : List Ty → Ty       -- tuples / records
  | func   : List Ty → Ty → Ty  -- function types
  | var : Nat → Ty              -- (plus option, union)

inductive Term (primCtx : PrimitiveCtx) where
  | prim (ty : Ty) : Ty.type primCtx ty → Term primCtx  -- a literal value of type `ty`
  | var : Nat → Term primCtx                            -- de Bruijn variable
  | app : Term primCtx → List (Term primCtx) → Term primCtx
  | ite : Term primCtx → Term primCtx → Term primCtx → Term primCtx
  | recurse (resultTy : Ty) (initState body : Term primCtx) : Term primCtx  -- bounded loop
  -- also: primFunc, primEq/primLt/primGt, mkStruct, structProj
```

Here `ite`, `app`, and `recurse` are *constructors of a datatype*, not Lean's own `if`, function application, or recursion. Morally, that is the whole point of a deep embedding: because a program is inert data, we can write Lean functions that take one apart and inspect it — an evaluator `Term.eval` that computes its result, a typing relation `hasType`, and the automations that pattern-match on its structure. (In a *shallow* embedding you would instead translate each source construct directly to the matching Lean construct; the program then dissolves into Lean and you can only reason about its translation, never about the program itself.)

To bring in a new language you supply three things. Take a small SSA language (similar to LLVM IR), in `Lang/SSA.lean`:

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

**2. The primitive semantics** — the built-in types and how operations evaluate:

```lean
abbrev natCtx : PrimitiveCtx := [("Nat", Nat), ("Bool", Bool)]
abbrev natFuncCtx : PrimFuncCtx natCtx :=
  [ ("add", natBinaryFunc Nat.add), ("sub", natBinaryFunc Nat.sub)
  , ("mul", natBinaryFunc Nat.mul), ("div", natBinaryFunc Nat.div) ]
```

where `natBinaryFunc` says how a binary operation evaluates on values.

**3. `toTerm`** — lower the AST into Zag's core `Term`, one structural clause per constructor. Most are direct: a source `ite` becomes a `Term.ite` on the lowered pieces,

```lean
| .ite cond thenExpr elseExpr, ctx => do
    let condTerm <- valueToTerm? cond ctx
    let thenTerm <- toTerm? thenExpr ctx
    let elseTerm <- toTerm? elseExpr ctx
    some (.ite condTerm thenTerm elseTerm)
```

while the interesting clauses encode the language's control flow: a loop lowers to `Term.recurse`, a `let_` extends the variable context, and a `yield` becomes a recursive call to the enclosing loop's motive. Programs can then be written with a custom `ssa%` syntax:

```lean
def lhsProgram (n : Nat) : Term natCtx :=
  (ssa% {
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
  } : SSAExpr natCtx).toTerm
```

The `ssa%` block is only sugar — `toTerm` erases it entirely, leaving a plain `Term` value. You can see the result directly (`#eval lhsProgram 3` prints the raw AST). For symbolic `n` it is the following, writing `NatTy` for `.prim "Nat"`, `stateTys` for the loop-state type `[NatTy, NatTy]`, and `Term.nat k` for a `Nat` literal:

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

# an extensible, verifiable automation layer

Everything comfortable about doing proofs — type-checkers, simplifiers, decision procedures, induction tactics — lives *above* the trust base as `MetaProgram`s. This is the part meant to grow: anyone can add a new automation, and the type of `MetaProgram` forces each one to certify its own reductions, so a broken automation is rejected at compile time instead of silently misbehaving. Contrast a tool like AutoCorres, whose convenience is delivered by ordinary ML metaprograms: nothing guarantees they terminate, and nothing guarantees a given run will actually close your goal rather than fail or diverge. (Lean's kernel still rejects any ill-formed proof they emit — so the risk is never a false theorem, only automation you cannot rely on.) In Zag the automation is a value that terminates by construction and whose `prove` field is a checked reduction; a bug is a type error, not a dead end you discover three steps into a proof. The comfort features are untrusted but fully verified.

Type-checking is the first such automation. `unifyType` (`Meta/UnifyType.lean`) is a `MetaProgram` that decomposes a `hasType` goal by the structure of the term — for example `hasType ctx (ite c t e) ty` splits into three subgoals, `c : Bool`, `t : ty`, `e : ty`. You run it with bounded fuel and check that no subgoals remain:

```lean
theorem bodyTerm_hasType : Term.hasType natCtx natFuncCtx bodyCtx bodyTerm NatTy := by
  let program := Zag.Pr.MetaProgram.iterate 20 (fun g => Zag.Pr.MetaProgram.unifyType g)
    (.hasType bodyCtx bodyTerm NatTy)
  have hclosed : program.goals = [] := by native_decide
  have hprov := Zag.Pr.MetaProgram.toProvable program hclosed
  ...
```

The `iterate 20` bounds the work, so termination is manifest rather than hoped for; `native_decide` checks the resulting goal list is empty; `toProvable` turns the closed program into a proof. Nothing here is trusted beyond the language spec — the emptiness check is decidable and `prove` carries its own soundness. Every future automation added to this layer inherits the same guarantee for free.

# propositions, and what it means to prove one

So far `Pr` has just been "the type of propositions." Its design deserves a closer look, because it is what makes automation possible at all.

`Pr` is an *inductive datatype* of propositions — not an arbitrary Lean `Prop`, but a small fixed grammar:

```lean
inductive Pr (primCtx : PrimitiveCtx) where
  | eq (ctx : List Ty) (ty : Ty) : Term primCtx → Term primCtx → Pr primCtx  -- two terms equal at a type
  | hasType (ctx : List Ty) : Term primCtx → Ty → Pr primCtx                 -- a term has a type
  | and : Pr primCtx → Pr primCtx → Pr primCtx                               -- (also: or, implies)
  | forallTy   : Pr primCtx → Pr primCtx                                     -- ∀ over types
  | forallTerm : Pr primCtx → Pr primCtx                                     -- ∀ over terms
```

Because a `Pr` is *data* with finitely many shapes, a `MetaProgram` can pattern-match on it and take it apart — turn a `hasType` of an `ite` into three smaller `hasType`s, peel a `forallTerm`, split an `and`. You cannot case-analyse an arbitrary Lean `Prop` like that. Restricting propositions to this grammar is exactly the price that buys the ability to automate reasoning over them.

A `Pr` is only syntax. Its *meaning* is a genuine Lean proposition, assigned by `Pr.interp`, which just reads each shape off as the corresponding logical connective:

```lean
Pr.interp ... (.eq ctx ty x y)  =  «x and y are typed-equal at ty»
Pr.interp ... (.and p q)        =  Pr.interp ... p ∧ Pr.interp ... q
Pr.interp ... (.forallTerm p)   =  ∀ x, Pr.interp ... p
```

And `Pr.Provable p` is nothing more than *holding a Lean proof of `Pr.interp p`*:

```lean
inductive Pr.Provable ... (p : Pr primCtx) : Prop
  | ofProof (proof : Pr.interp ... p)
```

That is the honest bottom line. Proving a `Pr` is *just* proving its interpretation as an ordinary Lean proposition. A `MetaProgram` never proves anything you could not have proved by hand — it only lightens the burden, rewriting one `Pr` into smaller `Pr`s whose interpretations are easier to establish, until the leaves are plain Lean proofs.

**The Gauss example.** The theorem "the loop summing `1 + 2 + ... + n` returns `n * (n + 1) / 2`" is the `Pr` that equates two programs — the loop `lhsProgram n` and the closed form `rhsTerm n`, at type `Nat`:

```lean
def gaussStatement (n : Nat) : Pr natCtx :=
  .eq [] NatTy (lhsProgram n) (rhsTerm n)
```

Its interpretation `Pr.interp ... (gaussStatement n)` unfolds to two familiar demands: that both programs are well-typed, and that they evaluate to the same `Nat`. The typing demand is handled by the `unifyType` automation from the previous section. The evaluation demand is the real mathematics — an ordinary Lean proof that the loop computes the closed form — and, crucially, it is a proof about the loop's *real executable semantics*, not about some unverified tool's translation of it.

# what you trust

That closes the loop on the opening promise. The trust base is exactly the language specification — `PrimitiveCtx` and `PrimFuncCtx`, the meaning of the primitives. The `MetaProgram` layer above it, `unifyType` today and more automation as the framework grows, is *total and self-certifying*: its `prove` field is a reduction Lean checks, so a broken automation is a compile-time type error rather than an unreliable tactic you debug at proof time. (Soundness — no false theorems — is guaranteed for everything by Lean's kernel regardless; what this layer adds is automation you can trust to actually work.) What is left for a human is only the genuine mathematical content — and even there, the surrounding framework guarantees you are proving something about the actual program.
