import Lean

/-!
The simp set the evaluation tactics run with.

Tagging a declaration `@[eval_step]` says "unfold this when stepping the machine". It is declared
here, in its own module, because a Lean attribute cannot be used in the file that registers it.

The point is that each layer tags its own: the machine tags `step`/`driveOp`, `Peano` tags its
operators, `PeanoHeap` tags `heapOpCtx`. `Meta/Eval.lean` then needs no knowledge of any of them,
where it previously carried a hardcoded list mixing machine internals with Peano specifics.
-/

register_simp_attr eval_step

/-!
`@[eval_fold]` is the opposite direction: rules that put a *residual* goal back into the notation
the user wrote. Stepping needs `Term.nat` unfolded to a `Term.prim`, but a literal that never got
stepped should not be left displayed as `Term.prim Peano.NatTy (Ty.ofNat ..)`.

The two sets must stay separate -- a fold rule and its matching unfold rule in one `simp` call
loop. The tactics run this one once, after normalisation has finished.
-/
register_simp_attr eval_fold
