import Lean

open Lean

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

/-!
`@[eval_finish]` contains semantic simplifications for obligations left after machine evaluation.
Primitive libraries register their own value injectivity lemmas here, keeping `Meta.Eval`
independent of any particular primitive context.
-/
register_simp_attr eval_finish

structure EvalSemanticAttribute where
  attr : AttributeImpl
  ext : PersistentEnvExtension Name Name (Array Name)
deriving Inhabited

/-- Whole-term evaluation theorems used as cached backward rules by the symbolic evaluator. -/
initialize evalSemanticAttr : EvalSemanticAttribute ← do
  let ext ← registerPersistentEnvExtension {
    name := `evalSemanticExtension
    mkInitial := pure #[]
    addImportedFn := fun _ => pure #[]
    addEntryFn := fun entries name => entries.push name
    exportEntriesFn := fun entries => entries
  }
  let attr : AttributeImpl := {
    name := `eval_semantic
    descr := "register a whole-term semantic evaluation theorem"
    add := fun decl stx kind => do
      Attribute.Builtin.ensureNoArgs stx
      unless kind == AttributeKind.global do throwAttrMustBeGlobal `eval_semantic kind
      modifyEnv fun env => ext.addEntry env decl
  }
  registerBuiltinAttribute attr
  pure { attr, ext }

def EvalSemanticAttribute.getEntries (attr : EvalSemanticAttribute)
    (env : Environment) : Array Name :=
  let state := attr.ext.toEnvExtension.getState env
  state.importedEntries.flatMap id ++ state.state
