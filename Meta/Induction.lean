import Zag.Meta
import Lib.Peano.Defs

/-!
# Induction for block programs

The old rule was stated against `Term.recurse`: it located a loop, abstracted the loop's initial
state, and inducted on that. Blocks recurse by calling themselves, so there is no loop node to
find; the induction target is now the *argument a recursive block is called with*.

The rule itself never mentioned `recurse` and still does not mention `call`. It is a statement
about propositions:

    P(0)    ∀ x y : Nat, succ x = y → P(x) → P(y)
    ------------------------------------------------
                    ∀ n : Nat, P(n)

What changed is how `P` is found (`abstractCallArg`, which abstracts the argument of a call to a
named block) and that variables are named, which removes de Bruijn weakening entirely: the old
`weakenTermAt` / `weaken` / `interp_weaken_*` layer is replaced by a freshness side condition on
the two names the step goal binds.
-/

namespace Zag

namespace Pr

namespace Induction

/-! ### free variables -/

mutual

def Term.varNames {primCtx : PrimitiveCtx} : Term primCtx → List String
| .prim _ _ => []
| .var name => [name]
| .app f args => Term.varNames f ++ Term.varNamesList args
| .op _ args => Term.varNamesList args
| .call _ args => Term.varNamesList args

def Term.varNamesList {primCtx : PrimitiveCtx} : List (Term primCtx) → List String
| [] => []
| t :: ts => Term.varNames t ++ Term.varNamesList ts

end

def varNames {primCtx : PrimitiveCtx} : Pr (Term primCtx) → List String
| .eq _ _ lhs rhs => Term.varNames lhs ++ Term.varNames rhs
| .hasType _ e _ => Term.varNames e
| .and p q => varNames p ++ varNames q
| .or p q => varNames p ++ varNames q
| .implies p q => varNames p ++ varNames q
| .forallTy _ p => varNames p
| .forallTerm _ p => varNames p

def quantifierFree {primCtx : PrimitiveCtx} : Pr (Term primCtx) → Bool
| .eq _ _ _ _ => true
| .hasType _ _ _ => true
| .and p q => quantifierFree p && quantifierFree q
| .or p q => quantifierFree p && quantifierFree q
| .implies p q => quantifierFree p && quantifierFree q
| .forallTy _ _ => false
| .forallTerm _ _ => false

/-! ### substituting a single named variable -/

mutual

def Term.instantiateVar {primCtx : PrimitiveCtx} (name : String) (replacement : Term primCtx) :
    Term primCtx → Term primCtx
| .prim ty val => .prim ty val
| .var n => if n = name then replacement else .var n
| .app f args =>
    .app (Term.instantiateVar name replacement f) (Term.instantiateVarList name replacement args)
| .op n args => .op n (Term.instantiateVarList name replacement args)
| .call n args => .call n (Term.instantiateVarList name replacement args)

def Term.instantiateVarList {primCtx : PrimitiveCtx} (name : String)
    (replacement : Term primCtx) : List (Term primCtx) → List (Term primCtx)
| [] => []
| t :: ts =>
    Term.instantiateVar name replacement t :: Term.instantiateVarList name replacement ts

end

/- `instantiate name t p` is `p` with the free variable `name` replaced by `t`. It is only used
  on quantifier-free `p`, where `Pr.map` reaches every leaf and captures nothing. -/
def instantiate {primCtx : PrimitiveCtx} (name : String) (replacement : Term primCtx)
    (p : Pr (Term primCtx)) : Pr (Term primCtx) :=
  p.map (Term.instantiateVar name replacement)

@[simp] theorem instantiate_eq {primCtx : PrimitiveCtx} (name : String)
    (r : Term primCtx) (varCtx : VarCtx) (ty : Ty) (lhs rhs : Term primCtx) :
    instantiate name r (.eq varCtx ty lhs rhs) =
      .eq varCtx ty (Term.instantiateVar name r lhs) (Term.instantiateVar name r rhs) := rfl

@[simp] theorem instantiate_hasType {primCtx : PrimitiveCtx} (name : String)
    (r : Term primCtx) (varCtx : VarCtx) (e : Term primCtx) (ty : Ty) :
    instantiate name r (.hasType varCtx e ty) =
      .hasType varCtx (Term.instantiateVar name r e) ty := rfl

@[simp] theorem instantiate_and {primCtx : PrimitiveCtx} (name : String)
    (r : Term primCtx) (p q : Pr (Term primCtx)) :
    instantiate name r (.and p q) = .and (instantiate name r p) (instantiate name r q) := rfl

@[simp] theorem instantiate_or {primCtx : PrimitiveCtx} (name : String)
    (r : Term primCtx) (p q : Pr (Term primCtx)) :
    instantiate name r (.or p q) = .or (instantiate name r p) (instantiate name r q) := rfl

@[simp] theorem instantiate_implies {primCtx : PrimitiveCtx} (name : String)
    (r : Term primCtx) (p q : Pr (Term primCtx)) :
    instantiate name r (.implies p q) = .implies (instantiate name r p) (instantiate name r q) :=
  rfl

@[simp] theorem quantifierFree_instantiate {primCtx : PrimitiveCtx} (name : String)
    (replacement : Term primCtx) :
    ∀ p : Pr (Term primCtx), quantifierFree (instantiate name replacement p) = quantifierFree p
| .eq _ _ _ _ => rfl
| .hasType _ _ _ => rfl
| .and p q => by
    simp only [instantiate_and, quantifierFree, quantifierFree_instantiate name replacement p,
      quantifierFree_instantiate name replacement q]
| .or p q => by
    simp only [instantiate_or, quantifierFree, quantifierFree_instantiate name replacement p,
      quantifierFree_instantiate name replacement q]
| .implies p q => by
    simp only [instantiate_implies, quantifierFree,
      quantifierFree_instantiate name replacement p,
      quantifierFree_instantiate name replacement q]
| .forallTy _ _ => rfl
| .forallTerm _ _ => rfl

/-! ### how `Term.subst` and `instantiateVar` interact

  These replace the de Bruijn `subst_weakenTermAt_*` family. Because a scope lookup takes the
  *last* matching binding, extending the context with `(name, t)` is exactly substituting `name`
  by `t`, with no index shifting to account for. -/

mutual

theorem Term.subst_instantiateVar {primCtx : PrimitiveCtx} (ctxTerm : Scope (Term primCtx))
    (name : String) (t : Term primCtx) (ht : Term.subst ctxTerm t = t) :
    ∀ b : Term primCtx,
      Term.subst (ctxTerm ++ [(name, t)]) b = Term.subst ctxTerm (Term.instantiateVar name t b)
| .prim _ _ => by simp [Term.instantiateVar]
| .var n => by
    simp only [Term.instantiateVar, Term.subst_var, Scope.get?_append_singleton]
    by_cases h : n = name
    · simp [h, ht]
    · simp [h]
| .app f args => by
    simp only [Term.instantiateVar, Term.subst_app]
    rw [Term.subst_instantiateVar ctxTerm name t ht f,
      Term.subst_instantiateVarList ctxTerm name t ht args]
| .op n args => by
    simp only [Term.instantiateVar, Term.subst_op]
    rw [Term.subst_instantiateVarList ctxTerm name t ht args]
| .call n args => by
    simp only [Term.instantiateVar, Term.subst_call]
    rw [Term.subst_instantiateVarList ctxTerm name t ht args]

theorem Term.subst_instantiateVarList {primCtx : PrimitiveCtx} (ctxTerm : Scope (Term primCtx))
    (name : String) (t : Term primCtx) (ht : Term.subst ctxTerm t = t) :
    ∀ bs : List (Term primCtx),
      bs.map (Term.subst (ctxTerm ++ [(name, t)])) =
        (Term.instantiateVarList name t bs).map (Term.subst ctxTerm)
| [] => by simp [Term.instantiateVarList]
| b :: bs => by
    simp only [Term.instantiateVarList, List.map_cons]
    rw [Term.subst_instantiateVar ctxTerm name t ht b,
      Term.subst_instantiateVarList ctxTerm name t ht bs]

end

/- A binding for a name the term never mentions is invisible, so the outer `(name, u)` binding
  still wins. This is the analogue of the old `interp_weaken_concat`. -/
mutual

theorem Term.subst_shadowed {primCtx : PrimitiveCtx} (ctxTerm : Scope (Term primCtx))
    (name yName : String) (u t : Term primCtx) (hu : Term.subst ctxTerm u = u) :
    ∀ b : Term primCtx, yName ∉ Term.varNames b →
      Term.subst (ctxTerm ++ [(name, u), (yName, t)]) b =
        Term.subst ctxTerm (Term.instantiateVar name u b)
| .prim _ _, _ => by simp [Term.instantiateVar]
| .var n, hfresh => by
    simp only [Term.varNames, List.mem_singleton] at hfresh
    have hny : ¬ (n = yName) := fun hc => hfresh hc.symm
    simp only [Term.instantiateVar, Term.subst_var]
    rw [show ctxTerm ++ [(name, u), (yName, t)] = (ctxTerm ++ [(name, u)]) ++ [(yName, t)] by simp]
    rw [Scope.get?_append_singleton, Scope.get?_append_singleton]
    by_cases h : n = name
    · subst h
      simp [hny, hu]
    · simp [h, hny]
| .app f args, hfresh => by
    simp only [Term.varNames, List.mem_append, not_or] at hfresh
    simp only [Term.instantiateVar, Term.subst_app]
    rw [Term.subst_shadowed ctxTerm name yName u t hu f hfresh.1,
      Term.subst_shadowedList ctxTerm name yName u t hu args hfresh.2]
| .op n args, hfresh => by
    simp only [Term.varNames] at hfresh
    simp only [Term.instantiateVar, Term.subst_op]
    rw [Term.subst_shadowedList ctxTerm name yName u t hu args hfresh]
| .call n args, hfresh => by
    simp only [Term.varNames] at hfresh
    simp only [Term.instantiateVar, Term.subst_call]
    rw [Term.subst_shadowedList ctxTerm name yName u t hu args hfresh]

theorem Term.subst_shadowedList {primCtx : PrimitiveCtx} (ctxTerm : Scope (Term primCtx))
    (name yName : String) (u t : Term primCtx) (hu : Term.subst ctxTerm u = u) :
    ∀ bs : List (Term primCtx), yName ∉ Term.varNamesList bs →
      bs.map (Term.subst (ctxTerm ++ [(name, u), (yName, t)])) =
        (Term.instantiateVarList name u bs).map (Term.subst ctxTerm)
| [], _ => by simp [Term.instantiateVarList]
| b :: bs, hfresh => by
    simp only [Term.varNamesList, List.mem_append, not_or] at hfresh
    simp only [Term.instantiateVarList, List.map_cons]
    rw [Term.subst_shadowed ctxTerm name yName u t hu b hfresh.1,
      Term.subst_shadowedList ctxTerm name yName u t hu bs hfresh.2]

end

/- Renaming the hole to a fresh `yName` and binding that name to `t` is the same as
  instantiating the hole with `t`. This is the analogue of the old `interp_weaken_middle`. -/
mutual

theorem Term.subst_instantiateVar_rename {primCtx : PrimitiveCtx}
    (ctxTerm : Scope (Term primCtx)) (name yName : String) (hne : ¬ (yName = name))
    (u t : Term primCtx) (ht : Term.subst ctxTerm t = t) :
    ∀ b : Term primCtx, yName ∉ Term.varNames b →
      Term.subst (ctxTerm ++ [(name, u), (yName, t)])
          (Term.instantiateVar name (.var yName) b) =
        Term.subst ctxTerm (Term.instantiateVar name t b)
| .prim _ _, _ => by simp [Term.instantiateVar]
| .var n, hfresh => by
    simp only [Term.varNames, List.mem_singleton] at hfresh
    have hny : ¬ (n = yName) := fun hc => hfresh hc.symm
    have hscope : ctxTerm ++ [(name, u), (yName, t)]
        = (ctxTerm ++ [(name, u)]) ++ [(yName, t)] := by simp
    by_cases h : n = name
    · rw [show Term.instantiateVar name (Term.var yName) (Term.var n) = Term.var yName by
            simp [Term.instantiateVar, h],
          show Term.instantiateVar name t (Term.var n) = t by simp [Term.instantiateVar, h],
          hscope, Term.subst_var, Scope.get?_append_singleton]
      simp [ht]
    · rw [show Term.instantiateVar name (Term.var yName) (Term.var n) = Term.var n by
            simp [Term.instantiateVar, h],
          show Term.instantiateVar name t (Term.var n) = Term.var n by
            simp [Term.instantiateVar, h],
          hscope, Term.subst_var, Term.subst_var, Scope.get?_append_singleton,
          Scope.get?_append_singleton]
      simp [h, hny]
| .app f args, hfresh => by
    simp only [Term.varNames, List.mem_append, not_or] at hfresh
    simp only [Term.instantiateVar, Term.subst_app]
    rw [Term.subst_instantiateVar_rename ctxTerm name yName hne u t ht f hfresh.1,
      Term.subst_instantiateVarList_rename ctxTerm name yName hne u t ht args hfresh.2]
| .op n args, hfresh => by
    simp only [Term.varNames] at hfresh
    simp only [Term.instantiateVar, Term.subst_op]
    rw [Term.subst_instantiateVarList_rename ctxTerm name yName hne u t ht args hfresh]
| .call n args, hfresh => by
    simp only [Term.varNames] at hfresh
    simp only [Term.instantiateVar, Term.subst_call]
    rw [Term.subst_instantiateVarList_rename ctxTerm name yName hne u t ht args hfresh]

theorem Term.subst_instantiateVarList_rename {primCtx : PrimitiveCtx}
    (ctxTerm : Scope (Term primCtx)) (name yName : String) (hne : ¬ (yName = name))
    (u t : Term primCtx) (ht : Term.subst ctxTerm t = t) :
    ∀ bs : List (Term primCtx), yName ∉ Term.varNamesList bs →
      (Term.instantiateVarList name (.var yName) bs).map
          (Term.subst (ctxTerm ++ [(name, u), (yName, t)])) =
        (Term.instantiateVarList name t bs).map (Term.subst ctxTerm)
| [], _ => by simp [Term.instantiateVarList]
| b :: bs, hfresh => by
    simp only [Term.varNamesList, List.mem_append, not_or] at hfresh
    simp only [Term.instantiateVarList, List.map_cons]
    rw [Term.subst_instantiateVar_rename ctxTerm name yName hne u t ht b hfresh.1,
      Term.subst_instantiateVarList_rename ctxTerm name yName hne u t ht bs hfresh.2]

end

/-! ### the same three facts, lifted to `Pr.interp` -/

theorem interp_instantiate {ctx : Ctx} (ctxTy : Scope Ty) (ctxTerm : Scope (Term ctx.primCtx))
    (name : String) (t : Term ctx.primCtx) (ht : Term.subst ctxTerm t = t) :
    ∀ p : Pr (Term ctx.primCtx), quantifierFree p = true →
      (Pr.interp ctx ctxTy (ctxTerm ++ [(name, t)]) p ↔
        Pr.interp ctx ctxTy ctxTerm (instantiate name t p))
| .eq _ _ lhs rhs, _ => by
    simp only [Pr.interp, instantiate, Pr.map,
      Term.subst_instantiateVar ctxTerm name t ht lhs,
      Term.subst_instantiateVar ctxTerm name t ht rhs]
| .hasType _ e _, _ => by
    simp only [Pr.interp, instantiate, Pr.map, Term.subst_instantiateVar ctxTerm name t ht e]
| .and p q, hqf => by
    simp only [quantifierFree, Bool.and_eq_true] at hqf
    simp only [Pr.interp, instantiate, Pr.map]
    exact and_congr (interp_instantiate ctxTy ctxTerm name t ht p hqf.1)
      (interp_instantiate ctxTy ctxTerm name t ht q hqf.2)
| .or p q, hqf => by
    simp only [quantifierFree, Bool.and_eq_true] at hqf
    simp only [Pr.interp, instantiate, Pr.map]
    exact or_congr (interp_instantiate ctxTy ctxTerm name t ht p hqf.1)
      (interp_instantiate ctxTy ctxTerm name t ht q hqf.2)
| .implies p q, hqf => by
    simp only [quantifierFree, Bool.and_eq_true] at hqf
    simp only [Pr.interp, instantiate, Pr.map]
    exact imp_congr (interp_instantiate ctxTy ctxTerm name t ht p hqf.1)
      (interp_instantiate ctxTy ctxTerm name t ht q hqf.2)
| .forallTy _ _, hqf => by simp [quantifierFree] at hqf
| .forallTerm _ _, hqf => by simp [quantifierFree] at hqf

theorem interp_shadowed {ctx : Ctx} (ctxTy : Scope Ty) (ctxTerm : Scope (Term ctx.primCtx))
    (name yName : String) (u t : Term ctx.primCtx) (hu : Term.subst ctxTerm u = u) :
    ∀ p : Pr (Term ctx.primCtx), quantifierFree p = true → yName ∉ varNames p →
      (Pr.interp ctx ctxTy (ctxTerm ++ [(name, u), (yName, t)]) p ↔
        Pr.interp ctx ctxTy ctxTerm (instantiate name u p))
| .eq _ _ lhs rhs, _, hfresh => by
    simp only [varNames, List.mem_append, not_or] at hfresh
    simp only [Pr.interp, instantiate, Pr.map,
      Term.subst_shadowed ctxTerm name yName u t hu lhs hfresh.1,
      Term.subst_shadowed ctxTerm name yName u t hu rhs hfresh.2]
| .hasType _ e _, _, hfresh => by
    simp only [varNames] at hfresh
    simp only [Pr.interp, instantiate, Pr.map,
      Term.subst_shadowed ctxTerm name yName u t hu e hfresh]
| .and p q, hqf, hfresh => by
    simp only [quantifierFree, Bool.and_eq_true] at hqf
    simp only [varNames, List.mem_append, not_or] at hfresh
    simp only [Pr.interp, instantiate, Pr.map]
    exact and_congr (interp_shadowed ctxTy ctxTerm name yName u t hu p hqf.1 hfresh.1)
      (interp_shadowed ctxTy ctxTerm name yName u t hu q hqf.2 hfresh.2)
| .or p q, hqf, hfresh => by
    simp only [quantifierFree, Bool.and_eq_true] at hqf
    simp only [varNames, List.mem_append, not_or] at hfresh
    simp only [Pr.interp, instantiate, Pr.map]
    exact or_congr (interp_shadowed ctxTy ctxTerm name yName u t hu p hqf.1 hfresh.1)
      (interp_shadowed ctxTy ctxTerm name yName u t hu q hqf.2 hfresh.2)
| .implies p q, hqf, hfresh => by
    simp only [quantifierFree, Bool.and_eq_true] at hqf
    simp only [varNames, List.mem_append, not_or] at hfresh
    simp only [Pr.interp, instantiate, Pr.map]
    exact imp_congr (interp_shadowed ctxTy ctxTerm name yName u t hu p hqf.1 hfresh.1)
      (interp_shadowed ctxTy ctxTerm name yName u t hu q hqf.2 hfresh.2)
| .forallTy _ _, hqf, _ => by simp [quantifierFree] at hqf
| .forallTerm _ _, hqf, _ => by simp [quantifierFree] at hqf

theorem interp_instantiate_rename {ctx : Ctx} (ctxTy : Scope Ty)
    (ctxTerm : Scope (Term ctx.primCtx)) (name yName : String) (hne : ¬ (yName = name))
    (u t : Term ctx.primCtx) (ht : Term.subst ctxTerm t = t) :
    ∀ p : Pr (Term ctx.primCtx), quantifierFree p = true → yName ∉ varNames p →
      (Pr.interp ctx ctxTy (ctxTerm ++ [(name, u), (yName, t)])
          (instantiate name (.var yName) p) ↔
        Pr.interp ctx ctxTy ctxTerm (instantiate name t p))
| .eq _ _ lhs rhs, _, hfresh => by
    simp only [varNames, List.mem_append, not_or] at hfresh
    simp only [Pr.interp, instantiate, Pr.map,
      Term.subst_instantiateVar_rename ctxTerm name yName hne u t ht lhs hfresh.1,
      Term.subst_instantiateVar_rename ctxTerm name yName hne u t ht rhs hfresh.2]
| .hasType _ e _, _, hfresh => by
    simp only [varNames] at hfresh
    simp only [Pr.interp, instantiate, Pr.map,
      Term.subst_instantiateVar_rename ctxTerm name yName hne u t ht e hfresh]
| .and p q, hqf, hfresh => by
    simp only [quantifierFree, Bool.and_eq_true] at hqf
    simp only [varNames, List.mem_append, not_or] at hfresh
    simp only [Pr.interp, instantiate, Pr.map]
    exact and_congr
      (interp_instantiate_rename ctxTy ctxTerm name yName hne u t ht p hqf.1 hfresh.1)
      (interp_instantiate_rename ctxTy ctxTerm name yName hne u t ht q hqf.2 hfresh.2)
| .or p q, hqf, hfresh => by
    simp only [quantifierFree, Bool.and_eq_true] at hqf
    simp only [varNames, List.mem_append, not_or] at hfresh
    simp only [Pr.interp, instantiate, Pr.map]
    exact or_congr
      (interp_instantiate_rename ctxTy ctxTerm name yName hne u t ht p hqf.1 hfresh.1)
      (interp_instantiate_rename ctxTy ctxTerm name yName hne u t ht q hqf.2 hfresh.2)
| .implies p q, hqf, hfresh => by
    simp only [quantifierFree, Bool.and_eq_true] at hqf
    simp only [varNames, List.mem_append, not_or] at hfresh
    simp only [Pr.interp, instantiate, Pr.map]
    exact imp_congr
      (interp_instantiate_rename ctxTy ctxTerm name yName hne u t ht p hqf.1 hfresh.1)
      (interp_instantiate_rename ctxTy ctxTerm name yName hne u t ht q hqf.2 hfresh.2)
| .forallTy _ _, hqf, _ => by simp [quantifierFree] at hqf
| .forallTerm _ _, hqf, _ => by simp [quantifierFree] at hqf

/-! ### the induction rule

  `P(0)` and `∀ x y : Nat, succ x = y → P(x) → P(y)` give `∀ n, P(n)`. Nothing here mentions how
  the program recurses, which is why the rule survives the move from `recurse` to blocks intact:
  only the way `P` is discovered had to change. -/

def succEq {primCtx : PrimitiveCtx} [Peano.Types primCtx]
    (xName yName succName : String) : Pr (Term primCtx) :=
  .eq [] Peano.BoolTy
    (.op "eq" [.op succName [.var xName], .var yName])
    (Term.bool true)

def natStepGoal {primCtx : PrimitiveCtx} [Peano.Types primCtx]
    (name yName succName : String) (body : Pr (Term primCtx)) : Pr (Term primCtx) :=
  Pr.forallNat name (Pr.forallNat yName
    (.implies (succEq name yName succName)
      (.implies body (instantiate name (.var yName) body))))

def natInductionGoals {primCtx : PrimitiveCtx} [Peano.Types primCtx]
    (name yName succName : String) (body : Pr (Term primCtx)) : List (Pr (Term primCtx)) :=
  [instantiate name (Term.nat 0) body, natStepGoal name yName succName body]

/-- `succName` is a successor operator: it types as `Nat → Nat` and sends a value `m` to `m+1`.
  It used to be a primitive function applied with `Term.app`; primitive functions are now ops, so
  the spec is stated against `Term.op`. -/
structure SuccSpec (ctx : Ctx) [Peano.Types ctx.primCtx] (succName : String) : Prop where
  hasType_op : ∀ (varCtx : VarCtx) (t : Term ctx.primCtx),
    Term.hasType ctx varCtx t Peano.NatTy →
    Term.hasType ctx varCtx (.op succName [t]) Peano.NatTy
  eval_succ : ∀ (env : Env ctx.primCtx) (t : Term ctx.primCtx) (m : Nat),
    Term.eval ctx env t = some (Val.nat m) →
    Term.eval ctx env (.op succName [t]) = some (Val.nat (m + 1))

theorem eval_natLit {ctx : Ctx} [Peano.Types ctx.primCtx] (env : Env ctx.primCtx) (n : Nat) :
    Term.eval ctx env (Term.nat n) = some (Val.nat n) := by
  rw [Term.eval, Term.evalGo.eq_def]
  rfl

theorem subst_natLit {primCtx : PrimitiveCtx} [Peano.Types primCtx]
    (ctxTerm : Scope (Term primCtx)) (n : Nat) :
    Term.subst ctxTerm (Term.nat n) = Term.nat n := by
  simp [Term.nat]

theorem subst_var_append {primCtx : PrimitiveCtx} (ctxTerm : Scope (Term primCtx))
    (name : String) (t : Term primCtx) :
    Term.subst (ctxTerm ++ [(name, t)]) (.var name) = t := by
  simp [Term.subst_var, Scope.get?_append_singleton]

@[simp] theorem subst_natTy (ctxTy : Scope Ty) : Ty.subst ctxTy Peano.NatTy = Peano.NatTy := by
  simp [Ty.subst]

@[simp] theorem subst_boolTy (ctxTy : Scope Ty) : Ty.subst ctxTy Peano.BoolTy = Peano.BoolTy := by
  simp [Ty.subst]

@[simp] theorem varCtx_subst_nil (ctxTy : Scope Ty) : VarCtx.subst ctxTy [] = [] := rfl

/- the object-level equation `succ x = y` holds when `x` and `y` are the literals `k` and `k+1` -/
theorem succEq_natLit {ctx : Ctx} [Peano.Model ctx] {succName : String}
    (hspec : SuccSpec ctx succName) (ctxTy : Scope Ty) (ctxTerm : Scope (Term ctx.primCtx))
    (name yName : String) (hne : ¬ (yName = name)) (k : Nat) :
    Pr.interp ctx ctxTy (ctxTerm ++ [(name, Term.nat k)] ++ [(yName, Term.nat (k + 1))])
      (succEq name yName succName) := by
  have hx : Term.subst (ctxTerm ++ [(name, Term.nat k)] ++ [(yName, Term.nat (k + 1))])
      (.var name) = Term.nat k := by
    rw [Term.subst_var, Scope.get?_append_singleton, if_neg (fun h => hne h.symm),
      Scope.get?_append_singleton]
    simp
  have hy : Term.subst (ctxTerm ++ [(name, Term.nat k)] ++ [(yName, Term.nat (k + 1))])
      (.var yName) = Term.nat (k + 1) := subst_var_append _ _ _
  refine ⟨?_, ?_, ?_⟩
  · simp only [Pr.interp, Term.subst_op, List.map_cons, List.map_nil, hx, hy,
      varCtx_subst_nil, subst_boolTy]
    refine Term.hasType.binOp (argTy := Peano.NatTy) ?_ ?_ (Term.hasType.prim _)
    · unfold OpCtx.outTy?
      rw [Peano.Model.eqOp]
      simp [Op.eq, Op.compare]
    · exact hspec.hasType_op _ _ (Term.hasType.prim _)
  · simp only [Pr.interp, Term.bool, Term.subst_prim, varCtx_subst_nil, subst_boolTy]
    exact Term.hasType.prim _
  · intro env _
    simp only [Term.subst_op, List.map_cons, List.map_nil, hx, hy,
      Term.subst_prim, Term.bool]
    have hsucc : Term.evalGo ctx env (.op succName [Term.nat k]) = some (Val.nat (k + 1)) :=
      hspec.eval_succ env (Term.nat k) k (eval_natLit env k)
    have hlit : Term.evalGo ctx env (Term.nat (k + 1)) = some (Val.nat (k + 1)) :=
      eval_natLit env (k + 1)
    have heq := Term.evalGo_op_compare (ctx := ctx) (env := env) (name := "eq")
      (cmp := Val.primEq?) (a := .op succName [Term.nat k]) (b := Term.nat (k + 1))
      (va := Val.nat (k + 1)) (vb := Val.nat (k + 1))
      (by rw [Peano.Model.eqOp]; rfl) hsucc hlit rfl
    have hprimEq : Val.primEq? (Val.nat (k + 1) : Val ctx.primCtx) (Val.nat (k + 1)) =
        some true := by simp [Val.primEq?]
    rw [Term.eval, Term.eval, heq, hprimEq, Term.evalGo.eq_def]
    rfl

theorem natInductionChain {ctx : Ctx} [Peano.Model ctx] {ctxTy : Scope Ty}
    {ctxTerm : Scope (Term ctx.primCtx)} {body : Pr (Term ctx.primCtx)}
    {name yName succName : String}
    (hspec : SuccSpec ctx succName)
    (hne : ¬ (yName = name))
    (hqf : quantifierFree body = true)
    (hfresh : yName ∉ varNames body)
    (hbase : Pr.Provable ctx ctxTy ctxTerm (instantiate name (Term.nat 0) body))
    (hstep : Pr.Provable ctx ctxTy ctxTerm (natStepGoal name yName succName body)) :
    ∀ n, Pr.Provable ctx ctxTy ctxTerm (instantiate name (Term.nat n) body) := by
  cases hstep with
  | ofProof hstepProof =>
      intro n
      induction n with
      | zero => exact hbase
      | succ k ih =>
          cases ih with
          | ofProof ihProof =>
              refine Pr.Provable.ofProof ?_
              have hguardx : Pr.interp ctx ctxTy (ctxTerm ++ [(name, Term.nat k)])
                  (.hasType [] (.var name) Peano.NatTy) := by
                simp only [Pr.interp, subst_var_append, varCtx_subst_nil, subst_natTy]
                exact Term.hasType.prim _
              have hy := hstepProof (Term.nat k) hguardx (Term.nat (k + 1))
              have hguardy : Pr.interp ctx ctxTy
                  (ctxTerm ++ [(name, Term.nat k)] ++ [(yName, Term.nat (k + 1))])
                  (.hasType [] (.var yName) Peano.NatTy) := by
                simp only [Pr.interp, subst_var_append, varCtx_subst_nil, subst_natTy]
                exact Term.hasType.prim _
              have hstepAt := hy hguardy
                (succEq_natLit hspec ctxTy ctxTerm name yName hne k)
              have hassoc : ctxTerm ++ [(name, Term.nat k)] ++ [(yName, Term.nat (k + 1))] =
                  ctxTerm ++ [(name, Term.nat k), (yName, Term.nat (k + 1))] := by simp
              have hPk : Pr.interp ctx ctxTy
                  (ctxTerm ++ [(name, Term.nat k)] ++ [(yName, Term.nat (k + 1))]) body := by
                rw [hassoc]
                exact (interp_shadowed ctxTy ctxTerm name yName (Term.nat k)
                  (Term.nat (k + 1)) (subst_natLit ctxTerm k) body hqf hfresh).mpr ihProof
              have hPy := hstepAt hPk
              rw [hassoc] at hPy
              exact (interp_instantiate_rename ctxTy ctxTerm name yName hne (Term.nat k)
                (Term.nat (k + 1)) (subst_natLit ctxTerm (k + 1)) body hqf hfresh).mp hPy

def natInductionWithPredicate {ctx : Ctx} [Peano.Model ctx]
    {ctxTy : Scope Ty} {ctxTerm : Scope (Term ctx.primCtx)}
    (succName : String) (hspec : SuccSpec ctx succName)
    (goal body : Pr (Term ctx.primCtx)) (name yName : String) (target : Nat)
    (hne : ¬ (yName = name))
    (hqf : quantifierFree body = true)
    (hfresh : yName ∉ varNames body)
    (hinst : goal = instantiate name (Term.nat target) body) :
    Refinement ctx ctxTy ctxTerm goal where
  goals := natInductionGoals name yName succName body
  prove := by
    intro proveSubgoals
    simp only [Language.Provable_term] at proveSubgoals ⊢
    have hbase := proveSubgoals (instantiate name (Term.nat 0) body)
      (by simp [natInductionGoals])
    have hstep := proveSubgoals (natStepGoal name yName succName body)
      (by simp [natInductionGoals])
    rw [hinst]
    exact natInductionChain hspec hne hqf hfresh hbase hstep target

end Induction

end Pr

end Zag
