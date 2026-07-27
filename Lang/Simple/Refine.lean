import Lang.SSA

/-!
  Cross-context refinement scaffolding.

  No unfinished simulation theorem is marked `sorry`.
  When `evalGo` simulation is proved, attach it here as a real theorem.
-/

namespace Lang.Simple.Refine

open Zag

structure CtxRefine (A C : Ctx) where
  tyRel : Ty → Ty → Prop
  valRel : Val C.primCtx → Val A.primCtx → Prop

def CtxRefine.id (ctx : Ctx) : CtxRefine ctx ctx where
  tyRel := fun a b => a = b
  valRel := fun a b => a = b

def CtxRefine.trans {A B C : Ctx}
    (r₁ : CtxRefine A B) (r₂ : CtxRefine B C) : CtxRefine A C where
  tyRel := fun tC tA => ∃ tB, r₂.tyRel tC tB ∧ r₁.tyRel tB tA
  valRel := fun vC vA => ∃ vB, r₂.valRel vC vB ∧ r₁.valRel vB vA

def envRelated {A C : Ctx} (R : CtxRefine A C) :
    List (Val C.primCtx) → List (Val A.primCtx) → Prop
  | [], [] => True
  | vC :: eC, vA :: eA => R.valRel vC vA ∧ envRelated R eC eA
  | _, _ => False

theorem envRelated_refl (ctx : Ctx) :
    ∀ env, envRelated (CtxRefine.id ctx) env env
  | [] => trivial
  | _ :: env => ⟨rfl, envRelated_refl ctx env⟩

/--
  Open obligation (not a theorem): forward simulation of `Term.evalGo` under `R`.
  Proving this is M4′ in AutoCorres.md; do not stub with `sorry`.
-/
def EvalGoSimulate (A C : Ctx) (R : CtxRefine A C) : Prop :=
  ∀ (envC : List (Val C.primCtx)) (envA : List (Val A.primCtx))
    (tC : Term C.primCtx) (tA : Term A.primCtx) (vC : Val C.primCtx),
    envRelated R envC envA →
    Term.evalGo C [] envC tC = some vC →
    -- term relatedness left abstract until TermRelated exists
    ∃ vA, Term.evalGo A [] envA tA = some vA ∧ R.valRel vC vA

end Lang.Simple.Refine
