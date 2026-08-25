import Zag.EvalTriple

namespace Zag

class Language (primCtx : outParam PrimitiveCtx) (E : Type) where
  toTerm? : E → Option (Term primCtx)

class Language.Reflects (primCtx : outParam PrimitiveCtx) (E : Type)
    extends Language primCtx E where
  ofTerm : Term primCtx → E
  toTerm?_ofTerm : ∀ term, toTerm? (ofTerm term) = some term

@[reducible] instance instLanguageTerm (primCtx : PrimitiveCtx) :
    Language.Reflects primCtx (Term primCtx) where
  toTerm? := some
  ofTerm := id
  toTerm?_ofTerm _ := rfl

namespace Pr

variable {primCtx : PrimitiveCtx} {E : Type}

def toTerm? [Language primCtx E] : Pr E → Option (Pr (Term primCtx))
| .eq ctx ty lhs rhs => do
    let lhs ← Language.toTerm? lhs
    let rhs ← Language.toTerm? rhs
    some (.eq ctx ty lhs rhs)
| .hasType ctx e ty => do
    let e ← Language.toTerm? e
    some (.hasType ctx e ty)
| .and p q => return .and (← p.toTerm?) (← q.toTerm?)
| .or p q => return .or (← p.toTerm?) (← q.toTerm?)
| .implies p q => return .implies (← p.toTerm?) (← q.toTerm?)
| .forallTy name p => return .forallTy name (← p.toTerm?)
| .forallTerm name p => return .forallTerm name (← p.toTerm?)

def ofTerm [Language.Reflects primCtx E] (p : Pr (Term primCtx)) : Pr E :=
  p.map Language.Reflects.ofTerm

@[simp] theorem toTerm?_term : ∀ p : Pr (Term primCtx), p.toTerm? = some p
| .eq _ _ _ _ => rfl
| .hasType _ _ _ => rfl
| .and p q => by simp [toTerm?, toTerm?_term p, toTerm?_term q]
| .or p q => by simp [toTerm?, toTerm?_term p, toTerm?_term q]
| .implies p q => by simp [toTerm?, toTerm?_term p, toTerm?_term q]
| .forallTy _ p => by simp [toTerm?, toTerm?_term p]
| .forallTerm _ p => by simp [toTerm?, toTerm?_term p]

@[simp] theorem toTerm?_ofTerm [Language.Reflects primCtx E] :
    ∀ p : Pr (Term primCtx), (ofTerm (E := E) p).toTerm? = some p
| .eq _ _ lhs rhs => by simp [ofTerm, Pr.map, toTerm?, Language.Reflects.toTerm?_ofTerm lhs,
    Language.Reflects.toTerm?_ofTerm rhs]
| .hasType _ e _ => by
    simp [ofTerm, Pr.map, toTerm?, Language.Reflects.toTerm?_ofTerm e]
| .and p q => by
    change (ofTerm (E := E) p).toTerm?.bind (fun p' =>
      (ofTerm (E := E) q).toTerm?.bind (fun q' => some (Pr.and p' q'))) = some (Pr.and p q)
    rw [toTerm?_ofTerm p, toTerm?_ofTerm q]
    rfl
| .or p q => by
    change (ofTerm (E := E) p).toTerm?.bind (fun p' =>
      (ofTerm (E := E) q).toTerm?.bind (fun q' => some (Pr.or p' q'))) = some (Pr.or p q)
    rw [toTerm?_ofTerm p, toTerm?_ofTerm q]
    rfl
| .implies p q => by
    change (ofTerm (E := E) p).toTerm?.bind (fun p' =>
      (ofTerm (E := E) q).toTerm?.bind (fun q' => some (Pr.implies p' q'))) =
        some (Pr.implies p q)
    rw [toTerm?_ofTerm p, toTerm?_ofTerm q]
    rfl
| .forallTy name p => by
    change (ofTerm (E := E) p).toTerm?.bind (fun p' => some (Pr.forallTy name p')) =
      some (Pr.forallTy name p)
    rw [toTerm?_ofTerm p]
    rfl
| .forallTerm name p => by
    change (ofTerm (E := E) p).toTerm?.bind (fun p' => some (Pr.forallTerm name p')) =
      some (Pr.forallTerm name p)
    rw [toTerm?_ofTerm p]
    rfl

end Pr

def Language.Provable (ctx : Ctx) {E : Type} [Language ctx.primCtx E]
    (ctxTy : Scope Ty) (ctxTerm : Scope (Term ctx.primCtx)) (p : Pr E)
    (hM : ctx.M = Id := by first | assumption | rfl) : Prop :=
  ∃ termPr, p.toTerm? = some termPr ∧ Pr.Provable ctx ctxTy ctxTerm termPr hM

@[simp] theorem Language.Provable_term {ctx : Ctx} (ctxTy : Scope Ty)
    (ctxTerm : Scope (Term ctx.primCtx)) (p : Pr (Term ctx.primCtx))
    {hM : ctx.M = Id} :
    Language.Provable ctx ctxTy ctxTerm p hM ↔ Pr.Provable ctx ctxTy ctxTerm p hM := by
  simp [Language.Provable]

end Zag
