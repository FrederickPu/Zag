import Meta.UnifyTypeCore

namespace Zag

namespace Pr

namespace TypeUnification

/-! ### Completeness

`Tactic.CompleteOn unifyType (hasType ·)`: every provable `hasType` goal is closed
outright. Invertibility on closed states follows. Requires empty type/term
substitutions and unique primfunc names. -/

mutual
theorem Ty.subst_nil : (t : Ty) → Ty.subst [] t = t
| .var idx => by simp
| .prim n => by simp
| .option ty => by simp
| .union tys => by simp
| .struct tys => by simp
| .func args ret => by simp
| .m ty => by simp
| .«abbrev» name args => by simp
private theorem Ty.subst_nil_list : (ts : List Ty) → ts.map (Ty.subst []) = ts
| [] => rfl
| t :: ts => by simp [Ty.subst_nil t, Ty.subst_nil_list ts]
end

theorem list_map_subst_nil (varCtx : List Ty) :
    varCtx.map (Ty.subst []) = varCtx :=
  Ty.subst_nil_list varCtx

theorem hasType_of_provable {ctx : Ctx} {varCtx : VarCtx}
    {term : Term ctx.primCtx} {ty : Ty}
    (h : Pr.Provable ctx [] [] (.hasType varCtx term ty)) :
    Term.hasType ctx varCtx term ty := by
  cases h with
  | ofProof proof =>
      simpa [Pr.interp, Term.subst, Ty.subst_nil, list_map_subst_nil] using proof

syntax (name := hasTypeTactic) "has_type" : tactic
syntax (name := reduceUnifyType) "reduce_unify_type" : tactic

macro_rules
| `(tactic| reduce_unify_type) =>
    `(tactic|
      simp [unifyType, unifyTypeGoals, unifyTypeHasTypeGoals, unifyTypeArgGoals,
        inferType?, inferTypes?, inferFuncArgs?, primFuncMatch?, varMatch?,
        PrimFuncCtx.get?, CheckedTermAbbrevCtx.get?, TermAbbrevCtx.Raw.get?,
        PrimFunc.ty, PrimFunc.outTy,
        OpCtx.get?, OpCtx.outTy?,
        Ty.subst, Ty.validIn, Ty.validListIn, Ty.normalizeAbbrev, Ty.normalizeWith,
        TypeAbbrevCtx.Raw.getWithPrefix?, Lib.Peano.peanoCtx, Lib.Peano.natOpCtx,
        Lib.Peano.natFuncCtx,
        Lib.Peano.natBinaryFunc, Lib.Peano.succFunc, Peano.opCtx, Term.nat,
        Term.bool, Term.ite, Op.ite, Op.eq, Op.compare])
| `(tactic| has_type) =>
    `(tactic|
      apply Pr.TypeUnification.hasType_of_provable <;>
      applyTactic Pr.TypeUnification.unifyType reducing_by reduce_unify_type)

private theorem list_find?_eq_of_getElem_nodup {α : Type _} {β : Type _}
    (l : List (α × β)) [DecidableEq α]
    (hnames : (l.map Prod.fst).Nodup) (idx : Fin l.length) :
    l.find? (fun x => x.1 = l[idx].1) = some l[idx] := by
  induction l with
  | nil => exact Fin.elim0 idx
  | cons hd tl ih =>
      cases idx using Fin.cases with
      | zero => simp [List.find?]
      | succ idx =>
          have hnodupTail : (tl.map Prod.fst).Nodup :=
            (List.nodup_cons.mp hnames).right
          have hne : ¬ (hd.1 = tl[idx].1) := by
            intro h
            exact (List.nodup_cons.mp hnames).left
              (h ▸ List.mem_map.mpr ⟨tl[idx], List.getElem_mem idx.isLt, rfl⟩)
          show List.find? (fun x => x.1 = tl[idx].1) (hd :: tl) = some tl[idx]
          cases hdec : (decide (hd.1 = tl[idx].1) : Bool) with
          | true => exact absurd (of_decide_eq_true hdec) hne
          | false =>
              have hform :
                  List.find? (fun x => x.1 = tl[idx].1) (hd :: tl) =
                    List.find? (fun x => x.1 = tl[idx].1) tl := by
                simp only [List.find?]; rw [hdec]
              rw [hform]; exact ih hnodupTail idx

private theorem primFuncCtx_get?_of_idx {ctx : Ctx}
    (hnames : (ctx.primFuncCtx.map Prod.fst).Nodup)
    (idx : Fin ctx.primFuncCtx.length) :
    PrimFuncCtx.get? ctx.primFuncCtx ctx.primFuncCtx[idx].1 =
      some ctx.primFuncCtx[idx].2 := by
  unfold PrimFuncCtx.get?
  rw [list_find?_eq_of_getElem_nodup (l := ctx.primFuncCtx) hnames idx]
  rfl

/-- Syntactic inference recovers the unique type in every typing derivation. -/
private theorem inferType?_of_hasType {ctx : Ctx} [Peano.Model ctx] {varCtx : List Ty}
    {term : Term ctx.primCtx} {ty : Ty}
    (hnames : (ctx.primFuncCtx.map Prod.fst).Nodup)
    (hty : Term.hasType ctx varCtx term ty) :
    inferType? ctx varCtx term = some ty := by
  induction hty with
  | prim val => simp [inferType?]
  | primFunc =>
      rename_i varCtx' idx
      simp only [inferType?]
      rw [primFuncCtx_get?_of_idx (ctx := ctx) hnames idx]
      rfl
  | var h =>
      rename_i varCtx' idx _
      simp only [inferType?]
      rw [List.getElem?_eq_getElem idx.isLt]
      simpa using h
  | «op» hargs₁ hargs₂ hout ih =>
      rename_i varCtx' name args tys r
      simp only [inferType?]
      rw [inferTypes?_of_getElem hargs₁ (fun i ha _ => ih ⟨i, ha⟩)]
      exact hout
  | app hf hargs₁ hargs₂ ihf iha =>
      simp only [inferType?, ihf]
  | «abbrev» hget htypes htypeArgs hargs₁ hargs₂ ih =>
      rename_i varCtx' name typeArgs args definition prior
      have hlookup : ctx.termAbbrevCtx.get? name = some definition :=
        TermAbbrevCtx.Raw.get?_eq_some_of_getWithPrefix? hget
      let expectedTys := definition.varCtx.map fun sourceTy =>
        (Ty.subst typeArgs sourceTy).normalizeAbbrev ctx.tyAbbrevCtx
      have hinferred : inferTypes? ctx varCtx' args = some expectedTys := by
        apply inferTypes?_of_getElem (by simp [expectedTys, hargs₁])
        intro i ha ht
        simpa [expectedTys, List.getElem_map] using ih ⟨i, ha⟩
      simp only [inferType?, hlookup, hinferred]
      rw [if_pos ⟨htypes, htypeArgs, hargs₁, rfl⟩]
  | mkStruct => simp [inferType?]
  | structProj idx => simp [inferType?]
  | «recurse» hinit hbody ihinit ihbody => simp [inferType?]

private theorem inferType?_eq_of_hasType_nil {ctx : Ctx} [Peano.Model ctx] {varCtx : List Ty}
    {term : Term ctx.primCtx} {inferred ty : Ty}
    (hnames : (ctx.primFuncCtx.map Prod.fst).Nodup)
    (hinf : inferType? ctx varCtx term = some inferred)
    (hty : Term.hasType ctx varCtx term ty) :
    ty = inferred := by
  exact Option.some.inj ((inferType?_of_hasType hnames hty).symm.trans hinf)

/- If `primFuncMatch?` fails, no entry has the given name and type. -/
private theorem primFuncMatch?_eq_none {primCtx : PrimitiveCtx} :
    ∀ (primFuncCtx : PrimFuncCtx primCtx) (name : String) (ty : Ty),
      primFuncMatch? primFuncCtx name ty = none →
      ∀ (i : Fin primFuncCtx.length), ¬(primFuncCtx[i].1 = name ∧ primFuncCtx[i].2.ty = ty)
| [], _, _, _, i => Fin.elim0 i
| hd :: tl, name, ty, hnone, i => by
    simp only [primFuncMatch?] at hnone
    split at hnone
    · next h => cases hnone
    · next hne =>
        match i with
        | ⟨0, _⟩ =>
            intro h
            exact hne (by simpa using h)
        | ⟨n + 1, hlt⟩ =>
            have hn : n < tl.length := by
              simpa using hlt
            have hrec : primFuncMatch? tl name ty = none := by
              cases hmatch : primFuncMatch? tl name ty with
              | none => rfl
              | some found => simp [hmatch] at hnone
            have := primFuncMatch?_eq_none tl name ty hrec ⟨n, hn⟩
            intro h
            exact this (by simpa using h)

/- If `varMatch?` fails, the indexed variable does not have the target type. -/
private theorem varMatch?_eq_none (ctxTy : List Ty) :
    ∀ (varCtx : List Ty) (idx : Nat) (ty : Ty),
      varMatch? ctxTy varCtx idx ty = none →
      ∀ (hlt : idx < varCtx.length), ¬(Ty.subst ctxTy varCtx[idx] = Ty.subst ctxTy ty)
| [], idx, ty, hnone, hlt => by simp at hlt
| hd :: tl, 0, ty, hnone, hlt => by
    simp only [varMatch?] at hnone
    split at hnone
    · cases hnone
    · next hne =>
        intro h
        exact hne (by simpa using h)
| hd :: tl, n + 1, ty, hnone, hlt => by
    simp only [varMatch?] at hnone
    have hn : n < tl.length := by
      simpa using hlt
    have hrec : varMatch? ctxTy tl n ty = none := by
      cases hmatch : varMatch? ctxTy tl n ty with
      | none => rfl
      | some found => simp [hmatch] at hnone
    have := varMatch?_eq_none ctxTy tl n ty hrec hn
    intro h
    exact this (by simpa using h)

/- If every operand closes, the concatenated arg-goal list is empty. -/
private theorem unifyTypeArgGoals_eq_nil_of_getElem {ctx : Ctx}
    {ctxTy : List Ty} {ctxTerm : List (Term ctx.primCtx)} {varCtx : List Ty} :
    ∀ (args : List (Term ctx.primCtx)) (tys : List Ty),
      args.length = tys.length →
      (∀ (i : Nat) (ha : i < args.length) (ht : i < tys.length),
        unifyTypeHasTypeGoals (ctx := ctx) ctxTy ctxTerm varCtx args[i] tys[i] = []) →
      unifyTypeArgGoals (ctx := ctx) ctxTy ctxTerm varCtx args tys = []
| [], [], _, _ => rfl
| [], _ :: _, hlen, _ => by simp at hlen
| _ :: _, [], hlen, _ => by simp at hlen
| arg :: args, ty :: tys, hlen, hpt => by
    have hhead : unifyTypeHasTypeGoals (ctx := ctx) ctxTy ctxTerm varCtx arg ty = [] :=
      hpt 0 (by simp) (by simp)
    have htail := unifyTypeArgGoals_eq_nil_of_getElem args tys
      (by simpa using Nat.succ.inj hlen)
      (fun i ha ht => by
        exact hpt (i + 1) (by simpa using ha) (by simpa using ht))
    simp only [unifyTypeArgGoals, hhead, htail, List.nil_append]

/- Every well-typed closed term is closed outright by the recursive checker. -/
theorem unifyTypeHasTypeGoals_eq_nil_of_hasType {ctx : Ctx} [Peano.Model ctx]
    {varCtx : List Ty} {term : Term ctx.primCtx} {ty : Ty}
    (hnames : (ctx.primFuncCtx.map Prod.fst).Nodup)
    (hty : Term.hasType ctx varCtx term ty) :
    unifyTypeHasTypeGoals (ctx := ctx) [] [] varCtx term ty = [] := by
  induction hty with
    | prim val =>
        simp [unifyTypeHasTypeGoals]
    | primFunc =>
        rename_i source idx
        unfold unifyTypeHasTypeGoals
        cases hmatch : primFuncMatch? ctx.primFuncCtx ctx.primFuncCtx[idx].1
            (Ty.subst [] ctx.primFuncCtx[idx].2.ty) with
        | some _ => rfl
        | none =>
            have htyEq : ctx.primFuncCtx[idx].2.ty =
                Ty.subst [] ctx.primFuncCtx[idx].2.ty := (Ty.subst_nil _).symm
            exact absurd ⟨rfl, htyEq⟩
              (primFuncMatch?_eq_none ctx.primFuncCtx _ _ hmatch idx)
    | var hget =>
        rename_i source idx sourceTy
        have hsource : source[idx.val] = sourceTy := by
          simpa [List.get_eq_getElem] using hget
        unfold unifyTypeHasTypeGoals
        cases hvar : varMatch? ([] : List Ty) source idx.val sourceTy with
        | some _ => rfl
        | none =>
            have hne := varMatch?_eq_none ([] : List Ty) source idx.val sourceTy
              hvar idx.isLt
            exact absurd (by simpa only [Ty.substNil] using hsource) hne
    | «op» hargs₁ hargs₂ hout ih =>
        rename_i source name args tys r
        have hinf : inferTypes? ctx source args = some tys :=
          inferTypes?_of_getElem hargs₁ fun i ha _ =>
            inferType?_of_hasType hnames (hargs₂ ⟨i, ha⟩)
        have hargsNil : unifyTypeArgGoals (ctx := ctx) [] [] source args tys = [] :=
          unifyTypeArgGoals_eq_nil_of_getElem (ctx := ctx) (ctxTy := [])
            (ctxTerm := []) (varCtx := source) args tys hargs₁ fun i ha _ => ih ⟨i, ha⟩
        unfold unifyTypeHasTypeGoals
        simp only [hinf]
        have hok : tys.map (Ty.subst ([] : List Ty)) = tys ∧
            ctx.opCtx.outTy? name tys = some (Ty.subst [] r) :=
          ⟨Ty.subst_nil_list tys, by simpa [Ty.subst_nil] using hout⟩
        rw [if_pos hok, hargsNil]
    | app hf hargs₁ hargs₂ ihf iha =>
        rename_i source f fTy args argsTy
        have hinfF : inferType? ctx source f = some (.func argsTy fTy) :=
          inferType?_of_hasType hnames hf
        have hfun : inferFuncArgs? ctx source f = some argsTy := by
          simp only [inferFuncArgs?, hinfF]
        have hargsNil : unifyTypeArgGoals (ctx := ctx) [] [] source args argsTy = [] :=
          unifyTypeArgGoals_eq_nil_of_getElem (ctx := ctx) (ctxTy := [])
            (ctxTerm := []) (varCtx := source) args argsTy hargs₁ fun i ha _ => iha ⟨i, ha⟩
        unfold unifyTypeHasTypeGoals
        simp only [hfun]
        rw [if_pos hargs₁, ihf, hargsNil]
        simp
    | «abbrev» hget htypes htypeArgs hargs₁ hargs₂ ih =>
        rename_i source name typeArgs args definition prior
        have hlookup : ctx.termAbbrevCtx.get? name = some definition :=
          TermAbbrevCtx.Raw.get?_eq_some_of_getWithPrefix? hget
        let expectedTys := definition.varCtx.map fun sourceTy =>
          (Ty.subst typeArgs sourceTy).normalizeAbbrev ctx.tyAbbrevCtx
        have hinf : inferTypes? ctx source args = some expectedTys := by
          apply inferTypes?_of_getElem (by simp [expectedTys, hargs₁])
          intro i ha ht
          simpa [expectedTys, List.getElem_map] using
            inferType?_of_hasType hnames (hargs₂ ⟨i, ha⟩)
        have hargsNil : unifyTypeArgGoals (ctx := ctx) [] [] source args expectedTys = [] :=
          unifyTypeArgGoals_eq_nil_of_getElem (ctx := ctx) (ctxTy := [])
            (ctxTerm := []) (varCtx := source) args expectedTys
            (by simp [expectedTys, hargs₁]) fun i ha ht => by
              simpa [expectedTys, List.getElem_map] using ih ⟨i, ha⟩
        unfold unifyTypeHasTypeGoals
        simp only [hlookup, hinf]
        rw [if_pos ⟨htypes, htypeArgs, hargs₁, rfl, True.intro⟩, hargsNil]
    | mkStruct =>
        simp [unifyTypeHasTypeGoals]
    | structProj idx =>
        simp [unifyTypeHasTypeGoals]
    | «recurse» hinit hbody ihinit ihbody =>
        rename_i source stateTy resultTy init body
        have hstate : inferType? ctx source init = some stateTy :=
          inferType?_of_hasType hnames hinit
        have hcheck : Ty.subst ([] : List Ty) stateTy = stateTy ∧
            Ty.subst ([] : List Ty) resultTy = resultTy ∧
            resultTy = Ty.subst [] resultTy :=
          ⟨Ty.subst_nil stateTy, Ty.subst_nil resultTy, (Ty.subst_nil resultTy).symm⟩
        unfold unifyTypeHasTypeGoals
        simp only [hstate]
        rw [if_pos hcheck, ihinit, ihbody]
        simp


end TypeUnification

end Pr

end Zag
