import Zag.Meta
import Lib.Peano.Defs

namespace Zag

namespace Ty

def primitiveNames : Ty → List String
| .var _ => []
| .prim name => [name]
| .option ty => ty.primitiveNames
| .union tys => tys.flatMap primitiveNames
| .struct tys => tys.flatMap primitiveNames
| .func args result => args.flatMap primitiveNames ++ result.primitiveNames
| .m ty => ty.primitiveNames

end Ty

namespace Term

def primitiveNames {primCtx : PrimitiveCtx} : Term primCtx → List String
| .prim ty _ => ty.primitiveNames
| .primFunc _ => []
| .var _ => []
| .app f args => f.primitiveNames ++ args.flatMap primitiveNames
| .op _ args => args.flatMap primitiveNames
| .mkStruct tys => tys.flatMap Ty.primitiveNames
| .structProj tys _ => tys.flatMap Ty.primitiveNames
| .recurse resultTy init body =>
    resultTy.primitiveNames ++ init.primitiveNames ++ body.primitiveNames

end Term

namespace Pr

def primitiveNames {primCtx : PrimitiveCtx} : Pr (Term primCtx) → List String
| .eq varCtx ty lhs rhs =>
    varCtx.flatMap Ty.primitiveNames ++ ty.primitiveNames ++
      lhs.primitiveNames ++ rhs.primitiveNames
| .hasType varCtx term ty =>
    varCtx.flatMap Ty.primitiveNames ++ term.primitiveNames ++ ty.primitiveNames
| .and p q => p.primitiveNames ++ q.primitiveNames
| .or p q => p.primitiveNames ++ q.primitiveNames
| .implies p q => p.primitiveNames ++ q.primitiveNames
| .forallTy p => p.primitiveNames
| .forallTerm p => p.primitiveNames

namespace TypeUnification

def primitiveTypesDeclared (primCtx : PrimitiveCtx) (names : List String) : Prop :=
  ∀ name, name ∈ names → name ∈ primCtx.prims.map Primitive.name

def statePrimitiveNames {primCtx : PrimitiveCtx}
    (ctxTy : List Ty) (ctxTerm : List (Term primCtx)) (goal : Pr (Term primCtx)) : List String :=
  ctxTy.flatMap Ty.primitiveNames ++ ctxTerm.flatMap Term.primitiveNames ++ goal.primitiveNames

/- Faithful context assumptions for completeness of reflected type unification.

   `primFuncNames` is the simple sufficient condition for function lookup: if names
   are unique, `PrimFuncCtx.get?`/`primFuncMatch?` cannot infer a different function
   type from the one used by a `Term.hasType.primFunc` derivation.

   `primitiveNames` requires every primitive type mentioned by the current proof
   state to be declared in `PrimitiveCtx`; this deliberately does not rely on the
   reserved `Nat`/`Bool` fallback in `PrimitiveCtx.get?`. -/
structure UnifyTypePrecondition (ctx : Ctx)
    (ctxTy : List Ty) (ctxTerm : List (Term ctx.primCtx)) (goal : Pr (Term ctx.primCtx)) : Prop where
  primitiveCtxNames : (ctx.primCtx.prims.map Primitive.name).Nodup
  primFuncNames : (ctx.primFuncCtx.map Prod.fst).Nodup
  primitiveNames : primitiveTypesDeclared ctx.primCtx (statePrimitiveNames ctxTy ctxTerm goal)

private def primFuncMatch? {primCtx : PrimitiveCtx} :
    (primFuncCtx : PrimFuncCtx primCtx) → (name : String) → (ty : Ty) →
      Option { idx : Fin primFuncCtx.length //
        primFuncCtx[idx].1 = name ∧ primFuncCtx[idx].2.ty = ty }
| [], _, _ => none
| entry :: rest, name, ty =>
    if h : entry.1 = name ∧ entry.2.ty = ty then
      some ⟨⟨0, by simp⟩, by simpa using h⟩
    else
      match primFuncMatch? rest name ty with
      | some found =>
          some ⟨⟨found.val.val + 1, by simp [found.val.isLt]⟩, by simpa using found.property⟩
      | none => none

mutual

/- Type inference, mirroring `Term.hasType` rule for rule.

  No operator is special-cased: an operator's result type comes from `ctx.opCtx.outTy?`
  applied to the inferred operand types, exactly as `Term.hasType.op` requires. Zag is
  operator-agnostic, so the tactic must be too -- previously only `ite` was handled here
  and every other operator (`eq`, `lt`, `gt`, `pure`, `bind`, ...) was inferred as `none`,
  which is what made `unifyType` incomplete. -/
private def inferType? (ctx : Ctx) (varCtx : List Ty) : Term ctx.primCtx → Option Ty
| .prim ty _ => some ty
| .primFunc name => (PrimFuncCtx.get? ctx.primFuncCtx name).map PrimFunc.ty
| .var idx => varCtx[idx]?
| .app f _ =>
    match inferType? ctx varCtx f with
    | some (.func _ outTy) => some outTy
    | _ => none
| .op name args =>
    match inferTypes? ctx varCtx args with
    | some tys => ctx.opCtx.outTy? name tys
    | none => none
| .mkStruct tys => some (.func tys (.struct tys))
| .structProj tys idx => some (.func [.struct tys] tys[idx])
| .recurse resultTy _ _ => some resultTy

private def inferTypes? (ctx : Ctx) (varCtx : List Ty) :
    List (Term ctx.primCtx) → Option (List Ty)
| [] => some []
| arg :: args =>
    match inferType? ctx varCtx arg, inferTypes? ctx varCtx args with
    | some ty, some tys => some (ty :: tys)
    | _, _ => none

end

private def inferFuncArgs? (ctx : Ctx) (varCtx : List Ty) (term : Term ctx.primCtx) :
    Option (List Ty) :=
  match inferType? ctx varCtx term with
  | some (.func argsTy _) => some argsTy
  | _ => none

/- `inferTypes?` yields exactly one type per operand, so an operator branch that succeeded
  at inference never has to consider a length mismatch. -/
private theorem inferTypes?_length {ctx : Ctx} {varCtx : List Ty} :
    ∀ {args : List (Term ctx.primCtx)} {tys : List Ty},
      inferTypes? ctx varCtx args = some tys → args.length = tys.length
| [], tys, h => by simp [inferTypes?] at h; simp [h]
| arg :: args, tys, h => by
    simp only [inferTypes?] at h
    split at h
    · next ty tys' hty htys =>
        cases h
        simp [inferTypes?_length htys]
    · exact absurd h (by simp)

/- `inferTypes?` is pointwise `inferType?`. -/
private theorem inferTypes?_getElem {ctx : Ctx} {varCtx : List Ty} :
    ∀ {args : List (Term ctx.primCtx)} {tys : List Ty},
      inferTypes? ctx varCtx args = some tys →
      ∀ (i : Nat) (ha : i < args.length) (ht : i < tys.length),
        inferType? ctx varCtx args[i] = some tys[i]
| [], _, _, _, ha, _ => absurd ha (by simp)
| arg :: rest, tys, h, i, ha, ht => by
    simp only [inferTypes?] at h
    split at h
    · next ty tys' hty htys =>
        cases h
        cases i with
        | zero => simpa using hty
        | succ j =>
            exact inferTypes?_getElem htys j (by simpa using ha) (by simpa using ht)
    · exact absurd h (by simp)

/- Converse of `inferTypes?_getElem`: pointwise inference assembles into list inference. -/
private theorem inferTypes?_of_getElem {ctx : Ctx} {varCtx : List Ty} :
    ∀ {args : List (Term ctx.primCtx)} {tys : List Ty},
      args.length = tys.length →
      (∀ (i : Nat) (ha : i < args.length) (ht : i < tys.length),
        inferType? ctx varCtx args[i] = some tys[i]) →
      inferTypes? ctx varCtx args = some tys
| [], [], _, _ => by simp [inferTypes?]
| [], _ :: _, hlen, _ => by simp at hlen
| _ :: _, [], hlen, _ => by simp at hlen
| arg :: args, ty :: tys, hlen, hpt => by
    have hhead : inferType? ctx varCtx arg = some ty :=
      hpt 0 (by simp) (by simp)
    have htail : inferTypes? ctx varCtx args = some tys := by
      refine inferTypes?_of_getElem (by simpa using Nat.succ.inj hlen) ?_
      intro i ha ht
      exact hpt (i + 1) (by simpa using ha) (by simpa using ht)
    simp [inferTypes?, hhead, htail]

/- Substitution is the identity on each element of a list it fixes pointwise-as-a-list. -/
private theorem subst_getElem_of_map_eq {ctxTy tys : List Ty}
    (hsubst : tys.map (Ty.subst ctxTy) = tys) (j : Fin tys.length) :
    Ty.subst ctxTy tys[j] = tys[j] := by
  have h := congrArg (fun l => l[j.val]?) hsubst
  simp only [List.getElem?_map, List.getElem?_eq_getElem j.isLt] at h
  simpa using h

private def varMatch? (ctxTy : List Ty) :
    (varCtx : List Ty) → (idx : Nat) → (ty : Ty) →
      Option { finIdx : Fin (varCtx.map (Ty.subst ctxTy)).length //
        finIdx.val = idx ∧ (varCtx.map (Ty.subst ctxTy))[finIdx] = Ty.subst ctxTy ty }
| [], _, _ => none
| tyHead :: _, 0, ty =>
    if h : Ty.subst ctxTy tyHead = Ty.subst ctxTy ty then
      some ⟨⟨0, by simp⟩, by simp [h]⟩
    else none
| _ :: tys, idx + 1, ty =>
    match varMatch? ctxTy tys idx ty with
    | some found =>
        some ⟨⟨found.val.val + 1, by simpa using Nat.succ_lt_succ found.val.isLt⟩, by
          constructor
          · simp [found.property.left]
          · simpa using found.property.right⟩
    | none => none

mutual

/- Full recursive type checking: operand and subterm obligations are discharged by
  recursing structurally on the term rather than being handed back as subgoals, so a
  well-typed term closes outright. Recursion is on strict subterms throughout (`f` and
  `args` under `.app`, `args` under `.op`, `init`/`body` under `.recurse`), which is why
  this needs no fuel and admits plain structural induction. -/
private def unifyTypeHasTypeGoals {ctx : Ctx}
    (ctxTy : List Ty) (ctxTerm : List (Term ctx.primCtx))
    (varCtx : List Ty) (term : Term ctx.primCtx) (ty : Ty) : List (Pr (Term ctx.primCtx)) :=
    match term with
    | .prim actualTy _ =>
        if actualTy = Ty.subst ctxTy ty then [] else [.hasType varCtx term ty]
    | .primFunc name =>
        match primFuncMatch? ctx.primFuncCtx name (Ty.subst ctxTy ty) with
        | some _ => []
        | none => [.hasType varCtx term ty]
    | .var idx =>
        match ctxTerm with
        | [] =>
            match varMatch? ctxTy varCtx idx ty with
            | some _ => []
            | none => [.hasType varCtx term ty]
        | _ => [.hasType varCtx term ty]
    | .app f args =>
        match ctxTerm with
        | _ :: _ => [.hasType varCtx term ty]
        | [] =>
            match inferFuncArgs? ctx varCtx f with
            | some argsTy =>
                if args.length = argsTy.length then
                  unifyTypeHasTypeGoals ctxTy ctxTerm varCtx f (.func argsTy ty) ++
                    unifyTypeArgGoals ctxTy ctxTerm varCtx args argsTy
                else [.hasType varCtx term ty]
            | none => [.hasType varCtx term ty]
    | .op name args =>
        match inferTypes? ctx varCtx args with
        | some tys =>
            /- the `tys.map (Ty.subst ctxTy) = tys` guard mirrors `.recurse` below: operand
              types are inferred before substitution, so we only proceed when substitution
              acts as the identity on them (always true for the closed states `ctxTy = []`
              that completeness is stated for). -/
            if tys.map (Ty.subst ctxTy) = tys ∧
                ctx.opCtx.outTy? name tys = some (Ty.subst ctxTy ty) then
              unifyTypeArgGoals ctxTy ctxTerm varCtx args tys
            else [.hasType varCtx term ty]
        | none => [.hasType varCtx term ty]

    | .mkStruct tys =>
        if (.func tys (.struct tys)) = Ty.subst ctxTy ty then [] else [.hasType varCtx term ty]
    | .structProj tys idx =>
        if (.func [.struct tys] tys[idx]) = Ty.subst ctxTy ty then []
        else [.hasType varCtx term ty]
    | .recurse resultTy init body =>
        match ctxTerm with
        | [] =>
            match inferType? ctx varCtx init with
            | some stateTy =>
                if Ty.subst ctxTy stateTy = stateTy ∧
                    Ty.subst ctxTy resultTy = resultTy ∧
                    resultTy = Ty.subst ctxTy ty then
                  unifyTypeHasTypeGoals ctxTy ctxTerm varCtx init stateTy ++
                    unifyTypeHasTypeGoals ctxTy ctxTerm
                      (varCtx ++ [stateTy, .func [stateTy] resultTy]) body resultTy
                else [.hasType varCtx term ty]
            | none => [.hasType varCtx term ty]
        | _ :: _ => [.hasType varCtx term ty]

/- Operand obligations, recursing into each operand. Mismatched lengths cannot arise from
  `inferTypes?` (see `inferTypes?_length`); the `_, _` case is for totality only. -/
private def unifyTypeArgGoals {ctx : Ctx}
    (ctxTy : List Ty) (ctxTerm : List (Term ctx.primCtx)) (varCtx : List Ty) :
    List (Term ctx.primCtx) → List Ty → List (Pr (Term ctx.primCtx))
| arg :: args, argTy :: tys =>
    unifyTypeHasTypeGoals ctxTy ctxTerm varCtx arg argTy ++
      unifyTypeArgGoals ctxTy ctxTerm varCtx args tys
| _, _ => []

end

private def unifyTypeGoals {ctx : Ctx}
    (ctxTy : List Ty) (ctxTerm : List (Term ctx.primCtx)) :
    Pr (Term ctx.primCtx) → List (Pr (Term ctx.primCtx))
| .hasType varCtx term ty => unifyTypeHasTypeGoals ctxTy ctxTerm varCtx term ty
| goal => [goal]

mutual

private theorem unifyTypeHasType_sound {ctx : Ctx} [Peano.Model ctx] {ctxTy : List Ty}
    {ctxTerm : List (Term ctx.primCtx)} {varCtx : List Ty} :
    ∀ (term : Term ctx.primCtx) (ty : Ty),
      (∀ subgoal, subgoal ∈ unifyTypeHasTypeGoals (ctx := ctx) ctxTy ctxTerm varCtx term ty →
        Pr.Provable ctx ctxTy ctxTerm subgoal) →
        Pr.interp ctx ctxTy ctxTerm (.hasType varCtx term ty)
| .prim actualTy val, ty => by
    classical
    by_cases hty : actualTy = Ty.subst ctxTy ty
    · intro _
      have hprim : Term.hasType ctx (varCtx.map (Ty.subst ctxTy))
          (.prim actualTy val) (Ty.subst ctxTy ty) := by
        rw [← hty]
        exact Term.hasType.prim val
      simpa [Pr.interp, Term.subst] using hprim
    · intro proveSubgoals
      have hself := proveSubgoals (.hasType varCtx (.prim actualTy val) ty)
        (by simp [unifyTypeHasTypeGoals, hty])
      cases hself with
      | ofProof proof => exact proof
| .primFunc name, ty => by
    classical
    cases hmatch : primFuncMatch? ctx.primFuncCtx name (Ty.subst ctxTy ty) with
    | some found =>
        intro _
        have hname := found.property.left
        have hty := found.property.right
        have hprim := @Term.hasType.primFunc ctx (varCtx.map (Ty.subst ctxTy)) found.val
        rw [hname, hty] at hprim
        simpa [Pr.interp, Term.subst] using hprim
    | none =>
        intro proveSubgoals
        have hself := proveSubgoals (.hasType varCtx (.primFunc name) ty)
          (by simp [unifyTypeHasTypeGoals, hmatch])
        cases hself with
        | ofProof proof => exact proof
| .var idx, ty => by
    classical
    cases ctxTerm with
    | nil =>
        cases hvar : varMatch? ctxTy varCtx idx ty with
        | some found =>
            intro _
            have hvarType : Term.hasType ctx (varCtx.map (Ty.subst ctxTy))
                (.var idx) (Ty.subst ctxTy ty) := by
              have hraw : Term.hasType ctx (varCtx.map (Ty.subst ctxTy))
                  (.var found.val) (Ty.subst ctxTy ty) :=
                Term.hasType.var (idx := found.val) found.property.right
              simpa [found.property.left] using hraw
            simpa [Pr.interp, Term.subst] using hvarType
        | none =>
            intro proveSubgoals
            have hself := proveSubgoals (.hasType varCtx (.var idx) ty)
              (by simp [unifyTypeHasTypeGoals, hvar])
            cases hself with
            | ofProof proof => exact proof
    | cons head tail =>
        intro proveSubgoals
        have hself := proveSubgoals (.hasType varCtx (.var idx) ty)
          (by simp [unifyTypeHasTypeGoals])
        cases hself with
        | ofProof proof => exact proof
| .app f args, ty => by
    classical
    cases ctxTerm with
    | cons head tail =>
        intro proveSubgoals
        have hself := proveSubgoals (.hasType varCtx (.app f args) ty)
          (by simp [unifyTypeHasTypeGoals])
        cases hself with
        | ofProof proof => exact proof
    | nil =>
        cases hfun : inferFuncArgs? ctx varCtx f with
        | none =>
            intro proveSubgoals
            have hself := proveSubgoals (.hasType varCtx (.app f args) ty)
              (by simp [unifyTypeHasTypeGoals, hfun])
            cases hself with
            | ofProof proof => exact proof
        | some argsTy =>
            by_cases hlen : args.length = argsTy.length
            · intro proveSubgoals
              have proveF : ∀ subgoal,
                  subgoal ∈ unifyTypeHasTypeGoals (ctx := ctx) ctxTy [] varCtx f
                    (.func argsTy ty) →
                  Pr.Provable ctx ctxTy [] subgoal := by
                intro subgoal hsubgoal
                exact proveSubgoals subgoal (by
                  simp [unifyTypeHasTypeGoals, hfun, hlen, hsubgoal])
              have proveArgs : ∀ subgoal,
                  subgoal ∈ unifyTypeArgGoals (ctx := ctx) ctxTy [] varCtx args argsTy →
                  Pr.Provable ctx ctxTy [] subgoal := by
                intro subgoal hsubgoal
                exact proveSubgoals subgoal (by
                  simp [unifyTypeHasTypeGoals, hfun, hlen, hsubgoal])
              have hfInterp := unifyTypeHasType_sound f (.func argsTy ty) proveF
              have hf : Term.hasType ctx (varCtx.map (Ty.subst ctxTy))
                  (Term.subst [] f)
                  (.func (argsTy.map (Ty.subst ctxTy)) (Ty.subst ctxTy ty)) := by
                simpa [Pr.interp, Ty.subst] using hfInterp
              have hargs := unifyTypeArg_sound args argsTy hlen proveArgs
              have happ : Term.hasType ctx (varCtx.map (Ty.subst ctxTy))
                  (.app (Term.subst [] f) (args.map (Term.subst [])))
                  (Ty.subst ctxTy ty) := by
                refine Term.hasType.app hf ?_ ?_
                · simp [hlen]
                · intro idx
                  have harg := hargs ⟨idx.val, by simpa using idx.isLt⟩
                  simpa [List.getElem_map] using harg
              simpa [Pr.interp, Term.subst] using happ
            · intro proveSubgoals
              have hself := proveSubgoals (.hasType varCtx (.app f args) ty)
                (by simp [unifyTypeHasTypeGoals, hfun, hlen])
              cases hself with
              | ofProof proof => exact proof
| .op name args, ty => by
    classical
    cases hinf : inferTypes? ctx varCtx args with
    | none =>
        intro proveSubgoals
        have hself := proveSubgoals (.hasType varCtx (.op name args) ty)
          (by simp [unifyTypeHasTypeGoals, hinf])
        cases hself with
        | ofProof proof => exact proof
    | some tys =>
        by_cases hok : tys.map (Ty.subst ctxTy) = tys ∧
            ctx.opCtx.outTy? name tys = some (Ty.subst ctxTy ty)
        · obtain ⟨hsubst, hout⟩ := hok
          have hlen : args.length = tys.length := inferTypes?_length hinf
          intro proveSubgoals
          have proveArgs : ∀ subgoal,
              subgoal ∈ unifyTypeArgGoals (ctx := ctx) ctxTy ctxTerm varCtx args tys →
              Pr.Provable ctx ctxTy ctxTerm subgoal := by
            intro subgoal hsubgoal
            exact proveSubgoals subgoal (by
              simp [unifyTypeHasTypeGoals, hinf, hsubst, hout, hsubgoal])
          have hargs := unifyTypeArg_sound args tys hlen proveArgs
          have hopType : Term.hasType ctx (varCtx.map (Ty.subst ctxTy))
              (.op name (args.map (Term.subst ctxTerm))) (Ty.subst ctxTy ty) := by
            refine Term.hasType.op (tys := tys) ?_ ?_ hout
            · simp [hlen]
            · intro idx
              have harg := hargs ⟨idx.val, by simpa using idx.isLt⟩
              rw [subst_getElem_of_map_eq hsubst] at harg
              simpa [List.getElem_map] using harg
          simpa [Pr.interp, Term.subst] using hopType
        · intro proveSubgoals
          have hself := proveSubgoals (.hasType varCtx (.op name args) ty)
            (by simp [unifyTypeHasTypeGoals, hinf, hok])
          cases hself with
          | ofProof proof => exact proof
| .mkStruct tys, ty => by
    classical
    by_cases hty : (.func tys (.struct tys)) = Ty.subst ctxTy ty
    · intro _
      have hmk : Term.hasType ctx (varCtx.map (Ty.subst ctxTy))
          (.mkStruct tys) (Ty.subst ctxTy ty) := by
        rw [← hty]
        exact Term.hasType.mkStruct
      simpa [Pr.interp, Term.subst] using hmk
    · intro proveSubgoals
      have hself := proveSubgoals (.hasType varCtx (.mkStruct tys) ty)
        (by simp [unifyTypeHasTypeGoals, hty])
      cases hself with
      | ofProof proof => exact proof
| .structProj tys idx, ty => by
    classical
    by_cases hty : (.func [.struct tys] tys[idx]) = Ty.subst ctxTy ty
    · intro _
      have hproj : Term.hasType ctx (varCtx.map (Ty.subst ctxTy))
          (.structProj tys idx) (Ty.subst ctxTy ty) := by
        rw [← hty]
        exact Term.hasType.structProj idx
      simpa [Pr.interp, Term.subst] using hproj
    · intro proveSubgoals
      have hself := proveSubgoals (.hasType varCtx (.structProj tys idx) ty)
        (by
          simp [unifyTypeHasTypeGoals]
          exact hty)
      cases hself with
      | ofProof proof => exact proof
| .recurse resultTy init body, ty => by
    classical
    cases ctxTerm with
    | nil =>
      cases hstateHint : inferType? ctx varCtx init with
      | none =>
          intro proveSubgoals
          have hself := proveSubgoals (.hasType varCtx (.recurse resultTy init body) ty)
            (by simp [unifyTypeHasTypeGoals, hstateHint])
          cases hself with
          | ofProof proof => exact proof
      | some stateTy =>
          by_cases hcheck : Ty.subst ctxTy stateTy = stateTy ∧
              Ty.subst ctxTy resultTy = resultTy ∧ resultTy = Ty.subst ctxTy ty
          · intro proveSubgoals
            have hstateFixed := hcheck.left
            have hresultFixed := hcheck.right.left
            have htarget := hcheck.right.right
            have proveInit : ∀ subgoal,
                subgoal ∈ unifyTypeHasTypeGoals (ctx := ctx) ctxTy [] varCtx init stateTy →
                Pr.Provable ctx ctxTy [] subgoal := by
              intro subgoal hsubgoal
              exact proveSubgoals subgoal (by
                unfold unifyTypeHasTypeGoals
                simp only [hstateHint]
                rw [if_pos hcheck]
                exact List.mem_append_left _ hsubgoal)
            have proveBody : ∀ subgoal,
                subgoal ∈ unifyTypeHasTypeGoals (ctx := ctx) ctxTy []
                  (varCtx ++ [stateTy, .func [stateTy] resultTy]) body resultTy →
                Pr.Provable ctx ctxTy [] subgoal := by
              intro subgoal hsubgoal
              exact proveSubgoals subgoal (by
                unfold unifyTypeHasTypeGoals
                simp only [hstateHint]
                rw [if_pos hcheck]
                exact List.mem_append_right _ hsubgoal)
            have hinitInterp := unifyTypeHasType_sound init stateTy proveInit
            have hbodyInterp :=
              unifyTypeHasType_sound (varCtx := varCtx ++ [stateTy, .func [stateTy] resultTy])
                body resultTy proveBody
            have hinit : Term.hasType ctx (varCtx.map (Ty.subst ctxTy))
                (Term.subst [] init) stateTy := by
              simpa [Pr.interp, hstateFixed] using hinitInterp
            have hbody : Term.hasType ctx
                (varCtx.map (Ty.subst ctxTy) ++ [stateTy, .func [stateTy] resultTy])
                (Term.subst [] body) resultTy := by
              simpa [Pr.interp, Ty.subst, List.map_append, hstateFixed, hresultFixed]
                using hbodyInterp
            have hbodyRaw : Term.hasType ctx
                (varCtx.map (Ty.subst ctxTy) ++ [stateTy, .func [stateTy] resultTy])
                body resultTy := by
              simpa [Term.subst] using hbody
            have hrec : Term.hasType ctx (varCtx.map (Ty.subst ctxTy))
                (.recurse resultTy (Term.subst [] init) body)
                (Ty.subst ctxTy ty) := by
              rw [← htarget]
              exact Term.hasType.recurse hinit hbodyRaw
            simpa [Pr.interp, Term.subst] using hrec
          · intro proveSubgoals
            have hself := proveSubgoals (.hasType varCtx (.recurse resultTy init body) ty)
              (by simp [unifyTypeHasTypeGoals, hstateHint, hcheck])
            cases hself with
            | ofProof proof => exact proof
    | cons head tail =>
        intro proveSubgoals
        have hself := proveSubgoals (.hasType varCtx (.recurse resultTy init body) ty)
          (by simp [unifyTypeHasTypeGoals])
        cases hself with
        | ofProof proof => exact proof

private theorem unifyTypeArg_sound {ctx : Ctx} [Peano.Model ctx]
    {ctxTy : List Ty} {ctxTerm : List (Term ctx.primCtx)} {varCtx : List Ty} :
    ∀ (args : List (Term ctx.primCtx)) (tys : List Ty)
      (hlen : args.length = tys.length),
      (∀ subgoal, subgoal ∈ unifyTypeArgGoals (ctx := ctx) ctxTy ctxTerm varCtx args tys →
        Pr.Provable ctx ctxTy ctxTerm subgoal) →
      ∀ idx : Fin args.length,
        Term.hasType ctx (varCtx.map (Ty.subst ctxTy))
          (Term.subst ctxTerm args[idx])
          (Ty.subst ctxTy tys[Fin.cast hlen idx])
| [], [], _hlen, _proveSubgoals, idx => nomatch idx
| arg :: args, ty :: tys, hlen, proveSubgoals, ⟨0, _⟩ => by
    have proveHead : ∀ subgoal,
        subgoal ∈ unifyTypeHasTypeGoals (ctx := ctx) ctxTy ctxTerm varCtx arg ty →
        Pr.Provable ctx ctxTy ctxTerm subgoal := by
      intro subgoal hsubgoal
      exact proveSubgoals subgoal (by simp [unifyTypeArgGoals, hsubgoal])
    have hhead := unifyTypeHasType_sound arg ty proveHead
    cases (Pr.Provable.ofProof hhead : Pr.Provable ctx ctxTy ctxTerm (.hasType varCtx arg ty)) with
    | ofProof proof =>
        simpa [Pr.interp, Term.subst, Ty.subst] using proof
| arg :: args, ty :: tys, hlen, proveSubgoals, ⟨val + 1, isLt⟩ => by
    have hlenTail : args.length = tys.length := by
      simpa using Nat.succ.inj hlen
    have proveTail : ∀ subgoal,
        subgoal ∈ unifyTypeArgGoals (ctx := ctx) ctxTy ctxTerm varCtx args tys →
        Pr.Provable ctx ctxTy ctxTerm subgoal := by
      intro subgoal hsubgoal
      exact proveSubgoals subgoal (by simp [unifyTypeArgGoals, hsubgoal])
    have htail := unifyTypeArg_sound args tys hlenTail proveTail
      ⟨val, by simp at isLt; omega⟩
    simpa [Term.subst, Ty.subst] using htail
| [], _ :: _, hlen, _, _ => by simp at hlen
| _ :: _, [], hlen, _, _ => by simp at hlen

end

private theorem unifyType_sound {ctx : Ctx} [Peano.Model ctx]
    {ctxTy : List Ty} {ctxTerm : List (Term ctx.primCtx)} {goal : Pr (Term ctx.primCtx)} :
    (∀ subgoal, subgoal ∈ unifyTypeGoals (ctx := ctx) ctxTy ctxTerm goal →
      Pr.Provable ctx ctxTy ctxTerm subgoal) →
      Pr.Provable ctx ctxTy ctxTerm goal := by
  cases goal with
  | eq varCtx ty lhs rhs =>
      intro proveSubgoals
      exact proveSubgoals (.eq varCtx ty lhs rhs) (by simp [unifyTypeGoals])
  | hasType varCtx term ty =>
      intro proveSubgoals
      exact Pr.Provable.ofProof (unifyTypeHasType_sound term ty proveSubgoals)
  | and p q =>
      intro proveSubgoals
      exact proveSubgoals (.and p q) (by simp [unifyTypeGoals])
  | or p q =>
      intro proveSubgoals
      exact proveSubgoals (.or p q) (by simp [unifyTypeGoals])
  | implies p q =>
      intro proveSubgoals
      exact proveSubgoals (.implies p q) (by simp [unifyTypeGoals])
  | forallTy p =>
      intro proveSubgoals
      exact proveSubgoals (.forallTy p) (by simp [unifyTypeGoals])
  | forallTerm p =>
      intro proveSubgoals
      exact proveSubgoals (.forallTerm p) (by simp [unifyTypeGoals])

def unifyType {ctx : Ctx} [Peano.Model ctx]
    {ctxTy : List Ty} {ctxTerm : List (Term ctx.primCtx)} (goal : Pr (Term ctx.primCtx)) :
    Refinement ctx ctxTy ctxTerm goal where
  goals := unifyTypeGoals (ctx := ctx) ctxTy ctxTerm goal
  prove := by
    intro proveSubgoals
    simp only [Language.Provable_term] at proveSubgoals ⊢
    exact unifyType_sound proveSubgoals

/-! ### Completeness

`Tactic.CompleteOn unifyType (hasType ·)`: every provable `hasType` goal is closed
outright. Invertibility on closed states follows. Requires empty type/term
substitutions and unique primfunc names. -/

mutual
private theorem Ty.subst_nil : (t : Ty) → Ty.subst [] t = t
| .var idx => by simp [Ty.subst]
| .prim n => by simp [Ty.subst]
| .option ty => by simp [Ty.subst, Ty.subst_nil ty]
| .union tys => by simp [Ty.subst, Ty.subst_nil_list tys]
| .struct tys => by simp [Ty.subst, Ty.subst_nil_list tys]
| .func args ret => by simp [Ty.subst, Ty.subst_nil_list args, Ty.subst_nil ret]
| .m ty => by simp [Ty.subst, Ty.subst_nil ty]
private theorem Ty.subst_nil_list : (ts : List Ty) → ts.map (Ty.subst []) = ts
| [] => rfl
| t :: ts => by simp [Ty.subst_nil t, Ty.subst_nil_list ts]
end

private theorem list_map_subst_nil (varCtx : List Ty) :
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
        PrimFuncCtx.get?, PrimFunc.ty, PrimFunc.outTy, OpCtx.get?, OpCtx.outTy?,
        Ty.subst, Lib.Peano.peanoCtx, Lib.Peano.natOpCtx, Lib.Peano.natFuncCtx,
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

/-- With empty `ctxTy`, syntactic inference recovers the unique `hasType` type. -/
/- Totality of inference on well-typed terms: every `Term.hasType` derivation is recovered
  exactly by `inferType?`. Together with `inferType?_eq_of_hasType_nil` (the converse) this
  says inference decides typing, which is what makes `unifyType` complete.

  This holds for *every* operator, with no per-operator knowledge: the `op` case just
  reassembles the operand types and appeals to `ctx.opCtx.outTy?`, the same function
  `Term.hasType.op` is stated against. -/
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
      rw [inferTypes?_of_getElem hargs₁ (fun i ha ht => ih ⟨i, ha⟩)]
      exact hout
  | app hf hargs₁ hargs₂ ihf iha =>
      rename_i varCtx' f fTy args argsTy
      simp only [inferType?, ihf]
  | mkStruct => simp [inferType?]
  | structProj idx => simp [inferType?]
  | «recurse» hinit hbody ihinit ihbody => simp [inferType?]

private theorem inferType?_eq_of_hasType_nil {ctx : Ctx} [Peano.Model ctx] {varCtx : List Ty}
    {term : Term ctx.primCtx} {inferred ty : Ty}
    (hnames : (ctx.primFuncCtx.map Prod.fst).Nodup)
    (hinf : inferType? ctx varCtx term = some inferred)
    (hty : Term.hasType ctx varCtx term ty) :
    ty = inferred := by
  induction hty generalizing inferred with
  | prim val =>
      simp [inferType?] at hinf; cases hinf; rfl
  | primFunc =>
      rename_i varCtx' idx
      simp only [inferType?] at hinf
      have hget := primFuncCtx_get?_of_idx (ctx := ctx) hnames idx
      simp only [hget, Option.map_some, PrimFunc.ty] at hinf
      cases hinf
      rfl
  | var h =>
      rename_i varCtx' idx _
      simp only [inferType?] at hinf
      have hidx : idx.val < varCtx'.length := idx.isLt
      simp only [List.getElem?_eq_getElem hidx] at hinf
      cases hinf; exact h.symm
  | «op» hargs₁ hargs₂ hout ih =>
      rename_i varCtx' name args tys r
      simp only [inferType?] at hinf
      cases hinfArgs : inferTypes? ctx varCtx' args with
      | none => simp only [hinfArgs] at hinf; exact absurd hinf (by simp)
      | some tys' =>
          simp only [hinfArgs] at hinf
          -- each operand's inferred type agrees with its declared type, so `tys' = tys`
          have hlen' : args.length = tys'.length := inferTypes?_length hinfArgs
          have htys : tys' = tys := by
            refine List.ext_getElem (by omega) ?_
            intro i h1 h2
            have hi : i < args.length := by omega
            exact (ih ⟨i, hi⟩ (inferTypes?_getElem hinfArgs i hi h1)).symm
          rw [htys, hout] at hinf
          cases hinf
          rfl
  | app hf hargs₁ hargs₂ ihf iha =>
      rename_i varCtx' f fTy args argsTy
      simp only [inferType?] at hinf
      cases hfInf : inferType? ctx varCtx' f with
      | none =>
          simp only [hfInf] at hinf
          cases hinf
      | some fInf =>
          cases fInf with
          | func argsInf outInf =>
              have hmatch : inferType? ctx varCtx' (.app f args) = some outInf := by
                simp only [inferType?, hfInf]
              -- hinf : infer = some inferred, hmatch : infer = some outInf
              have : inferred = outInf := by
                have := hinf.symm.trans hmatch
                exact Option.some.inj this
              subst this
              have hfEq := ihf hfInf
              injection hfEq
          | _ =>
              simp only [hfInf] at hinf
              cases hinf
  | mkStruct =>
      simp only [inferType?] at hinf; cases hinf; rfl
  | structProj =>
      simp only [inferType?] at hinf; cases hinf; rfl
  | «recurse» hi hb ihi ihb =>
      simp only [inferType?] at hinf; cases hinf; rfl

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
private theorem unifyTypeHasTypeGoals_eq_nil_of_hasType {ctx : Ctx} [Peano.Model ctx]
    {varCtx : List Ty} {term : Term ctx.primCtx} {ty : Ty}
    (hnames : (ctx.primFuncCtx.map Prod.fst).Nodup)
    (hty : Term.hasType ctx varCtx term ty) :
    unifyTypeHasTypeGoals (ctx := ctx) [] [] varCtx term ty = [] := by
  induction hty with
  | prim val =>
      simp only [unifyTypeHasTypeGoals, Ty.subst_nil, ↓reduceIte]
  | primFunc =>
      rename_i varCtx' idx
      unfold unifyTypeHasTypeGoals
      cases hmatch : primFuncMatch? ctx.primFuncCtx ctx.primFuncCtx[idx].1
          (Ty.subst [] ctx.primFuncCtx[idx].2.ty) with
      | some _ => rfl
      | none =>
          have htyEq : ctx.primFuncCtx[idx].2.ty = Ty.subst [] ctx.primFuncCtx[idx].2.ty :=
            (Ty.subst_nil _).symm
          exact absurd ⟨rfl, htyEq⟩
            (primFuncMatch?_eq_none ctx.primFuncCtx _ _ hmatch idx)
  | var h =>
      rename_i varCtx' idx ty'
      have hget : varCtx'[idx.val] = ty' := by
        simpa [List.get_eq_getElem] using h
      unfold unifyTypeHasTypeGoals
      cases hvar : varMatch? ([] : List Ty) varCtx' idx.val ty' with
      | some _ => rfl
      | none =>
          have hne := varMatch?_eq_none ([] : List Ty) varCtx' idx.val ty' hvar idx.isLt
          exact absurd (by simp [Ty.subst_nil, hget]) hne
  | «op» hargs₁ hargs₂ hout ih =>
      rename_i varCtx' name args tys r
      have hinf : inferTypes? ctx varCtx' args = some tys :=
        inferTypes?_of_getElem hargs₁ fun i ha _ht =>
          inferType?_of_hasType hnames (hargs₂ ⟨i, ha⟩)
      have hsubst : tys.map (Ty.subst ([] : List Ty)) = tys := Ty.subst_nil_list tys
      have hout' : ctx.opCtx.outTy? name tys = some (Ty.subst [] r) := by
        rw [Ty.subst_nil]; exact hout
      have hargsNil : unifyTypeArgGoals (ctx := ctx) [] [] varCtx' args tys = [] :=
        unifyTypeArgGoals_eq_nil_of_getElem (ctx := ctx) (ctxTy := [])
          (ctxTerm := []) (varCtx := varCtx') args tys hargs₁ fun i ha _ht =>
            ih ⟨i, ha⟩
      unfold unifyTypeHasTypeGoals
      simp only [hinf]
      have hok : tys.map (Ty.subst ([] : List Ty)) = tys ∧
          ctx.opCtx.outTy? name tys = some (Ty.subst [] r) := ⟨hsubst, hout'⟩
      rw [if_pos hok, hargsNil]
  | app hf hargs₁ hargs₂ ihf iha =>
      rename_i varCtx' f fTy args argsTy
      have hinfF : inferType? ctx varCtx' f = some (.func argsTy fTy) :=
        inferType?_of_hasType hnames hf
      have hfun : inferFuncArgs? ctx varCtx' f = some argsTy := by
        simp only [inferFuncArgs?, hinfF]
      have hargsNil : unifyTypeArgGoals (ctx := ctx) [] [] varCtx' args argsTy = [] :=
        unifyTypeArgGoals_eq_nil_of_getElem (ctx := ctx) (ctxTy := [])
          (ctxTerm := []) (varCtx := varCtx') args argsTy hargs₁ fun i ha _ht =>
            iha ⟨i, ha⟩
      unfold unifyTypeHasTypeGoals
      simp only [hfun]
      rw [if_pos hargs₁, ihf, hargsNil]
      simp only [List.nil_append]
  | mkStruct =>
      simp only [unifyTypeHasTypeGoals, Ty.subst_nil, ↓reduceIte]
  | structProj idx =>
      simp only [unifyTypeHasTypeGoals, Ty.subst_nil, ↓reduceIte]
  | «recurse» hinit hbody ihinit ihbody =>
      rename_i varCtx' stateTy resultTy init body
      have hstate : inferType? ctx varCtx' init = some stateTy :=
        inferType?_of_hasType hnames hinit
      have hcheck : Ty.subst ([] : List Ty) stateTy = stateTy ∧
          Ty.subst ([] : List Ty) resultTy = resultTy ∧
          resultTy = Ty.subst ([] : List Ty) resultTy :=
        ⟨Ty.subst_nil stateTy, Ty.subst_nil resultTy, (Ty.subst_nil resultTy).symm⟩
      unfold unifyTypeHasTypeGoals
      simp only [hstate]
      rw [if_pos hcheck, ihinit, ihbody]
      simp only [List.nil_append]

/-- Every provable `hasType` goal is closed outright by `unifyType`. -/
theorem unifyType_completeOn_hasType {ctx : Ctx} [Peano.Model ctx]
    (hnames : (ctx.primFuncCtx.map Prod.fst).Nodup) :
    Tactic.CompleteOn
      (ctx := ctx) (ctxTy := []) (ctxTerm := [])
      unifyType
      (fun goal => ∃ varCtx term ty, goal = .hasType varCtx term ty) := by
  intro goal hdomain hprov
  rcases hdomain with ⟨varCtx, term, ty, rfl⟩
  simp only [unifyType, unifyTypeGoals]
  simp only [Language.Provable_term] at hprov
  have hty : Term.hasType ctx varCtx term ty := by
    cases hprov with
    | ofProof p =>
        simpa [Pr.interp, Term.subst, Ty.subst_nil, list_map_subst_nil] using p
  exact unifyTypeHasTypeGoals_eq_nil_of_hasType hnames hty

/-- Invertibility of `unifyType` for closed proof states follows from completeness on
  `hasType` goals and the identity behaviour on every other connective. -/
theorem unifyType_invertible {ctx : Ctx} [Peano.Model ctx] {goal : Pr (Term ctx.primCtx)}
    (hnames : (ctx.primFuncCtx.map Prod.fst).Nodup) :
    Refinement.invertible (unifyType (ctx := ctx) (ctxTy := []) (ctxTerm := []) goal) := by
  intro hgoal subgoal hsubgoal
  simp only [Language.Provable_term] at hgoal ⊢
  cases goal with
  | hasType varCtx term ty =>
      have hnil := unifyType_completeOn_hasType (ctx := ctx) hnames
        (.hasType varCtx term ty) ⟨varCtx, term, ty, rfl⟩ (by
          simpa only [Language.Provable_term] using hgoal)
      simp [unifyType, unifyTypeGoals] at hsubgoal hnil
      simp [hnil] at hsubgoal
  | eq varCtx ty lhs rhs =>
      simp [unifyType, unifyTypeGoals] at hsubgoal; subst hsubgoal; exact hgoal
  | and p q =>
      simp [unifyType, unifyTypeGoals] at hsubgoal; subst hsubgoal; exact hgoal
  | or p q =>
      simp [unifyType, unifyTypeGoals] at hsubgoal; subst hsubgoal; exact hgoal
  | implies p q =>
      simp [unifyType, unifyTypeGoals] at hsubgoal; subst hsubgoal; exact hgoal
  | forallTy p =>
      simp [unifyType, unifyTypeGoals] at hsubgoal; subst hsubgoal; exact hgoal
  | forallTerm p =>
      simp [unifyType, unifyTypeGoals] at hsubgoal; subst hsubgoal; exact hgoal

end TypeUnification

end Pr

end Zag
