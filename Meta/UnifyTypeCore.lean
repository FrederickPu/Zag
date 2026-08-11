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
| .«abbrev» _ args => args.flatMap primitiveNames

end Ty

namespace Term

def primitiveNames {primCtx : PrimitiveCtx} : Term primCtx → List String
| .prim ty _ => ty.primitiveNames
| .primFunc _ => []
| .var _ => []
| .app f args => f.primitiveNames ++ args.flatMap primitiveNames
| .op _ args => args.flatMap primitiveNames
| .«abbrev» _ typeArgs args =>
    typeArgs.flatMap Ty.primitiveNames ++ args.flatMap primitiveNames
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

private def termAbbrevPrimitiveNames (ctx : Ctx) : List String :=
  ctx.termAbbrevCtx.val.flatMap fun entry =>
    entry.2.varCtx.flatMap Ty.primitiveNames ++ entry.2.outTy.primitiveNames ++
      entry.2.body.primitiveNames

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
  primitiveNames : primitiveTypesDeclared ctx.primCtx
    (statePrimitiveNames ctxTy ctxTerm goal ++ termAbbrevPrimitiveNames ctx)

def primFuncMatch? {primCtx : PrimitiveCtx} :
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

/- Type inference, mirroring `Term.hasType` rule for rule.

  No operator is special-cased: an operator's result type comes from `ctx.opCtx.outTy?`
  applied to the inferred operand types, exactly as `Term.hasType.op` requires. Zag is
  operator-agnostic, so the tactic must be too -- previously only `ite` was handled here
  and every other operator (`eq`, `lt`, `gt`, `pure`, `bind`, ...) was inferred as `none`,
  which is what made `unifyType` incomplete. -/
mutual

def inferType? (ctx : Ctx) (varCtx : List Ty) : Term ctx.primCtx → Option Ty
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
| .«abbrev» name typeArgs args =>
    match ctx.termAbbrevCtx.get? name, inferTypes? ctx varCtx args with
    | some definition, some inferredTys =>
        let expectedTys := definition.varCtx.map fun ty =>
          (Ty.subst typeArgs ty).normalizeAbbrev ctx.tyAbbrevCtx
        /- These are actual arguments in a public typing judgment, not type variables
          occurring inside a declaration body. -/
        if typeArgs.length = definition.typeArity ∧
            Ty.validListIn ctx.tyAbbrevCtx.val 0 typeArgs = true ∧
            args.length = definition.varCtx.length ∧ inferredTys = expectedTys then
          some ((Ty.subst typeArgs definition.outTy).normalizeAbbrev ctx.tyAbbrevCtx)
        else none
    | _, _ => none
| .mkStruct tys => some (.func tys (.struct tys))
| .structProj tys idx => some (.func [.struct tys] tys[idx])
| .recurse resultTy _ _ => some resultTy

def inferTypes? (ctx : Ctx) (varCtx : List Ty) :
    List (Term ctx.primCtx) → Option (List Ty)
| [] => some []
| arg :: args =>
    match inferType? ctx varCtx arg, inferTypes? ctx varCtx args with
    | some ty, some tys => some (ty :: tys)
    | _, _ => none

end

mutual
@[simp] theorem Ty.substNil : (ty : Ty) → Ty.subst [] ty = ty
| .var idx | .prim idx => by simp [Ty.subst]
| .option ty | .m ty => by simp [Ty.subst, Ty.substNil ty]
| .union tys | .struct tys => by simp [Ty.subst, Ty.substNilList tys]
| .func args out => by simp [Ty.subst, Ty.substNilList args, Ty.substNil out]
| .«abbrev» name args => by simp [Ty.subst, Ty.substNilList args]

@[simp] theorem Ty.substNilList : (tys : List Ty) → tys.map (Ty.subst []) = tys
| [] => rfl
| ty :: tys => by simp [Ty.substNil ty, Ty.substNilList tys]
end

def inferFuncArgs? (ctx : Ctx) (varCtx : List Ty) (term : Term ctx.primCtx) :
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
theorem inferTypes?_of_getElem {ctx : Ctx} {varCtx : List Ty} :
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

def varMatch? (ctxTy : List Ty) :
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
def unifyTypeHasTypeGoals {ctx : Ctx}
    (ctxTy : List Ty) (ctxTerm : List (Term ctx.primCtx))
    (varCtx : List Ty) (term : Term ctx.primCtx) (ty : Ty) : List (Pr (Term ctx.primCtx)) :=
    match term with
    | .prim actualTy _ =>
        if actualTy = Ty.subst ctxTy ty then []
        else [.hasType varCtx term ty]
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
        | some sourceTys =>
            /- the `tys.map (Ty.subst ctxTy) = tys` guard mirrors `.recurse` below: operand
              types are inferred before substitution, so we only proceed when substitution
              acts as the identity on them (always true for the closed states `ctxTy = []`
              that completeness is stated for). -/
            if sourceTys.map (Ty.subst ctxTy) = sourceTys ∧
                ctx.opCtx.outTy? name sourceTys = some (Ty.subst ctxTy ty) then
              unifyTypeArgGoals ctxTy ctxTerm varCtx args sourceTys
            else [.hasType varCtx term ty]
        | none => [.hasType varCtx term ty]

    | .«abbrev» name typeArgs args =>
        match ctxTy with
        | _ :: _ => [.hasType varCtx term ty]
        | [] =>
            match ctx.termAbbrevCtx.get? name with
            | some definition =>
                let expectedTys := definition.varCtx.map fun sourceTy =>
                  (Ty.subst typeArgs sourceTy).normalizeAbbrev ctx.tyAbbrevCtx
                let outputTy :=
                  (Ty.subst typeArgs definition.outTy).normalizeAbbrev ctx.tyAbbrevCtx
                match inferTypes? ctx varCtx args with
                | some inferredTys =>
                    if typeArgs.length = definition.typeArity ∧
                        Ty.validListIn ctx.tyAbbrevCtx.val 0 typeArgs = true ∧
                        args.length = definition.varCtx.length ∧
                        inferredTys = expectedTys ∧
                        outputTy = ty then
                      unifyTypeArgGoals [] ctxTerm varCtx args inferredTys
                    else [.hasType varCtx term ty]
                | none => [.hasType varCtx term ty]
            | none => [.hasType varCtx term ty]

    | .mkStruct tys =>
        if (.func tys (.struct tys)) = Ty.subst ctxTy ty
        then [] else [.hasType varCtx term ty]
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
def unifyTypeArgGoals {ctx : Ctx}
    (ctxTy : List Ty) (ctxTerm : List (Term ctx.primCtx)) (varCtx : List Ty) :
    List (Term ctx.primCtx) → List Ty → List (Pr (Term ctx.primCtx))
| arg :: args, argTy :: tys =>
    unifyTypeHasTypeGoals ctxTy ctxTerm varCtx arg argTy ++
      unifyTypeArgGoals ctxTy ctxTerm varCtx args tys
| _, _ => []

end

def unifyTypeGoals {ctx : Ctx}
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
    | some sourceTys =>
        by_cases hok : sourceTys.map (Ty.subst ctxTy) = sourceTys ∧
            ctx.opCtx.outTy? name sourceTys = some (Ty.subst ctxTy ty)
        · obtain ⟨hsubst, hout⟩ := hok
          have hlen : args.length = sourceTys.length := inferTypes?_length hinf
          intro proveSubgoals
          have proveArgs : ∀ subgoal,
              subgoal ∈ unifyTypeArgGoals (ctx := ctx) ctxTy ctxTerm varCtx args sourceTys →
              Pr.Provable ctx ctxTy ctxTerm subgoal := by
            intro subgoal hsubgoal
            exact proveSubgoals subgoal (by
              simp [unifyTypeHasTypeGoals, hinf, hsubst, hout, hsubgoal])
          have hargs := unifyTypeArg_sound args sourceTys hlen proveArgs
          have hopType : Term.hasType ctx (varCtx.map (Ty.subst ctxTy))
               (.op name (args.map (Term.subst ctxTerm))) (Ty.subst ctxTy ty) := by
            refine Term.hasType.op (tys := sourceTys) ?_ ?_ hout
            · simp [hlen]
            · intro idx
              have harg := hargs ⟨idx.val, by simpa using idx.isLt⟩
              rw [subst_getElem_of_map_eq hsubst] at harg
              simpa [List.getElem_map] using harg
          simpa [Pr.interp, Term.subst] using hopType
        · intro proveSubgoals
          have hself := proveSubgoals (.hasType varCtx (.op name args) ty)
            (by
              unfold unifyTypeHasTypeGoals
              simp only [hinf]
              rw [if_neg hok]
              simp)
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
| .«abbrev» name typeArgs args, ty => by
    classical
    cases ctxTy with
    | cons head tail =>
        intro proveSubgoals
        have hself := proveSubgoals (.hasType varCtx (.«abbrev» name typeArgs args) ty)
          (by simp [unifyTypeHasTypeGoals])
        cases hself with | ofProof proof => exact proof
    | nil =>
      cases hget : ctx.termAbbrevCtx.get? name with
      | none =>
          intro proveSubgoals
          have hself := proveSubgoals (.hasType varCtx (.«abbrev» name typeArgs args) ty)
            (by simp [unifyTypeHasTypeGoals, hget])
          cases hself with | ofProof proof => exact proof
      | some definition =>
        cases hinf : inferTypes? ctx varCtx args with
        | none =>
            intro proveSubgoals
            have hself := proveSubgoals (.hasType varCtx (.«abbrev» name typeArgs args) ty)
              (by simp [unifyTypeHasTypeGoals, hget, hinf])
            cases hself with | ofProof proof => exact proof
        | some inferredTys =>
            let expectedTys := definition.varCtx.map fun sourceTy =>
              (Ty.subst typeArgs sourceTy).normalizeAbbrev ctx.tyAbbrevCtx
            let outputTy :=
              (Ty.subst typeArgs definition.outTy).normalizeAbbrev ctx.tyAbbrevCtx
            by_cases hcheck : typeArgs.length = definition.typeArity ∧
                Ty.validListIn ctx.tyAbbrevCtx.val 0 typeArgs = true ∧
                args.length = definition.varCtx.length ∧ inferredTys = expectedTys ∧
                outputTy = ty
            · intro proveSubgoals
              have hlen : args.length = inferredTys.length := inferTypes?_length hinf
              have hargs := unifyTypeArg_sound (varCtx := varCtx) args inferredTys hlen (by
                intro subgoal hsubgoal
                exact proveSubgoals subgoal (by
                  unfold unifyTypeHasTypeGoals
                  simp only [hget, hinf]
                  rw [if_pos (by
                    simpa [expectedTys, outputTy, Function.comp_def] using hcheck)]
                  exact hsubgoal))
              have habbrev : Term.hasType ctx varCtx
                  (.«abbrev» name typeArgs (args.map (Term.subst ctxTerm)))
                  outputTy := by
                obtain ⟨prior, hprefix⟩ :=
                  TermAbbrevCtx.Raw.exists_getWithPrefix?_of_get? hget
                refine Term.hasType.«abbrev» (by
                  simpa [CheckedTermAbbrevCtx.getWithPrefix?] using hprefix)
                  hcheck.1 hcheck.2.1 (by simpa using hcheck.2.2.1) ?_
                intro idx
                let argIdx : Fin args.length := ⟨idx.val, by simpa using idx.isLt⟩
                let expectedIdx : Fin expectedTys.length := ⟨idx.val, by
                  have ha : idx.val < args.length := by simpa using idx.isLt
                  have hv : idx.val < definition.varCtx.length := by omega
                  simpa [expectedTys] using hv⟩
                have harg := hargs argIdx
                have hty : inferredTys[Fin.cast hlen argIdx] =
                    expectedTys[expectedIdx] := by
                  have := congrArg (fun tys => tys[idx.val]?) hcheck.2.2.2.1
                  have hi : idx.val < inferredTys.length := by
                    simpa [argIdx] using (Fin.cast hlen argIdx).isLt
                  have he : idx.val < expectedTys.length := expectedIdx.isLt
                  rw [List.getElem?_eq_getElem hi, List.getElem?_eq_getElem he] at this
                  simpa [argIdx, expectedIdx] using Option.some.inj this
                rw [hty] at harg
                simpa [argIdx, expectedIdx, expectedTys, List.getElem_map] using harg
              rw [hcheck.2.2.2.2] at habbrev
              simpa [Pr.interp, Term.subst] using habbrev
            · intro proveSubgoals
              have hself := proveSubgoals (.hasType varCtx (.«abbrev» name typeArgs args) ty)
                (by
                  unfold unifyTypeHasTypeGoals
                  simp only [hget, hinf]
                  rw [if_neg (by
                    simpa [expectedTys, outputTy, Function.comp_def] using hcheck)]
                  simp)
              cases hself with | ofProof proof => exact proof

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


end TypeUnification

end Pr

end Zag
