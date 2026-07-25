import Zag.Meta

namespace Zag

namespace Ty

def primitiveNames : Ty → List String
| .var _ => []
| .prim name => [name]
| .option ty => ty.primitiveNames
| .union tys => tys.flatMap primitiveNames
| .struct tys => tys.flatMap primitiveNames
| .func args result => args.flatMap primitiveNames ++ result.primitiveNames

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
| .ite cond thenTerm elseTerm =>
    cond.primitiveNames ++ thenTerm.primitiveNames ++ elseTerm.primitiveNames
| .recurse resultTy init body =>
    resultTy.primitiveNames ++ init.primitiveNames ++ body.primitiveNames

end Term

namespace Pr

def primitiveNames {primCtx : PrimitiveCtx} : Pr primCtx → List String
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

namespace MetaProgram

def primitiveTypesDeclared (primCtx : PrimitiveCtx) (names : List String) : Prop :=
  ∀ name, name ∈ names → name ∈ primCtx.map Prod.fst

def statePrimitiveNames {primCtx : PrimitiveCtx}
    (ctxTy : List Ty) (ctxTerm : List (Term primCtx)) (goal : Pr primCtx) : List String :=
  ctxTy.flatMap Ty.primitiveNames ++ ctxTerm.flatMap Term.primitiveNames ++ goal.primitiveNames

/- Faithful context assumptions for completeness of reflected type unification.

   `primFuncNames` is the simple sufficient condition for function lookup: if names
   are unique, `PrimFuncCtx.get?`/`primFuncMatch?` cannot infer a different function
   type from the one used by a `Term.hasType.primFunc` derivation.

   `primitiveNames` requires every primitive type mentioned by the current proof
   state to be declared in `PrimitiveCtx`; this deliberately does not rely on the
   reserved `Nat`/`Bool` fallback in `PrimitiveCtx.get?`. -/
structure UnifyTypePrecondition (ctx : Ctx)
    (ctxTy : List Ty) (ctxTerm : List (Term ctx.primCtx)) (goal : Pr ctx.primCtx) : Prop where
  primitiveCtxNames : (ctx.primCtx.map Prod.fst).Nodup
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

private def inferType? {primCtx : PrimitiveCtx} (primFuncCtx : PrimFuncCtx primCtx)
    (varCtx : List Ty) : Term primCtx → Option Ty
| .prim ty _ => some ty
| .primFunc name => (PrimFuncCtx.get? primFuncCtx name).map PrimFunc.ty
| .var idx => varCtx[idx]?
| .app f _ =>
    match inferType? primFuncCtx varCtx f with
    | some (.func _ outTy) => some outTy
    | _ => none
| .op _ _ => none
| .mkStruct tys => some (.func tys (.struct tys))
| .structProj tys idx => some (.func [.struct tys] tys[idx])
| .ite _ thenTerm _ => inferType? primFuncCtx varCtx thenTerm
| .recurse resultTy _ _ => some resultTy

private def inferFuncArgs? {primCtx : PrimitiveCtx} (primFuncCtx : PrimFuncCtx primCtx)
    (varCtx : List Ty) (term : Term primCtx) : Option (List Ty) :=
  match inferType? primFuncCtx varCtx term with
  | some (.func argsTy _) => some argsTy
  | _ => none

private def inferPrimName? {primCtx : PrimitiveCtx} (primFuncCtx : PrimFuncCtx primCtx)
    (varCtx : List Ty) (term : Term primCtx) : Option String :=
  match inferType? primFuncCtx varCtx term with
  | some (.prim name) => some name
  | _ => none

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

private def argGoals {primCtx : PrimitiveCtx} (varCtx : List Ty) :
    List (Term primCtx) → List Ty → List (Pr primCtx)
| arg :: args, ty :: tys => .hasType varCtx arg ty :: argGoals varCtx args tys
| _, _ => []

private def unifyTypeHasTypeGoals {ctx : Ctx}
    (ctxTy : List Ty) (ctxTerm : List (Term ctx.primCtx))
    (varCtx : List Ty) (term : Term ctx.primCtx) (ty : Ty) : List (Pr ctx.primCtx) :=
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
            match inferFuncArgs? ctx.primFuncCtx varCtx f with
            | some argsTy =>
                if args.length = argsTy.length then
                  .hasType varCtx f (.func argsTy ty) :: argGoals varCtx args argsTy
                else [.hasType varCtx term ty]
            | none => [.hasType varCtx term ty]
    | .op _ _ =>
        [.hasType varCtx term ty]

    | .mkStruct tys =>
        if (.func tys (.struct tys)) = Ty.subst ctxTy ty then [] else [.hasType varCtx term ty]
    | .structProj tys idx =>
        if (.func [.struct tys] tys[idx]) = Ty.subst ctxTy ty then []
        else [.hasType varCtx term ty]
    | .ite cond thenTerm elseTerm =>
        [.hasType varCtx cond (.prim "Bool"), .hasType varCtx thenTerm ty,
          .hasType varCtx elseTerm ty]
    | .recurse resultTy init body =>
        match ctxTerm with
        | [] =>
            match inferType? ctx.primFuncCtx varCtx init with
            | some stateTy =>
                if Ty.subst ctxTy stateTy = stateTy ∧
                    Ty.subst ctxTy resultTy = resultTy ∧
                    resultTy = Ty.subst ctxTy ty then
                  [ .hasType varCtx init stateTy
                  , .hasType (varCtx ++ [stateTy, .func [stateTy] resultTy]) body resultTy
                  ]
                else [.hasType varCtx term ty]
            | none => [.hasType varCtx term ty]
        | _ :: _ => [.hasType varCtx term ty]

private def unifyTypeGoals {ctx : Ctx}
    (ctxTy : List Ty) (ctxTerm : List (Term ctx.primCtx)) :
    Pr ctx.primCtx → List (Pr ctx.primCtx)
| .hasType varCtx term ty => unifyTypeHasTypeGoals ctxTy ctxTerm varCtx term ty
| goal => [goal]

private theorem argGoals_sound {ctx : Ctx}
    {ctxTy : List Ty} {ctxTerm : List (Term ctx.primCtx)} {varCtx : List Ty}
    {args : List (Term ctx.primCtx)} {tys : List Ty}
    (hlen : args.length = tys.length)
    (proveSubgoals : ∀ subgoal, subgoal ∈ argGoals varCtx args tys →
      Pr.Provable ctx ctxTy ctxTerm subgoal) :
    ∀ idx : Fin args.length,
      Term.hasType ctx (varCtx.map (Ty.subst ctxTy))
        (Term.subst ctxTerm args[idx])
        (Ty.subst ctxTy tys[Fin.cast hlen idx]) := by
  induction args generalizing tys with
  | nil =>
      intro idx
      cases idx with
      | mk val isLt => simp at isLt
  | cons arg args ih =>
      cases tys with
      | nil => simp at hlen
      | cons ty tys =>
          intro idx
          cases idx with
          | mk val isLt =>
              cases val with
              | zero =>
                  have harg : Pr.Provable ctx ctxTy ctxTerm (.hasType varCtx arg ty) :=
                    proveSubgoals (.hasType varCtx arg ty) (by simp [argGoals])
                  cases harg with
                  | ofProof proof => simpa [Pr.interp, Term.subst, Ty.subst] using proof
              | succ val =>
                  have hlenTail : args.length = tys.length := by
                    simpa using Nat.succ.inj hlen
                  have proveTail : ∀ subgoal, subgoal ∈ argGoals varCtx args tys →
                      Pr.Provable ctx ctxTy ctxTerm subgoal := by
                    intro subgoal hsubgoal
                    exact proveSubgoals subgoal (by simp [argGoals, hsubgoal])
                  have htail := ih hlenTail proveTail ⟨val, by simp at isLt; omega⟩
                  simpa [Term.subst, Ty.subst] using htail

private theorem unifyTypeHasType_sound {ctx : Ctx} {ctxTy : List Ty}
    {ctxTerm : List (Term ctx.primCtx)} {varCtx : List Ty} {term : Term ctx.primCtx} {ty : Ty} :
    (∀ subgoal, subgoal ∈ unifyTypeHasTypeGoals (ctx := ctx) ctxTy ctxTerm varCtx term ty →
      Pr.Provable ctx ctxTy ctxTerm subgoal) →
      Pr.interp ctx ctxTy ctxTerm (.hasType varCtx term ty) := by
  classical
  cases term with
  | prim actualTy val =>
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
  | primFunc name =>
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
  | var idx =>
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
  | app f args =>
      cases ctxTerm with
      | cons head tail =>
          intro proveSubgoals
          have hself := proveSubgoals (.hasType varCtx (.app f args) ty)
            (by simp [unifyTypeHasTypeGoals])
          cases hself with
          | ofProof proof => exact proof
      | nil =>
          cases hfun : inferFuncArgs? ctx.primFuncCtx varCtx f with
          | none =>
              intro proveSubgoals
              have hself := proveSubgoals (.hasType varCtx (.app f args) ty)
                (by simp [unifyTypeHasTypeGoals, hfun])
              cases hself with
              | ofProof proof => exact proof
          | some argsTy =>
              by_cases hlen : args.length = argsTy.length
              · intro proveSubgoals
                have hfProv : Pr.Provable ctx ctxTy []
                    (.hasType varCtx f (.func argsTy ty)) :=
                  proveSubgoals (.hasType varCtx f (.func argsTy ty))
                    (by simp [unifyTypeHasTypeGoals, hfun, hlen])
                have proveArgs : ∀ subgoal, subgoal ∈ argGoals varCtx args argsTy →
                    Pr.Provable ctx ctxTy [] subgoal := by
                  intro subgoal hsubgoal
                  exact proveSubgoals subgoal
                    (by simp [unifyTypeHasTypeGoals, hfun, hlen, hsubgoal])
                cases hfProv with
                | ofProof hfProof =>
                    have hf : Term.hasType ctx (varCtx.map (Ty.subst ctxTy))
                        (Term.subst [] f)
                        (.func (argsTy.map (Ty.subst ctxTy)) (Ty.subst ctxTy ty)) := by
                      simpa [Pr.interp, Ty.subst] using hfProof
                    have hargs := argGoals_sound (ctx := ctx)
                      (ctxTy := ctxTy) (ctxTerm := []) (varCtx := varCtx)
                      (args := args) (tys := argsTy) hlen proveArgs
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
  | «op» name args =>
      intro proveSubgoals
      have hself := proveSubgoals (.hasType varCtx (.op name args) ty)
        (by simp [unifyTypeHasTypeGoals])
      cases hself with
      | ofProof proof => exact proof
  | mkStruct tys =>
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
  | structProj tys idx =>
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
  | ite cond thenTerm elseTerm =>
      intro proveSubgoals
      have hcondProv : Pr.Provable ctx ctxTy ctxTerm
          (.hasType varCtx cond (.prim "Bool")) :=
        proveSubgoals (.hasType varCtx cond (.prim "Bool"))
          (by simp [unifyTypeHasTypeGoals])
      have hthenProv : Pr.Provable ctx ctxTy ctxTerm
          (.hasType varCtx thenTerm ty) :=
        proveSubgoals (.hasType varCtx thenTerm ty)
          (by simp [unifyTypeHasTypeGoals])
      have helseProv : Pr.Provable ctx ctxTy ctxTerm
          (.hasType varCtx elseTerm ty) :=
        proveSubgoals (.hasType varCtx elseTerm ty)
          (by simp [unifyTypeHasTypeGoals])
      cases hcondProv with
      | ofProof hcondProof =>
          cases hthenProv with
          | ofProof hthenProof =>
              cases helseProv with
              | ofProof helseProof =>
                  have hcond : Term.hasType ctx (varCtx.map (Ty.subst ctxTy))
                      (Term.subst ctxTerm cond) (.prim "Bool") := by
                    simpa [Pr.interp, Ty.subst] using hcondProof
                  have hthen : Term.hasType ctx (varCtx.map (Ty.subst ctxTy))
                      (Term.subst ctxTerm thenTerm) (Ty.subst ctxTy ty) := by
                    simpa [Pr.interp] using hthenProof
                  have helse : Term.hasType ctx (varCtx.map (Ty.subst ctxTy))
                      (Term.subst ctxTerm elseTerm) (Ty.subst ctxTy ty) := by
                    simpa [Pr.interp] using helseProof
                  have hite : Term.hasType ctx (varCtx.map (Ty.subst ctxTy))
                      (.ite (Term.subst ctxTerm cond) (Term.subst ctxTerm thenTerm)
                        (Term.subst ctxTerm elseTerm)) (Ty.subst ctxTy ty) :=
                    Term.hasType.ite hcond hthen helse
                  simpa [Pr.interp, Term.subst] using hite
  | «recurse» resultTy init body =>
      cases ctxTerm with
      | nil =>
        cases hstateHint : inferType? ctx.primFuncCtx varCtx init with
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
              have hinitProv : Pr.Provable ctx ctxTy []
                  (.hasType varCtx init stateTy) :=
                proveSubgoals (.hasType varCtx init stateTy)
                  (by
                    unfold unifyTypeHasTypeGoals
                    simp [hstateHint]
                    rw [if_pos hcheck]
                    simp)
              have hbodyProv : Pr.Provable ctx ctxTy []
                  (.hasType (varCtx ++ [stateTy, .func [stateTy] resultTy]) body resultTy) :=
                proveSubgoals
                  (.hasType (varCtx ++ [stateTy, .func [stateTy] resultTy]) body resultTy)
                  (by
                    unfold unifyTypeHasTypeGoals
                    simp [hstateHint]
                    rw [if_pos hcheck]
                    simp)
              cases hinitProv with
              | ofProof hinitProof =>
                  cases hbodyProv with
                  | ofProof hbodyProof =>
                      have hinit : Term.hasType ctx (varCtx.map (Ty.subst ctxTy))
                          (Term.subst [] init) stateTy := by
                        simpa [Pr.interp, hstateFixed] using hinitProof
                      have hbody : Term.hasType ctx
                          (varCtx.map (Ty.subst ctxTy) ++ [stateTy, .func [stateTy] resultTy])
                          (Term.subst [] body) resultTy := by
                        simpa [Pr.interp, Ty.subst, List.map_append, hstateFixed, hresultFixed]
                          using hbodyProof
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

private theorem unifyType_sound {ctx : Ctx}
    {ctxTy : List Ty} {ctxTerm : List (Term ctx.primCtx)} {goal : Pr ctx.primCtx} :
    (∀ subgoal, subgoal ∈ unifyTypeGoals (ctx := ctx) ctxTy ctxTerm goal →
      Pr.Provable ctx ctxTy ctxTerm subgoal) →
      Pr.Provable ctx ctxTy ctxTerm goal := by
  cases goal with
  | eq varCtx ty lhs rhs =>
      intro proveSubgoals
      exact proveSubgoals (.eq varCtx ty lhs rhs) (by simp [unifyTypeGoals])
  | hasType varCtx term ty =>
      intro proveSubgoals
      exact Pr.Provable.ofProof (unifyTypeHasType_sound proveSubgoals)
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

def unifyType {ctx : Ctx}
    {ctxTy : List Ty} {ctxTerm : List (Term ctx.primCtx)} (goal : Pr ctx.primCtx) :
    MetaProgram ctx ctxTy ctxTerm goal where
  goals := unifyTypeGoals (ctx := ctx) ctxTy ctxTerm goal
  prove := by
    intro proveSubgoals
    exact unifyType_sound proveSubgoals


/-! ### Completeness

`MetaProgram.complete (unifyType goal)`: if the goal is provable, every generated
subgoal is provable.  Proved for empty type/term substitutions and unique primfunc names. -/

mutual
private theorem Ty.subst_nil : (t : Ty) → Ty.subst [] t = t
| .var idx => by simp [Ty.subst]
| .prim n => by simp [Ty.subst]
| .option ty => by simp [Ty.subst, Ty.subst_nil ty]
| .union tys => by simp [Ty.subst, Ty.subst_nil_list tys]
| .struct tys => by simp [Ty.subst, Ty.subst_nil_list tys]
| .func args ret => by simp [Ty.subst, Ty.subst_nil_list args, Ty.subst_nil ret]
private theorem Ty.subst_nil_list : (ts : List Ty) → ts.map (Ty.subst []) = ts
| [] => rfl
| t :: ts => by simp [Ty.subst_nil t, Ty.subst_nil_list ts]
end

private theorem list_map_subst_nil (varCtx : List Ty) :
    varCtx.map (Ty.subst []) = varCtx :=
  Ty.subst_nil_list varCtx

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
private theorem inferType?_eq_of_hasType_nil {ctx : Ctx} {varCtx : List Ty}
    {term : Term ctx.primCtx} {inferred ty : Ty}
    (hnames : (ctx.primFuncCtx.map Prod.fst).Nodup)
    (hinf : inferType? ctx.primFuncCtx varCtx term = some inferred)
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
      simp only [inferType?] at hinf
      cases hinf
  | app hf hargs₁ hargs₂ ihf iha =>
      rename_i varCtx' f fTy args argsTy
      simp only [inferType?] at hinf
      cases hfInf : inferType? ctx.primFuncCtx varCtx' f with
      | none =>
          simp only [hfInf] at hinf
          cases hinf
      | some fInf =>
          cases fInf with
          | func argsInf outInf =>
              have hmatch : inferType? ctx.primFuncCtx varCtx' (.app f args) = some outInf := by
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
  | ite hc ht he ihc iht ihe =>
      simp only [inferType?] at hinf
      exact iht hinf
  | «recurse» hi hb ihi ihb =>
      simp only [inferType?] at hinf; cases hinf; rfl

private theorem argGoals_complete_nil {ctx : Ctx} {varCtx : List Ty}
    {args : List (Term ctx.primCtx)} {tys : List Ty}
    (hlen : args.length = tys.length)
    (hargs : ∀ idx : Fin args.length,
      Term.hasType ctx varCtx args[idx] tys[Fin.cast hlen idx]) :
    ∀ subgoal, subgoal ∈ argGoals varCtx args tys →
      Pr.Provable ctx [] ([] : List (Term ctx.primCtx)) subgoal := by
  induction args generalizing tys with
  | nil =>
      intro subgoal hsubgoal
      cases tys <;> simp [argGoals] at hsubgoal
  | cons arg args ih =>
      cases tys with
      | nil => simp at hlen
      | cons ty tys =>
          intro subgoal hsubgoal
          simp [argGoals] at hsubgoal
          rcases hsubgoal with rfl | hsubgoal
          · exact Pr.Provable.ofProof (by
              simpa [Pr.interp, Term.subst, Ty.subst_nil, list_map_subst_nil]
                using hargs ⟨0, by simp⟩)
          · have hlenTail : args.length = tys.length := by
              simpa using Nat.succ.inj hlen
            exact ih hlenTail (fun idx => by
              simpa using hargs ⟨idx.val + 1, by simp [idx.isLt]⟩) subgoal hsubgoal

private theorem unifyTypeHasType_complete_nil {ctx : Ctx} {varCtx : List Ty}
    {term : Term ctx.primCtx} {ty : Ty}
    (hnames : (ctx.primFuncCtx.map Prod.fst).Nodup)
    (hgoal : Pr.Provable ctx [] [] (.hasType varCtx term ty)) :
    ∀ subgoal, subgoal ∈ unifyTypeHasTypeGoals (ctx := ctx) [] [] varCtx term ty →
      Pr.Provable ctx [] [] subgoal := by
  classical
  intro subgoal hsubgoal
  have proof' : Term.hasType ctx varCtx term ty := by
    cases hgoal with
    | ofProof p =>
        simpa [Pr.interp, Term.subst, Ty.subst_nil, list_map_subst_nil] using p
  cases term with
  | prim actualTy val =>
      by_cases hty : actualTy = Ty.subst [] ty
      · simp [unifyTypeHasTypeGoals, hty] at hsubgoal
      · simp [unifyTypeHasTypeGoals, hty] at hsubgoal; subst hsubgoal; exact hgoal
  | primFunc name =>
      cases hmatch : primFuncMatch? ctx.primFuncCtx name (Ty.subst [] ty) with
      | some _ => simp [unifyTypeHasTypeGoals, hmatch] at hsubgoal
      | none =>
          simp [unifyTypeHasTypeGoals, hmatch] at hsubgoal; subst hsubgoal; exact hgoal
  | var idx =>
      cases hvar : varMatch? [] varCtx idx ty with
      | some _ => simp [unifyTypeHasTypeGoals, hvar] at hsubgoal
      | none =>
          simp [unifyTypeHasTypeGoals, hvar] at hsubgoal; subst hsubgoal; exact hgoal
  | app f args =>
      cases hfun : inferFuncArgs? ctx.primFuncCtx varCtx f with
      | none =>
          simp [unifyTypeHasTypeGoals, hfun] at hsubgoal; subst hsubgoal; exact hgoal
      | some argsTy =>
          by_cases hlen : args.length = argsTy.length
          · simp [unifyTypeHasTypeGoals, hfun, hlen] at hsubgoal
            cases proof' with
            | app hf hargs₁ hargs₂ =>
                rename_i argsTy'
                have ⟨out, hinfF⟩ : ∃ out,
                    inferType? ctx.primFuncCtx varCtx f = some (.func argsTy out) := by
                  simp [inferFuncArgs?] at hfun
                  split at hfun
                  · next out heq => cases hfun; exact ⟨out, heq⟩
                  · cases hfun
                have hfEq := inferType?_eq_of_hasType_nil hnames hinfF hf
                injection hfEq with hargsEq hretEq
                rcases hsubgoal with rfl | hsg
                · have hf' : Term.hasType ctx varCtx f (.func argsTy ty) := by
                    rwa [hargsEq] at hf
                  exact Pr.Provable.ofProof (by
                    simpa [Pr.interp, Term.subst, Ty.subst_nil, list_map_subst_nil, Ty.subst]
                      using hf')
                · refine argGoals_complete_nil hlen ?_ subgoal hsg
                  intro idx
                  simpa [hargsEq, Fin.cast] using hargs₂ idx
          · simp [unifyTypeHasTypeGoals, hfun, hlen] at hsubgoal
            subst hsubgoal; exact hgoal
  | «op» name args =>
      simp [unifyTypeHasTypeGoals] at hsubgoal; subst hsubgoal; exact hgoal
  | mkStruct tys =>
      by_cases hty : (.func tys (.struct tys)) = Ty.subst [] ty
      · simp [unifyTypeHasTypeGoals, hty] at hsubgoal
      · simp [unifyTypeHasTypeGoals, hty] at hsubgoal; subst hsubgoal; exact hgoal
  | structProj tys idx =>
      by_cases hty : (.func [.struct tys] tys[idx]) = Ty.subst [] ty
      · have hty' : (.func [.struct tys] tys[idx.val]) = Ty.subst [] ty := hty
        simp [unifyTypeHasTypeGoals, hty'] at hsubgoal
      · have hty' : ¬((.func [.struct tys] tys[idx.val]) = Ty.subst [] ty) := hty
        simp [unifyTypeHasTypeGoals, hty'] at hsubgoal; subst hsubgoal; exact hgoal
  | ite cond thenTerm elseTerm =>
      simp [unifyTypeHasTypeGoals] at hsubgoal
      cases proof' with
      | ite hcond hthen helse =>
          rcases hsubgoal with rfl | rfl | rfl
          · exact Pr.Provable.ofProof (by
              simpa [Pr.interp, Term.subst, Ty.subst_nil, list_map_subst_nil] using hcond)
          · exact Pr.Provable.ofProof (by
              simpa [Pr.interp, Term.subst, Ty.subst_nil, list_map_subst_nil] using hthen)
          · exact Pr.Provable.ofProof (by
              simpa [Pr.interp, Term.subst, Ty.subst_nil, list_map_subst_nil] using helse)
  | «recurse» resultTy init body =>
      cases hstate : inferType? ctx.primFuncCtx varCtx init with
      | none =>
          simp [unifyTypeHasTypeGoals, hstate] at hsubgoal; subst hsubgoal; exact hgoal
      | some stateTy =>
          -- Ty.subst [] is id, so the check simplifies
          have hstateFixed := Ty.subst_nil stateTy
          have hresultFixed := Ty.subst_nil resultTy
          by_cases htarget : resultTy = ty
          · have hcheck : Ty.subst [] stateTy = stateTy ∧
                Ty.subst [] resultTy = resultTy ∧ resultTy = Ty.subst [] ty := by
              refine ⟨hstateFixed, hresultFixed, ?_⟩
              rwa [Ty.subst_nil]
            unfold unifyTypeHasTypeGoals at hsubgoal
            simp [hstate] at hsubgoal
            rw [if_pos hcheck] at hsubgoal
            simp at hsubgoal
            cases proof' with
            | «recurse» hinit hbody =>
                rename_i stateTy'
                have hstateEq := inferType?_eq_of_hasType_nil hnames hstate hinit
                rcases hsubgoal with rfl | rfl
                · exact Pr.Provable.ofProof (by
                    simp [Pr.interp, list_map_subst_nil, Ty.subst_nil]
                    rwa [hstateEq] at hinit)
                · -- term is recurse ty init body (resultTy unified with ty)
                  have hbody' : Term.hasType ctx
                      (varCtx ++ [stateTy, .func [stateTy] ty]) body ty := by
                    rwa [hstateEq] at hbody
                  exact Pr.Provable.ofProof (by
                    simpa [Pr.interp, Term.subst, Ty.subst_nil, list_map_subst_nil,
                      List.map_append, Ty.subst] using hbody')
          · have hcheck : ¬(Ty.subst [] stateTy = stateTy ∧
                Ty.subst [] resultTy = resultTy ∧ resultTy = Ty.subst [] ty) := by
              intro ⟨_, _, ht⟩
              exact htarget (by rwa [Ty.subst_nil] at ht)
            simp [unifyTypeHasTypeGoals, hstate, hcheck] at hsubgoal
            subst hsubgoal; exact hgoal

/-- Completeness of `unifyType` for closed proof states (empty type and term contexts). -/
theorem unifyType_complete {ctx : Ctx} {goal : Pr ctx.primCtx}
    (hnames : (ctx.primFuncCtx.map Prod.fst).Nodup) :
    complete (unifyType (ctx := ctx) (ctxTy := []) (ctxTerm := []) goal) := by
  intro hgoal subgoal hsubgoal
  cases goal with
  | hasType varCtx term ty =>
      simp [unifyType, unifyTypeGoals] at hsubgoal
      exact unifyTypeHasType_complete_nil hnames hgoal subgoal hsubgoal
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

end MetaProgram

end Pr

end Zag
