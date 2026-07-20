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
| .primEq lhs rhs => lhs.primitiveNames ++ rhs.primitiveNames
| .primLt lhs rhs => lhs.primitiveNames ++ rhs.primitiveNames
| .primGt lhs rhs => lhs.primitiveNames ++ rhs.primitiveNames
| .mkStruct tys => tys.flatMap Ty.primitiveNames
| .structProj tys _ => tys.flatMap Ty.primitiveNames
| .ite cond thenTerm elseTerm =>
    cond.primitiveNames ++ thenTerm.primitiveNames ++ elseTerm.primitiveNames
| .recurse resultTy init body =>
    resultTy.primitiveNames ++ init.primitiveNames ++ body.primitiveNames

end Term

namespace Pr

def primitiveNames {primCtx : PrimitiveCtx} : Pr primCtx → List String
| .eq ctx ty lhs rhs =>
    ctx.flatMap Ty.primitiveNames ++ ty.primitiveNames ++
      lhs.primitiveNames ++ rhs.primitiveNames
| .hasType ctx term ty =>
    ctx.flatMap Ty.primitiveNames ++ term.primitiveNames ++ ty.primitiveNames
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
structure UnifyTypePrecondition {primCtx : PrimitiveCtx} (primFuncCtx : PrimFuncCtx primCtx)
    (ctxTy : List Ty) (ctxTerm : List (Term primCtx)) (goal : Pr primCtx) : Prop where
  primitiveCtxNames : (primCtx.map Prod.fst).Nodup
  primFuncNames : (primFuncCtx.map Prod.fst).Nodup
  primitiveNames : primitiveTypesDeclared primCtx (statePrimitiveNames ctxTy ctxTerm goal)

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
    (ctx : List Ty) : Term primCtx → Option Ty
| .prim ty _ => some ty
| .primFunc name => (PrimFuncCtx.get? primFuncCtx name).map PrimFunc.ty
| .var idx => ctx[idx]?
| .app f _ =>
    match inferType? primFuncCtx ctx f with
    | some (.func _ outTy) => some outTy
    | _ => none
| .primEq _ _ => some (.prim "Bool")
| .primLt _ _ => some (.prim "Bool")
| .primGt _ _ => some (.prim "Bool")
| .mkStruct tys => some (.func tys (.struct tys))
| .structProj tys idx => some (.func [.struct tys] tys[idx])
| .ite _ thenTerm _ => inferType? primFuncCtx ctx thenTerm
| .recurse resultTy _ _ => some resultTy

private def inferFuncArgs? {primCtx : PrimitiveCtx} (primFuncCtx : PrimFuncCtx primCtx)
    (ctx : List Ty) (term : Term primCtx) : Option (List Ty) :=
  match inferType? primFuncCtx ctx term with
  | some (.func argsTy _) => some argsTy
  | _ => none

private def inferPrimName? {primCtx : PrimitiveCtx} (primFuncCtx : PrimFuncCtx primCtx)
    (ctx : List Ty) (term : Term primCtx) : Option String :=
  match inferType? primFuncCtx ctx term with
  | some (.prim name) => some name
  | _ => none

private def varMatch? (ctxTy : List Ty) :
    (ctx : List Ty) → (idx : Nat) → (ty : Ty) →
      Option { finIdx : Fin (ctx.map (Ty.subst ctxTy)).length //
        finIdx.val = idx ∧ (ctx.map (Ty.subst ctxTy))[finIdx] = Ty.subst ctxTy ty }
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

private def argGoals {primCtx : PrimitiveCtx} (ctx : List Ty) :
    List (Term primCtx) → List Ty → List (Pr primCtx)
| arg :: args, ty :: tys => .hasType ctx arg ty :: argGoals ctx args tys
| _, _ => []

private def unifyTypeHasTypeGoals {primCtx : PrimitiveCtx}
    (primFuncCtx : PrimFuncCtx primCtx) (ctxTy : List Ty) (ctxTerm : List (Term primCtx))
    (ctx : List Ty) (term : Term primCtx) (ty : Ty) : List (Pr primCtx) :=
    match term with
    | .prim actualTy _ =>
        if actualTy = Ty.subst ctxTy ty then [] else [.hasType ctx term ty]
    | .primFunc name =>
        match primFuncMatch? primFuncCtx name (Ty.subst ctxTy ty) with
        | some _ => []
        | none => [.hasType ctx term ty]
    | .var idx =>
        match ctxTerm with
        | [] =>
            match varMatch? ctxTy ctx idx ty with
            | some _ => []
            | none => [.hasType ctx term ty]
        | _ => [.hasType ctx term ty]
    | .app f args =>
        match inferFuncArgs? primFuncCtx ctx f with
        | some argsTy =>
            if args.length = argsTy.length then
              .hasType ctx f (.func argsTy ty) :: argGoals ctx args argsTy
            else [.hasType ctx term ty]
        | none => [.hasType ctx term ty]
    | .primEq lhs rhs =>
        if Ty.subst ctxTy ty = .prim "Bool" then
          match inferPrimName? primFuncCtx ctx lhs <|> inferPrimName? primFuncCtx ctx rhs with
          | some primName => [.hasType ctx lhs (.prim primName), .hasType ctx rhs (.prim primName)]
          | none => [.hasType ctx term ty]
        else [.hasType ctx term ty]
    | .primLt lhs rhs =>
        if Ty.subst ctxTy ty = .prim "Bool" then
          match inferPrimName? primFuncCtx ctx lhs <|> inferPrimName? primFuncCtx ctx rhs with
          | some primName => [.hasType ctx lhs (.prim primName), .hasType ctx rhs (.prim primName)]
          | none => [.hasType ctx term ty]
        else [.hasType ctx term ty]
    | .primGt lhs rhs =>
        if Ty.subst ctxTy ty = .prim "Bool" then
          match inferPrimName? primFuncCtx ctx lhs <|> inferPrimName? primFuncCtx ctx rhs with
          | some primName => [.hasType ctx lhs (.prim primName), .hasType ctx rhs (.prim primName)]
          | none => [.hasType ctx term ty]
        else [.hasType ctx term ty]
    | .mkStruct tys =>
        if (.func tys (.struct tys)) = Ty.subst ctxTy ty then [] else [.hasType ctx term ty]
    | .structProj tys idx =>
        if (.func [.struct tys] tys[idx]) = Ty.subst ctxTy ty then [] else [.hasType ctx term ty]
    | .ite cond thenTerm elseTerm =>
        [.hasType ctx cond (.prim "Bool"), .hasType ctx thenTerm ty, .hasType ctx elseTerm ty]
    | .recurse resultTy init body =>
        match ctxTerm with
        | [] =>
            match inferType? primFuncCtx ctx init with
            | some stateTy =>
                if Ty.subst ctxTy stateTy = stateTy ∧
                    Ty.subst ctxTy resultTy = resultTy ∧
                    resultTy = Ty.subst ctxTy ty then
                  [ .hasType ctx init stateTy
                  , .hasType (ctx ++ [stateTy, .func [stateTy] resultTy]) body resultTy
                  ]
                else [.hasType ctx term ty]
            | none => [.hasType ctx term ty]
        | _ :: _ => [.hasType ctx term ty]

private def unifyTypeGoals {primCtx : PrimitiveCtx}
    (primFuncCtx : PrimFuncCtx primCtx) (ctxTy : List Ty) (ctxTerm : List (Term primCtx)) :
    Pr primCtx → List (Pr primCtx)
| .hasType ctx term ty => unifyTypeHasTypeGoals primFuncCtx ctxTy ctxTerm ctx term ty
| goal => [goal]

private theorem argGoals_sound {primCtx : PrimitiveCtx} {primFuncCtx : PrimFuncCtx primCtx}
    {ctxTy : List Ty} {ctxTerm : List (Term primCtx)} {ctx : List Ty}
    {args : List (Term primCtx)} {tys : List Ty}
    (hlen : args.length = tys.length)
    (proveSubgoals : ∀ subgoal, subgoal ∈ argGoals ctx args tys →
      Pr.Provable primCtx primFuncCtx ctxTy ctxTerm subgoal) :
    ∀ idx : Fin args.length,
      Term.hasType primCtx primFuncCtx (ctx.map (Ty.subst ctxTy))
        (Term.subst ctxTerm args[idx])
        (Ty.subst ctxTy tys[Fin.cast hlen idx]) := by
  induction args generalizing tys with
  | nil =>
      intro idx
      cases idx with
      | mk val isLt => simp at isLt
  | cons arg args ih =>
      cases tys with
      | nil =>
          simp at hlen
      | cons ty tys =>
          intro idx
          cases idx with
          | mk val isLt =>
              cases val with
              | zero =>
                  have harg : Pr.Provable primCtx primFuncCtx ctxTy ctxTerm (.hasType ctx arg ty) :=
                    proveSubgoals (.hasType ctx arg ty) (by simp [argGoals])
                  cases harg with
                  | ofProof proof => simpa [Pr.interp, Term.subst, Ty.subst] using proof
              | succ val =>
                  have hlenTail : args.length = tys.length := by
                    simpa using Nat.succ.inj hlen
                  have proveTail : ∀ subgoal, subgoal ∈ argGoals ctx args tys →
                      Pr.Provable primCtx primFuncCtx ctxTy ctxTerm subgoal := by
                    intro subgoal hsubgoal
                    exact proveSubgoals subgoal (by simp [argGoals, hsubgoal])
                  have htail := ih hlenTail proveTail ⟨val, by simp at isLt; omega⟩
                  simpa [Term.subst, Ty.subst] using htail

private theorem unifyTypeHasType_sound {primCtx : PrimitiveCtx}
    {primFuncCtx : PrimFuncCtx primCtx} {ctxTy : List Ty}
    {ctxTerm : List (Term primCtx)} {ctx : List Ty} {term : Term primCtx} {ty : Ty} :
    (∀ subgoal, subgoal ∈ unifyTypeHasTypeGoals primFuncCtx ctxTy ctxTerm ctx term ty →
      Pr.Provable primCtx primFuncCtx ctxTy ctxTerm subgoal) →
      Pr.interp primCtx primFuncCtx ctxTy ctxTerm (.hasType ctx term ty) := by
  classical
  cases term with
  | prim actualTy val =>
      by_cases hty : actualTy = Ty.subst ctxTy ty
      · intro _
        have hprim : Term.hasType primCtx primFuncCtx (ctx.map (Ty.subst ctxTy))
            (.prim actualTy val) (Ty.subst ctxTy ty) := by
          rw [← hty]
          exact Term.hasType.prim val
        simpa [Pr.interp, Term.subst] using hprim
      · intro proveSubgoals
        have hself := proveSubgoals (.hasType ctx (.prim actualTy val) ty)
          (by simp [unifyTypeHasTypeGoals, hty])
        cases hself with
        | ofProof proof => exact proof
  | primFunc name =>
      cases hmatch : primFuncMatch? primFuncCtx name (Ty.subst ctxTy ty) with
      | some found =>
          intro _
          have hname := found.property.left
          have hty := found.property.right
          have hprim := @Term.hasType.primFunc primCtx primFuncCtx
            (ctx.map (Ty.subst ctxTy)) found.val
          rw [hname, hty] at hprim
          simpa [Pr.interp, Term.subst] using hprim
      | none =>
          intro proveSubgoals
          have hself := proveSubgoals (.hasType ctx (.primFunc name) ty)
            (by simp [unifyTypeHasTypeGoals, hmatch])
          cases hself with
          | ofProof proof => exact proof
  | var idx =>
      cases ctxTerm with
      | nil =>
          cases hvar : varMatch? ctxTy ctx idx ty with
          | some found =>
              intro _
              have hvarType : Term.hasType primCtx primFuncCtx (ctx.map (Ty.subst ctxTy))
                  (.var idx) (Ty.subst ctxTy ty) := by
                have hraw : Term.hasType primCtx primFuncCtx (ctx.map (Ty.subst ctxTy))
                    (.var found.val) (Ty.subst ctxTy ty) :=
                  Term.hasType.var (idx := found.val) found.property.right
                simpa [found.property.left] using hraw
              simpa [Pr.interp, Term.subst] using hvarType
          | none =>
              intro proveSubgoals
              have hself := proveSubgoals (.hasType ctx (.var idx) ty)
                (by simp [unifyTypeHasTypeGoals, hvar])
              cases hself with
              | ofProof proof => exact proof
      | cons head tail =>
          intro proveSubgoals
          have hself := proveSubgoals (.hasType ctx (.var idx) ty)
            (by simp [unifyTypeHasTypeGoals])
          cases hself with
          | ofProof proof => exact proof
  | app f args =>
      cases hfun : inferFuncArgs? primFuncCtx ctx f with
      | none =>
          intro proveSubgoals
          have hself := proveSubgoals (.hasType ctx (.app f args) ty)
            (by simp [unifyTypeHasTypeGoals, hfun])
          cases hself with
          | ofProof proof => exact proof
      | some argsTy =>
          by_cases hlen : args.length = argsTy.length
          · intro proveSubgoals
            have hfProv : Pr.Provable primCtx primFuncCtx ctxTy ctxTerm
                (.hasType ctx f (.func argsTy ty)) :=
              proveSubgoals (.hasType ctx f (.func argsTy ty))
                (by simp [unifyTypeHasTypeGoals, hfun, hlen])
            have proveArgs : ∀ subgoal, subgoal ∈ argGoals ctx args argsTy →
                Pr.Provable primCtx primFuncCtx ctxTy ctxTerm subgoal := by
              intro subgoal hsubgoal
              exact proveSubgoals subgoal
                (by simp [unifyTypeHasTypeGoals, hfun, hlen, hsubgoal])
            cases hfProv with
            | ofProof hfProof =>
                have hf : Term.hasType primCtx primFuncCtx (ctx.map (Ty.subst ctxTy))
                    (Term.subst ctxTerm f) (.func (argsTy.map (Ty.subst ctxTy)) (Ty.subst ctxTy ty)) := by
                  simpa [Pr.interp, Ty.subst] using hfProof
                have hargs := argGoals_sound (primFuncCtx := primFuncCtx)
                  (ctxTy := ctxTy) (ctxTerm := ctxTerm) (ctx := ctx)
                  (args := args) (tys := argsTy) hlen proveArgs
                have happ : Term.hasType primCtx primFuncCtx (ctx.map (Ty.subst ctxTy))
                    (.app (Term.subst ctxTerm f) (args.map (Term.subst ctxTerm)))
                    (Ty.subst ctxTy ty) := by
                  refine Term.hasType.app hf ?_ ?_
                  · simp [hlen]
                  · intro idx
                    have harg := hargs ⟨idx.val, by simpa using idx.isLt⟩
                    simpa [List.getElem_map] using harg
                simpa [Pr.interp, Term.subst] using happ
          · intro proveSubgoals
            have hself := proveSubgoals (.hasType ctx (.app f args) ty)
              (by simp [unifyTypeHasTypeGoals, hfun, hlen])
            cases hself with
            | ofProof proof => exact proof
  | «primEq» lhs rhs =>
      by_cases hbool : Ty.subst ctxTy ty = .prim "Bool"
      · cases hprim : inferPrimName? primFuncCtx ctx lhs <|> inferPrimName? primFuncCtx ctx rhs with
        | none =>
            intro proveSubgoals
            have hself := proveSubgoals (.hasType ctx (.primEq lhs rhs) ty)
              (by simp [unifyTypeHasTypeGoals, hbool, hprim])
            cases hself with
            | ofProof proof => exact proof
        | some primName =>
            intro proveSubgoals
            have hlProv : Pr.Provable primCtx primFuncCtx ctxTy ctxTerm
                (.hasType ctx lhs (.prim primName)) :=
              proveSubgoals (.hasType ctx lhs (.prim primName))
                (by simp [unifyTypeHasTypeGoals, hbool, hprim])
            have hrProv : Pr.Provable primCtx primFuncCtx ctxTy ctxTerm
                (.hasType ctx rhs (.prim primName)) :=
              proveSubgoals (.hasType ctx rhs (.prim primName))
                (by simp [unifyTypeHasTypeGoals, hbool, hprim])
            cases hlProv with
            | ofProof hlProof =>
                cases hrProv with
                | ofProof hrProof =>
                    have hl : Term.hasType primCtx primFuncCtx (ctx.map (Ty.subst ctxTy))
                        (Term.subst ctxTerm lhs) (.prim primName) := by
                      simpa [Pr.interp, Ty.subst] using hlProof
                    have hr : Term.hasType primCtx primFuncCtx (ctx.map (Ty.subst ctxTy))
                        (Term.subst ctxTerm rhs) (.prim primName) := by
                      simpa [Pr.interp, Ty.subst] using hrProof
                    have hcmp : Term.hasType primCtx primFuncCtx (ctx.map (Ty.subst ctxTy))
                        (.primEq (Term.subst ctxTerm lhs) (Term.subst ctxTerm rhs))
                        (Ty.subst ctxTy ty) := by
                      rw [hbool]
                      exact Term.hasType.primEq hl hr
                    simpa [Pr.interp, Term.subst] using hcmp
      · intro proveSubgoals
        have hself := proveSubgoals (.hasType ctx (.primEq lhs rhs) ty)
          (by simp [unifyTypeHasTypeGoals, hbool])
        cases hself with
        | ofProof proof => exact proof
  | «primLt» lhs rhs =>
      by_cases hbool : Ty.subst ctxTy ty = .prim "Bool"
      · cases hprim : inferPrimName? primFuncCtx ctx lhs <|> inferPrimName? primFuncCtx ctx rhs with
        | none =>
            intro proveSubgoals
            have hself := proveSubgoals (.hasType ctx (.primLt lhs rhs) ty)
              (by simp [unifyTypeHasTypeGoals, hbool, hprim])
            cases hself with
            | ofProof proof => exact proof
        | some primName =>
            intro proveSubgoals
            have hlProv : Pr.Provable primCtx primFuncCtx ctxTy ctxTerm
                (.hasType ctx lhs (.prim primName)) :=
              proveSubgoals (.hasType ctx lhs (.prim primName))
                (by simp [unifyTypeHasTypeGoals, hbool, hprim])
            have hrProv : Pr.Provable primCtx primFuncCtx ctxTy ctxTerm
                (.hasType ctx rhs (.prim primName)) :=
              proveSubgoals (.hasType ctx rhs (.prim primName))
                (by simp [unifyTypeHasTypeGoals, hbool, hprim])
            cases hlProv with
            | ofProof hlProof =>
                cases hrProv with
                | ofProof hrProof =>
                    have hl : Term.hasType primCtx primFuncCtx (ctx.map (Ty.subst ctxTy))
                        (Term.subst ctxTerm lhs) (.prim primName) := by
                      simpa [Pr.interp, Ty.subst] using hlProof
                    have hr : Term.hasType primCtx primFuncCtx (ctx.map (Ty.subst ctxTy))
                        (Term.subst ctxTerm rhs) (.prim primName) := by
                      simpa [Pr.interp, Ty.subst] using hrProof
                    have hcmp : Term.hasType primCtx primFuncCtx (ctx.map (Ty.subst ctxTy))
                        (.primLt (Term.subst ctxTerm lhs) (Term.subst ctxTerm rhs))
                        (Ty.subst ctxTy ty) := by
                      rw [hbool]
                      exact Term.hasType.primLt hl hr
                    simpa [Pr.interp, Term.subst] using hcmp
      · intro proveSubgoals
        have hself := proveSubgoals (.hasType ctx (.primLt lhs rhs) ty)
          (by simp [unifyTypeHasTypeGoals, hbool])
        cases hself with
        | ofProof proof => exact proof
  | «primGt» lhs rhs =>
      by_cases hbool : Ty.subst ctxTy ty = .prim "Bool"
      · cases hprim : inferPrimName? primFuncCtx ctx lhs <|> inferPrimName? primFuncCtx ctx rhs with
        | none =>
            intro proveSubgoals
            have hself := proveSubgoals (.hasType ctx (.primGt lhs rhs) ty)
              (by simp [unifyTypeHasTypeGoals, hbool, hprim])
            cases hself with
            | ofProof proof => exact proof
        | some primName =>
            intro proveSubgoals
            have hlProv : Pr.Provable primCtx primFuncCtx ctxTy ctxTerm
                (.hasType ctx lhs (.prim primName)) :=
              proveSubgoals (.hasType ctx lhs (.prim primName))
                (by simp [unifyTypeHasTypeGoals, hbool, hprim])
            have hrProv : Pr.Provable primCtx primFuncCtx ctxTy ctxTerm
                (.hasType ctx rhs (.prim primName)) :=
              proveSubgoals (.hasType ctx rhs (.prim primName))
                (by simp [unifyTypeHasTypeGoals, hbool, hprim])
            cases hlProv with
            | ofProof hlProof =>
                cases hrProv with
                | ofProof hrProof =>
                    have hl : Term.hasType primCtx primFuncCtx (ctx.map (Ty.subst ctxTy))
                        (Term.subst ctxTerm lhs) (.prim primName) := by
                      simpa [Pr.interp, Ty.subst] using hlProof
                    have hr : Term.hasType primCtx primFuncCtx (ctx.map (Ty.subst ctxTy))
                        (Term.subst ctxTerm rhs) (.prim primName) := by
                      simpa [Pr.interp, Ty.subst] using hrProof
                    have hcmp : Term.hasType primCtx primFuncCtx (ctx.map (Ty.subst ctxTy))
                        (.primGt (Term.subst ctxTerm lhs) (Term.subst ctxTerm rhs))
                        (Ty.subst ctxTy ty) := by
                      rw [hbool]
                      exact Term.hasType.primGt hl hr
                    simpa [Pr.interp, Term.subst] using hcmp
      · intro proveSubgoals
        have hself := proveSubgoals (.hasType ctx (.primGt lhs rhs) ty)
          (by simp [unifyTypeHasTypeGoals, hbool])
        cases hself with
        | ofProof proof => exact proof
  | mkStruct tys =>
      by_cases hty : (.func tys (.struct tys)) = Ty.subst ctxTy ty
      · intro _
        have hmk : Term.hasType primCtx primFuncCtx (ctx.map (Ty.subst ctxTy))
            (.mkStruct tys) (Ty.subst ctxTy ty) := by
          rw [← hty]
          exact Term.hasType.mkStruct
        simpa [Pr.interp, Term.subst] using hmk
      · intro proveSubgoals
        have hself := proveSubgoals (.hasType ctx (.mkStruct tys) ty)
          (by simp [unifyTypeHasTypeGoals, hty])
        cases hself with
        | ofProof proof => exact proof
  | structProj tys idx =>
      by_cases hty : (.func [.struct tys] tys[idx]) = Ty.subst ctxTy ty
      · intro _
        have hproj : Term.hasType primCtx primFuncCtx (ctx.map (Ty.subst ctxTy))
            (.structProj tys idx) (Ty.subst ctxTy ty) := by
          rw [← hty]
          exact Term.hasType.structProj idx
        simpa [Pr.interp, Term.subst] using hproj
      · intro proveSubgoals
        have hself := proveSubgoals (.hasType ctx (.structProj tys idx) ty)
          (by
            simp [unifyTypeHasTypeGoals]
            exact hty)
        cases hself with
        | ofProof proof => exact proof
  | ite cond thenTerm elseTerm =>
      intro proveSubgoals
      have hcondProv : Pr.Provable primCtx primFuncCtx ctxTy ctxTerm
          (.hasType ctx cond (.prim "Bool")) :=
        proveSubgoals (.hasType ctx cond (.prim "Bool"))
          (by simp [unifyTypeHasTypeGoals])
      have hthenProv : Pr.Provable primCtx primFuncCtx ctxTy ctxTerm
          (.hasType ctx thenTerm ty) :=
        proveSubgoals (.hasType ctx thenTerm ty)
          (by simp [unifyTypeHasTypeGoals])
      have helseProv : Pr.Provable primCtx primFuncCtx ctxTy ctxTerm
          (.hasType ctx elseTerm ty) :=
        proveSubgoals (.hasType ctx elseTerm ty)
          (by simp [unifyTypeHasTypeGoals])
      cases hcondProv with
      | ofProof hcondProof =>
          cases hthenProv with
          | ofProof hthenProof =>
              cases helseProv with
              | ofProof helseProof =>
                  have hcond : Term.hasType primCtx primFuncCtx (ctx.map (Ty.subst ctxTy))
                      (Term.subst ctxTerm cond) (.prim "Bool") := by
                    simpa [Pr.interp, Ty.subst] using hcondProof
                  have hthen : Term.hasType primCtx primFuncCtx (ctx.map (Ty.subst ctxTy))
                      (Term.subst ctxTerm thenTerm) (Ty.subst ctxTy ty) := by
                    simpa [Pr.interp] using hthenProof
                  have helse : Term.hasType primCtx primFuncCtx (ctx.map (Ty.subst ctxTy))
                      (Term.subst ctxTerm elseTerm) (Ty.subst ctxTy ty) := by
                    simpa [Pr.interp] using helseProof
                  have hite : Term.hasType primCtx primFuncCtx (ctx.map (Ty.subst ctxTy))
                      (.ite (Term.subst ctxTerm cond) (Term.subst ctxTerm thenTerm)
                        (Term.subst ctxTerm elseTerm)) (Ty.subst ctxTy ty) :=
                    Term.hasType.ite hcond hthen helse
                  simpa [Pr.interp, Term.subst] using hite
  | «recurse» resultTy init body =>
      cases ctxTerm with
      | nil =>
        cases hstateHint : inferType? primFuncCtx ctx init with
        | none =>
            intro proveSubgoals
            have hself := proveSubgoals (.hasType ctx (.recurse resultTy init body) ty)
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
              have hinitProv : Pr.Provable primCtx primFuncCtx ctxTy []
                  (.hasType ctx init stateTy) :=
                proveSubgoals (.hasType ctx init stateTy)
                  (by
                    unfold unifyTypeHasTypeGoals
                    simp [hstateHint]
                    rw [if_pos hcheck]
                    simp)
              have hbodyProv : Pr.Provable primCtx primFuncCtx ctxTy []
                  (.hasType (ctx ++ [stateTy, .func [stateTy] resultTy]) body resultTy) :=
                proveSubgoals (.hasType (ctx ++ [stateTy, .func [stateTy] resultTy]) body resultTy)
                  (by
                    unfold unifyTypeHasTypeGoals
                    simp [hstateHint]
                    rw [if_pos hcheck]
                    simp)
              cases hinitProv with
              | ofProof hinitProof =>
                  cases hbodyProv with
                  | ofProof hbodyProof =>
                      have hinit : Term.hasType primCtx primFuncCtx (ctx.map (Ty.subst ctxTy))
                          (Term.subst [] init) stateTy := by
                        simpa [Pr.interp, hstateFixed] using hinitProof
                      have hbody : Term.hasType primCtx primFuncCtx
                          (ctx.map (Ty.subst ctxTy) ++ [stateTy, .func [stateTy] resultTy])
                          (Term.subst [] body) resultTy := by
                        simpa [Pr.interp, Ty.subst, List.map_append, hstateFixed, hresultFixed]
                          using hbodyProof
                      have hbodyRaw : Term.hasType primCtx primFuncCtx
                          (ctx.map (Ty.subst ctxTy) ++ [stateTy, .func [stateTy] resultTy])
                          body resultTy := by
                        simpa [Term.subst] using hbody
                      have hrec : Term.hasType primCtx primFuncCtx (ctx.map (Ty.subst ctxTy))
                          (.recurse resultTy (Term.subst [] init) body)
                          (Ty.subst ctxTy ty) := by
                        rw [← htarget]
                        exact Term.hasType.recurse hinit hbodyRaw
                      simpa [Pr.interp, Term.subst] using hrec
            · intro proveSubgoals
              have hself := proveSubgoals (.hasType ctx (.recurse resultTy init body) ty)
                (by simp [unifyTypeHasTypeGoals, hstateHint, hcheck])
              cases hself with
              | ofProof proof => exact proof
      | cons head tail =>
          intro proveSubgoals
          have hself := proveSubgoals (.hasType ctx (.recurse resultTy init body) ty)
            (by simp [unifyTypeHasTypeGoals])
          cases hself with
          | ofProof proof => exact proof

private theorem unifyType_sound {primCtx : PrimitiveCtx} {primFuncCtx : PrimFuncCtx primCtx}
    {ctxTy : List Ty} {ctxTerm : List (Term primCtx)} {goal : Pr primCtx} :
    (∀ subgoal, subgoal ∈ unifyTypeGoals primFuncCtx ctxTy ctxTerm goal →
      Pr.Provable primCtx primFuncCtx ctxTy ctxTerm subgoal) →
      Pr.Provable primCtx primFuncCtx ctxTy ctxTerm goal := by
  cases goal with
  | eq ctx ty lhs rhs =>
      intro proveSubgoals
      exact proveSubgoals (.eq ctx ty lhs rhs) (by simp [unifyTypeGoals])
  | hasType ctx term ty =>
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

def unifyType {primCtx : PrimitiveCtx} {primFuncCtx : PrimFuncCtx primCtx}
    {ctxTy : List Ty} {ctxTerm : List (Term primCtx)} (goal : Pr primCtx) :
    MetaProgram primCtx primFuncCtx ctxTy ctxTerm goal where
  goals := unifyTypeGoals primFuncCtx ctxTy ctxTerm goal
  prove := by
    intro proveSubgoals
    exact unifyType_sound proveSubgoals

end MetaProgram

end Pr

end Zag
