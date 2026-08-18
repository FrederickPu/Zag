import Zag.Meta
import Lib.Peano.Defs

namespace Zag

namespace Pr

namespace TypeUnification

structure TypedArgs (ctx : Ctx) (varCtx : VarCtx)
    (args : List (Term ctx.primCtx)) where
  tys : List Ty
  length_eq : args.length = tys.length
  hasType : ∀ idx : Fin args.length, Term.hasType ctx varCtx args[idx] tys[idx]

mutual

/- Infer the unique type that the syntax-directed typing rules assign, returning the proof as a
  witness. Calls are typed from the callee block's declared `outTy`; recursive and forward calls
  therefore need no result-type inference. -/
def inferType? (ctx : Ctx) (varCtx : VarCtx) :
    (term : Term ctx.primCtx) → Option { ty : Ty // Term.hasType ctx varCtx term ty }
| .prim ty val => some ⟨ty, Term.hasType.prim val⟩
| .var name =>
    match h : Scope.get? varCtx name with
    | some ty => some ⟨ty, Term.hasType.var h⟩
    -- no local binding: the name may still be a block, and a block is a value
    | none =>
        match hb : ctx.blockCtx.get? name with
        | some block =>
            some ⟨.func (block.params.map Prod.snd) block.outTy, Term.hasType.varBlock h hb⟩
        | none => none
| .op name args =>
    match inferTypes? ctx varCtx args with
    | none => none
    | some typedArgs =>
        match h : ctx.opCtx.outTy? name typedArgs.tys with
        | some outTy =>
            some ⟨outTy, Term.hasType.op typedArgs.length_eq typedArgs.hasType h⟩
        | none => none
| .call name args =>
    match hget : ctx.blockCtx.get? name with
    | none => none
    | some block =>
        match inferTypes? ctx varCtx args with
        | none => none
        | some typedArgs =>
            if htys : typedArgs.tys = block.params.map Prod.snd then
              have hlen : args.length = block.params.length := by
                rw [typedArgs.length_eq, htys, List.length_map]
              some ⟨block.outTy, Term.hasType.call hget hlen (by
                intro idx
                have harg := typedArgs.hasType idx
                simpa [htys, List.getElem_map] using harg)⟩
            else none
| .exit _ _ => none
| .app f args =>
    match inferType? ctx varCtx f with
    | none => none
    | some fTyped =>
        match hfun : fTyped.val with
        | .func argTys outTy =>
            match inferTypes? ctx varCtx args with
            | none => none
            | some typedArgs =>
                if htys : typedArgs.tys = argTys then
                  have hf : Term.hasType ctx varCtx f (.func argTys outTy) := by
                    simpa [hfun] using fTyped.property
                  have hlen : args.length = argTys.length := by
                    rw [typedArgs.length_eq, htys]
                  some ⟨outTy, Term.hasType.app hf hlen (by
                    intro idx
                    have harg := typedArgs.hasType idx
                    simpa [htys] using harg)⟩
                else none
        | _ => none

def inferTypes? (ctx : Ctx) (varCtx : VarCtx) :
    (args : List (Term ctx.primCtx)) → Option (TypedArgs ctx varCtx args)
| [] => some { tys := [], length_eq := rfl, hasType := fun idx => Fin.elim0 idx }
| arg :: args =>
    match inferType? ctx varCtx arg, inferTypes? ctx varCtx args with
    | some argTyped, some restTyped =>
        some {
          tys := argTyped.val :: restTyped.tys
          length_eq := by simp [restTyped.length_eq]
          hasType := by
            intro idx
            cases idx using Fin.cases with
            | zero => simpa using argTyped.property
            | succ idx => simpa using restTyped.hasType idx }
    | _, _ => none

end

def checkHasType? (ctx : Ctx) (varCtx : VarCtx) :
    (term : Term ctx.primCtx) → (ty : Ty) → Option (PLift (Term.hasType ctx varCtx term ty))
| .exit name value, _ =>
    match hget : ctx.blockCtx.get? name with
    | none => none
    | some block =>
        match checkHasType? ctx varCtx value block.outTy with
        | none => none
        | some hvalue => some ⟨Term.hasType.exit hget hvalue.down⟩
| term, ty =>
    match inferType? ctx varCtx term with
    | none => none
    | some inferred =>
        if h : inferred.val = ty then
          some ⟨by cases h; exact inferred.property⟩
        else none

theorem hasType_of_isSome {ctx : Ctx} {varCtx : VarCtx}
    {term : Term ctx.primCtx} {ty : Ty}
    (h : (checkHasType? ctx varCtx term ty).isSome = true) :
    Term.hasType ctx varCtx term ty := by
  cases hcheck : checkHasType? ctx varCtx term ty with
  | none => simp [hcheck] at h
  | some proof => exact proof.down

structure CheckedInstrs (ctx : Ctx) (varCtx : VarCtx)
    (instrs : List (Instr ctx.primCtx)) where
  scope : VarCtx
  proof : Block.instrsHaveType ctx varCtx instrs scope

def checkInstrs? (ctx : Ctx) :
    (varCtx : VarCtx) → (instrs : List (Instr ctx.primCtx)) →
      Option (CheckedInstrs ctx varCtx instrs)
| varCtx, [] => some { scope := varCtx, proof := Block.instrsHaveType.nil }
| varCtx, instr :: instrs =>
    match inferType? ctx varCtx instr.value with
    | none => none
    | some typedValue =>
        match checkInstrs? ctx (varCtx ++ [(instr.name, typedValue.val)]) instrs with
        | none => none
        | some rest =>
            some {
              scope := rest.scope
              proof := Block.instrsHaveType.cons typedValue.property rest.proof }

def checkBlock? (ctx : Ctx) (block : Block ctx.primCtx) :
    Option (PLift (Block.WellTyped ctx block)) :=
  match checkInstrs? ctx block.params block.instrs with
  | none => none
  | some checkedInstrs =>
      match checkHasType? ctx checkedInstrs.scope block.result block.outTy with
      | none => none
      | some hresult => some ⟨⟨checkedInstrs.scope, checkedInstrs.proof, hresult.down⟩⟩

def checkBlocks? (ctx : Ctx) :
    (blocks : BlockCtx.Raw ctx.primCtx) →
      Option (PLift (∀ entry, entry ∈ blocks → Block.WellTyped ctx entry.2))
| [] => some ⟨by intro entry hentry; cases hentry⟩
| entry :: rest =>
    match checkBlock? ctx entry.2, checkBlocks? ctx rest with
    | some hentry, some hrest =>
        some ⟨by
          intro candidate hcandidate
          simp only [List.mem_cons] at hcandidate
          cases hcandidate with
          | inl h => cases h; exact hentry.down
          | inr h => exact hrest.down candidate h⟩
    | _, _ => none

def checkCtx? (ctx : Ctx) : Option (PLift (Ctx.WellTyped ctx)) :=
  checkBlocks? ctx ctx.blockCtx.val

theorem blockWellTyped_of_isSome {ctx : Ctx} {block : Block ctx.primCtx}
    (h : (checkBlock? ctx block).isSome = true) : Block.WellTyped ctx block := by
  cases hcheck : checkBlock? ctx block with
  | none => simp [hcheck] at h
  | some proof => exact proof.down

theorem ctxWellTyped_of_isSome {ctx : Ctx}
    (h : (checkCtx? ctx).isSome = true) : Ctx.WellTyped ctx := by
  cases hcheck : checkCtx? ctx with
  | none => simp [hcheck] at h
  | some proof => exact proof.down

private def unifyTypeGoals {ctx : Ctx}
    (ctxTy : Scope Ty) (ctxTerm : Scope (Term ctx.primCtx)) :
    Pr (Term ctx.primCtx) → List (Pr (Term ctx.primCtx))
| .hasType varCtx term ty =>
    match checkHasType? ctx (VarCtx.subst ctxTy varCtx)
        (Term.subst ctxTerm term) (Ty.subst ctxTy ty) with
    | some _ => []
    | none => [.hasType varCtx term ty]
| goal => [goal]

private theorem unifyType_sound {ctx : Ctx}
    {ctxTy : Scope Ty} {ctxTerm : Scope (Term ctx.primCtx)}
    {goal : Pr (Term ctx.primCtx)} :
    (∀ subgoal, subgoal ∈ unifyTypeGoals (ctx := ctx) ctxTy ctxTerm goal →
      Pr.Provable ctx ctxTy ctxTerm subgoal) →
      Pr.Provable ctx ctxTy ctxTerm goal := by
  cases goal with
  | eq varCtx ty lhs rhs =>
      intro proveSubgoals
      exact proveSubgoals (.eq varCtx ty lhs rhs) (by simp [unifyTypeGoals])
  | hasType varCtx term ty =>
      intro proveSubgoals
      cases hcheck : checkHasType? ctx (VarCtx.subst ctxTy varCtx)
          (Term.subst ctxTerm term) (Ty.subst ctxTy ty) with
      | none =>
          exact proveSubgoals (.hasType varCtx term ty) (by
            unfold unifyTypeGoals
            change Pr.hasType varCtx term ty ∈
              match checkHasType? ctx (VarCtx.subst ctxTy varCtx)
                  (Term.subst ctxTerm term) (Ty.subst ctxTy ty) with
              | some _ => []
              | none => [Pr.hasType varCtx term ty]
            rw [hcheck]
            simp)
      | some proof =>
          exact Pr.Provable.ofProof (by simpa [Pr.interp] using proof.down)
  | and p q =>
      intro proveSubgoals
      exact proveSubgoals (.and p q) (by simp [unifyTypeGoals])
  | or p q =>
      intro proveSubgoals
      exact proveSubgoals (.or p q) (by simp [unifyTypeGoals])
  | implies p q =>
      intro proveSubgoals
      exact proveSubgoals (.implies p q) (by simp [unifyTypeGoals])
  | forallTy name p =>
      intro proveSubgoals
      exact proveSubgoals (.forallTy name p) (by simp [unifyTypeGoals])
  | forallTerm name p =>
      intro proveSubgoals
      exact proveSubgoals (.forallTerm name p) (by simp [unifyTypeGoals])

def unifyType {ctx : Ctx}
    {ctxTy : Scope Ty} {ctxTerm : Scope (Term ctx.primCtx)}
    (goal : Pr (Term ctx.primCtx)) : PrRefinement ctx ctxTy ctxTerm goal where
  goals := unifyTypeGoals (ctx := ctx) ctxTy ctxTerm goal
  prove := by
    intro proveSubgoals
    simp only [Language.Provable_term] at proveSubgoals ⊢
    exact unifyType_sound proveSubgoals

mutual

theorem Ty.subst_nil : (ty : Ty) → Ty.subst [] ty = ty
| .var name => by simp [Ty.subst]
| .prim name args => by simp [Ty.subst, Ty.subst_nil_list args]
| .func args result => by simp [Ty.subst, Ty.subst_nil_list args, Ty.subst_nil result]

theorem Ty.subst_nil_list : (tys : List Ty) → tys.map (Ty.subst []) = tys
| [] => rfl
| ty :: tys => by simp [Ty.subst_nil ty, Ty.subst_nil_list tys]

end

theorem VarCtx.subst_nil : (varCtx : VarCtx) → VarCtx.subst [] varCtx = varCtx
| [] => rfl
| (name, ty) :: rest => by
    simp [VarCtx.subst, Ty.subst_nil ty]
    exact VarCtx.subst_nil rest

theorem hasType_of_provable {ctx : Ctx} {varCtx : VarCtx}
    {term : Term ctx.primCtx} {ty : Ty}
    (h : Pr.Provable ctx [] [] (.hasType varCtx term ty)) :
    Term.hasType ctx varCtx term ty := by
  cases h with
  | ofProof proof =>
      simpa [Pr.interp, Term.subst_nil, Ty.subst_nil, VarCtx.subst_nil] using proof

syntax (name := hasTypeTactic) "has_type" : tactic
syntax (name := blockWellTypedTactic) "typecheck_block" : tactic
syntax (name := ctxWellTypedTactic) "typecheck_ctx" : tactic
syntax (name := reduceUnifyType) "reduce_unify_type" : tactic

macro_rules
| `(tactic| reduce_unify_type) =>
    `(tactic|
      set_option linter.unusedSimpArgs false in
        simp [unifyType, unifyTypeGoals, checkHasType?, inferType?, inferTypes?,
          checkInstrs?, checkBlock?, checkBlocks?, checkCtx?, hasType_of_isSome,
          blockWellTyped_of_isSome, ctxWellTyped_of_isSome, VarCtx.subst, Ty.subst,
          Term.subst, Scope.get?, Scope.get?_append_singleton, BlockCtx.get?,
          BlockCtx.Raw.get?, BlockCtx.empty, OpCtx.get?, OpCtx.outTy?, Lib.Peano.peanoCtx,
          Lib.Peano.natOpCtx, Peano.opCtx, Term.nat, Term.bool, Term.ite, Op.ite,
          Op.eq, Op.compare, Op.fixed, Op.natBinary, Op.natUnary, Op.ofVals])
| `(tactic| has_type) =>
    `(tactic|
      apply Pr.TypeUnification.hasType_of_isSome <;>
      decide)
| `(tactic| typecheck_block) =>
    `(tactic|
      apply Pr.TypeUnification.blockWellTyped_of_isSome <;>
      decide)
| `(tactic| typecheck_ctx) =>
    `(tactic|
      apply Pr.TypeUnification.ctxWellTyped_of_isSome <;>
      decide)

end TypeUnification

end Pr

end Zag
