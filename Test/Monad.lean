import Lib.Peano.Defs

namespace Zag.Test.Monad

def stateCtx : PrimitiveCtx where
  prims := [.of "Nat" Nat, .of "Bool" Bool]
  M := StateM Nat
  monad := inferInstance

instance : Peano.Types stateCtx where
  natType := by rfl
  boolType := by rfl

def ctx : Ctx where
  primCtx := stateCtx
  primFuncCtx := []
  opCtx := []

instance : Peano.Types ctx.primCtx := by
  change Peano.Types stateCtx
  infer_instance

def NatTy : Ty := .prim "Nat"

example : OpCtx.outTy? ([] : OpCtx stateCtx) "pure" [NatTy] = some (.m NatTy) := by
  rfl

example : OpCtx.outTy? ([] : OpCtx stateCtx) "pure" [] = none := by
  rfl

theorem lift_hasType (n : Nat) :
    Term.hasType ctx [] (Term.lift (Term.nat n)) (.m NatTy) := by
  apply Term.hasType_lift
  simpa [ctx, NatTy, Term.nat] using
    (Term.hasType.prim (ctx := ctx) (varCtx := []) (Ty.ofNat stateCtx n))

theorem lift_eval (n : Nat) :
    Term.eval ctx [] (Term.lift (Term.nat n)) =
      some (Val.mk (.m (Val.nat (primCtx := stateCtx) n).ty)
        (Ty.ofM stateCtx (Val.nat (primCtx := stateCtx) n).ty
          (Pure.pure (some (Val.nat (primCtx := stateCtx) n).val)))) := by
  unfold Term.eval
  exact Term.evalGo_lift (ctx := ctx) (motives := []) (env := [])
      (term := Term.nat n) (value := Val.nat n)
      (by simp only [Term.nat, Term.evalGo]; rfl)

example :
    ctx.opCtx.outTy? "bind" [.m NatTy, .func [NatTy] (.m NatTy)] = some (.m NatTy) := by
  rfl

example : ctx.opCtx.outTy? "bind" [.m NatTy] = none := by
  rfl

noncomputable def identityContinuationValue : Ty.type ctx.primCtx (.func [NatTy] (.m NatTy)) :=
  cast (Ty.type.eq_6 ctx.primCtx [NatTy] (.m NatTy)).symm fun args =>
    some (Ty.ofM ctx.primCtx NatTy (Pure.pure (some (args 0))))

noncomputable def identityContinuation : Term ctx.primCtx :=
  .prim (.func [NatTy] (.m NatTy)) identityContinuationValue

theorem bind_hasType (n : Nat) :
    Term.hasType ctx [] (Term.bind (Term.lift (Term.nat n)) identityContinuation) (.m NatTy) := by
  apply Term.hasType.op (tys := [.m NatTy, .func [NatTy] (.m NatTy)]) (by rfl)
  · intro idx
    match idx with
    | ⟨0, _⟩ => exact lift_hasType n
    | ⟨1, _⟩ => exact Term.hasType.prim _
    | ⟨i + 2, h⟩ =>
        have : False := by
          change i + 2 < 2 at h
          omega
        contradiction
  · simp [ctx, OpCtx.outTy?, OpCtx.get?, Op.bind]

theorem bind_eval (n : Nat) :
    Term.eval ctx [] (Term.bind (Term.lift (Term.nat n)) identityContinuation) =
      Op.applyVals Op.bind
        [Val.mk (.m NatTy) (Ty.ofM stateCtx NatTy (Pure.pure (some (Ty.ofNat stateCtx n)))),
         Val.mk (.func [NatTy] (.m NatTy)) identityContinuationValue] := by
  have hlift : Term.evalGo ctx [] [] (Term.lift (Term.nat n)) =
      some (Val.mk (.m NatTy)
        (Ty.ofM stateCtx NatTy (Pure.pure (some (Ty.ofNat stateCtx n))))) := by
    exact Term.evalGo_lift (ctx := ctx) (motives := []) (env := [])
      (term := Term.nat n) (value := Val.nat n)
      (by simp only [Term.nat, Term.evalGo]; rfl)
  have hcontinuation : Term.evalGo ctx [] [] identityContinuation =
      some (Val.mk (.func [NatTy] (.m NatTy)) identityContinuationValue) := by
    unfold identityContinuation
    simp only [Term.evalGo]
  simp [Term.eval, Term.bind, Term.evalGo, OpCtx.get?, Op.applyVals, Op.bind]
  exact Term.evalBody_eagerBody_two ctx [] [] _ _ _ _ _ hlift hcontinuation

end Zag.Test.Monad
