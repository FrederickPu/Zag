import Lib.Peano.Defs

/-!
`m` used to be a constructor of `Ty` and `pure`/`bind` were hardcoded into `OpCtx.get?`.
Neither is built in any more: a context that wants suspended computations declares `m` as an
ordinary arity-1 primitive and supplies `pure`/`bind` as ordinary ops. The monad is a choice of
the `PrimitiveCtx`, exactly as before -- it is just no longer a field of it.
-/

namespace Zag.Test.Monad

abbrev M : Type → Type := StateM Nat

/- `m(α)`: a computation in `M` that may get stuck, which is what `Ty.m` used to mean -/
def mPrim : Primitive where
  name := "m"
  arity := 1
  type := fun
    | [α] => M (Option α)
    | _ => Empty
  repr := fun _ => none

abbrev stateCtx : PrimitiveCtx := .ofPrims [.of "Nat" Nat, .of "Bool" Bool, mPrim]

instance : Peano.Types stateCtx where
  natType := by rfl
  boolType := by rfl

abbrev NatTy : Ty := Peano.NatTy
abbrev MTy (t : Ty) : Ty := .prim "m" [t]

theorem type_m (t : Ty) : Ty.type stateCtx (MTy t) = M (Option (Ty.type stateCtx t)) := by
  rw [Ty.type_prim_of_find (primitive := mPrim) [t] rfl, Ty.types_cons, Ty.types_nil]
  rfl

def ofM (t : Ty) : M (Option (Ty.type stateCtx t)) → Ty.type stateCtx (MTy t) :=
  cast (type_m t).symm

def toM (t : Ty) : Ty.type stateCtx (MTy t) → M (Option (Ty.type stateCtx t)) :=
  cast (type_m t)

@[simp] theorem toM_ofM (t : Ty) (value : M (Option (Ty.type stateCtx t))) :
    toM t (ofM t value) = value := by
  simp [toM, ofM]

def pureOp : Op stateCtx :=
  (Op.Signature.unary MTy fun ty value => ofM ty (Pure.pure (some value))).toOp

@[simp] private def bindShape? (a b : Ty) :
    Option {s : Ty × Ty // MTy s.1 = a ∧ .func [s.1] (MTy s.2) = b} :=
  match a, b with
  | .prim "m" [input], .func [arg] (.prim "m" [result]) =>
      if h : input = arg then some ⟨(input, result), rfl, by simp [h]⟩ else none
  | _, _ => none

def bindOp : Op stateCtx :=
  (Op.Signature.binary (shape := Ty × Ty) (fun s => MTy s.1)
    (fun s => .func [s.1] (MTy s.2)) (fun s => MTy s.2)
    bindShape? fun (inputTy, resultTy) computation continuation =>
      ofM resultTy do
        let input? ← toM inputTy computation
        match input? with
        | none => Pure.pure none
        | some input =>
            match Ty.applyUnary? stateCtx inputTy (MTy resultTy) continuation input with
            | none => Pure.pure none
            | some next => toM resultTy next).toOp

abbrev ctx : Ctx where
  primCtx := stateCtx
  opCtx := [("pure", pureOp), ("bind", bindOp)]

def lift (term : Term stateCtx) : Term stateCtx := .op "pure" [term]

def bindTerm (computation continuation : Term stateCtx) : Term stateCtx :=
  .op "bind" [computation, continuation]

/-! ### the operators infer the same result types the built-ins used to -/

example : ctx.opCtx.outTy? "pure" [NatTy] = some (MTy NatTy) := by rfl

example : ctx.opCtx.outTy? "pure" [] = none := by rfl

example : ctx.opCtx.outTy? "bind" [MTy NatTy, .func [NatTy] (MTy NatTy)] = some (MTy NatTy) := by
  rfl

example : ctx.opCtx.outTy? "bind" [MTy NatTy] = none := by rfl

/-! ### typing -/

theorem lift_hasType (n : Nat) :
    Term.hasType ctx [] (lift (Term.nat n)) (MTy NatTy) :=
  Term.hasType.unOp (by rfl) (Term.hasType.prim _)

noncomputable def identityContinuationValue : Ty.type ctx.primCtx (.func [NatTy] (MTy NatTy)) :=
  cast (Ty.type_func ctx.primCtx [NatTy] (MTy NatTy)).symm fun args =>
    some (ofM NatTy (Pure.pure (some (args 0))))

noncomputable def identityContinuation : Term ctx.primCtx :=
  .prim (.func [NatTy] (MTy NatTy)) identityContinuationValue

theorem bind_hasType (n : Nat) :
    Term.hasType ctx [] (bindTerm (lift (Term.nat n)) identityContinuation) (MTy NatTy) := by
  refine Term.hasType.op (tys := [MTy NatTy, .func [NatTy] (MTy NatTy)]) rfl ?_ (by rfl)
  intro idx
  match idx with
  | ⟨0, _⟩ => exact lift_hasType n
  | ⟨1, _⟩ => exact Term.hasType.prim _
  | ⟨i + 2, h⟩ =>
      have : False := by
        change i + 2 < 2 at h
        omega
      contradiction

/-! ### evaluation, run through the context's monad -/

/- evaluate a term of type `m(Nat)` and run the resulting `StateM Nat` computation -/
def runM (term : Term stateCtx) (state : Nat) : Option (Option Nat × Nat) := do
  let value <- Term.eval ctx [] term
  let computation <- value.as? (MTy NatTy)
  let (result, state) := (toM NatTy computation).run state
  some (result.map (Ty.toNat stateCtx), state)

/-- info: some (some 7, 0) -/
#guard_msgs in
#eval runM (lift (Term.nat 7)) 0

/- `identityContinuation` embeds a Lean function as a `prim` value, so it is `noncomputable` and
  the `bind` case is checked by proof rather than by `#eval`. -/
theorem lift_eval (n : Nat) :
    Term.eval ctx [] (lift (Term.nat n)) = Op.applyVals pureOp [Val.nat n] := by
  have hnat : Term.evalGo ctx [] (Term.nat n) = some (Val.nat n) := by
    rw [Term.evalGo.eq_def]
    rfl
  simp [Term.eval, lift, Term.evalGo, OpCtx.get?, Op.applyVals, pureOp]
  exact Term.evalBody_eager_one ctx [] _ _ _ hnat

theorem lift_eval_val (n : Nat) :
    Term.eval ctx [] (lift (Term.nat n)) =
      some (Val.mk (MTy NatTy) (ofM NatTy (Pure.pure (some (Ty.ofNat stateCtx n))))) := by
  rw [lift_eval]
  exact Op.Signature.applyVals_unary MTy
    (fun ty value => ofM ty (Pure.pure (some value))) NatTy (Ty.ofNat stateCtx n)

theorem bind_eval (n : Nat) :
    Term.eval ctx [] (bindTerm (lift (Term.nat n)) identityContinuation) =
      Op.applyVals bindOp
        [Val.mk (MTy NatTy) (ofM NatTy (Pure.pure (some (Ty.ofNat stateCtx n)))),
         Val.mk (.func [NatTy] (MTy NatTy)) identityContinuationValue] := by
  have hlift : Term.evalGo ctx [] (lift (Term.nat n)) =
      some (Val.mk (MTy NatTy) (ofM NatTy (Pure.pure (some (Ty.ofNat stateCtx n))))) :=
    lift_eval_val n
  have hcontinuation : Term.evalGo ctx [] identityContinuation =
      some (Val.mk (.func [NatTy] (MTy NatTy)) identityContinuationValue) := by
    rw [Term.evalGo.eq_def]
    rfl
  simp [Term.eval, bindTerm, Term.evalGo, OpCtx.get?, Op.applyVals, bindOp]
  exact Term.evalBody_eager_two ctx [] _ _ _ _ _ hlift hcontinuation

end Zag.Test.Monad
