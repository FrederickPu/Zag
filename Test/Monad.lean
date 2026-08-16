import Lib.Peano.Defs
import Meta.Eval

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
  { arity := 2
    out := fun tys => (bindShape? (tys 0) (tys 1)).map fun shape => MTy shape.val.2
    body := .next true fun
      | none => .fail
      | some computation => .next true fun
          | none => .fail
          | some continuation =>
              match bindShape? computation.ty continuation.ty with
              | none => .fail
              | some shape =>
                  let inputTy := shape.val.1
                  let resultTy := shape.val.2
                  let computation' : Ty.type stateCtx (MTy inputTy) :=
                    cast (congrArg (Ty.type stateCtx) shape.property.1.symm) computation.val
                  let continuation' : Ty.type stateCtx (.func [inputTy] (MTy resultTy)) :=
                    cast (congrArg (Ty.type stateCtx) shape.property.2.symm) continuation.val
                  .done (Val.mk (MTy resultTy) <| ofM resultTy do
                    let input? ← toM inputTy computation'
                    match input? with
                    | none => Pure.pure none
                    | some input =>
                        match Ty.applyUnary? stateCtx inputTy (MTy resultTy) continuation' input with
                        | none => Pure.pure none
                        | some next => toM resultTy next) }

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
  let value <- (EvalState.run ctx 100 (EvalState.start [] term)).result?
  let computation <- value.as? (MTy NatTy)
  let (result, state) := (toM NatTy computation).run state
  some (result.map (Ty.toNat stateCtx), state)

/-- info: some (some 7, 0) -/
#guard_msgs in
#eval runM (lift (Term.nat 7)) 0

/- `identityContinuation` embeds a Lean function as a `prim` value, so it is `noncomputable` and
   the `bind` case is checked by proof rather than by `#eval`. -/
theorem lift_eval_val (n : Nat) :
    EvaluatesTo ctx [] (lift (Term.nat n))
      (Val.mk (MTy NatTy) (ofM NatTy (Pure.pure (some (Ty.ofNat stateCtx n))))) := by
  refine EvaluatesTo.op_applyVals (ctx := ctx) (env := []) (name := "pure")
    (args := [Term.nat n]) (values := [Val.nat n]) (oper := pureOp) rfl ?_ ?_
  · constructor
    · simpa [Term.nat] using
        (EvaluatesTo.prim (ctx := ctx) (env := []) NatTy (Ty.ofNat stateCtx n))
    · exact EvaluatesToAll.nil
  · simpa [pureOp] using Op.Signature.applyVals_unary MTy
      (fun ty value => ofM ty (Pure.pure (some value))) NatTy (Ty.ofNat stateCtx n)

theorem bind_eval (n : Nat) :
    EvaluatesTo ctx [] (bindTerm (lift (Term.nat n)) identityContinuation)
      (Val.mk (MTy NatTy) (ofM NatTy (Pure.pure (some (Ty.ofNat stateCtx n))))) := by
  refine EvaluatesTo.op_applyVals (ctx := ctx) (env := []) (name := "bind")
    (args := [lift (Term.nat n), identityContinuation])
    (values := [Val.mk (MTy NatTy) (ofM NatTy (Pure.pure (some (Ty.ofNat stateCtx n)))),
      Val.mk (.func [NatTy] (MTy NatTy)) identityContinuationValue])
    (oper := bindOp) rfl ?_ ?_
  · constructor
    · exact lift_eval_val n
    · constructor
      · simpa [identityContinuation] using
          (EvaluatesTo.prim (ctx := ctx) (env := []) (.func [NatTy] (MTy NatTy))
            identityContinuationValue)
      · exact EvaluatesToAll.nil
  · set_option linter.unusedSimpArgs false in
      simp [Op.applyVals, bindOp, bindShape?, Op.Signature.apply, Op.Signature.eagerBody,
        Op.Body.eager, Op.Body.applyVals, MTy, NatTy, ofM, toM, type_m,
        identityContinuationValue, Ty.applyUnary?]

end Zag.Test.Monad
