import Lib.Peano.Defs
import Meta.UnifyType

namespace Zag

open Lib.Peano
open Pr.TypeUnification

/- The typing rules handle symbolic literal payloads without inspecting them. -/
example (m n : Nat) :
    Term.hasType peanoCtx [] (.op "lt" [Term.nat m, Term.nat n]) Peano.BoolTy := by
  refine Term.hasType.binOp ?_ (Term.hasType.prim _) (Term.hasType.prim _)
  unfold OpCtx.outTy?
  rw [Peano.Model.ltOp]
  simp [Op.compare, Op.fixed]

example (condition : Bool) (m n : Nat) :
    Term.hasType peanoCtx [] (Term.ite (Term.bool condition) (Term.nat m) (Term.nat n))
      Peano.NatTy := by
  exact Term.hasType.ite (Term.hasType.prim _) (Term.hasType.prim _) (Term.hasType.prim _)

example (m n : Nat) :
    Term.hasType peanoCtx [("add", .func [Peano.NatTy, Peano.NatTy] Peano.NatTy)]
      (.app (.var "add") [Term.nat m, Term.nat n])
      Peano.NatTy := by
  refine Term.hasType.app (argsTy := [Peano.NatTy, Peano.NatTy]) ?_ rfl ?_
  · exact Term.hasType.var (by rfl)
  · intro idx
    match idx with
    | ⟨0, _⟩ => exact Term.hasType.prim _
    | ⟨1, _⟩ => exact Term.hasType.prim _
    | ⟨k + 2, h⟩ =>
        have : False := by
          change k + 2 < 2 at h
          omega
        contradiction

private abbrev comparisonCtx : PrimitiveCtx :=
  .ofPrims [
    .of "Nat" Nat,
    .of "Bool" Bool
  ]

private instance : Peano.Types comparisonCtx where
  natType := by rfl
  boolType := by rfl

private def opaqueFn (name : String) : Val comparisonCtx :=
  .blockRef name [] Peano.NatTy

example : Val.primEq? (Val.nat (primCtx := comparisonCtx) 0) (Val.bool false) = none := by
  have hboolNat : (Val.bool (primCtx := comparisonCtx) false).asNat? = none := by
    simp only [Val.asNat?, Val.bool, Val.as?]
    simp
  have hnatBool : (Val.nat (primCtx := comparisonCtx) 0).asBool? = none := by
    simp only [Val.asBool?, Val.nat, Val.as?]
    simp
  simp [Val.primEq?, hboolNat, hnatBool]

example : Val.primLt? (Val.bool (primCtx := comparisonCtx) false) (Val.nat 1) = none := by
  have hboolNat : (Val.bool (primCtx := comparisonCtx) false).asNat? = none := by
    simp only [Val.asNat?, Val.bool, Val.as?]
    simp
  have hnatBool : (Val.nat (primCtx := comparisonCtx) 1).asBool? = none := by
    simp only [Val.asBool?, Val.nat, Val.as?]
    simp
  simp [Val.primLt?, hboolNat, hnatBool]

example :
    (Op.compare (primCtx := comparisonCtx) Val.primEq?).out
      [Peano.NatTy, Peano.BoolTy] = none := by
  simp [Op.compare, Op.fixed]

example :
  Op.applyValsAt "compare" (Op.compare Val.primEq?)
      [opaqueFn "left", opaqueFn "right"] = none := by
  simp [Op.applyValsAt, Op.compare, Op.fixed, Op.Body.applyVals, opaqueFn, Val.primEq?,
    Val.asNat?, Val.asBool?, Val.as?]

example :
    Op.applyValsAt "compare" (Op.compare (primCtx := comparisonCtx) (fun _ _ => none))
      [Val.nat 1, Val.nat 1] = none := by
  simp [Op.applyValsAt, Op.compare, Op.fixed, Op.Body.applyVals]

end Zag
