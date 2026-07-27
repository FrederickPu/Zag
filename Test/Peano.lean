import Lib.Peano.Defs

namespace Zag

private abbrev comparisonCtx : PrimitiveCtx :=
  .ofPrims [
    .of "Nat" Nat,
    .of "Bool" Bool
  ]

private instance : Peano.Types comparisonCtx where
  natType := by rfl
  boolType := by rfl

private def optionNat (value : Option Nat) : Val comparisonCtx :=
  .mk (.option Peano.NatTy) (cast (by
    rw [Ty.type.eq_3, Ty.type.eq_2, Peano.Types.natType]
    rfl : Option Nat = Ty.type comparisonCtx (.option Peano.NatTy)) value)

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
      (fun i : Fin 2 => if i = 0 then Peano.NatTy else Peano.BoolTy) = none := by
  simp [Op.compare]

example :
    Op.applyVals (Op.compare Val.primEq?)
      [optionNat none, optionNat (some 1)] = none := by
  simp [Op.applyVals, Op.compare, Op.Body.applyVals, optionNat, Val.primEq?, Val.asNat?,
    Val.asBool?, Val.as?]

example :
    Op.applyVals (Op.compare (primCtx := comparisonCtx) (fun _ _ => none))
      [Val.nat 1, Val.nat 1] = none := by
  simp [Op.applyVals, Op.compare, Op.Body.applyVals]

end Zag
