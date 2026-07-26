import Zag.Theory
import Meta.Induction

namespace Zag.Lib.Peano

open Zag
open Zag.Pr.Induction

abbrev natCtx : PrimitiveCtx := [("Nat", Nat), ("Bool", Bool)]
abbrev NatTy : Ty := .prim "Nat"

def natBinaryFunc (f : Nat → Nat → Nat) : PrimFunc natCtx where
  args := ["Nat", "Nat"]
  out := "Nat"
  hprim := by
    intro x hx
    simp at hx
    simp [natCtx]
    exact Or.inl hx
  interp := fun
    | [lhsVal, rhsVal] => do
        let lhs ← lhsVal.asNat?
        let rhs ← rhsVal.asNat?
        some (Val.nat (f lhs rhs))
    | _ => none

def succFunc : PrimFunc natCtx where
  args := ["Nat"]
  out := "Nat"
  hprim := by
    intro x hx
    simp at hx
    simp [natCtx]
    exact Or.inl hx
  interp := fun
    | [v] => do
        let n ← v.asNat?
        some (Val.nat (n + 1))
    | _ => none

def natFuncCtx : PrimFuncCtx natCtx :=
  [ ("add", natBinaryFunc Nat.add)
  , ("sub", natBinaryFunc Nat.sub)
  , ("mul", natBinaryFunc Nat.mul)
  , ("div", natBinaryFunc Nat.div)
  , ("succ", succFunc)
  ]

def natOpCtx : OpCtx natCtx :=
  [ ("lt", Op.compare Val.primLt?)
  , ("gt", Op.compare Val.primGt?)
  ]

abbrev peanoCtx : Ctx :=
  { primCtx := natCtx
  , primFuncCtx := natFuncCtx
  , opCtx := natOpCtx }

def succName : String := "succ"

private theorem get_succ : PrimFuncCtx.get? natFuncCtx "succ" = some succFunc := rfl

private theorem asNat?_eq_some {v : Val natCtx} {k : Nat}
    (h : v.asNat? = some k) : v = Val.nat k := by
  unfold Val.asNat? Val.as? at h
  by_cases hty : v.ty = .prim "Nat"
  · simp [hty] at h
    cases v with
    | mk ty val =>
        simp at hty; subst hty
        rw [← Val.mk_ofNat]; congr 1
        rw [← h]; simp [Ty.ofNat, Ty.toNat]
  · simp [hty] at h

private theorem apply_succ_nat (m : Nat) :
    PrimFunc.apply succFunc [Val.nat (primCtx := natCtx) m] = some (Val.nat (m + 1)) := by
  simp [PrimFunc.apply, succFunc]

/-- `app succ [t]` evaluates like `app succ [nat m]` when `t ↝ m`. -/
private theorem eval_succ_congr (t : Term natCtx) (m : Nat)
    (ht : Term.eval peanoCtx [] t = some (Val.nat m)) :
    Term.eval peanoCtx [] (.app (.primFunc "succ") [t]) =
      Term.eval peanoCtx [] (.app (.primFunc "succ") [Term.nat m]) := by
  have ht' : Term.evalGo peanoCtx [] [] t = some (Val.nat m) := ht
  have hn : Term.evalGo peanoCtx [] [] (Term.nat m) = some (Val.nat m) := by
    simp [Term.evalGo, Term.nat]
  have hmap_t : List.mapM (Term.evalGo peanoCtx [] []) [t] = some [Val.nat m] := by
    simp [List.mapM, List.mapM.loop, ht']
  have hmap_n : List.mapM (Term.evalGo peanoCtx [] []) [Term.nat m] = some [Val.nat m] := by
    simp [List.mapM, List.mapM.loop, hn]
  simp only [Term.eval, Term.evalGo, Term.evalList, peanoCtx, get_succ, hmap_t, hmap_n]

private theorem eval_succ_natLit (m : Nat) :
    Term.eval peanoCtx [] (.app (.primFunc "succ") [Term.nat m]) =
      some (Val.nat (m + 1)) := by
  have hn : Term.evalGo peanoCtx [] [] (Term.nat m) = some (Val.nat m) := by
    simp [Term.evalGo, Term.nat]
  have hmap : List.mapM (Term.evalGo peanoCtx [] []) [Term.nat m] = some [Val.nat m] := by
    simp [List.mapM, List.mapM.loop, hn]
  simp only [Term.eval, Term.evalGo, Term.evalList, peanoCtx, get_succ, hmap]
  exact apply_succ_nat m

private theorem eval_succ_inv_go (t : Term natCtx) (v : Val natCtx)
    (hv : Term.eval peanoCtx [] (.app (.primFunc "succ") [t]) = some v) :
    ∃ m, Term.eval peanoCtx [] t = some (Val.nat m) ∧ v = Val.nat (m + 1) := by
  have hv' : Term.evalGo peanoCtx [] [] (.app (.primFunc "succ") [t]) = some v := hv
  simp only [Term.evalGo, Term.evalList, peanoCtx, get_succ] at hv'
  cases ht : Term.evalGo peanoCtx [] [] t with
  | none =>
      have hmap : List.mapM (Term.evalGo peanoCtx [] []) [t] = (none : Option (List (Val natCtx))) := by
        simp [List.mapM, List.mapM.loop, ht]
      simp [hmap] at hv'
  | some vt =>
      have hmap : List.mapM (Term.evalGo peanoCtx [] []) [t] = some [vt] := by
        simp [List.mapM, List.mapM.loop, ht]
      simp only [hmap] at hv'
      have happly : PrimFunc.apply succFunc [vt] = some v := by simpa using hv'
      simp only [PrimFunc.apply, succFunc] at happly
      split at happly
      · cases hn : vt.asNat? with
        | none => simp [hn] at happly
        | some m =>
            simp [hn] at happly
            cases happly
            exact ⟨m, by
              simp only [Term.eval]
              have : vt = Val.nat m := asNat?_eq_some hn
              rw [this] at ht
              exact ht, rfl⟩
      · simp at happly

theorem succ_spec : SuccSpec peanoCtx succName where
  hasType_app := fun varCtx t ht => by
    have hf0 := Term.hasType.primFunc (ctx := peanoCtx) (varCtx := varCtx)
      (idx := ⟨4, by decide⟩)
    -- dsimp reduces [4] to ("succ", succFunc)
    have hf : Term.hasType peanoCtx varCtx (.primFunc succName)
        (.func [.prim "Nat"] (.prim "Nat")) := by
      dsimp [peanoCtx, natFuncCtx, PrimFunc.ty, succFunc, succName] at hf0 ⊢
      exact hf0
    exact Term.hasType.app hf rfl (fun idx => by
      cases idx using Fin.cases with
      | zero => exact ht
      | succ idx => exact Fin.elim0 idx)
  eval_succ := fun t m ht => by
    rw [show succName = "succ" from rfl]
    rw [eval_succ_congr t m ht, eval_succ_natLit m]
  eval_succ_inv := fun t v hv => by
    rw [show succName = "succ" from rfl] at hv
    exact eval_succ_inv_go t v hv

theorem hsucc (m : Nat) :
    Term.eval peanoCtx [] (.app (.primFunc succName) [Term.nat m]) =
      some (Val.nat (m + 1)) :=
  succ_spec.eval_succ (Term.nat m) m (by simp [Term.eval, Term.evalGo, Term.nat])

end Zag.Lib.Peano
