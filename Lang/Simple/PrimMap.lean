import Lang.SSA

/-!
  Leaf-driven SSA rewrite engine (for WA/HL-style tables).

  `apply` is executable. There is **no** `correct` theorem until
  `EvalGoSimulate` is proved — do not add a sorry'd claim.
-/

namespace Lang.Simple.PrimMap

open Zag
open Zag.Lang.SSA

abbrev Rewrite (A : Ctx) :=
  List (SSAValue A.primCtx) →
    StateM (List (String × SSAValue A.primCtx)) (SSAValue A.primCtx)

structure PrimMap (A C : Ctx) where
  primMap : String → Option String
  funcMap : String → Option (Rewrite A)
  opMap : String → Option String

def tyMap {A C : Ctx} (m : PrimMap A C) : Ty → Ty
  | .prim n => match m.primMap n with | some n' => .prim n' | none => .prim n
  | .struct ts => .struct (ts.map (tyMap m))
  | .func as r => .func (as.map (tyMap m)) (tyMap m r)
  | .m t => .m (tyMap m t)
  | .option t => .option (tyMap m t)
  | .union ts => .union (ts.map (tyMap m))
  | .var i => .var i

mutual

partial def applyValue {A C : Ctx} (m : PrimMap A C) :
    SSAValue C.primCtx →
      StateM (List (String × SSAValue A.primCtx)) (Option (SSAValue A.primCtx))
  | .raw (.primFunc name) => pure (some (.primFunc name))
  | .raw (.var idx) => pure (some (.raw (.var idx)))
  | .raw (.mkStruct tys) => pure (some (.raw (.mkStruct (tys.map (tyMap m)))))
  | .raw (.structProj tys idx) =>
      let tys' := tys.map (tyMap m)
      if h : idx.val < tys'.length then
        pure (some (.raw (.structProj tys' ⟨idx.val, h⟩)))
      else pure none
  | .raw (.prim _ _) => pure none
  | .raw _ => pure none
  | .var name => pure (some (.var name))
  | .call fn args => do
      let fn' ← applyValue m fn
      let args' ← applyValues m args
      match fn', args' with
      | some (.primFunc name), some argsA =>
          match m.funcMap name with
          | some rw => pure (some (← rw argsA))
          | none => pure (some (.call (.primFunc name) argsA))
      | some fnA, some argsA => pure (some (.call fnA argsA))
      | _, _ => pure none
  | .struct tys fields => do
      match ← applyValues m fields with
      | some fs => pure (some (.struct (tys.map (tyMap m)) fs))
      | none => pure none
  | .field tys idx value => do
      match ← applyValue m value with
      | some v =>
          let tys' := tys.map (tyMap m)
          if h : idx.val < tys'.length then pure (some (.field tys' ⟨idx.val, h⟩ v))
          else pure none
      | none => pure none
  | .op name args => do
      match ← applyValues m args with
      | some as => pure (some (.op ((m.opMap name).getD name) as))
      | none => pure none
  | .block resultTy body =>
      match applyExpr m body with
      | some b => pure (some (.block (tyMap m resultTy) b))
      | none => pure none
  | .phi _ _ => pure none
  | .loopBody varCtx state init resultTy body => do
      match (← applyValues m init), applyExpr m body with
      | some inits, some body' =>
          let state' := state.map fun v => { name := v.name, ty := tyMap m v.ty }
          pure (some (.loopBody varCtx state' inits (tyMap m resultTy) body'))
      | _, _ => pure none

partial def applyValues {A C : Ctx} (m : PrimMap A C) :
    List (SSAValue C.primCtx) →
      StateM (List (String × SSAValue A.primCtx)) (Option (List (SSAValue A.primCtx)))
  | [] => pure (some [])
  | v :: vs => do
      match (← applyValue m v), (← applyValues m vs) with
      | some x, some xs => pure (some (x :: xs))
      | _, _ => pure none

partial def applyExpr {A C : Ctx} (m : PrimMap A C) :
    SSAExpr C.primCtx → Option (SSAExpr A.primCtx)
  | .ret value =>
      let (result, bindings) := StateT.run (applyValue m value) []
      match result with
      | some v => some (bindings.reverse.foldr (fun b e => .let_ b.1 b.2 e) (.ret v))
      | none => none
  | .let_ name value next =>
      let (result, bindings) := StateT.run (applyValue m value) []
      match result, applyExpr m next with
      | some v, some n =>
          some (bindings.reverse.foldr (fun b e => .let_ b.1 b.2 e) (.let_ name v n))
      | _, _ => none
  | .seq a b =>
      match applyExpr m a, applyExpr m b with
      | some x, some y => some (.seq x y)
      | _, _ => none
  | .ite c t e =>
      let (result, bindings) := StateT.run (applyValue m c) []
      match result, applyExpr m t, applyExpr m e with
      | some c', some t', some e' =>
          some (bindings.reverse.foldr (fun b body => .let_ b.1 b.2 body) (.ite c' t' e'))
      | _, _, _ => none
  | .yield vs =>
      let (result, bindings) := StateT.run (applyValues m vs) []
      match result with
      | some vs' => some (bindings.reverse.foldr (fun b e => .let_ b.1 b.2 e) (.yield vs'))
      | none => none

end

def apply {A C : Ctx} (m : PrimMap A C) (e : SSAExpr C.primCtx) :
    Option (SSAExpr A.primCtx) :=
  applyExpr m e

-- Correctness of `apply` is not stated here until EvalGoSimulate exists.
-- Do not add a trivial `True` placeholder named like a proof obligation.

end Lang.Simple.PrimMap
