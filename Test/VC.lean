import Meta.Eval.VC

namespace Zag.Test.VC

open scoped Std.Do

/-- Relational triples retain arbitrary `PostShape` state and exception layers without requiring
a total Lean evaluator. A pure relation leaves those state arguments unchanged. -/
example {α σ : Type} (relation : α → Prop) (value : α) (initial : σ)
    (hrelation : relation value) :
  Zag.VC.Triple (ps := .except String (.arg σ .pure)) relation
      (fun state => ULift.up (state = initial))
      (Std.Do.PostCond.noThrow fun result state =>
        ULift.up (result = value ∧ state = initial)) := by
  zspec hrelation
  zintro hstate
  simp_all

example {α : Type} (relation : α → Prop) (P : Prop) (Q : α → Prop) :
    Zag.VC.Triple (ps := .pure) relation (Std.Do.SPred.pure P)
        (Std.Do.PostCond.noThrow fun value => Std.Do.SPred.pure (Q value)) ↔
      (P → ∃ value, relation value ∧ Q value) :=
  Zag.VC.Triple.iff_pure

example {α σ : Type} (relation : σ → α → σ → Prop)
    (initial final : σ) (value : α) (hrelation : relation initial value final) :
    Zag.VC.StateTriple relation
      (fun state => ULift.up (state = initial))
      (Std.Do.PostCond.noThrow fun result state =>
        ULift.up (result = value ∧ state = final)) := by
  zspec hrelation
  zintro hinitial
  simp_all

/-- An exact finite StateM run is adapted to the generic term derivation before consequence. -/
example {σ : Type} (primCtx : PrimitiveCtx) (opCtx : OpCtx primCtx (StateM σ))
    (blockCtx : BlockCtx primCtx) (env : Env primCtx) (term : Term primCtx)
    (initial final : σ) (value : Val primCtx)
    (hrun : EvalTriple.State.EvaluatesTo primCtx opCtx blockCtx env term
      initial value final) :
    Zag.EvaluatesTo (Machine.stateCtx primCtx opCtx blockCtx) env term
      (fun state => ULift.up (state = initial))
      (Std.Do.PostCond.noThrow fun result state =>
        ULift.up (result = value ∧ state = final)) := by
  zspec hrun
  · zintro hinitial
    simp_all
  · simp [EvalTriple.Singleton.statePost, Std.Do.PostCond.entails]

/-- The call adapter targets the surface call itself, with the public parameter order unchanged. -/
example {σ : Type} (primCtx : PrimitiveCtx) (opCtx : OpCtx primCtx (StateM σ))
    (blockCtx : BlockCtx primCtx) (name : String) (args : List (Term primCtx))
    (initial final : σ) (value : Val primCtx)
    (hrun : EvalTriple.State.EvaluatesCall primCtx opCtx blockCtx name args
      initial value final) :
    Zag.EvaluatesCall (Machine.stateCtx primCtx opCtx blockCtx) name args
      (fun state => ULift.up (state = initial))
      (Std.Do.PostCond.noThrow fun result state =>
        ULift.up (result = value ∧ state = final)) := by
  zspec hrun
  · zintro hinitial
    simp_all
  · simp [EvalTriple.Singleton.statePost, Std.Do.PostCond.entails]

end Zag.Test.VC
