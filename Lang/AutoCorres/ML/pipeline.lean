import Lang.AutoCorres.Pipeline

/-!
# Executable adjacent-phase adapters

Both adapters are total over source-indexed support and construct their
whole-denotation equalities internally.
-/

namespace Zag.Lang.AutoCorres.ML.Pipeline

open Zag.Lang.AutoCorres

private theorem behavior_ext {State Result : Type}
    {left right : Behavior State Result}
    (results : left.results = right.results)
    (failed : left.failed = right.failed) : left = right := by
  cases left
  cases right
  cases results
  cases failed
  rfl

namespace HeapToWord

/-- Reify an actual HeapLift guarded read as a closed WordAbstract source. -/
noncomputable def adapt {width : Nat} {State : Type}
    {target : HeapLift.Kernel.Target State (BitVec width) (BitVec width)}
    (supported : Zag.Lang.AutoCorres.Pipeline.HeapToWord.Supported width target) :
    Zag.Lang.AutoCorres.Pipeline.HeapToWord.Certificate width target :=
  match supported with
  | .guardedGets (rewriteGuard := rewriteGuard) (expressionGuard := expressionGuard)
      (read := read) (names := names) expression
      rewriteHolds expressionHolds expressionExact =>
      { source := .gets expression names
        exact := by
          funext state
          simp only [HeapLift.Kernel.Target.denote,
            WordAbstract.Kernel.Source.Syntax.denote]
          apply behavior_ext
          · funext result
            apply propext
            rcases result with ⟨outcome, post⟩
            change ((outcome, post) ∈
                (L2.seq (L2.guard fun current =>
                  rewriteGuard current ∧ expressionGuard current)
                  (fun _ => L2.gets read names) state).results) ↔
              ((outcome, post) ∈
                (L2.gets (fun current => expression.eval () current) names
                  state).results)
            simp [expressionExact state, rewriteHolds state, expressionHolds state]
          · apply propext
            change (L2.seq (L2.guard fun current =>
                rewriteGuard current ∧ expressionGuard current)
                (fun _ => L2.gets read names) state).failed ↔
              (L2.gets (fun current => expression.eval () current) names
                state).failed
            simp [rewriteHolds state, expressionHolds state] }

end HeapToWord

namespace TypedHeapToWord

open WordAbstract.Kernel

/-- Reify the typed stateful HeapLift subset without changing its denotation. -/
noncomputable def adapt {Argument : ValueType} {State : Type}
    {exception result : ValueType}
    {target : HeapLift.Kernel.Target State
      (Source.Value exception) (Source.Value result)}
    (supported : @Zag.Lang.AutoCorres.Pipeline.TypedHeapToWord.Supported
      Argument State exception result target) :
    @Zag.Lang.AutoCorres.Pipeline.TypedHeapToWord.Certificate
      Argument State exception result target :=
  match supported with
  | .guardedGets (rewriteGuard := rewriteGuard)
      (expressionGuard := expressionGuard) (read := read) (names := names)
      expression rewriteHolds expressionHolds expressionExact =>
      { source := .gets expression names
        exact := by
          intro argument
          funext state
          simp only [HeapLift.Kernel.Target.denote, Source.Syntax.denote]
          apply behavior_ext
          · funext result
            apply propext
            rcases result with ⟨outcome, post⟩
            change ((outcome, post) ∈
                (L2.seq (L2.guard fun current =>
                  rewriteGuard current ∧ expressionGuard current)
                  (fun _ => L2.gets read names) state).results) ↔
              ((outcome, post) ∈
                (L2.gets (fun current => expression.eval argument current) names
                  state).results)
            simp [expressionExact argument state, rewriteHolds state,
              expressionHolds state]
          · apply propext
            change (L2.seq (L2.guard fun current =>
                rewriteGuard current ∧ expressionGuard current)
                (fun _ => L2.gets read names) state).failed ↔
              (L2.gets (fun current => expression.eval argument current) names
                state).failed
            simp [rewriteHolds state, expressionHolds state] }
  | .exact source equality =>
      { source := source, exact := equality }
  | .seq firstSupported nextSupported =>
      let first := adapt firstSupported
      let next := fun value => adapt (nextSupported value)
      { source := .seq first.source fun value => (next value).source
        exact := by
          intro argument
          simp only [HeapLift.Kernel.Target.denote, Source.Syntax.denote]
          rw [first.exact argument]
          congr 1
          funext value
          exact (next value).exact argument }

end TypedHeapToWord

namespace WordToStrengthen

/-- Reify a generated WordAbstract guard/read target as closed TS syntax. -/
noncomputable def adapt {width : Nat} {State : Type}
    {target : WordAbstract.Kernel.Target.Syntax .unit State (.word width) (.word width)}
    (supported : Zag.Lang.AutoCorres.Pipeline.WordToStrengthen.Supported width target) :
    Zag.Lang.AutoCorres.Pipeline.WordToStrengthen.Certificate width target :=
  match supported with
  | .guardedGets (guard := guard) (expression := expression) (names := names)
      test testExact =>
      { source := .seq (.guard fun _ state => test state)
          (.gets (fun _ state => expression.eval () state) names)
        supported := .optionSeq .optionGuard .optionRead
        exact := by
          funext state
          simp only [WordAbstract.Kernel.Target.Syntax.denote,
            TypeStrengthen.Kernel.Source.Term.denote]
          have guardEquality : (fun state => test state = true) = guard () := by
            funext current
            exact propext (testExact current)
          rw [guardEquality] }

end WordToStrengthen

end Zag.Lang.AutoCorres.ML.Pipeline
