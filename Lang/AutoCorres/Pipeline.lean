import Lang.AutoCorres.AutoCorres
import Lang.AutoCorres.SimplConv
import Lang.AutoCorres.LocalVarExtract

/-!
# Trusted interfaces for adjacent AutoCorres adapters

These interfaces cover only the first closed unsigned `guardedGets` path. Their
support is indexed by the actual preceding target and contains local evidence,
never a selected endpoint or whole-program equality.
-/

namespace Zag.Lang.AutoCorres.Pipeline

open Zag.Lang.AutoCorres

namespace HeapToWord

/-- Local evidence for reifying one actual HeapLift guarded read. -/
inductive Supported (width : Nat) {State : Type} :
    HeapLift.Kernel.Target State (BitVec width) (BitVec width) -> Type 1 where
  | guardedGets
      {rewriteGuard expressionGuard : State -> Prop}
      {read : State -> BitVec width} {names : List String}
      (expression : WordAbstract.Kernel.Source.Expr .unit State (.word width))
      (rewriteHolds : forall state, rewriteGuard state)
      (expressionHolds : forall state, expressionGuard state)
      (expressionExact : forall state, expression.eval () state = read state) :
      Supported width (.guardedGets rewriteGuard expressionGuard read names)

/-- A computed WordAbstract source equal to the exact HeapLift target. -/
structure Certificate (width : Nat) {State : Type}
    (target : HeapLift.Kernel.Target State (BitVec width) (BitVec width)) where
  source : WordAbstract.Kernel.Source.Syntax .unit State (.word width) (.word width)
  exact : target.denote = source.denote ()

end HeapToWord

namespace TypedHeapToWord

open WordAbstract.Kernel

/-- Typed structural evidence for the HeapLift fragment consumed by WordAbstract. -/
inductive Supported (Argument : ValueType) {State : Type} :
    {exception result : ValueType} ->
      HeapLift.Kernel.Target State (Source.Value exception) (Source.Value result) ->
        Type 1 where
  | guardedGets {exception result : ValueType}
      {rewriteGuard expressionGuard : State -> Prop}
      {read : State -> Source.Value result} {names : List String}
      (expression : Source.Expr Argument State result)
      (rewriteHolds : forall state, rewriteGuard state)
      (expressionHolds : forall state, expressionGuard state)
      (expressionExact : forall argument state,
        expression.eval argument state = read state) :
      Supported Argument (.guardedGets rewriteGuard expressionGuard read names)
  | exact {exception result : ValueType}
      {target : HeapLift.Kernel.Target State
        (Source.Value exception) (Source.Value result)}
      (source : Source.Syntax Argument State exception result)
      (equality : forall argument, target.denote = source.denote argument) :
      Supported Argument target
  | seq {exception middle result : ValueType}
      {first : HeapLift.Kernel.Target State
        (Source.Value exception) (Source.Value middle)}
      {next : Source.Value middle -> HeapLift.Kernel.Target State
        (Source.Value exception) (Source.Value result)}
      (firstSupported : @Supported Argument State exception middle first)
      (nextSupported : forall value,
        @Supported Argument State exception result (next value)) :
      Supported Argument (.seq first next)

/-- A typed WordAbstract source equal to the exact generated HeapLift target. -/
structure Certificate {Argument : ValueType} {State : Type}
    {exception result : ValueType}
    (target : HeapLift.Kernel.Target State
      (Source.Value exception) (Source.Value result)) where
  source : Source.Syntax Argument State exception result
  exact : forall argument, target.denote = source.denote argument

end TypedHeapToWord

namespace WordToStrengthen

/-- Boolean reification evidence for one generated WordAbstract guard/read target. -/
inductive Supported (width : Nat) {State : Type} :
    WordAbstract.Kernel.Target.Syntax .unit State (.word width) (.word width) ->
      Type 1 where
  | guardedGets
      {guard : Unit -> State -> Prop}
      {expression : WordAbstract.Kernel.Target.Expr .unit State (.word width)}
      {names : List String} (test : State -> Bool)
      (testExact : forall state, test state = true <-> guard () state) :
      Supported width (.seq (.guard guard) fun _ => .gets expression names)

/-- A computed closed TypeStrengthen source and its generated option support. -/
structure Certificate (width : Nat) {State : Type}
    (target : WordAbstract.Kernel.Target.Syntax .unit State (.word width) (.word width)) where
  source : TypeStrengthen.Kernel.Source.Closed State Nat Nat
  supported : TypeStrengthen.Kernel.Supported .option source
  exact : target.denote () = source.denote ()

end WordToStrengthen

/-- Generated artifacts for the unsigned path. -/
structure UnsignedTranslation (width : Nat) (checkTermination : Bool)
    (env : Simpl.Body Full Proc Fault) (source : Simpl.Com Full Proc Fault)
    (model : LocalVarExtract.Kernel.StateModel Full (BitVec width) Globals)
    (State : Type) where
  l1 : SimplConv.Kernel.Certificate checkTermination env source
  l2 : LocalVarExtract.Kernel.ClosedCertificate model l1.target
  initialLocals : BitVec width
  stateMap : Globals -> State
  heapLift : HeapLift.Kernel.Certificate stateMap (l2.target initialLocals)
  heapAdapter : HeapToWord.Certificate width heapLift.target
  wordAbstract : WordAbstract.Kernel.Certificate heapAdapter.source
  wordAdapter : WordToStrengthen.Certificate width wordAbstract.target
  typeStrengthen : TypeStrengthen.Kernel.ClosedCertificate .option wordAdapter.source

namespace UnsignedTranslation

/-- The canonical final chain, derived entirely from the generated artifacts. -/
noncomputable def chain
    {Full Proc Fault Globals State : Type}
    {width : Nat} {checkTermination : Bool}
    {env : Simpl.Body Full Proc Fault} {source : Simpl.Com Full Proc Fault}
    {model : LocalVarExtract.Kernel.StateModel Full (BitVec width) Globals}
    (translation : UnsignedTranslation width checkTermination env source model State) :
    ChainCertificate (L2State := Globals)
    (L2Exception := BitVec width) (L2Result := BitVec width)
    (HLState := State) (WAException := Nat)
    checkTermination env source
    (TypeStrengthen.Kernel.embed (Exception := Unit) .option
      translation.typeStrengthen.target.denote) :=
  { stateProjectL2 := model.projectGlobals
    returnExtractL2 := model.projectLocals
    exceptionExtractL2 := model.projectLocals
    preconditionL2 := fun state => model.projectLocals state = translation.initialLocals
    stateProjectHL := translation.stateMap
    preconditionWA := fun _ => True
    returnExtractWA := BitVec.toNat
    exceptionExtractWA := BitVec.toNat
    l1 := translation.l1.target.denote
    l1Corres := translation.l1.corres
    l2 := LocalVarExtract.Kernel.CanonicalTarget.Syntax.denote
      translation.l2.target translation.initialLocals
    l2Corres := translation.l2.corres translation.initialLocals
    heapLifted := translation.heapLift.target.denote
    heapLiftCorres := translation.heapLift.correctness
    wordAbstracted := translation.wordAbstract.target.denote ()
    wordAbstractCorres := by
      rw [translation.heapAdapter.exact]
      exact translation.wordAbstract.corres ()
    typeStrengthen := by
      rw [translation.wordAdapter.exact]
      exact translation.typeStrengthen.exact Unit }

end UnsignedTranslation

end Zag.Lang.AutoCorres.Pipeline
