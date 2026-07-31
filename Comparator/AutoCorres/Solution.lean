import Comparator.AutoCorres.Main
import Lang.AutoCorres.ML.autocorres

/-!
# AutoCorres Comparator solution

Only this independently built module imports the untrusted ML pass
implementations. Comparator checks each definition and dependent theorem against
the declarations in `Challenge`.
-/

namespace Comparator.AutoCorres

open Zag.Lang.AutoCorres

def simplConv
    (checkTermination : Bool)
    (env : Simpl.Body State Proc Fault)
    {source : Simpl.Com State Proc Fault}
    (supported : SimplConv.Kernel.Supported source) :
    SimplConv.Kernel.Target State :=
  (ML.SimplConv.simplConv checkTermination env supported).target

theorem simplConv_correct
    (checkTermination : Bool)
    (env : Simpl.Body State Proc Fault)
    {source : Simpl.Com State Proc Fault}
    (supported : SimplConv.Kernel.Supported source) :
    L1.L1Corres checkTermination env
      (simplConv checkTermination env supported).denote source :=
  (ML.SimplConv.simplConv checkTermination env supported).corres

def localVarExtract
    (model : LocalVarExtract.Kernel.StateModel Full Locals Globals)
    {source : LocalVarExtract.Kernel.Source.Syntax Full Locals Globals}
    (supported : LocalVarExtract.Kernel.Supported source) :
    LocalVarExtract.Kernel.Target.Syntax Locals Globals :=
  (ML.LocalVarExtract.extract model supported).target

theorem localVarExtract_correct
    (model : LocalVarExtract.Kernel.StateModel Full Locals Globals)
    {source : LocalVarExtract.Kernel.Source.Syntax Full Locals Globals}
    (supported : LocalVarExtract.Kernel.Supported source) :
    LocalVarExtract.Kernel.Extracts model
      (localVarExtract model supported) source :=
  (ML.LocalVarExtract.extract model supported).corres

def heapLift
    {ConcreteState AbstractState Exception Result : Type}
    (stateMap : ConcreteState -> AbstractState)
    {source : HeapLift.Kernel.Source ConcreteState Exception Result}
    (supported : HeapLift.Kernel.Supported stateMap source) :
    HeapLift.Kernel.Target AbstractState Exception Result :=
  (ML.HeapLift.transform supported).target

theorem heapLift_correct
    {ConcreteState AbstractState Exception Result : Type}
    (stateMap : ConcreteState -> AbstractState)
    {source : HeapLift.Kernel.Source ConcreteState Exception Result}
    (supported : HeapLift.Kernel.Supported stateMap source) :
    HeapLift.L2Tcorres stateMap
      (heapLift stateMap supported).denote source.denote :=
  (ML.HeapLift.transform supported).correctness

def wordAbstract
    {Argument : WordAbstract.Kernel.ValueType}
    {State : Type}
    {Exception Result : WordAbstract.Kernel.ValueType}
    (source : WordAbstract.Kernel.Source.Syntax Argument State Exception Result) :
    WordAbstract.Kernel.Target.Syntax Argument State Exception Result :=
  (ML.WordAbstract.transformSource source).target

theorem wordAbstract_correct
    {Argument : WordAbstract.Kernel.ValueType}
    {State : Type}
    {Exception Result : WordAbstract.Kernel.ValueType}
    (source : WordAbstract.Kernel.Source.Syntax Argument State Exception Result) :
    forall concreteArgument,
      WordAbstract.corresTA (fun _ => True)
        (WordAbstract.Kernel.typeMap Result).abstract
        (WordAbstract.Kernel.typeMap Exception).abstract
        ((wordAbstract source).denote
          ((WordAbstract.Kernel.typeMap Argument).abstract concreteArgument))
        (source.denote concreteArgument) :=
  (ML.WordAbstract.transformSource source).corres

def typeStrengthen
    {State Result : Type}
    {carrier : TypeStrengthen.Kernel.Carrier}
    {source : TypeStrengthen.Kernel.Source.Syntax State Result}
    (supported : TypeStrengthen.Kernel.Supported carrier source) :
    TypeStrengthen.Kernel.Target.Syntax carrier State Result :=
  (ML.TypeStrengthen.strengthen supported).target

theorem typeStrengthen_correct
    {State Result : Type}
    {carrier : TypeStrengthen.Kernel.Carrier}
    {source : TypeStrengthen.Kernel.Source.Syntax State Result}
    (supported : TypeStrengthen.Kernel.Supported carrier source) :
    forall Exception : Type,
      L2.call (Exception := Exception) (source.denote ()) =
        TypeStrengthen.Kernel.embed (Exception := Exception) carrier
          (typeStrengthen supported).denote :=
  (ML.TypeStrengthen.strengthen supported).exact

theorem finalChainCorrect :
    forall {ConcreteState Proc Fault L2State L2Exception L2Result HLState
      WAException WAResult TargetException : Type}
      {cL1 : L1.L1Program ConcreteState}
      {cL2 : L2.L2Program L2State L2Exception L2Result}
      {cHL : L2.L2Program HLState L2Exception L2Result}
      {cWA : L2.L2Program HLState WAException WAResult}
      {target : L2.L2Program HLState TargetException WAResult}
      {source : Simpl.Com ConcreteState Proc Fault}
      {checkTermination : Bool}
      {env : Simpl.Body ConcreteState Proc Fault}
      {stateProjectL2 : ConcreteState -> L2State}
      {returnExtractL2 : ConcreteState -> L2Result}
      {exceptionExtractL2 : ConcreteState -> L2Exception}
      {preconditionL2 : ConcreteState -> Prop}
      {stateProjectHL : L2State -> HLState}
      {preconditionWA : HLState -> Prop}
      {returnExtractWA : L2Result -> WAResult}
      {exceptionExtractWA : L2Exception -> WAException},
      L1.L1Corres checkTermination env cL1 source ->
      L2.L2Corres stateProjectL2 returnExtractL2
        exceptionExtractL2 preconditionL2 cL2 cL1 ->
      HeapLift.L2Tcorres stateProjectHL cHL cL2 ->
      WordAbstract.corresTA preconditionWA returnExtractWA
        exceptionExtractWA cWA cHL ->
      L2.call (Exception := TargetException) cWA = target ->
      acCorres
        (stateProjectHL ∘ stateProjectL2)
        checkTermination env
        (returnExtractWA ∘ returnExtractL2)
        (fun state => preconditionL2 state ∧
          preconditionWA (stateProjectHL (stateProjectL2 state)))
        target source :=
  fun l1Corres l2Corres heapLiftCorres wordAbstractCorres typeStrengthen => by
    simpa only [acCorres, Zag.Lang.AutoCorres.ac_corres] using
      ac_corres_chain l1Corres l2Corres heapLiftCorres wordAbstractCorres
        typeStrengthen

end Comparator.AutoCorres
