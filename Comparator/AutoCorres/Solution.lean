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
    (supported : LocalVarExtract.Kernel.Supported model source) :
    LocalVarExtract.Kernel.Target.Syntax Locals Globals :=
  (ML.LocalVarExtract.extract model supported).target

theorem localVarExtract_correct
    (model : LocalVarExtract.Kernel.StateModel Full Locals Globals)
    {source : LocalVarExtract.Kernel.Source.Syntax Full Locals Globals}
    (supported : LocalVarExtract.Kernel.Supported model source) :
    forall locals,
      CorresXF model.projectGlobals
        (fun _ state => model.projectLocals state)
        (fun _ state => model.projectLocals state)
        (fun state => model.projectLocals state = locals)
        (LocalVarExtract.Kernel.Target.Syntax.denote
          (localVarExtract model supported) locals)
        source.denote :=
  (ML.LocalVarExtract.extract model supported).corres

/-- The explicitly closed Type0 extraction endpoint used by HeapLift. -/
def localVarExtractCanonical
    (model : LocalVarExtract.Kernel.StateModel Full Locals Globals)
    {source : LocalVarExtract.Kernel.Source.Syntax Full Locals Globals}
    (supported : LocalVarExtract.Kernel.Supported model source) :
    LocalVarExtract.Kernel.CanonicalTarget.Syntax Locals Globals :=
  (ML.LocalVarExtract.extractCanonical model supported).target

theorem localVarExtractCanonical_correct
    (model : LocalVarExtract.Kernel.StateModel Full Locals Globals)
    {source : LocalVarExtract.Kernel.Source.Syntax Full Locals Globals}
    (supported : LocalVarExtract.Kernel.Supported model source) :
    forall locals,
      CorresXF model.projectGlobals
        (fun _ state => model.projectLocals state)
        (fun _ state => model.projectLocals state)
        (fun state => model.projectLocals state = locals)
        (LocalVarExtract.Kernel.CanonicalTarget.Syntax.denote
          (localVarExtractCanonical model supported) locals)
        source.denote :=
  (ML.LocalVarExtract.extractCanonical model supported).corres

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
    CorresXF stateMap (fun result _ => result) (fun exception _ => exception)
      (fun _ => True) (heapLift stateMap supported).denote source.denote :=
  (ML.HeapLift.transform supported).correctness

noncomputable def heapToWord
    {width : Nat} {State : Type}
    {target : HeapLift.Kernel.Target State (BitVec width) (BitVec width)}
    (supported : Pipeline.HeapToWord.Supported width target) :
    Pipeline.HeapToWord.Certificate width target :=
  ML.Pipeline.HeapToWord.adapt supported

theorem heapToWord_exact
    {width : Nat} {State : Type}
    {target : HeapLift.Kernel.Target State (BitVec width) (BitVec width)}
    (supported : Pipeline.HeapToWord.Supported width target) :
    target.denote = (heapToWord supported).source.denote () :=
  (heapToWord supported).exact

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
      CorresXF id
        (fun result _ => (WordAbstract.Kernel.typeMap Result).abstract result)
        (fun exception _ =>
          (WordAbstract.Kernel.typeMap Exception).abstract exception)
        (fun _ => True)
        ((wordAbstract source).denote
          ((WordAbstract.Kernel.typeMap Argument).abstract concreteArgument))
        (source.denote concreteArgument) :=
  (ML.WordAbstract.transformSource source).corres

noncomputable def wordToStrengthen
    {width : Nat} {State : Type}
    {target : WordAbstract.Kernel.Target.Syntax .unit State
      (.word width) (.word width)}
    (supported : Pipeline.WordToStrengthen.Supported width target) :
    Pipeline.WordToStrengthen.Certificate width target :=
  ML.Pipeline.WordToStrengthen.adapt supported

theorem wordToStrengthen_exact
    {width : Nat} {State : Type}
    {target : WordAbstract.Kernel.Target.Syntax .unit State
      (.word width) (.word width)}
    (supported : Pipeline.WordToStrengthen.Supported width target) :
    target.denote () = (wordToStrengthen supported).source.denote () :=
  (wordToStrengthen supported).exact

def typeStrengthenClosed
    {State InnerException Result : Type}
    {carrier : TypeStrengthen.Kernel.Carrier}
    {source : TypeStrengthen.Kernel.Source.Closed State InnerException Result}
    (supported : TypeStrengthen.Kernel.Supported carrier source) :
    TypeStrengthen.Kernel.Target.Syntax carrier State Result :=
  (ML.TypeStrengthen.strengthenClosed supported).target

theorem typeStrengthenClosed_exact
    {State InnerException Result : Type}
    {carrier : TypeStrengthen.Kernel.Carrier}
    {source : TypeStrengthen.Kernel.Source.Closed State InnerException Result}
    (supported : TypeStrengthen.Kernel.Supported carrier source) :
    forall OuterException : Type,
      L2.call (Exception := OuterException) (source.denote ()) =
        TypeStrengthen.Kernel.embed (Exception := OuterException) carrier
          (typeStrengthenClosed supported).denote :=
  (ML.TypeStrengthen.strengthenClosed supported).exact

def typeStrengthen
    {State Result : Type}
    {carrier : TypeStrengthen.Kernel.Carrier}
    {source : TypeStrengthen.Kernel.Source.Syntax State Result}
    (supported : TypeStrengthen.Kernel.Supported carrier source) :
    TypeStrengthen.Kernel.Target.Syntax carrier State Result :=
  typeStrengthenClosed supported

theorem typeStrengthen_exact
    {State Result : Type}
    {carrier : TypeStrengthen.Kernel.Carrier}
    {source : TypeStrengthen.Kernel.Source.Syntax State Result}
    (supported : TypeStrengthen.Kernel.Supported carrier source) :
    forall Exception : Type,
      L2.call (Exception := Exception) (source.denote ()) =
        TypeStrengthen.Kernel.embed (Exception := Exception) carrier
          (typeStrengthen supported).denote :=
  typeStrengthenClosed_exact supported

theorem typeStrengthen_correct
    {State Result : Type}
    {carrier : TypeStrengthen.Kernel.Carrier}
    {source : TypeStrengthen.Kernel.Source.Syntax State Result}
    (supported : TypeStrengthen.Kernel.Supported carrier source)
    (Exception : Type) (exceptionMap : Unit -> State -> Exception) :
    CorresXF id (fun result _ => result) exceptionMap
      (fun _ => True)
      (TypeStrengthen.Kernel.embed (Exception := Exception) carrier
        (typeStrengthen supported).denote)
      (source.denote ()) :=
  corresXF_from_L2_call exceptionMap
    (typeStrengthen_exact supported Exception)

noncomputable def translateUnsignedSupported
    (width : Nat) (checkTermination : Bool)
    (env : Simpl.Body Full Proc Fault) (source : Simpl.Com Full Proc Fault)
    (model : LocalVarExtract.Kernel.StateModel Full (BitVec width) Globals)
    (State : Type)
    (simplSupported : SimplConv.Kernel.Supported source)
    (lveSupported : LocalVarExtract.Kernel.Supported model
      (simplConv checkTermination env simplSupported))
    (initialLocals : BitVec width)
    (stateMap : Globals -> State)
    (heapSupported : HeapLift.Kernel.Supported stateMap
      ((localVarExtractCanonical model lveSupported) initialLocals))
    (heapToWordSupported : Pipeline.HeapToWord.Supported width
      (heapLift stateMap heapSupported))
    (wordToStrengthenSupported : Pipeline.WordToStrengthen.Supported width
      (wordAbstract (heapToWord heapToWordSupported).source)) :
    Pipeline.UnsignedTranslation width checkTermination env source model State :=
  let supported : ML.AutoCorres.UnsignedSupported width checkTermination
      env source model State :=
    { l2 :=
        { l1 :=
            { simplConv := simplSupported
              localVarExtract := lveSupported }
          initialLocals := initialLocals
          stateMap := stateMap
          heapLift := heapSupported }
      heapToWord := heapToWordSupported
      wordToStrengthen := wordToStrengthenSupported }
  ML.AutoCorres.translateUnsignedSupported width checkTermination
    env source model State supported

theorem translateUnsignedSupported_spec
    (width : Nat) (checkTermination : Bool)
    (env : Simpl.Body Full Proc Fault) (source : Simpl.Com Full Proc Fault)
    (model : LocalVarExtract.Kernel.StateModel Full (BitVec width) Globals)
    (State : Type)
    (simplSupported : SimplConv.Kernel.Supported source)
    (lveSupported : LocalVarExtract.Kernel.Supported model
      (simplConv checkTermination env simplSupported))
    (initialLocals : BitVec width)
    (stateMap : Globals -> State)
    (heapSupported : HeapLift.Kernel.Supported stateMap
      ((localVarExtractCanonical model lveSupported) initialLocals))
    (heapToWordSupported : Pipeline.HeapToWord.Supported width
      (heapLift stateMap heapSupported))
    (wordToStrengthenSupported : Pipeline.WordToStrengthen.Supported width
      (wordAbstract (heapToWord heapToWordSupported).source)) :
    let result := translateUnsignedSupported width checkTermination env source
      model State simplSupported lveSupported initialLocals stateMap
      heapSupported heapToWordSupported wordToStrengthenSupported
    result.l1.target = simplConv checkTermination env simplSupported ∧
    result.l2.target = localVarExtractCanonical model lveSupported ∧
    result.initialLocals = initialLocals ∧
    result.stateMap = stateMap ∧
    result.heapLift.target = heapLift stateMap heapSupported ∧
    result.heapAdapter.source = (heapToWord heapToWordSupported).source ∧
    result.wordAbstract.target =
      wordAbstract (heapToWord heapToWordSupported).source ∧
    result.wordAdapter.source =
      (wordToStrengthen wordToStrengthenSupported).source ∧
    result.typeStrengthen.target =
      typeStrengthenClosed (wordToStrengthen wordToStrengthenSupported).supported ∧
    result.chain.stateProjectL2 = model.projectGlobals ∧
    result.chain.stateProjectHL = stateMap ∧
    result.chain.preconditionL2 =
      (fun state => model.projectLocals state = initialLocals) ∧
    result.chain.preconditionWA = (fun _ => True) ∧
    result.chain.l1 = result.l1.target.denote ∧
    result.chain.l2 = LocalVarExtract.Kernel.CanonicalTarget.Syntax.denote
      result.l2.target result.initialLocals ∧
    result.chain.heapLifted = result.heapLift.target.denote ∧
    result.chain.wordAbstracted = result.wordAbstract.target.denote () := by
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
    rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem translateUnsignedSupported_correct
    (width : Nat) (checkTermination : Bool)
    (env : Simpl.Body Full Proc Fault) (source : Simpl.Com Full Proc Fault)
    (model : LocalVarExtract.Kernel.StateModel Full (BitVec width) Globals)
    (State : Type)
    (simplSupported : SimplConv.Kernel.Supported source)
    (lveSupported : LocalVarExtract.Kernel.Supported model
      (simplConv checkTermination env simplSupported))
    (initialLocals : BitVec width)
    (stateMap : Globals -> State)
    (heapSupported : HeapLift.Kernel.Supported stateMap
      ((localVarExtractCanonical model lveSupported) initialLocals))
    (heapToWordSupported : Pipeline.HeapToWord.Supported width
      (heapLift stateMap heapSupported))
    (wordToStrengthenSupported : Pipeline.WordToStrengthen.Supported width
      (wordAbstract (heapToWord heapToWordSupported).source)) :
    let result := translateUnsignedSupported width checkTermination env source
      model State simplSupported lveSupported initialLocals stateMap
      heapSupported heapToWordSupported wordToStrengthenSupported
    acCorres
      (result.chain.stateProjectHL ∘ result.chain.stateProjectL2)
      checkTermination env
      (result.chain.returnExtractWA ∘ result.chain.returnExtractL2)
      (fun state => result.chain.preconditionL2 state ∧
        result.chain.preconditionWA
          (result.chain.stateProjectHL (result.chain.stateProjectL2 state)))
      (TypeStrengthen.Kernel.embed (Exception := Unit) .option
        result.typeStrengthen.target.denote)
      source := by
  let result := translateUnsignedSupported width checkTermination env source
    model State simplSupported lveSupported initialLocals stateMap
    heapSupported heapToWordSupported wordToStrengthenSupported
  simpa only [acCorres, Zag.Lang.AutoCorres.ac_corres] using
    result.chain.acCorres

end Comparator.AutoCorres
