import Lang.AutoCorres.AutoCorres
import Lang.AutoCorres.ML.simpl_conv
import Lang.AutoCorres.ML.local_var_extract
import Lang.AutoCorres.ML.heap_lift
import Lang.AutoCorres.ML.word_abstract
import Lang.AutoCorres.ML.type_strengthen

/-!
# Pure AutoCorres pipeline orchestration

Corresponds only to [`tools/autocorres/autocorres.ML`](https://github.com/seL4/l4v/blob/bc2599a59c43e673dca021b10b9841e9b8da4430/tools/autocorres/autocorres.ML).

The upstream command also parses options and C output, computes call graphs and
SCC schedules, manages incremental theory data, and chooses phase rules by
theorem search. Those operations are intentionally not reproduced here.
`Passes` is the pure adapter boundary: parser, call-graph, and SCC machinery
must provide each successful adapter together with the certificate required by
its indexed result. The pipeline itself only invokes those adapters in upstream
L1, L2, HL, WA, TS order and composes their certificates.
-/

namespace Zag.Lang.AutoCorres.ML.AutoCorres

open Zag.Lang.AutoCorres

universe uConcrete uProc uFault uL2State uL2Exception uL2Result uHLState
universe uWAException uWAResult uTargetException

inductive Phase where
  | l1
  | l2
  | heapLift
  | wordAbstract
  | typeStrengthen
  deriving DecidableEq, Repr

/-- Explicit recognition or adapter failure at one pipeline phase. -/
structure PhaseError where
  phase : Phase
  reason : String
  deriving DecidableEq, Repr

/-! ## Dependently adjacent successful phase results -/

structure L1Success
    (checkTermination : Bool)
    (env : Simpl.Body ConcreteState Proc Fault)
    (source : Simpl.Com ConcreteState Proc Fault)
    (target : L1.L1Program ConcreteState) : Type where
  certificate : L1.L1Corres checkTermination env target source

structure L2Success
    (source : L1.L1Program ConcreteState)
    (target : L2.L2Program L2State L2Exception L2Result) where
  stateProject : ConcreteState -> L2State
  returnExtract : ConcreteState -> L2Result
  exceptionExtract : ConcreteState -> L2Exception
  precondition : ConcreteState -> Prop
  certificate : L2.L2Corres stateProject returnExtract exceptionExtract
    precondition target source

end Zag.Lang.AutoCorres.ML.AutoCorres

namespace Zag.Lang.AutoCorres.ML.LocalVarExtract

/-- Adapt a certified local-variable extraction at a selected initial locals value. -/
def toL2Success
    (model : StateModel Full Locals Globals)
    {source : Source.Syntax Full Locals Globals}
    (certificate : Certificate model source)
    (locals : Locals) :
    AutoCorres.L2Success (source.denote model) (certificate.target.denote locals) :=
  { stateProject := model.projectGlobals
    returnExtract := model.projectLocals
    exceptionExtract := model.projectLocals
    precondition := fun state => model.projectLocals state = locals
    certificate := certificate.corres locals }

end Zag.Lang.AutoCorres.ML.LocalVarExtract

namespace Zag.Lang.AutoCorres.ML.AutoCorres

structure HeapLiftSuccess
    (source : L2.L2Program L2State L2Exception L2Result)
    (target : L2.L2Program HLState L2Exception L2Result) where
  stateProject : L2State -> HLState
  certificate : HeapLift.L2Tcorres stateProject target source

structure WordAbstractSuccess
    (source : L2.L2Program HLState L2Exception L2Result)
    (target : L2.L2Program HLState WAException WAResult) where
  precondition : HLState -> Prop
  returnExtract : L2Result -> WAResult
  exceptionExtract : L2Exception -> WAException
  certificate : WordAbstract.corresTA precondition returnExtract
    exceptionExtract target source

structure TypeStrengthenSuccess
    {HLState WAResult WAException TargetException : Type}
    (source : L2.L2Program HLState WAException WAResult)
    (carrier : MonadTypes.Carrier)
    (target : MonadTypes.Repr carrier HLState WAResult) : Type where
  certificate : L2.call (Exception := TargetException) source =
      Zag.Lang.AutoCorres.TypeStrengthen.embed
        (Exception := TargetException) carrier target

/-! ## Certified identity options -/

/-- Transport a state along the equality required by a skipped heap lift. -/
def castState
    {SourceState TargetState : Type} (stateEq : TargetState = SourceState) :
    SourceState -> TargetState :=
  fun state => stateEq.symm ▸ state

/-- Transport an L2 program along the same exact state equality. -/
def castProgramState
    {SourceState TargetState Exception Result : Type}
    (stateEq : TargetState = SourceState)
    (source : L2.L2Program SourceState Exception Result) :
    L2.L2Program TargetState Exception Result :=
  stateEq.symm ▸ source

/-- Exact endpoint data for skipping heap lifting. -/
structure HeapIdentity
    {L2State L2Exception L2Result HLState : Type}
    (source : L2.L2Program L2State L2Exception L2Result)
    (target : L2.L2Program HLState L2Exception L2Result) where
  stateEq : HLState = L2State
  targetEq : target = castProgramState stateEq source

def HeapIdentity.success
    {source : L2.L2Program L2State L2Exception L2Result}
    {target : L2.L2Program HLState L2Exception L2Result}
    (identity : HeapIdentity source target) :
    HeapLiftSuccess source target := by
  cases identity with
  | mk stateEq targetEq =>
      cases stateEq
      cases targetEq
      exact
        { stateProject := id
          certificate := HeapLift.L2Tcorres_id source }

/-- Transport both value indices along exact skip equalities. -/
def castProgramSignature
    {State SourceException SourceResult TargetException TargetResult : Type}
    (exceptionEq : TargetException = SourceException)
    (resultEq : TargetResult = SourceResult)
    (source : L2.L2Program State SourceException SourceResult) :
    L2.L2Program State TargetException TargetResult := by
  cases exceptionEq
  cases resultEq
  exact source

def castResult {Source Target : Type} (typeEq : Target = Source) : Source -> Target :=
  fun value => typeEq.symm ▸ value

/-- Exact endpoint data for skipping word abstraction. -/
structure WordIdentity
    {HLState L2Exception L2Result WAException WAResult : Type}
    (source : L2.L2Program HLState L2Exception L2Result)
    (target : L2.L2Program HLState WAException WAResult) where
  exceptionEq : WAException = L2Exception
  resultEq : WAResult = L2Result
  targetEq : target = castProgramSignature exceptionEq resultEq source

def WordIdentity.success
    {source : L2.L2Program HLState L2Exception L2Result}
    {target : L2.L2Program HLState WAException WAResult}
    (identity : WordIdentity source target) :
    WordAbstractSuccess source target := by
  cases identity with
  | mk exceptionEq resultEq targetEq =>
      cases exceptionEq
      cases resultEq
      cases targetEq
      exact
        { precondition := fun _ => True
          returnExtract := id
          exceptionExtract := id
          certificate := corresTA_trivial source }

inductive HeapLiftOption
    {L2State L2Exception L2Result HLState : Type}
    (source : L2.L2Program L2State L2Exception L2Result)
    (target : L2.L2Program HLState L2Exception L2Result) where
  | run
  | skip (identity : HeapIdentity source target)

inductive WordAbstractOption
    {HLState L2Exception L2Result WAException WAResult : Type}
    (source : L2.L2Program HLState L2Exception L2Result)
    (target : L2.L2Program HLState WAException WAResult) where
  | run
  | skip (identity : WordIdentity source target)

/-!
Every function is ordinary and pure. A recognizer may return `Except.error`;
an `Except.ok` result cannot be constructed without the exact adjacent
certificate named by its result type.
-/
structure Passes
    {ConcreteState Proc Fault L2State L2Exception L2Result HLState WAException
      WAResult TargetException : Type}
    (checkTermination : Bool)
    (env : Simpl.Body ConcreteState Proc Fault)
    (source : Simpl.Com ConcreteState Proc Fault) where
  l1 : L1.L1Program ConcreteState
  l2 : L2.L2Program L2State L2Exception L2Result
  heapLifted : L2.L2Program HLState L2Exception L2Result
  wordAbstracted : L2.L2Program HLState WAException WAResult
  carrier : MonadTypes.Carrier
  target : MonadTypes.Repr carrier HLState WAResult
  simplConv : Unit -> Except PhaseError
    (L1Success checkTermination env source l1)
  localVarExtract : L1Success checkTermination env source l1 ->
    Except PhaseError (L2Success l1 l2)
  heapLift : L2Success l1 l2 ->
    Except PhaseError (HeapLiftSuccess l2 heapLifted)
  wordAbstract : HeapLiftSuccess l2 heapLifted ->
    Except PhaseError (WordAbstractSuccess heapLifted wordAbstracted)
  typeStrengthen : WordAbstractSuccess heapLifted wordAbstracted ->
    Except PhaseError (TypeStrengthenSuccess
      (TargetException := TargetException) wordAbstracted carrier target)

structure Options
    {L2State L2Exception L2Result HLState WAException WAResult : Type}
    (l2 : L2.L2Program L2State L2Exception L2Result)
    (heapLifted : L2.L2Program HLState L2Exception L2Result)
    (wordAbstracted : L2.L2Program HLState WAException WAResult) where
  heapLift : HeapLiftOption l2 heapLifted := .run
  wordAbstract : WordAbstractOption heapLifted wordAbstracted := .run

/-- The final carrier and target, adjacent chain, and projected end theorem. -/
structure Translation
    {ConcreteState Proc Fault L2State L2Exception L2Result HLState WAException
      WAResult TargetException : Type}
    (checkTermination : Bool)
    (env : Simpl.Body ConcreteState Proc Fault)
    (source : Simpl.Com ConcreteState Proc Fault) where
  carrier : MonadTypes.Carrier
  target : MonadTypes.Repr carrier HLState WAResult
  chain : ChainCertificate
    (L2State := L2State) (L2Result := L2Result)
    (L2Exception := L2Exception)
    (WAException := WAException) (TargetException := TargetException)
    checkTermination env source
    (Zag.Lang.AutoCorres.TypeStrengthen.embed
      (Exception := TargetException) carrier target)
  correctness : ac_corres
    (chain.stateProjectHL ∘ chain.stateProjectL2) checkTermination env
    (chain.returnExtractWA ∘ chain.returnExtractL2)
    (fun state => chain.preconditionL2 state ∧
      chain.preconditionWA (chain.stateProjectHL (chain.stateProjectL2 state)))
    (Zag.Lang.AutoCorres.TypeStrengthen.embed
      (Exception := TargetException) carrier target) source

/--
Run the five phases in upstream order and assemble their exact adjacent links.
No theorem search, metaprogram execution, or noncomputable choice occurs here.
Semantic denotations, when needed, are already present in adapter certificates.
-/
def translate
    (passes : Passes
      (L2State := L2State) (L2Result := L2Result)
      (L2Exception := L2Exception)
      (HLState := HLState) (WAException := WAException) (WAResult := WAResult)
      (TargetException := TargetException)
      checkTermination env source)
    (options : Options passes.l2 passes.heapLifted passes.wordAbstracted) :
    Except PhaseError
      (Translation (L2State := L2State) (L2Result := L2Result)
        (L2Exception := L2Exception)
        (HLState := HLState) (WAException := WAException) (WAResult := WAResult)
        (TargetException := TargetException) checkTermination env source) := do
  let l1Result <- passes.simplConv ()
  let l2Result <- passes.localVarExtract l1Result
  let heapResult <-
    match options.heapLift with
    | .run => passes.heapLift l2Result
    | .skip identity => .ok identity.success
  let wordResult <-
    match options.wordAbstract with
    | .run => passes.wordAbstract heapResult
    | .skip identity => .ok identity.success
  let tsResult <- passes.typeStrengthen wordResult
  let chain : ChainCertificate
      (L2State := L2State) (L2Result := L2Result)
      (L2Exception := L2Exception)
      (WAException := WAException) (TargetException := TargetException)
      checkTermination env source
      (Zag.Lang.AutoCorres.TypeStrengthen.embed
        (Exception := TargetException) passes.carrier passes.target) :=
    { stateProjectL2 := l2Result.stateProject
      returnExtractL2 := l2Result.returnExtract
      exceptionExtractL2 := l2Result.exceptionExtract
      preconditionL2 := l2Result.precondition
      stateProjectHL := heapResult.stateProject
      preconditionWA := wordResult.precondition
      returnExtractWA := wordResult.returnExtract
      exceptionExtractWA := wordResult.exceptionExtract
      l1 := passes.l1
      l1Corres := l1Result.certificate
      l2 := passes.l2
      l2Corres := l2Result.certificate
      heapLifted := passes.heapLifted
      heapLiftCorres := heapResult.certificate
      wordAbstracted := passes.wordAbstracted
      wordAbstractCorres := wordResult.certificate
      typeStrengthen := tsResult.certificate }
  return show
      Translation (L2State := L2State) (L2Result := L2Result)
        (L2Exception := L2Exception)
        (HLState := HLState) (WAException := WAException) (WAResult := WAResult)
        (TargetException := TargetException) checkTermination env source from
    { carrier := passes.carrier
      target := passes.target
      chain := chain
      correctness := chain.acCorres }

/-- Project final correctness from any successful ordinary pipeline run. -/
theorem translate_correct
    (passes : Passes
      (L2State := L2State) (L2Result := L2Result)
      (L2Exception := L2Exception)
      (HLState := HLState) (WAException := WAException) (WAResult := WAResult)
      (TargetException := TargetException)
      checkTermination env source)
    (options : Options passes.l2 passes.heapLifted passes.wordAbstracted)
    (result : Translation
      (L2State := L2State) (L2Result := L2Result)
      (L2Exception := L2Exception)
      (HLState := HLState) (WAException := WAException) (WAResult := WAResult)
      (TargetException := TargetException) checkTermination env source)
    (_success : translate (TargetException := TargetException) passes options = .ok result) :
    ac_corres
      (result.chain.stateProjectHL ∘ result.chain.stateProjectL2)
      checkTermination env
      (result.chain.returnExtractWA ∘ result.chain.returnExtractL2)
      (fun state => result.chain.preconditionL2 state ∧
        result.chain.preconditionWA
          (result.chain.stateProjectHL (result.chain.stateProjectL2 state)))
      (Zag.Lang.AutoCorres.TypeStrengthen.embed
        (Exception := TargetException) result.carrier result.target) source :=
  result.correctness

/-! ## Reduction pins -/

private def pinLocalVarModel :
    LocalVarExtract.StateModel (Bool × Nat) Bool Nat where
  projectGlobals := Prod.snd
  projectLocals := Prod.fst
  assemble := fun locals globals => (locals, globals)
  projectGlobals_assemble := by intros; rfl
  projectLocals_assemble := by intros; rfl
  assemble_project := by intro state; cases state; rfl

/-- The certified local-variable adapter reduces to its exact selected projections. -/
theorem localVarExtract_toL2Success_skip_pin :
    let certificate := LocalVarExtract.extract pinLocalVarModel
      LocalVarExtract.Supported.skip
    let success := LocalVarExtract.toL2Success pinLocalVarModel certificate true
    success.stateProject (true, 7) = 7 ∧
      success.returnExtract (true, 7) = true ∧
      success.exceptionExtract (false, 7) = false ∧
      success.precondition (true, 7) := by
  simp [LocalVarExtract.toL2Success, pinLocalVarModel]

private def pinEnv : Simpl.Body Unit Unit Unit := fun _ => none
private def pinSource : Simpl.Com Unit Unit Unit := .Skip
private def pinL1 : L1.L1Program Unit := L1.skip
private def pinL2 : L2.L2Program Unit Unit Unit := L2.skip
private def pinHeapLifted : L2.L2Program Unit Unit Unit := L2.skip
private def pinWordAbstracted : L2.L2Program Unit Unit Unit := L2.skip
private def pinTarget : Unit -> Unit := fun _ => ()

private def pinPasses : Passes
    (L2State := Unit) (L2Exception := Unit) (L2Result := Unit) (HLState := Unit)
    (WAException := Unit) (WAResult := Unit) (TargetException := Unit)
    false pinEnv pinSource where
  l1 := pinL1
  l2 := pinL2
  heapLifted := pinHeapLifted
  wordAbstracted := pinWordAbstracted
  carrier := .gets
  target := pinTarget
  simplConv := fun _ => .ok
    { certificate := L1.L1Corres_skip false pinEnv }
  localVarExtract := fun _ => .ok
    { stateProject := id
      returnExtract := fun _ => ()
      exceptionExtract := fun _ => ()
      precondition := fun _ => True
      certificate := L2.corres_skip }
  heapLift := fun _ => .ok
    { stateProject := id
      certificate := HeapLift.L2Tcorres_id pinL2 }
  wordAbstract := fun _ => .ok
    { precondition := fun _ => True
      returnExtract := id
      exceptionExtract := id
      certificate := corresTA_trivial pinHeapLifted }
  typeStrengthen := fun _ => .ok
    { certificate := by
        exact (Zag.Lang.AutoCorres.TypeStrengthen.L2_call_embed_exact
          (Exception := Unit) .gets pinTarget).eq }

private def pinOptions :
    Options (L2Exception := Unit) pinPasses.l2 pinPasses.heapLifted
      pinPasses.wordAbstracted where
  heapLift := .skip
    { stateEq := rfl
      targetEq := rfl }
  wordAbstract := .skip
    { exceptionEq := rfl
      resultEq := rfl
      targetEq := rfl }

/-- The identity adapters reduce through every phase and retain the TS carrier. -/
theorem identity_pipeline_carrier_pin :
    (translate (TargetException := Unit) pinPasses pinOptions).map
      (fun result => result.carrier) = .ok .gets := by
  rfl

/-- Both certified identity skips reduce to the unchanged state endpoint. -/
theorem identity_pipeline_endpoint_pin :
    match translate (TargetException := Unit) pinPasses pinOptions with
    | .error _ => False
    | .ok result => result.chain.stateProjectHL (result.chain.stateProjectL2 ()) = () := by
  rfl

/-- A successful pinned reduction exposes the composed `ac_corres` theorem. -/
theorem identity_pipeline_correctness_pin
    (result : Translation
      (L2State := Unit) (L2Exception := Unit) (L2Result := Unit) (HLState := Unit)
      (WAException := Unit) (WAResult := Unit) (TargetException := Unit)
      false pinEnv pinSource)
    (success : translate (TargetException := Unit) pinPasses pinOptions = .ok result) :
    ac_corres
      (result.chain.stateProjectHL ∘ result.chain.stateProjectL2) false pinEnv
      (result.chain.returnExtractWA ∘ result.chain.returnExtractL2)
      (fun state => result.chain.preconditionL2 state ∧
        result.chain.preconditionWA
          (result.chain.stateProjectHL (result.chain.stateProjectL2 state)))
      (Zag.Lang.AutoCorres.TypeStrengthen.embed
        (Exception := Unit) result.carrier result.target) pinSource :=
  translate_correct pinPasses pinOptions result success

end Zag.Lang.AutoCorres.ML.AutoCorres
