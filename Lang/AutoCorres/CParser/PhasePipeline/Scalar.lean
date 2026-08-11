import Lang.AutoCorres.CParser.ScalarSimpl
import Lang.AutoCorres.ML.autocorres

/-! # Fixture-derived C AutoCorres phase scheduling -/

namespace Zag.Lang.AutoCorres.CParser.PhasePipeline

open ProgramAnalysis
open Zag.Lang.AutoCorres

inductive Phase where
  | simplConv
  | localVarExtract
  | heapLift
  | wordAbstract
  | typeStrengthen
deriving Repr, DecidableEq, Inhabited

inductive PhaseMode where
  | translated
  | exactIdentity
deriving Repr, DecidableEq, Inhabited

structure PhaseEntry where
  phase : Phase
  mode : PhaseMode
deriving Repr, DecidableEq, Inhabited

structure FunctionMetadata where
  symbolId : Nat
  sourceName : String
  phases : List PhaseEntry
deriving Repr, DecidableEq, Inhabited

structure FileMetadata where
  file : String
  functions : List FunctionMetadata
deriving Repr, DecidableEq, Inhabited

structure Metadata where
  files : List FileMetadata
deriving Repr, DecidableEq, Inhabited

def FunctionMetadata.lookup (metadata : FunctionMetadata) (phase : Phase) : Option PhaseEntry :=
  metadata.phases.find? (·.phase = phase)

def Metadata.lookupFunction (metadata : Metadata) (file functionName : String) :
    Option FunctionMetadata := do
  let file ← metadata.files.find? (·.file = file)
  file.functions.find? (·.sourceName = functionName)

def Metadata.lookup (metadata : Metadata) (file functionName : String) (phase : Phase) :
    Option PhaseEntry := do
  let function ← metadata.lookupFunction file functionName
  function.lookup phase

structure Options where
  skipHeapAbs : Bool := false
  unsignedWordAbs : List String := []
  noSignedWordAbs : List String := []
  forceNondet : Bool := false
deriving Repr, DecidableEq, Inhabited

inductive WordMode where
  | concrete
  | abstract
deriving Repr, DecidableEq, Inhabited

def Options.wordMode (options : Options) (functionName : String)
    (signedness : ScalarSimpl.Signedness) : WordMode :=
  match signedness with
  | .unsigned =>
      if options.unsignedWordAbs.contains functionName then .abstract else .concrete
  | .signed =>
      if options.noSignedWordAbs.contains functionName then .concrete else .abstract

/-! ## Closed no-call/no-memory scalar functions -/

namespace Scalar

open ScalarSimpl

/-- The scalar operation widths for which WordAbstract has upstream rules. -/
abbrev Width := WordAbstract.WordWidth

def scalarType (signedness : Signedness) (width : Width) : ScalarType :=
  { signedness, width := width.bits }

/--
Typed recognition evidence for the initial production fragment. Variables must
be actual parameters of the selected function; addition nodes retain the C
signedness and width in their index.
-/
inductive AddExpression (signedness : Signedness) (width : Width)
    (parameters : List (Nat × ScalarType)) : ScalarSimpl.Expr → Type where
  | parameter (symbolId : Nat)
      (member : (symbolId, scalarType signedness width) ∈ parameters) :
      AddExpression signedness width parameters
        (.variable (scalarType signedness width) symbolId)
  | add {left right}
      (leftSupported : AddExpression signedness width parameters left)
      (rightSupported : AddExpression signedness width parameters right) :
      AddExpression signedness width parameters
        (.binary (scalarType signedness width) (scalarType signedness width)
          .add left right)

/-- A selected scalar function in the closed integer return-only fragment. -/
inductive Supported : Function → Type where
  | returnedAdd (name : String) {signedness : Signedness} (width : Width)
      (parameters : List (Nat × ScalarType)) (expression : ScalarSimpl.Expr)
      (expressionSupported : AddExpression signedness width parameters expression) :
      Supported
        { name
          returnType := scalarType signedness width
          parameters
          locals := []
          body := .seq (.return (scalarType signedness width) expression) .skip }

namespace Supported

def signedness : {function : Function} → Supported function → Signedness
  | _, .returnedAdd (signedness := signedness) .. => signedness

def width : {function : Function} → Supported function → Width
  | _, .returnedAdd _ width _ _ _ => width

def expression : {function : Function} → Supported function → ScalarSimpl.Expr
  | _, .returnedAdd _ _ _ expression _ => expression

def expressionEvidence : (supported : Supported function) →
    AddExpression supported.signedness supported.width function.parameters
      supported.expression
  | .returnedAdd _ _ _ _ expressionSupported => expressionSupported

def transport {left right : Function} (equality : left = right)
    (supported : Supported left) : Supported right :=
  equality ▸ supported

end Supported

private def recognizesExpression (type : ScalarType)
    (parameters : List (Nat × ScalarType)) : ScalarSimpl.Expr → Bool
  | .variable foundType id =>
      foundType = type && parameters.contains (id, type)
  | .binary foundType operandType .add left right =>
      foundType = type && operandType = type &&
        recognizesExpression type parameters left &&
        recognizesExpression type parameters right
  | _ => false

/-- Executable shape check used by schedulers before requesting typed evidence. -/
def recognizes : Function → Bool
  | { returnType, parameters, locals := [],
      body := .seq (.return returnType' expression) .skip, .. } =>
      returnType = returnType' &&
        (returnType.width = 8 || returnType.width = 16 ||
          returnType.width = 32 || returnType.width = 64) &&
        recognizesExpression returnType parameters expression
  | _ => false

/-- Function-derived frame metadata retained by LVE and later phase reports. -/
structure FrameLayout (function : Function) where
  parameters : List (Nat × ScalarType) := function.parameters
  locals : List Nat := function.locals
deriving Repr

/--
No C objects are addressable in this fragment. The complete scalar machine
state is therefore the L2 global state, while the extracted control-local value
is `Unit`; `FrameLayout` records exactly which analyzed slots belong to the
selected function.
-/
def lveModel (_layout : FrameLayout function) :
    LocalVarExtract.Kernel.StateModel State Unit State where
  projectGlobals := id
  projectLocals := fun _ => ()
  assemble := fun _ globals => globals
  projectGlobals_assemble := by intros; rfl
  projectLocals_assemble := by intros; rfl
  assemble_project := by intro state; rfl

private inductive NoSpec : {source : Simpl.Com State Nat Fault} →
    (evidence : SimplConv.Kernel.Supported source) → Type where
  | skip : NoSpec .skip
  | seq (left : NoSpec leftEvidence) (right : NoSpec rightEvidence) :
      NoSpec (.seq leftEvidence rightEvidence)
  | basic (transform : State → State) : NoSpec (.basic transform)
  | cond (thenEvidence : NoSpec thenSupported) (elseEvidence : NoSpec elseSupported) :
      NoSpec (.cond test thenSupported elseSupported)
  | «catch» (body : NoSpec bodySupported) (handler : NoSpec handlerSupported) :
      NoSpec (.catch bodySupported handlerSupported)
  | «while» (body : NoSpec bodySupported) : NoSpec (.while test bodySupported)
  | throw : NoSpec .throw
  | guard (body : NoSpec bodySupported) : NoSpec (.guard fault test bodySupported)

private def lveOfNoSpec (layout : FrameLayout function) :
    {source : Simpl.Com State Nat Fault} →
    (evidence : SimplConv.Kernel.Supported source) → NoSpec evidence →
      LocalVarExtract.Kernel.Supported (lveModel layout)
        (ML.SimplConv.simplConv false emptyEnvironment evidence).target
  | _, .skip, .skip => .skip
  | _, .seq left right, .seq leftNoSpec rightNoSpec =>
      .seq (lveOfNoSpec layout left leftNoSpec) (lveOfNoSpec layout right rightNoSpec)
  | _, .basic transform, .basic _ =>
      .globalUpdate fun _ state => transform state
  | _, .cond test thenSupported elseSupported, .cond thenNoSpec elseNoSpec =>
      .condition (fun _ state => test state)
        (lveOfNoSpec layout thenSupported thenNoSpec)
        (lveOfNoSpec layout elseSupported elseNoSpec)
  | _, .catch body handler, .catch bodyNoSpec handlerNoSpec =>
      .catch (lveOfNoSpec layout body bodyNoSpec)
        (lveOfNoSpec layout handler handlerNoSpec)
  | _, .while test body, .while bodyNoSpec =>
      .loop (fun _ state => test state) (lveOfNoSpec layout body bodyNoSpec)
  | _, .throw, .throw => .throw
  | _, .guard fault test body, .guard bodyNoSpec =>
      .seq (.guard fun _ state => test state) (lveOfNoSpec layout body bodyNoSpec)

private def statementNoSpec : (statement : Stmt) → NoSpec (ScalarSimpl.supported statement)
  | .skip => .skip
  | .seq first second => .seq (statementNoSpec first) (statementNoSpec second)
  | .assign .. => .guard (.basic _)
  | .declare _ _ none => .basic _
  | .declare _ _ (some _) => .seq (.basic _) (.guard (.basic _))
  | .return .. => .guard (.seq (.basic _) .throw)
  | .cond _ thenStmt elseStmt =>
      .guard (.cond (statementNoSpec thenStmt) (statementNoSpec elseStmt))
  | .while _ body => .while (.seq (.guard .skip) (statementNoSpec body))

private def functionNoSpec (function : Function) : NoSpec function.supported :=
  .seq (.basic _)
    (.seq (.catch (statementNoSpec function.body) .skip)
      (.seq (.basic _) (.guard .skip)))

private def functionLveSupported (function : Function)
    (layout : FrameLayout function) :
    LocalVarExtract.Kernel.Supported (lveModel layout)
      (ML.SimplConv.simplConv false emptyEnvironment function.supported).target :=
  lveOfNoSpec layout function.supported (functionNoSpec function)

private def lveSupportedFromCertificate
    (certificate : ScalarSimpl.Certificate target files entry name function)
    (layout : FrameLayout function) :
    LocalVarExtract.Kernel.Supported (lveModel layout)
      (ML.SimplConv.simplConv false emptyEnvironment certificate.supported).target := by
  rw [SimplConv.Kernel.Supported.unique certificate.supported function.supported]
  exact functionLveSupported function layout

def readWord (supported : Supported function) (state : State) :
    BitVec supported.width.bits :=
  BitVec.ofInt supported.width.bits state.result

/-- Re-embedding an unsigned scalar cast at the same width preserves the word. -/
theorem bitvecOfUnsignedCast (width : Width) (value : Int) :
    BitVec.ofInt width.bits ((scalarType .unsigned width).cast value) =
      BitVec.ofInt width.bits value := by
  apply BitVec.eq_of_toFin_eq
  simp [scalarType, ScalarType.cast, ScalarType.unsignedValue,
    ScalarType.modulus, BitVec.ofInt]

def AddExpression.unsignedWordExpression :
    (evidence : AddExpression .unsigned width parameters expression) →
      WordAbstract.Kernel.Source.Expr .unit State (.word width.bits)
  | .parameter symbolId _ =>
      .state (.word width.bits) fun state =>
        BitVec.ofInt width.bits ((state.read? symbolId).getD 0)
  | .add left right =>
      .add left.unsignedWordExpression right.unsignedWordExpression

def AddExpression.unsignedWordSupported
    (evidence : AddExpression .unsigned width parameters expression) :
    ML.WordAbstract.Expr.Supported evidence.unsignedWordExpression :=
  match evidence with
  | .parameter .. => .state _ _
  | .add left right => .add left.unsignedWordSupported right.unsignedWordSupported

def AddExpression.signedWordExpression :
    (evidence : AddExpression .signed width parameters expression) →
      WordAbstract.Kernel.Source.Expr .unit State (.sword width.bits)
  | .parameter symbolId _ =>
      .state (.sword width.bits) fun state =>
        BitVec.ofInt width.bits ((state.read? symbolId).getD 0)
  | .add left right =>
      .sbinary width .add left.signedWordExpression right.signedWordExpression

def AddExpression.signedWordSupported
    (evidence : AddExpression .signed width parameters expression) :
    ML.WordAbstract.Expr.Supported evidence.signedWordExpression :=
  match evidence with
  | .parameter .. => .state _ _
  | .add left right => .sbinary left.signedWordSupported right.signedWordSupported

def wordValueType (signedness : Signedness) (width : Width) :
    WordAbstract.Kernel.ValueType :=
  match signedness with
  | .unsigned => .word width.bits
  | .signed => .sword width.bits

/-- The reified expression and generated WordAbstract guard/value proof. -/
inductive WordArtifact : {function : Function} → Supported function → Type 2 where
  | ofEvidence
      (source : WordAbstract.Kernel.Source.Expr .unit State
        (wordValueType signedness width))
      (evidence : ML.WordAbstract.ValueEvidence source)
      (certificate : WordAbstract.Kernel.Certificate
        (WordAbstract.Kernel.Source.Syntax.gets (exception := .unit) source ["ret"])) :
      WordArtifact (.returnedAdd (signedness := signedness) name width parameters
        expression expressionSupported)

def makeWordArtifact (supported : Supported function) : WordArtifact supported :=
  match supported with
  | .returnedAdd (signedness := .unsigned) name width parameters expression
      expressionSupported =>
      let source := expressionSupported.unsignedWordExpression
      let evidence := expressionSupported.unsignedWordSupported
      .ofEvidence source (ML.WordAbstract.Expr.transform evidence)
        (ML.WordAbstract.transform (.gets (exception := .unit) evidence ["ret"]))
  | .returnedAdd (signedness := .signed) name width parameters expression
      expressionSupported =>
      let source := expressionSupported.signedWordExpression
      let evidence := expressionSupported.signedWordSupported
      .ofEvidence source (ML.WordAbstract.Expr.transform evidence)
        (ML.WordAbstract.transform (.gets (exception := .unit) evidence ["ret"]))

namespace WordArtifact

variable {function : Function} {fragment : Supported function}

noncomputable def sourceProgram : (artifact : WordArtifact fragment) →
    L2.L2Program State Unit
      (WordAbstract.Kernel.Source.Value
        (wordValueType fragment.signedness fragment.width))
  | .ofEvidence source _ _ =>
      (WordAbstract.Kernel.Source.Syntax.gets (exception := .unit) source ["ret"]).denote ()

def guard : (artifact : WordArtifact fragment) → State → Prop
  | .ofEvidence _ evidence _ => evidence.guard ()

end WordArtifact

/-- A generated TypeStrengthen certificate consuming its exact reified WordAbstract endpoint. -/
inductive ScalarStrengthenArtifact : {function : Function} → Supported function → Type 2 where
  | ofEvidence
      (wordSource : WordAbstract.Kernel.Source.Expr .unit State
        (wordValueType signedness width))
      (evidence : ML.WordAbstract.ValueEvidence wordSource)
      (wordCertificate : WordAbstract.Kernel.Certificate
        (WordAbstract.Kernel.Source.Syntax.gets (exception := .unit) wordSource ["ret"]))
      (source : TypeStrengthen.Kernel.Source.Closed State Unit
        (WordAbstract.Kernel.Target.Value (wordValueType signedness width)))
      (endpoint : wordCertificate.target.denote () = source.denote ())
      (certificate : TypeStrengthen.Kernel.ClosedCertificate .nondet source) :
      ScalarStrengthenArtifact
        (.returnedAdd (signedness := signedness) name width parameters expression
          expressionSupported)

noncomputable def makeScalarStrengthenArtifact
    (fragment : Supported function) : ScalarStrengthenArtifact fragment :=
  match fragment with
  | .returnedAdd (signedness := .unsigned) _ _ _ _ expressionSupported =>
      let wordSource := expressionSupported.unsignedWordExpression
      let evidence := ML.WordAbstract.Expr.transform expressionSupported.unsignedWordSupported
      let wordCertificate := ML.WordAbstract.transform
        (.gets (exception := .unit) expressionSupported.unsignedWordSupported ["ret"])
      let source : TypeStrengthen.Kernel.Source.Closed State Unit Nat :=
        .seq (.exactGuard fun _ state => evidence.guard () state)
          (.gets (fun _ state => evidence.target.eval () state) ["ret"])
      .ofEvidence wordSource evidence wordCertificate source rfl
        (ML.TypeStrengthen.strengthenClosed
          (.nondetSeq .nondetExactGuard .nondetRead))
  | .returnedAdd (signedness := .signed) _ _ _ _ expressionSupported =>
      let wordSource := expressionSupported.signedWordExpression
      let evidence := ML.WordAbstract.Expr.transform expressionSupported.signedWordSupported
      let wordCertificate := ML.WordAbstract.transform
        (.gets (exception := .unit) expressionSupported.signedWordSupported ["ret"])
      let source : TypeStrengthen.Kernel.Source.Closed State Unit Int :=
        .seq (.exactGuard fun _ state => evidence.guard () state)
          (.gets (fun _ state => evidence.target.eval () state) ["ret"])
      .ofEvidence wordSource evidence wordCertificate source rfl
        (ML.TypeStrengthen.strengthenClosed
          (.nondetSeq .nondetExactGuard .nondetRead))

namespace ScalarStrengthenArtifact

variable {function : Function} {fragment : Supported function}

noncomputable def wordSource (artifact : ScalarStrengthenArtifact fragment) :
    L2.L2Program State Unit
      (WordAbstract.Kernel.Source.Value
        (wordValueType fragment.signedness fragment.width)) :=
  match artifact with
  | .ofEvidence source _ _ _ _ _ =>
      (WordAbstract.Kernel.Source.Syntax.gets (exception := .unit) source ["ret"]).denote ()

noncomputable def wordTarget (artifact : ScalarStrengthenArtifact fragment) :
    L2.L2Program State Unit
      (WordAbstract.Kernel.Target.Value
        (wordValueType fragment.signedness fragment.width)) :=
  match artifact with
  | .ofEvidence _ _ certificate _ _ _ => certificate.target.denote ()

noncomputable def finalTarget (artifact : ScalarStrengthenArtifact fragment) :
    L2.L2Program State Unit
      (WordAbstract.Kernel.Target.Value
        (wordValueType fragment.signedness fragment.width)) :=
  match artifact with
  | .ofEvidence _ _ _ _ _ certificate =>
      TypeStrengthen.Kernel.embed .nondet certificate.target.denote

/-- The generated WordAbstract target consumes the artifact's exact concrete source. -/
theorem wordCorres (artifact : ScalarStrengthenArtifact fragment) :
    WordAbstract.corresTA (fun _ : State => True)
      (WordAbstract.Kernel.typeMap
        (wordValueType fragment.signedness fragment.width)).abstract id
      artifact.wordTarget artifact.wordSource := by
  cases artifact with
  | ofEvidence wordSource evidence wordCertificate source endpoint certificate =>
      exact wordCertificate.corres ()

/-- The generated TypeStrengthen certificate consumes the generated WordAbstract target. -/
theorem consumesWordTarget (artifact : ScalarStrengthenArtifact fragment) :
    L2.call (Exception := Unit) artifact.wordTarget = artifact.finalTarget := by
  cases artifact with
  | ofEvidence wordSource evidence wordCertificate source endpoint certificate =>
      change L2.call (Exception := Unit) (wordCertificate.target.denote ()) =
        TypeStrengthen.Kernel.embed .nondet certificate.target.denote
      rw [endpoint]
      exact certificate.exact Unit

/-- The exact WordAbstract and TypeStrengthen certificates at their shared endpoint. -/
structure AdjacentCertificates (artifact : ScalarStrengthenArtifact fragment) : Prop where
  word : WordAbstract.corresTA (fun _ : State => True)
    (WordAbstract.Kernel.typeMap
      (wordValueType fragment.signedness fragment.width)).abstract id
    artifact.wordTarget artifact.wordSource
  strengthen : L2.call (Exception := Unit) artifact.wordTarget = artifact.finalTarget

theorem adjacentCertificates (artifact : ScalarStrengthenArtifact fragment) :
    AdjacentCertificates artifact :=
  ⟨artifact.wordCorres, artifact.consumesWordTarget⟩

end ScalarStrengthenArtifact

/-- Certified identity lifting for a program whose state contains no byte-addressed heap. -/
structure HeapArtifact (program : L2.L2Program State Unit (BitVec width)) where
  target : L2.L2Program State Unit (BitVec width)
  target_eq : target = program
  corres : HeapLift.L2Tcorres id target program

def makeHeapArtifact (program : L2.L2Program State Unit (BitVec width)) :
    HeapArtifact program :=
  { target := program
    target_eq := rfl
    corres := HeapLift.L2Tcorres_id program }

/-- Exact final call boundary retained as the TypeStrengthen phase artifact. -/
structure TypeStrengthenArtifact {Result : Type}
    (program : L2.L2Program State Unit Result) where
  target : L2.L2Program State Unit Result
  exact : L2.call (Exception := Unit) program = target

def makeTypeStrengthenArtifact {Result : Type}
    (program : L2.L2Program State Unit Result) :
    TypeStrengthenArtifact program :=
  { target := L2.call program, exact := rfl }

/-- All generated artifacts for one selected fixture-derived scalar function. -/
structure Translation
    (certified : ScalarSimpl.Certified target files entry name)
    (supported : Supported certified.function) where
  layout : FrameLayout certified.function
  simpl : SimplConv.Kernel.Certificate false emptyEnvironment certified.function.command
  lve : LocalVarExtract.Kernel.ClosedCertificate (lveModel layout) simpl.target
  word : WordArtifact supported
  wordStrengthen : ScalarStrengthenArtifact supported
  metadata : FunctionMetadata

/-- Run the reusable five-phase scalar path over typed closed-fragment evidence. -/
noncomputable def translate
    (certified : ScalarSimpl.Certified target files entry name)
    (supported : Supported certified.function) : Translation certified supported :=
  let layout : FrameLayout certified.function := {}
  let simpl := ML.SimplConv.simplConv false emptyEnvironment
    certified.certificate.supported
  let lve := ML.LocalVarExtract.extractCanonical (lveModel layout)
    (lveSupportedFromCertificate certified.certificate layout)
  let word := makeWordArtifact supported
  { layout
    simpl
    lve
    word
    wordStrengthen := makeScalarStrengthenArtifact supported
    metadata :=
      { symbolId := certified.certificate.functionInfo.symbolId
        sourceName := certified.function.name
        phases :=
          [{ phase := .simplConv, mode := .translated },
           { phase := .localVarExtract, mode := .translated },
           { phase := .heapLift, mode := .exactIdentity },
           { phase := .wordAbstract, mode := .exactIdentity },
           { phase := .typeStrengthen, mode := .exactIdentity }] } }

/-- Metadata identity is retained from the selected frontend certificate. -/
theorem translateMetadataOrigin
    (certified : ScalarSimpl.Certified target files entry name)
    (supported : Supported certified.function) :
    (translate certified supported).metadata.symbolId =
        certified.certificate.functionInfo.symbolId ∧
      (translate certified supported).metadata.sourceName = certified.function.name := by
  exact ⟨rfl, rfl⟩

namespace Translation

variable {target : Target} {files : Preprocessor.FileMap} {entry name : String}
variable {certified : ScalarSimpl.Certified target files entry name}
variable {fragment : Supported certified.function}

noncomputable def l2 (translation : Translation certified fragment) :
    L2.L2Program State Unit (BitVec fragment.width.bits) :=
  L2.seq
    (LocalVarExtract.Kernel.CanonicalTarget.Syntax.denote translation.lve.target ())
    fun _ => L2.gets (readWord fragment) ["ret"]

private theorem projectCorres (translation : Translation certified fragment) :
    CorresXF id (fun _ post => readWord fragment post) (fun _ _ => ())
      (fun _ => True) translation.l2
      (LocalVarExtract.Kernel.CanonicalTarget.Syntax.denote translation.lve.target ()) := by
  intro state hypothesis
  constructor
  · intro result post member
    cases result with
    | error exception => exact ⟨Except.error (), post, member, rfl⟩
    | ok value =>
        refine ⟨Except.ok (), post, member, ?_⟩
        simp [L2.gets]
  · intro failed
    exact hypothesis.2 (Or.inl failed)

theorem l2Corres (translation : Translation certified fragment) :
    L2.L2Corres id (readWord fragment) (fun _ => ()) (fun _ => True)
      translation.l2 translation.simpl.target.denote := by
  change L2.L2Corres (fun state => state) (fun state => readWord fragment state)
    (fun _ => ()) (fun _ => True) translation.l2 translation.simpl.target.denote
  simpa [L2.L2Corres, Function.comp_def, lveModel] using
    CorresXF.merge (translation.lve.corres ()) translation.projectCorres

noncomputable def heap (translation : Translation certified fragment) :
    HeapArtifact translation.l2 := makeHeapArtifact translation.l2

theorem wordCorres (translation : Translation certified fragment) :
    WordAbstract.corresTA (fun _ : State => True) id id
      translation.heap.target translation.l2 := by
  rw [translation.heap.target_eq]
  exact WordAbstract.corresTA_refl (fun _ => True) translation.l2

noncomputable def strengthen (translation : Translation certified fragment) :
    TypeStrengthenArtifact translation.heap.target :=
  makeTypeStrengthenArtifact translation.heap.target

noncomputable def chain (translation : Translation certified fragment) :
    ChainCertificate (L2State := State) (L2Exception := Unit)
      (L2Result := BitVec fragment.width.bits) (HLState := State)
      (WAException := Unit) false emptyEnvironment certified.function.command
      translation.strengthen.target :=
  { stateProjectL2 := id
    returnExtractL2 := readWord fragment
    exceptionExtractL2 := fun _ => ()
    preconditionL2 := fun _ => True
    stateProjectHL := id
    preconditionWA := fun _ => True
    returnExtractWA := id
    exceptionExtractWA := id
    l1 := translation.simpl.target.denote
    l1Corres := translation.simpl.corres
    l2 := translation.l2
    l2Corres := translation.l2Corres
    heapLifted := translation.heap.target
    heapLiftCorres := translation.heap.corres
    wordAbstracted := translation.heap.target
    wordAbstractCorres := translation.wordCorres
    typeStrengthen := translation.strengthen.exact }

theorem finalCorres (translation : Translation certified fragment) :
    ac_corres id false emptyEnvironment (readWord fragment) (fun _ => True)
      translation.strengthen.target certified.function.command := by
  change ac_corres (fun state => state) false emptyEnvironment
    (fun state => readWord fragment state) (fun _ => True)
    translation.strengthen.target certified.function.command
  simpa [Translation.chain, Function.comp_def, id_eq] using translation.chain.acCorres

end Translation

end Scalar

end Zag.Lang.AutoCorres.CParser.PhasePipeline
