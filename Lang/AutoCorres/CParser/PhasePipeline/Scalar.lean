import Lang.AutoCorres.CParser.ScalarSimpl
import Lang.AutoCorres.ML.autocorres
import Lang.AutoCorres.Refinement

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

/-- Build the structural part of an addition-expression refinement, leaving membership goals. -/
syntax (name := deriveAddExpression) "derive_add_expression" : tactic

macro_rules
  | `(tactic| derive_add_expression) =>
      `(tactic| first
        | apply AddExpression.add <;> derive_add_expression
        | apply AddExpression.parameter)

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

inductive RecognitionError where
  | unsupportedWidth (width : Nat)
  | returnTypeMismatch
  | parameterNotFound (symbolId : Nat)
  | unsupportedExpression
  | unsupportedFunction
deriving Repr, Inhabited

private def widthOfBits? : (bits : Nat) → Option { width : Width // width.bits = bits }
  | 8 => some ⟨.w8, rfl⟩
  | 16 => some ⟨.w16, rfl⟩
  | 32 => some ⟨.w32, rfl⟩
  | 64 => some ⟨.w64, rfl⟩
  | _ => none

private def recognizeAddExpression (signedness : Signedness) (width : Width)
    (parameters : List (Nat × ScalarType)) :
    (expression : ScalarSimpl.Expr) →
      Except RecognitionError (AddExpression signedness width parameters expression)
  | .variable foundType symbolId => by
      by_cases typeEq : foundType = scalarType signedness width
      · subst foundType
        by_cases member : (symbolId, scalarType signedness width) ∈ parameters
        · exact .ok (.parameter symbolId member)
        · exact .error (.parameterNotFound symbolId)
      · exact .error .unsupportedExpression
  | .binary resultType operandType .add left right => by
      by_cases resultEq : resultType = scalarType signedness width
      · subst resultType
        by_cases operandEq : operandType = scalarType signedness width
        · subst operandType
          exact do
            let leftSupported ← recognizeAddExpression signedness width parameters left
            let rightSupported ← recognizeAddExpression signedness width parameters right
            return .add leftSupported rightSupported
        · exact .error .unsupportedExpression
      · exact .error .unsupportedExpression
  | _ => .error .unsupportedExpression

/-- Produce indexed support directly from a recognized scalar function shape. -/
def recognize (function : Function) : Except RecognitionError (Supported function) :=
  match function with
  | { name, returnType, parameters, locals := [],
      body := .seq (.return returnedType expression) .skip } => by
      cases returnType with
      | mk signedness bits =>
          match widthEq : widthOfBits? bits with
          | none => exact .error (.unsupportedWidth bits)
          | some found =>
              by_cases returnEq : returnedType = { signedness := signedness, width := bits }
              · subst returnedType
                let width := found.val
                have bitsEq : width.bits = bits := found.property
                let canonical : Function :=
                  { name
                    returnType := scalarType signedness width
                    parameters
                    locals := []
                    body := .seq (.return (scalarType signedness width) expression) .skip }
                have functionEq : canonical =
                    { name
                      returnType := { signedness := signedness, width := bits }
                      parameters
                      locals := []
                      body := .seq
                        (.return { signedness := signedness, width := bits } expression) .skip } := by
                  simp [canonical, scalarType, bitsEq]
                match recognizeAddExpression signedness width parameters expression with
                | .error error => exact .error error
                | .ok supported =>
                    exact .ok ((Supported.returnedAdd name width parameters expression supported).transport
                      functionEq)
              · exact .error .returnTypeMismatch
  | _ => .error .unsupportedFunction

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

/-- Positive simulation for the scalar LVE model. Unit locals and identity
globals make successful L1 and generated L2 outcomes identical. -/
private theorem lveResultMem (layout : FrameLayout function) {source}
    (supported : LocalVarExtract.Kernel.Supported (lveModel layout) source)
    {state post : State} {result : Except Unit Unit}
    (member : (result, post) ∈ (source.denote state).results) :
    (result, post) ∈ ((ML.LocalVarExtract.extract (lveModel layout) supported).target.denote ()
      state).results := by
  induction supported generalizing state post result with
  | skip =>
      change (result, post) = (Except.ok (), state) at member
      cases member
      change (Except.ok (), state) ∈ (L2.gets (fun _ => ()) [] state).results
      simp [L2.gets]
  | localUpdate update =>
      change (result, post) ∈ (liftE (AutoCorres.modify _) state).results at member
      rw [L2.mem_liftE_iff] at member
      rcases member with ⟨value, rfl, member⟩
      rw [mem_modify] at member
      rcases member with ⟨rfl, rfl⟩
      change (Except.ok (), post) ∈ (L2.gets (fun _ => ()) [] post).results
      simp [L2.gets]
  | globalUpdate update =>
      change (result, post) ∈ (liftE (AutoCorres.modify _) state).results at member
      rw [L2.mem_liftE_iff] at member
      rcases member with ⟨value, rfl, member⟩
      rw [mem_modify] at member
      rcases member with ⟨rfl, rfl⟩
      change (Except.ok (), update () state) ∈
        (bindE (L2.modify (update ())) (fun _ => L2.gets (fun _ => ()) []) state).results
      rw [mem_bindE_ok]
      exact ⟨(), update () state, by simp [L2.modify], by simp [L2.gets]⟩
  | guard test =>
      change (result, post) ∈
        (liftE (AutoCorres.guard (fun state => test () state)) state).results at member
      rw [L2.mem_liftE_iff] at member
      rcases member with ⟨value, rfl, member⟩
      rw [mem_guard] at member
      rcases member with ⟨holds, rfl, rfl⟩
      change (Except.ok (), post) ∈
        (bindE (L2.guard (test ())) (fun _ => L2.gets (fun _ => ()) []) post).results
      rw [mem_bindE_ok]
      exact ⟨(), post, by simp [L2.guard, mem_guard, holds], by simp [L2.gets]⟩
  | throw =>
      change (result, post) = (Except.error (), state) at member
      cases member
      rfl
  | seq firstSupported secondSupported firstIH secondIH =>
      change (result, post) ∈ (bindE _ _ state).results at member
      rcases member with ⟨firstResult, nextState, firstMember, continuation⟩
      change (result, post) ∈ (bindE _ _ state).results
      cases firstResult with
      | error error =>
          change (result, post) = (Except.error error, nextState) at continuation
          cases continuation
          exact ⟨Except.error (), post, firstIH firstMember, rfl⟩
      | ok value =>
          cases result with
          | ok result =>
              apply mem_bindE_ok.mpr
              exact ⟨(), nextState, firstIH firstMember, secondIH continuation⟩
          | error error =>
              exact ⟨Except.ok (), nextState, firstIH firstMember,
                secondIH continuation⟩
  | condition test thenSupported elseSupported thenIH elseIH =>
      classical
      change (result, post) ∈ (L1.condition (test ()) _ _ state).results at member
      change (result, post) ∈ (L2.condition (test ()) _ _ state).results
      unfold L1.condition at member
      unfold L2.condition
      by_cases holds : test () state
      · simp only [if_pos holds] at member ⊢
        exact thenIH member
      · simp only [if_neg holds] at member ⊢
        exact elseIH member
  | «catch» bodySupported handlerSupported bodyIH handlerIH =>
      change (result, post) ∈ (handle _ _ state).results at member
      rcases member with ⟨bodyResult, nextState, bodyMember, continuation⟩
      cases bodyResult with
      | ok value =>
          change (result, post) = (Except.ok value, nextState) at continuation
          cases continuation
          exact ⟨Except.ok (), post, bodyIH bodyMember, rfl⟩
      | error error =>
          exact ⟨Except.error (), nextState, bodyIH bodyMember,
            handlerIH continuation⟩
  | «loop» test bodySupported bodyIH =>
      rename_i body
      change (result, post) ∈ (L1.while (fun state => test () state)
        body.denote state).results at member
      unfold L1.while whileLoopE whileLoop at member
      simp only [Membership.mem] at member
      have mapLoop : ∀ {loopTest initial final}, WhileResult loopTest
          (whileLoopEBody fun _ => body.denote) initial final →
        ∀ outcome, final = some outcome →
          WhileResult loopTest
            (whileLoopEBody
              (ML.LocalVarExtract.extract (lveModel layout) bodySupported).target.denote)
            initial final := by
        intro loopTest initial final execution
        induction execution with
        | stop stopped =>
            intro outcome finalEq
            cases Option.some.inj finalEq
            exact .stop stopped
        | bodyFailure holds failed =>
            intro outcome finalEq
            cases finalEq
        | step holds sourceMember rest induction =>
            intro outcome finalEq
            rename_i value current next nextState final
            cases value with
            | error error =>
                exact .step holds sourceMember (induction outcome finalEq)
            | ok value =>
                cases value
                exact .step holds (bodyIH sourceMember)
                  (induction outcome finalEq)
      change WhileResult _ _ (some (Except.ok (), state))
        (some (result, post))
      exact mapLoop member (result, post) rfl
  | «call» bodySupported bodyIH => exact bodyIH member
  | fail => exact False.elim member

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

/-- A certified frontend result paired with all evidence needed to run the scalar phases. -/
structure Prepared (target : Target) (files : Preprocessor.FileMap) (entry name : String) where
  certified : ScalarSimpl.Certified target files entry name
  supported : Supported certified.function

inductive PreparationError where
  | frontend (error : ScalarSimpl.Error)
  | recognition (error : RecognitionError)
deriving Repr, Inhabited

/-- Parse, resolve, certify, and recognize one scalar fixture before phase translation. -/
@[irreducible] def prepare (target : Target) (files : Preprocessor.FileMap) (entry name : String) :
    Except PreparationError (Prepared target files entry name) := do
  let certified ← (ScalarSimpl.certifyFrontend target files entry name).mapError .frontend
  let supported ← (recognize certified.function).mapError .recognition
  return { certified, supported }

/-- A single embedded source file presented to the certified scalar frontend. -/
def sourceFiles (entry source : String) : Preprocessor.FileMap :=
  [{ name := entry, source }]

namespace Prepared

noncomputable def translation (prepared : Prepared target files entry name) :
    Translation prepared.certified prepared.supported :=
  translate prepared.certified prepared.supported

/-- Invoke the expression generated by recognition on a certified argument frame. -/
def invoke (prepared : Prepared target files entry name) (width : Nat)
    (arguments : List Int)
    (success : (prepared.certified.function.enter arguments).isOk) : BitVec width :=
  BitVec.ofInt width <| (prepared.supported.expression.eval
    (RefinementResult.get (prepared.certified.function.enter arguments) success)).getD 0

theorem invoke_eq_expression (prepared : Prepared target files entry name)
    (width : Nat) (arguments : List Int)
    (success : (prepared.certified.function.enter arguments).isOk)
    {expression : ScalarSimpl.Expr}
    (expressionEq : prepared.supported.expression = expression) :
    prepared.invoke width arguments success = BitVec.ofInt width
      ((expression.eval (RefinementResult.get
        (prepared.certified.function.enter arguments) success)).getD 0) := by
  rw [invoke, expressionEq]

theorem entered_eq_of_function_eq (prepared : Prepared target files entry name)
    (arguments : List Int)
    (success : (prepared.certified.function.enter arguments).isOk)
    {function : Function} (functionEq : prepared.certified.function = function) :
    RefinementResult.get (prepared.certified.function.enter arguments) success =
      RefinementResult.get (function.enter arguments) (by
        rw [← functionEq]
        exact success) := by
  subst function
  rfl

end Prepared

/-- Generated return-expression translation selected directly from embedded C source. -/
structure SourceSSA (target : Target) (source entry name : String) where
  prepared : Prepared target (sourceFiles entry source) entry name

/-- Translate a return-expression scalar function selected directly from embedded C source. -/
@[irreducible] def certifySSA (target : Target) (source entry name : String) :
    Except PreparationError (SourceSSA target source entry name) := do
  return { prepared := ← prepare target (sourceFiles entry source) entry name }

namespace SourceSSA

def function (artifact : SourceSSA target source entry name) : Function :=
  artifact.prepared.certified.function

noncomputable def translation (artifact : SourceSSA target source entry name) :
    Translation artifact.prepared.certified artifact.prepared.supported :=
  artifact.prepared.translation

def invoke (artifact : SourceSSA target source entry name) (width : Nat)
    (arguments : List Int) (success : (artifact.function.enter arguments).isOk) :
    BitVec width :=
  artifact.prepared.invoke width arguments success

end SourceSSA

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

/-! ## General scalar statement translation -/

/--
The statement pipeline does not require the return-only `Supported` recognizer.
That recognizer selects specialized word-expression artifacts; SimplConv and
local-variable extraction already cover every `ScalarSimpl.Stmt`, including
conditionals and loops.
-/
structure FunctionTranslation
    (certified : ScalarSimpl.Certified target files entry name) (width : Nat) where
  layout : FrameLayout certified.function
  simpl : SimplConv.Kernel.Certificate false emptyEnvironment certified.function.command
  lve : LocalVarExtract.Kernel.ClosedCertificate (lveModel layout) simpl.target

def translateFunction
    (certified : ScalarSimpl.Certified target files entry name) (width : Nat) :
    FunctionTranslation certified width :=
  let layout : FrameLayout certified.function := {}
  let simpl := ML.SimplConv.simplConv false emptyEnvironment
    certified.certificate.supported
  { layout
    simpl
    lve := ML.LocalVarExtract.extractCanonical (lveModel layout)
      (lveSupportedFromCertificate certified.certificate layout) }

/-- A statement-level scalar translation selected directly from embedded C source. -/
structure SourceTranslation (target : Target) (source entry name : String) (width : Nat) where
  certified : ScalarSimpl.Certified target (sourceFiles entry source) entry name

/-- Translate a scalar function, including control flow, directly from embedded C source. -/
@[irreducible] def certifyNondetSSA (target : Target) (source entry name : String) (width : Nat) :
    Except ScalarSimpl.Error (SourceTranslation target source entry name width) := do
  let certified ← ScalarSimpl.certifyFrontend target (sourceFiles entry source) entry name
  return { certified }

namespace SourceTranslation

def function (artifact : SourceTranslation target source entry name width) : Function :=
  artifact.certified.function

noncomputable def translation
    (artifact : SourceTranslation target source entry name width) :
    FunctionTranslation artifact.certified width :=
  translateFunction artifact.certified width

end SourceTranslation

namespace FunctionTranslation

def readResult (_translation : FunctionTranslation certified width) (state : State) :
    BitVec width :=
  BitVec.ofInt width state.result

noncomputable def l2 (translation : FunctionTranslation certified width) :
    L2.L2Program State Unit (BitVec width) :=
  L2.seq
    (LocalVarExtract.Kernel.CanonicalTarget.Syntax.denote translation.lve.target ())
    fun _ => L2.gets translation.readResult ["ret"]

theorem l2Functional (translation : FunctionTranslation certified width) :
    Nondet.Functional translation.l2 := by
  apply Nondet.Functional.bindE (translation.lve.functional ())
  intro _
  exact Nondet.Functional.liftE (Nondet.Functional.gets _)

private theorem projectCorres (translation : FunctionTranslation certified width) :
    CorresXF id (fun _ post => translation.readResult post) (fun _ _ => ())
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

theorem l2Corres (translation : FunctionTranslation certified width) :
    L2.L2Corres id translation.readResult (fun _ => ()) (fun _ => True)
      translation.l2 translation.simpl.target.denote := by
  change L2.L2Corres (fun state => state) translation.readResult
    (fun _ => ()) (fun _ => True) translation.l2 translation.simpl.target.denote
  simpa [L2.L2Corres, Function.comp_def, lveModel] using
    CorresXF.merge (translation.lve.corres ()) translation.projectCorres

noncomputable def target (translation : FunctionTranslation certified width) :
    L2.L2Program State Unit (BitVec width) :=
  L2.call translation.l2

theorem targetFunctional (translation : FunctionTranslation certified width) :
    Nondet.Functional translation.target := by
  unfold target L2.call
  exact Nondet.Functional.handle translation.l2Functional
    (fun _ => Nondet.Functional.fail)

/-- A normal source execution appears in the target produced by the canonical
scalar translation, without assuming target no-failure. -/
theorem translatedResultMem (certified : ScalarSimpl.Certified cTarget files entry name)
    (width : Nat) {state post : State}
    (execution : Simpl.Exec emptyEnvironment certified.function.command
      (.normal state) (.normal post)) :
    (Except.ok (BitVec.ofInt width post.result), post) ∈
      ((translateFunction certified width).target state).results := by
  let translation := translateFunction certified width
  have l1Member := ML.SimplConv.execution_mem false emptyEnvironment
    certified.certificate.supported execution
  have l2UnitMember := lveResultMem translation.layout
    (lveSupportedFromCertificate certified.certificate translation.layout) l1Member
  have closedUnitMember : (Except.ok (), post) ∈
      (LocalVarExtract.Kernel.CanonicalTarget.Syntax.denote translation.lve.target ()
        state).results := by
    rw [show translation.lve.target = LocalVarExtract.Kernel.CanonicalTarget.Syntax.ofGeneric
      (ML.LocalVarExtract.extract (lveModel translation.layout)
        (lveSupportedFromCertificate certified.certificate translation.layout)).target by rfl]
    rw [LocalVarExtract.Kernel.CanonicalTarget.Syntax.denote_ofGeneric]
    exact l2UnitMember
  have projectedMember :
      (Except.ok (BitVec.ofInt width post.result), post) ∈
        (translation.l2 state).results := by
    change (Except.ok (BitVec.ofInt width post.result), post) ∈
      (bindE (LocalVarExtract.Kernel.CanonicalTarget.Syntax.denote
        translation.lve.target ()) (fun _ => L2.gets translation.readResult ["ret"])
        state).results
    rw [mem_bindE_ok]
    exact ⟨(), post, closedUnitMember, by simp [L2.gets, readResult]⟩
  exact TypeStrengthen.mem_call_ok.mpr projectedMember

theorem translatedNoFailure (certified : ScalarSimpl.Certified cTarget files entry name)
    (width : Nat) {state post : State}
    (execution : Simpl.Exec emptyEnvironment certified.function.command
      (.normal state) (.normal post)) :
    ¬((translateFunction certified width).target state).failed :=
  (translateFunction certified width).targetFunctional.success state
    (translatedResultMem certified width execution)

theorem corres (translation : FunctionTranslation certified width) :
    ac_corres id false emptyEnvironment translation.readResult (fun _ => True)
      translation.target certified.function.command := by
  let chain : ChainCertificate (L2State := State) (L2Exception := Unit)
      (L2Result := BitVec width) (HLState := State) (WAException := Unit)
      false emptyEnvironment certified.function.command translation.target :=
    { stateProjectL2 := id
      returnExtractL2 := translation.readResult
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
      heapLifted := translation.l2
      heapLiftCorres := HeapLift.L2Tcorres_id translation.l2
      wordAbstracted := translation.l2
      wordAbstractCorres := CorresXF.refl (fun _ => True) translation.l2
      typeStrengthen := rfl }
  change ac_corres (fun state => state) false emptyEnvironment translation.readResult
    (fun _ => True) translation.target certified.function.command
  simpa [chain, Function.comp_def, id_eq] using chain.acCorres

end FunctionTranslation

namespace SourceTranslation

/-- Enter function arguments on the supplied caller state, then execute the generated target. -/
noncomputable def invoke
    (artifact : SourceTranslation target source entry name width)
    (arguments : List Int) : L2.L2Program State Unit (BitVec width) := fun state =>
  match artifact.certified.function.enter arguments state with
  | .error _ => AutoCorres.fail state
  | .ok entered => artifact.translation.target entered

end SourceTranslation

/-- Execute a return-expression function selected directly from embedded C source. -/
@[irreducible] def toSSA (target : Target) (source entry name : String) (width : Nat)
    (arguments : List Int) : BitVec width :=
  match prepare target (sourceFiles entry source) entry name with
  | .error _ => 0
  | .ok artifact =>
      match artifact.certified.function.enter arguments with
      | .error _ => 0
      | .ok entered =>
          BitVec.ofInt width ((artifact.supported.expression.eval entered).getD 0)

/-- The direct source callable is exactly the invocation of any certificate
returned by the same source translation. -/
theorem toSSA_eq_invoke (artifact : SourceSSA target source entry name)
    (certified : certifySSA target source entry name = .ok artifact)
    (width : Nat) (arguments : List Int) {entered : State}
    (enteredEq : artifact.function.enter arguments = .ok entered) :
    toSSA target source entry name width arguments =
      BitVec.ofInt width ((artifact.prepared.supported.expression.eval entered).getD 0) := by
  unfold certifySSA at certified
  cases preparedEq : prepare target (sourceFiles entry source) entry name with
  | error error =>
      rw [preparedEq] at certified
      cases certified
  | ok prepared =>
      rw [preparedEq] at certified
      have artifactEq : ({ prepared := prepared } : SourceSSA target source entry name) =
          artifact := Except.ok.inj certified
      cases artifactEq
      unfold toSSA
      rw [preparedEq]
      dsimp only
      change prepared.certified.function.enter arguments = .ok entered at enteredEq
      rw [enteredEq]

theorem toSSA_eq_artifact_invoke (artifact : SourceSSA target source entry name)
    (certified : certifySSA target source entry name = .ok artifact)
    (width : Nat) (arguments : List Int)
    (success : (artifact.function.enter arguments).isOk) :
    toSSA target source entry name width arguments =
      artifact.invoke width arguments success := by
  unfold SourceSSA.invoke Prepared.invoke
  exact toSSA_eq_invoke artifact certified width arguments
    (RefinementResult.eq_ok_get _ success)

/-- Execute a statement-level function selected directly from embedded C source.
Frontend or argument errors become monadic failure. -/
@[irreducible] noncomputable def toNondetSSA (target : Target) (source entry name : String)
    (width : Nat) (arguments : List Int) : L2.L2Program State Unit (BitVec width) :=
  match ScalarSimpl.certifyFrontend target (sourceFiles entry source) entry name with
  | .error _ => AutoCorres.fail
  | .ok certified => fun state =>
      match certified.function.enter arguments state with
      | .error _ => AutoCorres.fail state
      | .ok entered => (translateFunction certified width).target entered

/-- The direct nondeterministic source callable is exactly the invocation of a
certificate returned by the same frontend run. -/
theorem toNondetSSA_eq_invoke
    (artifact : SourceTranslation target source entry name width)
    (certified : certifyNondetSSA target source entry name width = .ok artifact)
    (arguments : List Int) :
    toNondetSSA target source entry name width arguments = artifact.invoke arguments := by
  unfold certifyNondetSSA at certified
  cases frontendEq : ScalarSimpl.certifyFrontend target (sourceFiles entry source) entry name with
  | error error =>
      rw [frontendEq] at certified
      cases certified
  | ok generated =>
      rw [frontendEq] at certified
      have artifactEq :
          ({ certified := generated } : SourceTranslation target source entry name width) =
            artifact := Except.ok.inj certified
      cases artifactEq
      unfold toNondetSSA SourceTranslation.invoke
      rw [frontendEq]
      rfl

namespace Prepared

/-- Refinement metadata remains tied to the selected frontend certificate. -/
theorem metadataOrigin (prepared : Prepared target files entry name) :
    prepared.translation.metadata.symbolId =
        prepared.certified.certificate.functionInfo.symbolId ∧
      prepared.translation.metadata.sourceName = prepared.certified.function.name :=
  translateMetadataOrigin prepared.certified prepared.supported

/-- Final correspondence exposed directly from a prepared refinement run. -/
theorem finalCorres (prepared : Prepared target files entry name) :
    ac_corres id false emptyEnvironment (readWord prepared.supported) (fun _ => True)
      prepared.translation.strengthen.target prepared.certified.function.command :=
  prepared.translation.finalCorres

/-- One argument-bound pure refinement generated from a selected scalar function. -/
structure Invocation (function : Function) (initial : State) (width : Nat)
    (value : BitVec width) where
  post : State
  execution : function.Exec initial (.normal post)
  resultEq : BitVec.ofInt width post.result = value

namespace Invocation

variable {function : Function} {initial : State} {width : Nat}
variable {value : BitVec width}

def generatedTarget (invocation : Invocation function initial width value) :
    L2.L2Program State Unit (BitVec width) :=
  fun _ => returnOk value invocation.post

theorem noFailure (invocation : Invocation function initial width value)
    (state : State) : ¬(invocation.generatedTarget state).failed := by
  simp [generatedTarget, returnOk, pure]

/-- Kernel-checked transport from the selected parsed command to its generated value. -/
theorem corres (invocation : Invocation function initial width value) :
    ac_corres id false emptyEnvironment (fun state => BitVec.ofInt width state.result)
      (fun state => state = initial) invocation.generatedTarget function.command := by
  intro state hypothesis
  rw [hypothesis.1]
  constructor
  · intro final execution
    have resolved := function.command_complete execution
    have equality := resolved.deterministic invocation.execution
    cases equality
    refine ⟨invocation.post, rfl, ?_⟩
    change (Except.ok (BitVec.ofInt width invocation.post.result), invocation.post) =
      (Except.ok value, invocation.post)
    rw [invocation.resultEq]
  · simp

/-- Read the generated result back from a transported concrete execution. -/
theorem transportResult (invocation : Invocation function initial width value)
    {post : State}
    (execution : Simpl.Exec emptyEnvironment function.command
      (.normal initial) (.normal post)) :
    BitVec.ofInt width post.result = value := by
  have noFail := invocation.noFailure initial
  have transported := invocation.corres initial ⟨rfl, noFail⟩
  obtain ⟨targetPost, equality, member⟩ := transported.1 _ execution
  injection equality with postEq
  subst targetPost
  change (Except.ok (BitVec.ofInt width post.result), post) =
    (Except.ok value, invocation.post) at member
  exact Except.ok.inj (congrArg Prod.fst member)

end Invocation

end Prepared

end Scalar

end Zag.Lang.AutoCorres.CParser.PhasePipeline
