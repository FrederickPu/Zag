import Lang.AutoCorres.CParser.CallGraph
import Lang.AutoCorres.CParser.MemorySimpl
import Lang.AutoCorres.CParser.PhasePipeline.Scalar

/-! # Fixture-derived C AutoCorres phase scheduling -/

namespace Zag.Lang.AutoCorres.CParser.PhasePipeline

open ProgramAnalysis
open Zag.Lang.AutoCorres

inductive Error where
  | frontend
  | callGraph (checks : CallGraph.InvariantChecks)
  | memory (error : MemorySimpl.Error)
  | localVarExtract
  | heapLiftUnsupported
deriving Repr, Inhabited

abbrev Full := MemorySimpl.State
abbrev Locals := Unit
abbrev Globals := MemorySimpl.State

/-- Preserve the analyzed byte-memory state as L2 globals. -/
def stateModel : LocalVarExtract.Kernel.StateModel Full Locals Globals where
  projectGlobals := id
  projectLocals := fun _ => ()
  assemble := fun _ globals => globals
  projectGlobals_assemble := by intros; rfl
  projectLocals_assemble := by intros; rfl
  assemble_project := by intro state; rfl

def recognizeLve :
    (source : L1.Syntax Full) →
      Except Unit (LocalVarExtract.Kernel.Supported stateModel source)
  | .skip => .ok .skip
  | .modify update => .ok (.globalUpdate fun _ state => update state)
  | .guard test => .ok (.guard fun _ state => test state)
  | .throw => .ok .throw
  | .seq first second => do
      return .seq (← recognizeLve first) (← recognizeLve second)
  | .condition test thenBranch elseBranch => do
      return .condition (fun _ state => test state)
        (← recognizeLve thenBranch) (← recognizeLve elseBranch)
  | .catch body handler => do
      return .catch (← recognizeLve body) (← recognizeLve handler)
  | .while test body => do
      return .loop (fun _ state => test state) (← recognizeLve body)
  | .call body => do
      return .call (← recognizeLve body)
  | .fail => .ok .fail
  | .spec _ => .error ()

private def append (entries : List PhaseEntry) (phase : Phase) (mode : PhaseMode) :=
  entries ++ [{ phase := phase, mode := mode }]

private def runFunction (options : Options) (target : Target)
    (files : Preprocessor.FileMap) (entry : String) (program : Program)
    (function : FunctionInfo) : Except Error FunctionMetadata := do
  let symbol ← match program.symbolById? function.symbolId with
    | some symbol => .ok symbol
    | none => .error .frontend
  let memory ← (MemorySimpl.certifyFrontend target files entry symbol.sourceName).mapError .memory
  let simpl := ML.SimplConv.simplConv false MemorySimpl.emptyEnvironment
    memory.certificate.supported
  let mut phases := append [] .simplConv .translated
  let _ ← (recognizeLve simpl.target).mapError fun _ => .localVarExtract
  phases := append phases .localVarExtract .translated
  if options.skipHeapAbs then Except.ok () else Except.error .heapLiftUnsupported
  phases := append phases .wordAbstract .exactIdentity
  phases := append phases .typeStrengthen .exactIdentity
  return { symbolId := function.symbolId, sourceName := symbol.sourceName, phases }

/-- Execute phase dispatch for every analyzed function and retain the resulting table. -/
def run (options : Options) (target : Target) (files : Preprocessor.FileMap)
    (entry : String) : Except Error Metadata := do
  let frontend := Frontend.preprocessAndAnalyze target files entry
  let program ← match frontend.program with
    | some program => .ok program
    | none => .error .frontend
  if !frontend.isSuccess then Except.error .frontend
  let _ ← (CallGraph.certify program).mapError .callGraph
  let functions ← program.functions.mapM (runFunction options target files entry program)
  return { files := [{ file := entry, functions }] }

/-- Proof artifacts for the branch where HeapLift was not scheduled. -/
structure SkippedHeapTranslation
    (certified : MemorySimpl.Certified target files entry name) where
  simpl : SimplConv.Kernel.Certificate false MemorySimpl.emptyEnvironment
    (certified.function.command certified.certificate.layout)
  lve : LocalVarExtract.Kernel.ClosedCertificate stateModel simpl.target

noncomputable def translateSkippedHeap
    (certified : MemorySimpl.Certified target files entry name)
    (supported : LocalVarExtract.Kernel.Supported stateModel
      (ML.SimplConv.simplConv false MemorySimpl.emptyEnvironment
        certified.certificate.supported).target) :
    SkippedHeapTranslation certified :=
  let simpl := ML.SimplConv.simplConv false MemorySimpl.emptyEnvironment
    certified.certificate.supported
  { simpl
    lve := ML.LocalVarExtract.extractCanonical stateModel supported }

namespace SkippedHeapTranslation

noncomputable def nonLifted (translation : SkippedHeapTranslation certified) :
    L2.L2Program Globals Unit Unit :=
  LocalVarExtract.Kernel.CanonicalTarget.Syntax.denote translation.lve.target ()

noncomputable def wordAbstracted (translation : SkippedHeapTranslation certified) :
    L2.L2Program Globals Unit Unit := translation.nonLifted

theorem wordAbstractCorres (translation : SkippedHeapTranslation certified) :
    WordAbstract.corresTA (fun _ => True) id id
      translation.wordAbstracted translation.nonLifted :=
  WordAbstract.corresTA_refl (fun _ => True) translation.nonLifted

noncomputable def strengthened (translation : SkippedHeapTranslation certified) :
    L2.L2Program Globals Unit Unit := L2.call translation.wordAbstracted

theorem typeStrengthenExact (translation : SkippedHeapTranslation certified) :
    L2.call translation.wordAbstracted = translation.strengthened := rfl

end SkippedHeapTranslation

end Zag.Lang.AutoCorres.CParser.PhasePipeline
