import Lang.AutoCorres.AutoCorres
import Lang.AutoCorres.ML.simpl_conv
import Lang.AutoCorres.ML.local_var_extract
import Lang.AutoCorres.ML.heap_lift
import Lang.AutoCorres.ML.word_abstract
import Lang.AutoCorres.ML.type_strengthen
import Lang.AutoCorres.ML.pipeline

/-!
# AutoCorres phase implementation facade

Imports the proof-producing implementations of the five immediate AutoCorres
phases. The direct APIs below compose the adjacent SimplConv, LocalVarExtract,
and HeapLift implementations over their shared canonical syntax.
-/

namespace Zag.Lang.AutoCorres.ML.AutoCorres

open Zag.Lang.AutoCorres

universe u v w x y

/-- Narrow support for the exact L1 term generated from a supported SIMPL source. -/
structure L1Supported (checkTermination : Bool)
    (env : Simpl.Body Full Proc Fault) (source : Simpl.Com Full Proc Fault)
    (model : LocalVarExtract.Kernel.StateModel Full Locals Globals) where
  simplConv : SimplConv.Kernel.Supported source
  localVarExtract : LocalVarExtract.Kernel.Supported model
    (ML.SimplConv.simplConv checkTermination env simplConv).target

/-- The first two actual phase certificates, joined by a shared canonical L1 term. -/
structure L1Translation (checkTermination : Bool)
    (env : Simpl.Body Full Proc Fault) (source : Simpl.Com Full Proc Fault)
    (model : LocalVarExtract.Kernel.StateModel Full Locals Globals) where
  l1 : SimplConv.Kernel.Certificate checkTermination env source
  l2 : LocalVarExtract.Kernel.Certificate model l1.target

/-- Direct total SimplConv-to-LocalVarExtract translation over supported input. -/
def translateL1Supported (checkTermination : Bool)
    (env : Simpl.Body Full Proc Fault) (source : Simpl.Com Full Proc Fault)
    (model : LocalVarExtract.Kernel.StateModel Full Locals Globals)
    (supported : L1Supported checkTermination env source model) :
    L1Translation checkTermination env source model :=
  let l1 := ML.SimplConv.simplConv checkTermination env supported.simplConv
  let l2 := ML.LocalVarExtract.extract model supported.localVarExtract
  { l1, l2 }

/--
Support for the direct three-phase path. HeapLift evidence is indexed by the
actual LVE output selected at `initialLocals`, so no adapter or endpoint
equality can be supplied.
-/
structure L2Supported (checkTermination : Bool)
    (env : Simpl.Body Full Proc Fault) (source : Simpl.Com Full Proc Fault)
    (model : LocalVarExtract.Kernel.StateModel Full Locals Globals)
    (AbstractState : Type x) where
  l1 : L1Supported checkTermination env source model
  initialLocals : Locals
  stateMap : Globals -> AbstractState
  heapLift : HeapLift.Kernel.Supported stateMap
    ((ML.LocalVarExtract.extractCanonical model l1.localVarExtract).target
      initialLocals)

/-- Three certificates whose L1 and canonical L2 endpoints are shared by type. -/
structure L2Translation (checkTermination : Bool)
    (env : Simpl.Body Full Proc Fault) (source : Simpl.Com Full Proc Fault)
    (model : LocalVarExtract.Kernel.StateModel Full Locals Globals)
    (AbstractState : Type x) where
  l1 : SimplConv.Kernel.Certificate checkTermination env source
  l2 : LocalVarExtract.Kernel.ClosedCertificate model l1.target
  initialLocals : Locals
  stateMap : Globals -> AbstractState
  heapLift : HeapLift.Kernel.Certificate stateMap (l2.target initialLocals)

/-- Run SimplConv, LocalVarExtract, and HeapLift directly over indexed support. -/
def translateL2Supported (checkTermination : Bool)
    (env : Simpl.Body Full Proc Fault) (source : Simpl.Com Full Proc Fault)
    (model : LocalVarExtract.Kernel.StateModel Full Locals Globals)
    (AbstractState : Type x)
    (supported : L2Supported checkTermination env source model AbstractState) :
    L2Translation checkTermination env source model AbstractState :=
  let l1 := ML.SimplConv.simplConv checkTermination env supported.l1.simplConv
  let l2 := ML.LocalVarExtract.extractCanonical model supported.l1.localVarExtract
  let heapLift := ML.HeapLift.transform supported.heapLift
  { l1, l2
    initialLocals := supported.initialLocals
    stateMap := supported.stateMap
    heapLift }

/-! ## Complete closed unsigned read path -/

/--
Support for the first complete unsigned path. Every later item is indexed by
the actual output generated immediately before it.
-/
structure UnsignedSupported (width : Nat) (checkTermination : Bool)
    (env : Simpl.Body Full Proc Fault) (source : Simpl.Com Full Proc Fault)
    (model : LocalVarExtract.Kernel.StateModel Full (BitVec width) Globals)
    (State : Type) where
  l2 : L2Supported checkTermination env source model State
  heapToWord : Zag.Lang.AutoCorres.Pipeline.HeapToWord.Supported width
    (ML.HeapLift.transform l2.heapLift).target
  wordToStrengthen : Zag.Lang.AutoCorres.Pipeline.WordToStrengthen.Supported width
    (ML.WordAbstract.transformSource
      (ML.Pipeline.HeapToWord.adapt heapToWord).source).target

/-- Trusted result shape for the generated unsigned artifacts. -/
abbrev UnsignedTranslation (width : Nat) (checkTermination : Bool)
    (env : Simpl.Body Full Proc Fault) (source : Simpl.Com Full Proc Fault)
    (model : LocalVarExtract.Kernel.StateModel Full (BitVec width) Globals)
    (State : Type) :=
  Zag.Lang.AutoCorres.Pipeline.UnsignedTranslation width checkTermination
    env source model State

/--
Run SimplConv, LVE, HeapLift, WordAbstract, and TypeStrengthen directly over the
closed unsigned support slice.
-/
noncomputable def translateUnsignedSupported (width : Nat) (checkTermination : Bool)
    (env : Simpl.Body Full Proc Fault) (source : Simpl.Com Full Proc Fault)
    (model : LocalVarExtract.Kernel.StateModel Full (BitVec width) Globals)
    (State : Type)
    (supported : UnsignedSupported width checkTermination env source model State) :
    UnsignedTranslation width checkTermination env source model State :=
  let l1 := ML.SimplConv.simplConv checkTermination env supported.l2.l1.simplConv
  let l2 := ML.LocalVarExtract.extractCanonical model supported.l2.l1.localVarExtract
  let heapLift := ML.HeapLift.transform supported.l2.heapLift
  let heapAdapter := ML.Pipeline.HeapToWord.adapt supported.heapToWord
  let wordAbstract := ML.WordAbstract.transformSource heapAdapter.source
  let wordAdapter := ML.Pipeline.WordToStrengthen.adapt supported.wordToStrengthen
  let typeStrengthen := ML.TypeStrengthen.strengthenClosed wordAdapter.supported
  { l1, l2
    initialLocals := supported.l2.initialLocals
    stateMap := supported.l2.stateMap
    heapLift, heapAdapter, wordAbstract, wordAdapter, typeStrengthen }

end Zag.Lang.AutoCorres.ML.AutoCorres
