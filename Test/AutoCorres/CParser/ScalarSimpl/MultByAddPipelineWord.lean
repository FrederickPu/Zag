import Test.AutoCorres.CParser.ScalarSimpl.MultByAddPipelineSimpl

/-! # Fixture-derived `mult_by_add` through sound no-heap HeapLift and WordAbstract -/

namespace Zag.Test.AutoCorres.CParser.ScalarSimpl.MultByAddPipeline

open Zag.Lang.AutoCorres
open Zag.Lang.AutoCorres.CParser.ScalarSimpl
open FixtureHelpers

noncomputable section

/-- The fixture has no heap operations, so HeapLift is the sound identity certificate. -/
theorem heapLiftCorres : HeapLift.L2Tcorres id projectedL2 projectedL2 :=
  HeapLift.L2Tcorres_id projectedL2

noncomputable def propositionBool (proposition : Prop) : Bool :=
  @ite Bool proposition (Classical.propDecidable _) true false

theorem propositionBool_exact (proposition : Prop) :
    propositionBool proposition = true ↔ proposition := by
  simp [propositionBool]

def wordGuard (test : Globals -> Prop) (locals : Bool) :
    WordAbstract.Kernel.Source.Syntax .unit Globals .bool .bool :=
  .seq (.exactGuard test) fun _ => .gets (.bool locals) []

def wordSkip (locals : Bool) :
    WordAbstract.Kernel.Source.Syntax .unit Globals .bool .bool :=
  .gets (.bool locals) []

def wordGlobalUpdate (update : Globals -> Globals) (locals : Bool) :
    WordAbstract.Kernel.Source.Syntax .unit Globals .bool .bool :=
  .seq (.modify update) fun _ => .gets (.bool locals) []

def wordDeclaration (locals : Bool) :
    WordAbstract.Kernel.Source.Syntax .unit Globals .bool .bool :=
  .seq (wordGlobalUpdate (clearSlot 3 locals) locals) fun locals =>
    .seq (wordGuard (splitValid (.literal s32 0) locals) locals) fun locals =>
      wordGlobalUpdate (updateExpression 3 u32 (.literal s32 0) locals) locals

def wordReturnTail (locals : Bool) :
    WordAbstract.Kernel.Source.Syntax .unit Globals .bool .bool :=
  .seq
    ((.seq (wordGuard (splitValid (.variable u32 3) locals) locals)
        fun (locals : Bool) =>
          .seq
            (.seq (wordGlobalUpdate (setResult locals) locals) fun _ =>
              .gets (.bool true) [])
            fun locals => .throw locals []) :
      WordAbstract.Kernel.Source.Syntax .unit Globals .bool .bool)
    fun (locals : Bool) => wordSkip locals

def exactLoopBody (locals : Bool) : L2.Syntax Globals Bool Bool :=
  (ML.LocalVarExtract.extractCanonical model lveLoopBodySupported).target locals

def wordCatchBody (initial : Bool) :
    WordAbstract.Kernel.Source.Syntax .unit Globals .bool .bool :=
  .seq (wordDeclaration initial) fun locals =>
    .seq (.while .bool .bool splitLoopTest exactLoopBody locals []) wordReturnTail

def wordLveSource :
    WordAbstract.Kernel.Source.Syntax .unit Globals .bool .bool :=
  .seq (.gets (.bool false) []) fun initial =>
    .seq
      (.catch (wordCatchBody initial) fun exception => .gets (.bool exception) [])
      fun locals =>
        .seq (.gets (.bool locals) []) fun locals =>
          .seq (wordGuard (splitReturned locals) locals) wordSkip

def wordSource :
    WordAbstract.Kernel.Source.Syntax .unit Globals .bool (.word 32) :=
  .seq wordLveSource fun _ => .gets (.state (.word 32) readResult) []

theorem heap_to_word_endpoint_exact : projectedL2 = wordSource.denote () := by
  simp only [projectedL2, projectedL2Syntax, wordSource, wordLveSource,
    wordCatchBody, wordDeclaration, wordReturnTail, wordGuard, wordSkip,
    wordGlobalUpdate, exactLoopBody, lveCertificate, lveSupported,
    lveDeclarationSupported, lveLoopBodySupported,
    ML.LocalVarExtract.extractCanonical, ML.LocalVarExtract.extract,
    LocalVarExtract.Kernel.Certificate.close,
    LocalVarExtract.Kernel.CanonicalTarget.Syntax.ofGeneric,
    L2.Syntax.denote, WordAbstract.Kernel.Source.Syntax.denote,
    WordAbstract.Kernel.Source.Expr.eval]
  rfl

def wordCertificate := ML.WordAbstract.transformSource wordSource

/-- Loop-aware WordAbstract consumes the exact HeapLift endpoint and preserves updates. -/
theorem word_consumes_heap_endpoint :
    WordAbstract.corresTA (fun _ => True) BitVec.toNat id
      (wordCertificate.target.denote ()) projectedL2 := by
  rw [heap_to_word_endpoint_exact]
  exact wordCertificate.corres ()

end

end Zag.Test.AutoCorres.CParser.ScalarSimpl.MultByAddPipeline
