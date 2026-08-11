import Test.AutoCorres.CParser.ScalarSimpl.GcdPipelineSimpl

/-! # Fixture-derived `gcd` through HeapLift and guarded WordAbstract -/

namespace Zag.Test.AutoCorres.CParser.ScalarSimpl.GcdPipeline

open Zag.Lang.AutoCorres
open Zag.Lang.AutoCorres.CParser.ScalarSimpl
open FixtureHelpers

noncomputable section

abbrev UInt32 := WordAbstract.Kernel.ValueType.uwordInt 32
abbrev GcdPair := WordAbstract.Kernel.ValueType.prod UInt32 UInt32

def wordGuard (test : Globals -> Prop) (locals : Bool) :
    WordAbstract.Kernel.Source.Syntax .unit Globals .bool .bool :=
  .seq (.exactGuard test) fun _ => .gets (.bool locals) []

def wordSkip (locals : Bool) :
    WordAbstract.Kernel.Source.Syntax .unit Globals .bool .bool :=
  .gets (.bool locals) []

def wordGlobalUpdate (update : Globals -> Globals) (locals : Bool) :
    WordAbstract.Kernel.Source.Syntax .unit Globals .bool .bool :=
  .seq (.modify update) fun _ => .gets (.bool locals) []

def wordReturnTail (locals : Bool) :
    WordAbstract.Kernel.Source.Syntax .unit Globals .bool .bool :=
  .seq
    ((.seq (wordGuard (splitValid (.variable u32 2) locals) locals)
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
  .seq (wordGlobalUpdate (clearSlot 3 initial) initial) fun locals =>
    .seq (.while .bool .bool splitLoopTest exactLoopBody locals []) wordReturnTail

def wordLveSource :
    WordAbstract.Kernel.Source.Syntax .unit Globals .bool .bool :=
  .seq (.gets (.bool false) []) fun initial =>
    .seq
      (.catch (wordCatchBody initial) fun exception => .gets (.bool exception) [])
      fun locals =>
        .seq (.gets (.bool locals) []) fun locals =>
          .seq (wordGuard (splitReturned locals) locals) wordSkip

def wordProjectedSource :
    WordAbstract.Kernel.Source.Syntax .unit Globals .bool UInt32 :=
  .seq wordLveSource fun _ => .gets (.state UInt32 readResult) []

theorem heap_to_word_projected_exact : projectedL2 = wordProjectedSource.denote () := by
  simp only [projectedL2, projectedL2Syntax, wordProjectedSource, wordLveSource,
    wordCatchBody, wordReturnTail, wordGuard, wordSkip, wordGlobalUpdate,
    exactLoopBody, lveCertificate, lveSupported, lveLoopBodySupported,
    ML.LocalVarExtract.extractCanonical, ML.LocalVarExtract.extract,
    LocalVarExtract.Kernel.Certificate.close,
    LocalVarExtract.Kernel.CanonicalTarget.Syntax.ofGeneric,
    L2.Syntax.denote, WordAbstract.Kernel.Source.Syntax.denote,
    WordAbstract.Kernel.Source.Expr.eval]
  rfl

def readPair (globals : Globals) : Int × Int :=
  (globals.value 1, globals.value 2)

def canonicalPair (pair : Int × Int) : Prop :=
  WordAbstract.Kernel.intUnsignedCanonical 32 pair.1 /\
    WordAbstract.Kernel.intUnsignedCanonical 32 pair.2

def gcdPairTest (pair : Int × Int) (_ : Globals) : Prop := pair.1 ≠ 0

def gcdPairBody (pair : Int × Int) :
    WordAbstract.Kernel.Source.Syntax .unit Globals .bool GcdPair :=
  .gets
    (.pair
      (.umod (.uint 32 pair.2) (.uint 32 pair.1))
      (.uint 32 pair.1)) []

def gcdPairLoop (initial : Int × Int) :
    WordAbstract.Kernel.Source.Syntax .unit Globals .bool GcdPair :=
  .whileMappedGuarded .bool GcdPair gcdPairTest gcdPairBody initial ["gcd"]

def pairOfWords (a b : GcdWord32) : Int × Int :=
  (Int.ofNat a.toNat, Int.ofNat b.toNat)

def finalPairOfWords (a b : GcdWord32) : Int × Int :=
  (0, Int.ofNat (gcdWord a b).toNat)

private theorem toNat_nonzero {a : GcdWord32} (nonzero : a ≠ 0) :
    a.toNat ≠ 0 := by
  intro zero
  apply nonzero
  exact BitVec.toNat_inj.mp (by simpa using zero)

private theorem remainder_int_eq (a b : GcdWord32) (nonzero : a ≠ 0) :
    Int.ofNat b.toNat % Int.ofNat a.toNat =
      Int.ofNat (b % a).toNat := by
  calc
    Int.ofNat b.toNat % Int.ofNat a.toNat =
        Int.ofNat (b.toNat % a.toNat) := (Int.natCast_emod _ _).symm
    _ = Int.ofNat (b % a).toNat := congrArg Int.ofNat (gcd_remainder_toNat a b)

private theorem gcdPairBody_member (a b : GcdWord32) (nonzero : a ≠ 0)
    (state : Globals) :
    (Except.ok (pairOfWords (b % a) a), state) ∈
      ((gcdPairBody (pairOfWords a b)).denote () state).results := by
  simp [gcdPairBody, pairOfWords, WordAbstract.Kernel.Source.Syntax.denote,
    WordAbstract.Kernel.Source.Expr.eval, L2.gets, remainder_int_eq a b nonzero]

set_option maxHeartbeats 1000000 in
theorem gcdPairLoop_result (a b : GcdWord32) (state : Globals) :
    (Except.ok (finalPairOfWords a b), state) ∈
      ((gcdPairLoop (pairOfWords a b)).denote () state).results := by
  change WhileResult _ _ (some (Except.ok (pairOfWords a b), state))
    (some (Except.ok (finalPairOfWords a b), state))
  induction a, b using gcdWord.induct with
  | case1 b =>
      rw [show finalPairOfWords 0 b = pairOfWords 0 b by
        simp [finalPairOfWords, pairOfWords, gcdWord]]
      apply WhileResult.stop
      simp [gcdPairTest, pairOfWords]
  | case2 a b nonzero induction =>
      apply WhileResult.step
      · simpa [gcdPairTest, pairOfWords] using toNat_nonzero nonzero
      · exact gcdPairBody_member a b nonzero state
      · rw [show finalPairOfWords a b = finalPairOfWords (b % a) a by
          unfold finalPairOfWords
          rw [gcdWord_nonzero a b nonzero]]
        exact induction

theorem gcdPairLoop_terminates (a b : GcdWord32) (state : Globals) :
    WhileTerminates
      (fun result state => match result with
        | .error _ => False
        | .ok value => gcdPairTest value state)
      (whileLoopEBody fun value => (gcdPairBody value).denote ())
      (.ok (pairOfWords a b)) state := by
  induction a, b using gcdWord.induct with
  | case1 b =>
      apply WhileTerminates.stop
      simp [gcdPairTest, pairOfWords]
  | case2 a b nonzero induction =>
      apply WhileTerminates.step
      · simpa [gcdPairTest, pairOfWords] using toNat_nonzero nonzero
      · intro next nextState member
        simp only [whileLoopEBody, gcdPairBody, pairOfWords,
          WordAbstract.Kernel.Source.Syntax.denote,
          WordAbstract.Kernel.Source.Expr.eval, L2.gets, L2.mem_liftE_iff] at member
        rcases member with ⟨value, rfl, member⟩
        rw [mem_gets] at member
        rcases member with ⟨rfl, rfl⟩
        simpa [pairOfWords, remainder_int_eq a b nonzero] using induction

def wordSource :
    WordAbstract.Kernel.Source.Syntax .unit Globals .bool UInt32 :=
  .seq (.gets (.state GcdPair readPair) []) fun initial =>
    .seq (.exactGuard fun _ => canonicalPair initial) fun _ =>
      .seq wordProjectedSource fun concreteResult =>
        .seq (gcdPairLoop initial) fun loopResult =>
          .seq (.exactGuard fun _ => loopResult.2 = concreteResult) fun _ =>
            .gets (.uint 32 loopResult.2) []

def wordCertificate := ML.WordAbstract.transformSource wordSource

theorem wordSource_denote_exact :
    wordSource.denote () =
      L2.seq (L2.gets readPair []) fun initial =>
        L2.seq (L2.guard fun _ => canonicalPair initial) fun _ =>
          L2.seq projectedL2 fun concreteResult =>
            L2.seq ((gcdPairLoop initial).denote ()) fun loopResult =>
              L2.seq (L2.guard fun _ => loopResult.2 = concreteResult) fun _ =>
                L2.gets (fun _ => loopResult.2) [] := by
  simp only [wordSource, WordAbstract.Kernel.Source.Syntax.denote,
    WordAbstract.Kernel.Source.Expr.eval]
  rw [← heap_to_word_projected_exact]

private theorem int_roundTrip_of_canonical (value : Int)
    (canonical : WordAbstract.Kernel.intUnsignedCanonical 32 value) :
    Int.ofNat value.toNat = value := by
  calc
    Int.ofNat value.toNat = max value 0 := Int.ofNat_toNat value
    _ = value := by
      unfold WordAbstract.Kernel.intUnsignedCanonical at canonical
      omega

private theorem pair_words (pair : Int × Int) (canonical : canonicalPair pair) :
    ∃ a b : GcdWord32, pairOfWords a b = pair := by
  let a : GcdWord32 := BitVec.ofNat 32 pair.1.toNat
  let b : GcdWord32 := BitVec.ofNat 32 pair.2.toNat
  have firstBound := WordAbstract.Kernel.abstractGuard_of_intUnsignedCanonical
    32 pair.1 canonical.1
  have secondBound := WordAbstract.Kernel.abstractGuard_of_intUnsignedCanonical
    32 pair.2 canonical.2
  have firstNatBound : pair.1.toNat < 2 ^ 32 := by
    apply Int.ofNat_lt.mp
    calc
      Int.ofNat pair.1.toNat = pair.1 := int_roundTrip_of_canonical pair.1 canonical.1
      _ < Int.ofNat (2 ^ 32) := canonical.1.2
  have secondNatBound : pair.2.toNat < 2 ^ 32 := by
    apply Int.ofNat_lt.mp
    calc
      Int.ofNat pair.2.toNat = pair.2 := int_roundTrip_of_canonical pair.2 canonical.2
      _ < Int.ofNat (2 ^ 32) := canonical.2.2
  have firstToNat : a.toNat = pair.1.toNat := by
    simp [a, BitVec.toNat_ofNat, Nat.mod_eq_of_lt firstNatBound]
  have secondToNat : b.toNat = pair.2.toNat := by
    simp [b, BitVec.toNat_ofNat, Nat.mod_eq_of_lt secondNatBound]
  refine ⟨a, b, ?_⟩
  apply Prod.ext
  · change Int.ofNat a.toNat = pair.1
    rw [firstToNat]
    exact int_roundTrip_of_canonical pair.1 canonical.1
  · change Int.ofNat b.toNat = pair.2
    rw [secondToNat]
    exact int_roundTrip_of_canonical pair.2 canonical.2

/-- The checked recomputation wrapper is a sound no-heap HeapLift endpoint. -/
theorem heapLiftCorres : HeapLift.L2Tcorres id (wordSource.denote ()) projectedL2 := by
  rw [wordSource_denote_exact]
  intro state hypothesis
  let initial := readPair state
  have initialMember : (Except.ok initial, state) ∈
      (L2.gets (Exception := Bool) readPair [] state).results := by
    simp [L2.gets, initial]
  have afterInitialNoFail :
      ¬(L2.seq (L2.guard fun _ : Globals => canonicalPair initial) (fun _ =>
        L2.seq projectedL2 fun concreteResult =>
          L2.seq ((gcdPairLoop initial).denote ()) fun loopResult =>
            L2.seq (L2.guard fun _ => loopResult.2 = concreteResult) fun _ =>
              L2.gets (fun _ => loopResult.2) []) state).failed := by
    intro failed
    exact hypothesis.2 (WordAbstract.failed_L2_seq_iff.mpr
      (Or.inr ⟨initial, state, initialMember, failed⟩))
  have canonicalGuardNoFail :
      ¬(L2.guard (Exception := Bool) (fun _ : Globals => canonicalPair initial) state).failed :=
    fun failed => afterInitialNoFail (WordAbstract.failed_L2_seq_iff.mpr (Or.inl failed))
  have canonical := WordAbstract.guard_holds_of_noFail
    (fun _ : Globals => canonicalPair initial) canonicalGuardNoFail
  have canonicalMember := WordAbstract.guard_member
    (Exception := Bool) (state := state)
    (fun _ : Globals => canonicalPair initial) canonical
  have afterCanonicalNoFail :
      ¬(L2.seq projectedL2 (fun concreteResult =>
        L2.seq ((gcdPairLoop initial).denote ()) fun loopResult =>
          L2.seq (L2.guard fun _ => loopResult.2 = concreteResult) fun _ =>
            L2.gets (fun _ => loopResult.2) []) state).failed := by
    intro failed
    exact afterInitialNoFail (WordAbstract.failed_L2_seq_iff.mpr
      (Or.inr ⟨(), state, canonicalMember, failed⟩))
  have projectedNoFail : ¬(projectedL2 state).failed := fun failed =>
    afterCanonicalNoFail (WordAbstract.failed_L2_seq_iff.mpr (Or.inl failed))
  obtain ⟨a, b, initialEq⟩ := pair_words initial canonical
  refine ⟨?_, fun failed => projectedNoFail failed⟩
  intro result post member
  cases result with
  | error exception =>
      apply WordAbstract.mem_L2_seq_iff.mpr
      exact Or.inr ⟨initial, state, initialMember,
        WordAbstract.mem_L2_seq_iff.mpr (Or.inr ⟨(), state, canonicalMember,
          WordAbstract.mem_L2_seq_iff.mpr
            (Or.inl ⟨exception, post, member, rfl, rfl⟩)⟩)⟩
  | ok concreteResult =>
      have recomputeNoFail :
          ¬(L2.seq ((gcdPairLoop initial).denote ()) (fun loopResult =>
            L2.seq (L2.guard fun _ : Globals => loopResult.2 = concreteResult)
              (fun _ => L2.gets (fun _ => loopResult.2) [])) post).failed := by
        intro failed
        exact afterCanonicalNoFail (WordAbstract.failed_L2_seq_iff.mpr
          (Or.inr ⟨concreteResult, post, member, failed⟩))
      have loopMember : (Except.ok (finalPairOfWords a b), post) ∈
          ((gcdPairLoop initial).denote () post).results := by
        rw [← initialEq]
        exact gcdPairLoop_result a b post
      have equalityGuardNoFail :
          ¬(L2.guard (Exception := Bool)
            (fun _ : Globals => (finalPairOfWords a b).2 = concreteResult) post).failed :=
        fun failed => recomputeNoFail (WordAbstract.failed_L2_seq_iff.mpr
          (Or.inr ⟨finalPairOfWords a b, post, loopMember,
            WordAbstract.failed_L2_seq_iff.mpr (Or.inl failed)⟩))
      have equality := WordAbstract.guard_holds_of_noFail
        (fun _ : Globals => (finalPairOfWords a b).2 = concreteResult)
        equalityGuardNoFail
      have equalityMember := WordAbstract.guard_member
        (Exception := Bool)
        (state := post)
        (fun _ : Globals => (finalPairOfWords a b).2 = concreteResult) equality
      apply WordAbstract.mem_L2_seq_iff.mpr
      exact Or.inr ⟨initial, state, initialMember,
        WordAbstract.mem_L2_seq_iff.mpr (Or.inr ⟨(), state, canonicalMember,
          WordAbstract.mem_L2_seq_iff.mpr (Or.inr ⟨concreteResult, post, member,
            WordAbstract.mem_L2_seq_iff.mpr
              (Or.inr ⟨finalPairOfWords a b, post, loopMember,
                WordAbstract.mem_L2_seq_iff.mpr (Or.inr ⟨(), post, equalityMember,
                  by simpa [L2.gets, equality]⟩)⟩)⟩)⟩)⟩

theorem word_consumes_heap_endpoint :
    WordAbstract.corresTA (fun _ => True)
      (WordAbstract.Kernel.typeMap UInt32).abstract id
      (wordCertificate.target.denote ()) (wordSource.denote ()) :=
  wordCertificate.corres ()

end

end Zag.Test.AutoCorres.CParser.ScalarSimpl.GcdPipeline
