import Lang.AutoCorres.L1
import Lang.AutoCorres.L2
import Lang.AutoCorres.HeapLift
import Lang.AutoCorres.WordAbstract
import Lang.AutoCorres.TypeStrengthen
import Lang.AutoCorres.CorresXF

/-!
# Top-level AutoCorres correspondence

Corresponds only to [`tools/autocorres/AutoCorres.thy`](https://github.com/seL4/l4v/blob/bc2599a59c43e673dca021b10b9841e9b8da4430/tools/autocorres/AutoCorres.thy).
-/

namespace Zag.Lang.AutoCorres

universe u v w x y z
universe uState uConcrete uL2State uHLState
universe uException uSourceException uTargetException uL2Exception uWAException
universe uResult uL2Result uWAResult uProc uFault

variable {State : Type uState} {ConcreteState : Type uConcrete}
variable {L2State : Type uL2State} {HLState : Type uHLState}
variable {Exception : Type uException}
variable {SourceException : Type uSourceException}
variable {TargetException : Type uTargetException}
variable {L2Exception : Type uL2Exception}
variable {WAException : Type uWAException}
variable {Result : Type uResult} {L2Result : Type uL2Result}
variable {WAResult : Type uWAResult}
variable {Proc : Type uProc} {Fault : Type uFault}

/-- Identity word-abstraction correspondence. -/
theorem corresTA_trivial (program : L2.L2Program State Exception Result) :
    WordAbstract.corresTA (fun _ => True) id id program program := by
  exact CorresXF.refl (fun _ => True) program

/-- Use the identity heap-lift phase when heap lifting is skipped. -/
theorem L2Tcorres_trivial_from_local_var_extract
    {stateProject : ConcreteState → State}
    {returnExtract : ConcreteState → Result}
    {exceptionExtract : ConcreteState → Exception}
    {precondition : ConcreteState → Prop}
    {abstract : L2.L2Program State Exception Result}
    {concrete : L1.L1Program ConcreteState}
    (_ : L2.L2Corres stateProject returnExtract exceptionExtract precondition
      abstract concrete) :
    HeapLift.L2Tcorres id abstract abstract := by
  exact HeapLift.L2Tcorres_id abstract

/-- Use the identity word-abstraction phase when word abstraction is skipped. -/
theorem corresTA_trivial_from_heap_lift
    {stateMap : ConcreteState → State}
    {abstract : L2.L2Program State Exception Result}
    {concrete : L2.L2Program ConcreteState Exception Result}
    (_ : HeapLift.L2Tcorres stateMap abstract concrete) :
    WordAbstract.corresTA (fun _ => True) id id abstract abstract := by
  exact corresTA_trivial abstract

/-- The exception-discarding `L2.call` wrapper is a final correspondence link. -/
theorem corresXF_from_L2_call
    {source : L2.L2Program State SourceException Result}
    {target : L2.L2Program State TargetException Result}
    (exceptionMap : SourceException → State → TargetException)
    (equality : L2.call (Exception := TargetException) source = target) :
    CorresXF id (fun result _ => result) exceptionMap (fun _ => True)
      target source := by
  intro state hypothesis
  have callNoFail :
      ¬ (L2.call (Exception := TargetException) source state).failed := by
    rw [equality]
    exact hypothesis.2
  constructor
  · intro result post member
    cases result with
    | error exception =>
        exact False.elim (callNoFail
          (TypeStrengthen.failed_call.mpr (Or.inr ⟨exception, post, member⟩)))
    | ok result =>
        have callMember : (Except.ok result, post) ∈
            (L2.call (Exception := TargetException) source state).results :=
          TypeStrengthen.mem_call_ok.mpr member
        rw [equality] at callMember
        exact callMember
  · intro sourceFailed
    exact callNoFail (TypeStrengthen.failed_call.mpr (Or.inl sourceFailed))

/--
Expose the final `L2.call`/TypeStrengthen link as an exact closed-SSA
refinement. The generated expressions remain monadic calls in `PrimFuncCtx`.
-/
def corresXF_from_L2_call_toSSA
    {State SourceException TargetException Result : Type}
    [Repr (Except SourceException Result)]
    [Repr (Except TargetException Result)]
    {source : L2.L2Program State SourceException Result}
    {target : L2.L2Program State TargetException Result}
    (exceptionMap : SourceException → State → TargetException)
    (equality : L2.call (Exception := TargetException) source = target) :
    SSABridge.Refinement (L2.toSSA source) (L2.toSSA target) :=
  SSABridge.Refinement.ofCorresXF id (fun result _ => result) exceptionMap
    (fun _ => True) (corresXF_from_L2_call exceptionMap equality)

/--
The final AutoCorres relation. Every SIMPL execution must be normal and map to
the target result set. The premise retains target no-failure, and termination is
required exactly when `checkTermination` is enabled.
-/
def ac_corres
    (stateProject : ConcreteState → State)
    (checkTermination : Bool)
    (env : Simpl.Body ConcreteState Proc Fault)
    (returnExtract : ConcreteState → Result)
    (precondition : ConcreteState → Prop)
    (target : L2.L2Program State Exception Result)
    (source : Simpl.Com ConcreteState Proc Fault) : Prop :=
  ∀ state, (precondition state ∧ ¬ (target (stateProject state)).failed) →
    (∀ final, Simpl.Exec env source (.normal state) final →
      ∃ post, final = .normal post ∧
        (Except.ok (returnExtract post), stateProject post) ∈
          (target (stateProject state)).results) ∧
    (checkTermination = true →
      Simpl.Terminates env source (.normal state))

/-- Compose the adjacent L1, L2, heap-lift, word-abstraction, and TS links. -/
theorem ac_corres_chain
    {cL1 : L1.L1Program ConcreteState}
    {cL2 : L2.L2Program L2State L2Exception L2Result}
    {cHL : L2.L2Program HLState L2Exception L2Result}
    {cWA : L2.L2Program HLState WAException WAResult}
    {target : L2.L2Program HLState TargetException WAResult}
    {source : Simpl.Com ConcreteState Proc Fault}
    {checkTermination : Bool}
    {env : Simpl.Body ConcreteState Proc Fault}
    {stateProjectL2 : ConcreteState → L2State}
    {returnExtractL2 : ConcreteState → L2Result}
    {exceptionExtractL2 : ConcreteState → L2Exception}
    {preconditionL2 : ConcreteState → Prop}
    {stateProjectHL : L2State → HLState}
    {preconditionWA : HLState → Prop}
    {returnExtractWA : L2Result → WAResult}
    {exceptionExtractWA : L2Exception → WAException}
    (l1Corres : L1.L1Corres checkTermination env cL1 source)
    (l2Corres : L2.L2Corres stateProjectL2 returnExtractL2
      exceptionExtractL2 preconditionL2 cL2 cL1)
    (heapLiftCorres : HeapLift.L2Tcorres stateProjectHL cHL cL2)
    (wordAbstractCorres : WordAbstract.corresTA preconditionWA
      returnExtractWA exceptionExtractWA cWA cHL)
    (typeStrengthen : L2.call (Exception := TargetException) cWA = target) :
    ac_corres (stateProjectHL ∘ stateProjectL2) checkTermination env
      (returnExtractWA ∘ returnExtractL2)
      (fun state => preconditionL2 state ∧
        preconditionWA (stateProjectHL (stateProjectL2 state)))
      target source := by
  intro state hypothesis
  have callNoFail :
      ¬ (L2.call (Exception := TargetException) cWA
        (stateProjectHL (stateProjectL2 state))).failed := by
    rw [typeStrengthen]
    exact hypothesis.2
  have waNoFail :
      ¬ (cWA (stateProjectHL (stateProjectL2 state))).failed := by
    intro failed
    exact callNoFail (TypeStrengthen.failed_call.mpr (Or.inl failed))
  have waRefinement := wordAbstractCorres
    (stateProjectHL (stateProjectL2 state)) ⟨hypothesis.1.2, waNoFail⟩
  have hlRefinement := heapLiftCorres (stateProjectL2 state)
    ⟨True.intro, waRefinement.2⟩
  have l2Refinement := l2Corres state
    ⟨hypothesis.1.1, hlRefinement.2⟩
  have l1 := l1Corres state l2Refinement.2
  constructor
  · intro final execution
    have matched := l1.1 final execution
    cases final with
    | normal post =>
        refine ⟨post, rfl, ?_⟩
        have l2Member := l2Refinement.1 (Except.ok ()) post matched
        have hlMember := hlRefinement.1
          (Except.ok (returnExtractL2 post)) (stateProjectL2 post) l2Member
        have waMember := waRefinement.1
          (Except.ok (returnExtractL2 post))
          (stateProjectHL (stateProjectL2 post)) hlMember
        have callMember : (Except.ok (returnExtractWA (returnExtractL2 post)),
            stateProjectHL (stateProjectL2 post)) ∈
            (L2.call (Exception := TargetException) cWA
              (stateProjectHL (stateProjectL2 state))).results :=
          TypeStrengthen.mem_call_ok.mpr waMember
        rw [typeStrengthen] at callMember
        exact callMember
    | abrupt post =>
        have l2Member := l2Refinement.1 (Except.error ()) post matched
        have hlMember := hlRefinement.1
          (Except.error (exceptionExtractL2 post))
          (stateProjectL2 post) l2Member
        have waMember := waRefinement.1
          (Except.error (exceptionExtractL2 post))
          (stateProjectHL (stateProjectL2 post)) hlMember
        exact False.elim (callNoFail
          (TypeStrengthen.failed_call.mpr (Or.inr
            ⟨exceptionExtractWA (exceptionExtractL2 post),
              stateProjectHL (stateProjectL2 post), by
              simpa [Function.comp_def] using waMember⟩)))
    | fault label => exact False.elim matched
    | stuck => exact False.elim matched
  · exact l1.2

/--
A phase certificate whose correspondence fields share their endpoints by
construction. In particular, each phase consumes the preceding program, and
the final equality consumes the word-abstraction output.
-/
structure ChainCertificate
    {ConcreteState : Type u}
    {Proc : Type v}
    {Fault : Type w}
    {L2State : Type x}
    {L2Exception : Type uL2Exception}
    {L2Result : Type y}
    {HLState : Type z}
    {WAException : Type uWAException}
    {WAResult : Type uWAResult}
    {TargetException : Type uTargetException}
    (checkTermination : Bool)
    (env : Simpl.Body ConcreteState Proc Fault)
    (source : Simpl.Com ConcreteState Proc Fault)
    (target : L2.L2Program HLState TargetException WAResult) where
  stateProjectL2 : ConcreteState → L2State
  returnExtractL2 : ConcreteState → L2Result
  exceptionExtractL2 : ConcreteState → L2Exception
  preconditionL2 : ConcreteState → Prop
  stateProjectHL : L2State → HLState
  preconditionWA : HLState → Prop
  returnExtractWA : L2Result → WAResult
  exceptionExtractWA : L2Exception → WAException
  l1 : L1.L1Program ConcreteState
  l1Corres : L1.L1Corres checkTermination env l1 source
  l2 : L2.L2Program L2State L2Exception L2Result
  l2Corres : L2.L2Corres stateProjectL2 returnExtractL2 exceptionExtractL2
    preconditionL2 l2 l1
  heapLifted : L2.L2Program HLState L2Exception L2Result
  heapLiftCorres : HeapLift.L2Tcorres stateProjectHL heapLifted l2
  wordAbstracted : L2.L2Program HLState WAException WAResult
  wordAbstractCorres : WordAbstract.corresTA preconditionWA returnExtractWA
    exceptionExtractWA wordAbstracted heapLifted
  typeStrengthen :
    L2.call (Exception := TargetException) wordAbstracted = target

/-- Project the final AutoCorres theorem from an adjacent chain certificate. -/
theorem ChainCertificate.acCorres
    (certificate : ChainCertificate
      (L2State := L2State) (L2Result := L2Result)
      (L2Exception := L2Exception)
      (WAException := WAException)
      checkTermination env source target) :
    ac_corres (certificate.stateProjectHL ∘ certificate.stateProjectL2)
      checkTermination env
      (certificate.returnExtractWA ∘ certificate.returnExtractL2)
      (fun state => certificate.preconditionL2 state ∧
        certificate.preconditionWA
          (certificate.stateProjectHL (certificate.stateProjectL2 state)))
      target source :=
  ac_corres_chain certificate.l1Corres certificate.l2Corres
    certificate.heapLiftCorres certificate.wordAbstractCorres
    certificate.typeStrengthen

end Zag.Lang.AutoCorres
