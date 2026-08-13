import Lang.AutoCorres.L2

/-!
# Local-variable extraction kernel interface

Logical support corresponds to [`tools/autocorres/LocalVarExtract.thy`](https://github.com/seL4/l4v/blob/bc2599a59c43e673dca021b10b9841e9b8da4430/tools/autocorres/LocalVarExtract.thy).
The `Kernel` namespace is the trusted pass-facing interface used by the ML
proof-producing implementation.
-/

namespace Zag.Lang.AutoCorres.LocalVarExtract

universe u v w

/-- Intersection of two predicates collected over pairs. -/
theorem Collect_prod_inter {α : Type u} {β : Type v} (P Q : α → β → Prop) :
    (fun pair : α × β =>
        pair ∈ ((fun pair : α × β => P pair.1 pair.2) : Set (α × β)) ∧
        pair ∈ ((fun pair : α × β => Q pair.1 pair.2) : Set (α × β))) =
      (fun pair : α × β => P pair.1 pair.2 ∧ Q pair.1 pair.2) := by
  rfl

/-- Union of two predicates collected over pairs. -/
theorem Collect_prod_union {α : Type u} {β : Type v} (P Q : α → β → Prop) :
    (fun pair : α × β =>
        pair ∈ ((fun pair : α × β => P pair.1 pair.2) : Set (α × β)) ∨
        pair ∈ ((fun pair : α × β => Q pair.1 pair.2) : Set (α × β))) =
      (fun pair : α × β => P pair.1 pair.2 ∨ Q pair.1 pair.2) := by
  rfl

namespace Kernel

/--
An exact decomposition of the L1 state into all locals and globals. These laws
make projection and assembly a lossless round trip rather than an approximation.
-/
structure StateModel (Full : Type u) (Locals : Type v) (Globals : Type w) where
  projectGlobals : Full -> Globals
  projectLocals : Full -> Locals
  assemble : Locals -> Globals -> Full
  projectGlobals_assemble : forall locals globals,
    projectGlobals (assemble locals globals) = globals
  projectLocals_assemble : forall locals globals,
    projectLocals (assemble locals globals) = locals
  assemble_project : forall state,
    assemble (projectLocals state) (projectGlobals state) = state

namespace Source

/-- Compatibility alias: LocalVarExtract consumes canonical reified L1 syntax. -/
abbrev Syntax (Full : Type u) (_Locals : Type v) (_Globals : Type w) :=
  L1.Syntax Full

/-- The concrete full-state transformation represented by a local update. -/
def localTransform (model : StateModel Full Locals Globals)
    (update : Locals -> Globals -> Locals) (state : Full) : Full :=
  model.assemble (update (model.projectLocals state) (model.projectGlobals state))
    (model.projectGlobals state)

/-- The concrete full-state transformation represented by a global update. -/
def globalTransform (model : StateModel Full Locals Globals)
    (update : Locals -> Globals -> Globals) (state : Full) : Full :=
  model.assemble (model.projectLocals state)
    (update (model.projectLocals state) (model.projectGlobals state))

namespace Syntax

/-- Compatibility name for the canonical L1 denotation. -/
noncomputable abbrev denote : Syntax Full Locals Globals -> L1.L1Program Full :=
  L1.Syntax.denote

end Syntax

end Source

namespace Target

/-- Reified L2 output for the universe-polymorphic all-locals fragment. -/
inductive Syntax (Locals : Type v) (Globals : Type w) where
  | skip
  | localUpdate (update : Locals -> Globals -> Locals)
  | globalUpdate (update : Locals -> Globals -> Globals)
  | guard (test : Locals -> Globals -> Prop)
  | throw
  | seq (first second : Syntax Locals Globals)
  | condition (test : Locals -> Globals -> Prop)
      (thenBranch elseBranch : Syntax Locals Globals)
  | «catch» (body handler : Syntax Locals Globals)
  | loop (test : Locals -> Globals -> Prop) (body : Syntax Locals Globals)
  | «call» (body : Syntax Locals Globals)
  | fail

namespace Syntax

/--
Interpret target syntax with explicit locals input. Returned and exceptional
locals are values; only globals inhabit the L2 monadic state. The certificate
requires the input to equal the locals projected from the related concrete
state. Catch receives exceptional locals extracted from the L1 post-state.
-/
noncomputable def denote :
    Syntax Locals Globals -> Locals -> L2.L2Program Globals Locals Locals
  | .skip, locals => L2.gets (fun _ => locals) []
  | .localUpdate update, locals => L2.gets (update locals) []
  | .globalUpdate update, locals =>
      L2.seq (L2.modify (update locals)) fun _ => L2.gets (fun _ => locals) []
  | .guard test, locals =>
      L2.seq (L2.guard (test locals)) fun _ => L2.gets (fun _ => locals) []
  | .throw, locals => L2.throw locals []
  | .seq first second, locals =>
      L2.seq (first.denote locals) fun nextLocals => second.denote nextLocals
  | .condition test thenBranch elseBranch, locals =>
      L2.condition (test locals) (thenBranch.denote locals) (elseBranch.denote locals)
  | .catch body handler, locals =>
      L2.catch (body.denote locals) fun exceptionalLocals =>
        handler.denote exceptionalLocals
  | .loop test body, locals => L2.while test body.denote locals []
  | .call body, locals => body.denote locals
  | .fail, _ => L2.fail

/-- Generated local-extraction targets have one result path and cannot both
return and fail. This excludes the nondeterministic `spec`/`unknown` L2 forms. -/
theorem functional {Locals Globals : Type} (target : Syntax Locals Globals)
    (locals : Locals) :
    Nondet.Functional (target.denote locals) := by
  induction target generalizing locals with
  | skip => exact Nondet.Functional.liftE (Nondet.Functional.gets _)
  | localUpdate => exact Nondet.Functional.liftE (Nondet.Functional.gets _)
  | globalUpdate update =>
      exact Nondet.Functional.bindE
        (Nondet.Functional.liftE (Nondet.Functional.modify _))
        (fun _ => Nondet.Functional.liftE (Nondet.Functional.gets _))
  | guard test =>
      apply Nondet.Functional.bindE
      · apply Nondet.Functional.liftE
        constructor
        · intro state left right leftMember rightMember
          exact leftMember.2.trans rightMember.2.symm
        · intro state result member failed
          exact failed member.1
      · intro _
        exact Nondet.Functional.liftE (Nondet.Functional.gets _)
  | throw => exact Nondet.Functional.throw _
  | seq first second firstIH secondIH =>
      exact Nondet.Functional.bindE (firstIH locals) secondIH
  | condition test thenBranch elseBranch thenIH elseIH =>
      classical
      simp only [denote]
      unfold L2.condition
      constructor
      · intro state left right leftMember rightMember
        by_cases holds : test locals state
        · simp only [if_pos holds] at leftMember rightMember
          exact (thenIH locals).unique state leftMember rightMember
        · simp only [if_neg holds] at leftMember rightMember
          exact (elseIH locals).unique state leftMember rightMember
      · intro state result member failed
        by_cases holds : test locals state
        · simp only [if_pos holds] at member failed
          exact (thenIH locals).success state member failed
        · simp only [if_neg holds] at member failed
          exact (elseIH locals).success state member failed
  | «catch» body handler bodyIH handlerIH =>
      exact Nondet.Functional.handle (bodyIH locals) handlerIH
  | «loop» test body bodyIH =>
      exact Nondet.Functional.whileLoopE0 bodyIH locals
  | «call» body bodyIH => exact bodyIH locals
  | fail => exact Nondet.Functional.fail

end Syntax

end Target

/-! ## Closed canonical seam -/

/-!
The Type0 canonical L2 output consumed definitionally by HeapLift. This seam is
separate from `Target.Syntax`, whose locals and globals remain universe-polymorphic.
-/
namespace CanonicalTarget

abbrev Syntax (Locals Globals : Type) :=
  Locals -> L2.Syntax Globals Locals Locals

namespace Syntax

/-- Structurally reify a closed generic extraction target in canonical L2 syntax. -/
@[simp] def ofGeneric : Target.Syntax Locals Globals -> Syntax Locals Globals
  | .skip, locals => .gets (fun _ => locals) []
  | .localUpdate update, locals => .gets (update locals) []
  | .globalUpdate update, locals =>
      .seq (.modify (update locals)) fun _ => .gets (fun _ => locals) []
  | .guard test, locals =>
      .seq (.guard (test locals)) fun _ => .gets (fun _ => locals) []
  | .throw, locals => .throw locals []
  | .seq first second, locals =>
      .seq (ofGeneric first locals) fun nextLocals => ofGeneric second nextLocals
  | .condition test thenBranch elseBranch, locals =>
      .condition (test locals) (ofGeneric thenBranch locals)
        (ofGeneric elseBranch locals)
  | .catch body handler, locals =>
      .catch (ofGeneric body locals) fun exceptionalLocals =>
        ofGeneric handler exceptionalLocals
  | .loop test body, locals => .while test (ofGeneric body) locals []
  | .call body, locals => .call (ofGeneric body locals)
  | .fail, _ => .fail

/-- Interpret the closed canonical target selected at an explicit locals value. -/
noncomputable def denote :
    Syntax Locals Globals -> Locals -> L2.L2Program Globals Locals Locals
  | target, locals => (target locals).denote

@[simp] theorem denote_ofGeneric (target : Target.Syntax Locals Globals)
    (locals : Locals) :
    denote (ofGeneric target) locals = target.denote locals := by
  induction target generalizing locals with
  | skip | localUpdate | globalUpdate | guard | throw | fail => rfl
  | seq first second firstIH secondIH =>
      simp only [ofGeneric, denote, L2.Syntax.denote, Target.Syntax.denote]
      change L2.seq (denote (ofGeneric first) locals)
          (fun value => denote (ofGeneric second) value) =
        L2.seq (first.denote locals) fun nextLocals => second.denote nextLocals
      rw [firstIH locals]
      congr 1
      funext nextLocals
      rw [secondIH nextLocals]
  | condition test thenBranch elseBranch thenIH elseIH =>
      simp only [ofGeneric, denote, L2.Syntax.denote, Target.Syntax.denote]
      change L2.condition (test locals)
          (denote (ofGeneric thenBranch) locals)
          (denote (ofGeneric elseBranch) locals) = _
      rw [thenIH locals, elseIH locals]
  | «catch» body handler bodyIH handlerIH =>
      simp only [ofGeneric, denote, L2.Syntax.denote, Target.Syntax.denote]
      change L2.catch (denote (ofGeneric body) locals)
          (fun exception => denote (ofGeneric handler) exception) = _
      rw [bodyIH locals]
      congr 1
      funext exceptionalLocals
      rw [handlerIH exceptionalLocals]
  | «loop» test body bodyIH =>
      simp only [ofGeneric, denote, L2.Syntax.denote, Target.Syntax.denote]
      change L2.while test (fun value => denote (ofGeneric body) value)
          locals [] = _
      congr 1
      funext nextLocals
      rw [bodyIH nextLocals]
  | «call» body bodyIH =>
      simp only [ofGeneric, denote, L2.Syntax.denote, Target.Syntax.denote]
      exact bodyIH locals

end Syntax

end CanonicalTarget

/-- Upstream-direction, failure-conditional L2/L1 correspondence. -/
abbrev Extracts (model : StateModel Full Locals Globals)
    (target : Target.Syntax Locals Globals)
    (source : Source.Syntax Full Locals Globals) : Prop :=
  forall locals,
    L2.L2Corres model.projectGlobals model.projectLocals model.projectLocals
      (fun state => model.projectLocals state = locals)
      (Target.Syntax.denote target locals) source.denote

/-- A generated target paired with its `L2Corres` certificate. -/
structure Certificate (model : StateModel Full Locals Globals)
    (source : Source.Syntax Full Locals Globals) where
  target : Target.Syntax Locals Globals
  corres : Extracts model target source

/-- Correspondence for the closed Type0 target passed directly to HeapLift. -/
abbrev ClosedExtracts (model : StateModel Full Locals Globals)
    (target : CanonicalTarget.Syntax Locals Globals)
    (source : Source.Syntax Full Locals Globals) : Prop :=
  forall locals,
    L2.L2Corres model.projectGlobals model.projectLocals model.projectLocals
      (fun state => model.projectLocals state = locals)
      (CanonicalTarget.Syntax.denote target locals) source.denote

/-- A closed canonical target and its inherited, equal-strength L2 certificate. -/
structure ClosedCertificate (model : StateModel Full Locals Globals)
    (source : Source.Syntax Full Locals Globals) where
  target : CanonicalTarget.Syntax Locals Globals
  corres : ClosedExtracts model target source
  functional : ∀ locals,
    Nondet.Functional (CanonicalTarget.Syntax.denote target locals)

/-- Close a Type0 generic certificate without changing its denotation or proof. -/
def Certificate.close {Full : Type u} {Locals Globals : Type}
    {model : StateModel Full Locals Globals}
    {source : Source.Syntax Full Locals Globals}
    (certificate : Certificate model source) : ClosedCertificate model source :=
  { target := CanonicalTarget.Syntax.ofGeneric certificate.target
    corres := fun locals => by
      rw [CanonicalTarget.Syntax.denote_ofGeneric]
      exact certificate.corres locals
    functional := fun locals => by
      rw [CanonicalTarget.Syntax.denote_ofGeneric]
      exact Target.Syntax.functional certificate.target locals }

/-- Evidence for the exact canonical L1 terms handled by local extraction. -/
inductive Supported {Full : Type u} {Locals : Type v} {Globals : Type w}
    (model : StateModel Full Locals Globals) :
    Source.Syntax Full Locals Globals -> Type (max u v w) where
  | skip : Supported model .skip
  | localUpdate (update : Locals -> Globals -> Locals) :
      Supported model (.modify (Source.localTransform model update))
  | globalUpdate (update : Locals -> Globals -> Globals) :
      Supported model (.modify (Source.globalTransform model update))
  | guard (test : Locals -> Globals -> Prop) :
      Supported model (.guard fun state =>
        test (model.projectLocals state) (model.projectGlobals state))
  | throw : Supported model .throw
  | seq {first second} : Supported model first -> Supported model second ->
      Supported model (.seq first second)
  | condition (test : Locals -> Globals -> Prop) {thenBranch elseBranch} :
      Supported model thenBranch -> Supported model elseBranch ->
        Supported model (.condition
          (fun state => test (model.projectLocals state) (model.projectGlobals state))
          thenBranch elseBranch)
  | «catch» {body handler} :
      Supported model body -> Supported model handler ->
        Supported model (.catch body handler)
  | loop (test : Locals -> Globals -> Prop) {body} :
      Supported model body ->
        Supported model (.while
          (fun state => test (model.projectLocals state) (model.projectGlobals state)) body)
  | «call» {body} : Supported model body -> Supported model (.call body)
  | fail : Supported model .fail

end Kernel

end Zag.Lang.AutoCorres.LocalVarExtract
