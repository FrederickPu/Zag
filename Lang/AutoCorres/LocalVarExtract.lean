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

/-- Reified L1 syntax. No constructor contains an opaque `L1Program` leaf. -/
inductive Syntax (Full : Type u) (Locals : Type v) (Globals : Type w) where
  | skip
  | localUpdate (update : Locals -> Globals -> Locals)
  | globalUpdate (update : Locals -> Globals -> Globals)
  | guard (test : Locals -> Globals -> Prop)
  | throw
  | seq (first second : Syntax Full Locals Globals)
  | condition (test : Locals -> Globals -> Prop)
      (thenBranch elseBranch : Syntax Full Locals Globals)
  | «catch» (body handler : Syntax Full Locals Globals)
  | spec (relation : Set (Full × Full))
  | loop (test : Locals -> Globals -> Prop) (body : Syntax Full Locals Globals)
  | fail

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

/-- Interpret the reified source fragment in L1. -/
noncomputable def Syntax.denote (model : StateModel Full Locals Globals) :
    Syntax Full Locals Globals -> L1.L1Program Full
  | .skip => L1.skip
  | .localUpdate update => L1.modify (localTransform model update)
  | .globalUpdate update => L1.modify (globalTransform model update)
  | .guard test =>
      L1.guard fun state => test (model.projectLocals state) (model.projectGlobals state)
  | .throw => L1.throw
  | .seq first second => L1.seq (first.denote model) (second.denote model)
  | .condition test thenBranch elseBranch =>
      L1.condition
        (fun state => test (model.projectLocals state) (model.projectGlobals state))
        (thenBranch.denote model) (elseBranch.denote model)
  | .catch body handler => L1.catch (body.denote model) (handler.denote model)
  | .spec relation => L1.spec relation
  | .loop test body =>
      L1.while
        (fun state => test (model.projectLocals state) (model.projectGlobals state))
        (body.denote model)
  | .fail => L1.fail

end Source

namespace Target

/-- Reified L2 output for the certified all-locals fragment. -/
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

/--
Interpret target syntax with explicit locals input. Returned and exceptional
locals are values; only globals inhabit the L2 monadic state. The certificate
requires the input to equal the locals projected from the related concrete
state. Catch receives exceptional locals extracted from the L1 post-state.
-/
noncomputable def Syntax.denote :
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
  | .loop test body, locals =>
      L2.while test body.denote locals []

end Target

/-- Upstream-direction, failure-conditional L2/L1 correspondence. -/
abbrev Extracts (model : StateModel Full Locals Globals)
    (target : Target.Syntax Locals Globals)
    (source : Source.Syntax Full Locals Globals) : Prop :=
  forall locals,
    L2.L2Corres model.projectGlobals model.projectLocals model.projectLocals
      (fun state => model.projectLocals state = locals)
      (target.denote locals) (source.denote model)

/-- A generated target paired with its `L2Corres` certificate. -/
structure Certificate (model : StateModel Full Locals Globals)
    (source : Source.Syntax Full Locals Globals) where
  target : Target.Syntax Locals Globals
  corres : Extracts model target source

/-- Indexed evidence that a source tree lies wholly in the certified fragment. -/
inductive Supported {Full : Type u} {Locals : Type v} {Globals : Type w} :
    Source.Syntax Full Locals Globals -> Type (max u v w) where
  | skip : Supported .skip
  | localUpdate (update : Locals -> Globals -> Locals) : Supported (.localUpdate update)
  | globalUpdate (update : Locals -> Globals -> Globals) : Supported (.globalUpdate update)
  | guard (test : Locals -> Globals -> Prop) : Supported (.guard test)
  | throw : Supported .throw
  | seq {first second} : Supported first -> Supported second -> Supported (.seq first second)
  | condition (test : Locals -> Globals -> Prop) {thenBranch elseBranch} :
      Supported thenBranch -> Supported elseBranch ->
        Supported (.condition test thenBranch elseBranch)
  | «catch» {body handler} :
      Supported body -> Supported handler -> Supported (.catch body handler)
  | loop (test : Locals -> Globals -> Prop) {body} :
      Supported body -> Supported (.loop test body)

end Kernel

end Zag.Lang.AutoCorres.LocalVarExtract
