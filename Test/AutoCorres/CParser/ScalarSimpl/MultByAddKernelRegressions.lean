import Lang.AutoCorres.ML.autocorres

/-! Phase-local kernel regressions used by the upstream `MultByAdd` port. -/

namespace Zag.Test.AutoCorres.Upstream.MultByAdd

open Zag.Lang.AutoCorres

abbrev Word32 := BitVec 32
private def w32 (value : Nat) : Word32 := BitVec.ofNat 32 value

namespace SimplConv

structure State where
  a : Word32
  b : Word32
  result : Word32
  deriving DecidableEq

def env : Simpl.Body State Unit Unit := fun _ => none
def initResult (state : State) : State := { state with result := 0 }
def add (state : State) : State := { state with result := state.result + state.b }
def decrement (state : State) : State := { state with a := state.a - 1 }

def source : Simpl.Com State Unit Unit :=
  .Seq (.Basic initResult)
    (.While (fun state => state.a != 0)
      (.Seq (.Basic add) (.Basic decrement)))

def supported : Zag.Lang.AutoCorres.SimplConv.Kernel.Supported source :=
  .seq (.basic initResult)
    (.while (fun state => state.a != 0)
      (.seq (.basic add) (.basic decrement)))

def certificate := ML.SimplConv.simplConv false env supported

theorem keeps_loop_and_body :
    match certificate.target with
    | .seq (.modify _) (.while _ (.seq (.modify _) (.modify _))) => True
    | _ => False := by
  trivial

theorem kernel_source_corres : L1.L1Corres false env certificate.target.denote source :=
  certificate.corres

end SimplConv

namespace LocalVarExtract

structure Locals where
  a : Word32
  b : Word32
  result : Word32
  deriving DecidableEq

abbrev Full := Locals × Unit

def model : ML.LocalVarExtract.StateModel Full Locals Unit where
  projectGlobals := Prod.snd
  projectLocals := Prod.fst
  assemble := fun locals globals => (locals, globals)
  projectGlobals_assemble := by intros; rfl
  projectLocals_assemble := by intros; rfl
  assemble_project := by intro state; cases state; rfl

def initResult (locals : Locals) (_ : Unit) : Locals := { locals with result := 0 }

def step (locals : Locals) (_ : Unit) : Locals :=
  { locals with a := locals.a - 1, result := locals.result + locals.b }

def source : ML.LocalVarExtract.Source.Syntax Full Locals Unit :=
  .seq (.modify (ML.LocalVarExtract.Source.localTransform model initResult))
    (.while
      (fun state => state.1.a != 0)
      (.modify (ML.LocalVarExtract.Source.localTransform model step)))

def supported : ML.LocalVarExtract.Supported model source :=
  .seq (.localUpdate initResult)
    (.loop (fun locals _ => locals.a != 0) (.localUpdate step))

def certificate := ML.LocalVarExtract.extract model supported

theorem extracts_loop_state :
    certificate.target =
      ML.LocalVarExtract.Target.Syntax.seq (.localUpdate initResult)
        (.loop (fun locals _ => locals.a != 0) (.localUpdate step)) := by
  rfl

theorem run_succeeds :
    (ML.LocalVarExtract.run model supported).target =
      ML.LocalVarExtract.Target.Syntax.seq (.localUpdate initResult)
        (.loop (fun locals _ => locals.a != 0) (.localUpdate step)) := by
  rfl

theorem kernel_source_extracts :
    ML.LocalVarExtract.Extracts model certificate.target source :=
  certificate.corres

end LocalVarExtract

namespace TypeStrengthen

open Zag.Lang.AutoCorres.TypeStrengthen.Kernel

structure LoopVars where
  a : Word32
  result : Word32
  deriving DecidableEq

abbrev Arguments := Word32 × Word32

def body : Source.Term (Arguments × LoopVars) Unit Unit LoopVars :=
  .pure (fun input =>
    { input.2 with
      a := input.2.a - 1
      result := input.2.result + input.1.2 }) []

def source : Source.Term Arguments Unit Unit LoopVars :=
  .while (fun _ locals _ => locals.a != 0) body
    (fun arguments => { a := arguments.1, result := 0 })
    ["a", "result"]

theorem manual_nondet_model_is_supported :
    match ML.TypeStrengthen.buildSupported .nondet source with
    | .ok _ => True
    | .error _ => False := by
  simp [ML.TypeStrengthen.buildSupported, source, body]

def supported : Supported .nondet source := .nondetWhile .nondetValue
def certificate (arguments : Arguments) :=
  ML.TypeStrengthen.strengthenAt supported arguments

def bodyCertificate (input : Arguments) (current : LoopVars) :=
  ML.TypeStrengthen.strengthenAt (Supported.nondetValue : Supported .nondet body)
    (input, current)

theorem body_computes_one_iteration (input : Arguments) (current : LoopVars) :
    (bodyCertificate input current).target =
      Zag.Lang.AutoCorres.TypeStrengthen.Kernel.Target.Syntax.atom
        (Zag.Lang.AutoCorres.gets fun _ : Unit =>
          { a := current.a - 1, result := current.result + input.2 }) := by
  rfl

theorem keeps_loop_arguments (input : Arguments) :
    match (certificate input).target with
    | .nondetWhile _ _ initial =>
        initial = { a := input.1, result := 0 }
    | _ => False := by
  rfl

theorem kernel_phase_exact (input : Arguments) :
    source.denote input =
      Zag.Lang.AutoCorres.TypeStrengthen.embed .nondet
        (certificate input).target.denote :=
  (certificate input).equality

end TypeStrengthen

end Zag.Test.AutoCorres.Upstream.MultByAdd
