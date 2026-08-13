import Lang.AutoCorres.ML.autocorres

/-! Phase-local kernel regressions used by the upstream `Plus` port. -/

namespace Zag.Test.AutoCorres.Upstream.Plus

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
def update (state : State) : State := { state with result := state.a + state.b }
def source : Simpl.Com State Unit Unit := .Basic update
def supported : Zag.Lang.AutoCorres.SimplConv.Kernel.Supported source := .basic update
def certificate := ML.SimplConv.simplConv false env supported

theorem recognized :
    match ML.SimplConv.run false env source with
    | .ok result => match result.target with | .modify _ => True | _ => False
    | .error _ => False := by
  trivial

theorem manual_target : certificate.target = .modify update := by rfl

theorem manual_source_corres : L1.L1Corres false env certificate.target.denote source :=
  certificate.corres

def initial : State := { a := w32 3, b := w32 4, result := 0 }

theorem target_runs :
    (Except.ok (), update initial) ∈ (certificate.target.denote initial).results := by
  simp [certificate, supported, ML.SimplConv.simplConv,
    Zag.Lang.AutoCorres.SimplConv.Kernel.Target.denote, L1.modify, update, initial]

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

def update (locals : Locals) (_ : Unit) : Locals :=
  { locals with result := locals.a + locals.b }

def source : ML.LocalVarExtract.Source.Syntax Full Locals Unit :=
  .modify (ML.LocalVarExtract.Source.localTransform model update)
def supported : ML.LocalVarExtract.Supported model source := .localUpdate update
def certificate := ML.LocalVarExtract.extract model supported
def initial : Locals := { a := w32 3, b := w32 4, result := 0 }

theorem target_returns_updated_locals :
    (Except.ok { initial with result := w32 7 }, ()) ∈
      (certificate.target.denote initial ()).results := by
  simp [certificate, supported, ML.LocalVarExtract.extract,
    Zag.Lang.AutoCorres.LocalVarExtract.Kernel.Target.Syntax.denote,
    L2.gets, update, initial, w32]

theorem manual_source_extracts :
    ML.LocalVarExtract.Extracts model certificate.target source :=
  certificate.corres

end LocalVarExtract

namespace TypeStrengthen

open Zag.Lang.AutoCorres.TypeStrengthen.Kernel

abbrev Arguments := Word32 × Word32

def source : Source.Term Arguments Unit Unit Word32 :=
  .pure (fun arguments => arguments.1 + arguments.2) ["ret"]

theorem supports_pure :
    match ML.TypeStrengthen.buildSupported .pure source with
    | .ok _ => True
    | .error _ => False := by
  simp [ML.TypeStrengthen.buildSupported, source]

def supported : Supported .pure source := .pureValue
def certificate (arguments : Arguments) :=
  ML.TypeStrengthen.strengthenAt supported arguments

theorem target_computes (arguments : Arguments) :
    (certificate arguments).target.denote = arguments.1 + arguments.2 := by
  rfl

theorem manual_phase_exact (arguments : Arguments) :
    source.denote arguments =
      Zag.Lang.AutoCorres.TypeStrengthen.embed .pure
        (certificate arguments).target.denote :=
  (certificate arguments).equality

end TypeStrengthen

end Zag.Test.AutoCorres.Upstream.Plus
