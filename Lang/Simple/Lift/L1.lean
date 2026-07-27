import Lang.Simple.Defs
import Lang.Simple.Corres
import Lang.Simple.Dialect
import Lang.SSA

/-!
  # L1 — AutoCorres SimplConv

  Upstream: <https://github.com/seL4/l4v/tree/master/tools/autocorres>
  (`L1Defs.thy`, `simpl_conv.ML`). Every definition below names the AC
  constant it stands for; line numbers are against l4v `master`.

  * `type_synonym 's L1_monad = ('s, unit+unit) nondet_monad` — L1Defs.thy:16
  * combinators `L1_seq`/`L1_skip`/`L1_modify`/`L1_condition`/`L1_catch`/
    `L1_while`/`L1_throw`/`L1_guard` — L1Defs.thy:17–25
  * `L1corres` Normal↦`Inr ()`, Abrupt↦`Inl ()`, Fault/Stuck↦False — L1Defs.thy:54–65
  * the SIMPL→L1 case table this file mirrors — simpl_conv.ML:118–150
  * `'s` = full C-parser record = `ABI.FullState` (locals + Globals/heap)

  Zag §5.0: `M := Id`, state explicit SSA; the `unit+unit` exception sum of
  L1Defs.thy:16 is encoded as two boolean flags:

  ```
  AC (L1corres, L1Defs.thy:58–64)   flagged [fault, abrupt, FullState]
  Normal s'  ↦ (Inr (), s')      ≅  (false, false, s')
  Abrupt s'  ↦ (Inl (), s')      ≅  (false, true,  s')
  Fault/Stuck ↦ False            ≅  (true,  false, s)
  ```

  `toSSA?` is structural (not `partial`) so equations are available.
  Faithfulness is the **general** `Corres.SimplExceptionFaithful` instantiated
  below; Word2 ladder demos live in `Test/L1.lean`.
-/

namespace Lang.Simple.Lift.L1

open Zag
open Zag.Lang.SSA
open Lang.Simple
open Lang.Simple.Corres

abbrev SSAValue (p : PrimitiveCtx) := Zag.Lang.SSA.SSAValue p
abbrev SSAExpr (p : PrimitiveCtx) := Zag.Lang.SSA.SSAExpr p

def boolTy : Ty := .prim "Bool"

/-- Carrier of `'s L1_monad` results — AC L1Defs.thy:16 (`('s, unit+unit) nondet_monad`). -/
def flaggedTy (stateTy : Ty) : Ty := flaggedStateTy stateTy

/-- Build an L1 result. Zag encoding of the `unit+unit`×state pair — L1Defs.thy:16. -/
def packFlagged {p : PrimitiveCtx} (stateTy : Ty)
    (fault abrupt st : SSAValue p) : SSAValue p :=
  .struct [boolTy, boolTy, stateTy] [fault, abrupt, st]

def falseB {p : PrimitiveCtx} [Peano.Types p] : SSAValue p := .bool false
def trueB {p : PrimitiveCtx} [Peano.Types p] : SSAValue p := .bool true

/-- `fault` flag = AC's `| _ ⇒ False` (Fault/Stuck) arm — L1Defs.thy:64. -/
def projFault {p : PrimitiveCtx} (st : Ty) (v : SSAValue p) : SSAValue p :=
  .field [boolTy, boolTy, st] faultIdx v
/-- `abrupt` flag = AC's `Abrupt s' ⇒ (Inl (), s')` arm — L1Defs.thy:63. -/
def projAbrupt {p : PrimitiveCtx} (st : Ty) (v : SSAValue p) : SSAValue p :=
  .field [boolTy, boolTy, st] abruptIdx v
/-- Result state `s'` of L1corres — L1Defs.thy:62–63. -/
def projState {p : PrimitiveCtx} (st : Ty) (v : SSAValue p) : SSAValue p :=
  .field [boolTy, boolTy, st] stateIdx v

/--
  State update of a SIMPL `Basic m`.
  AC: `L1_modify m ≡ liftE (modify m)` — L1Defs.thy:19; emitted by
  simpl_conv.ML:126–128 (`Basic m` ↦ `L1_modify m`, thm `L1corres_modify`).
-/
def basicUpdate {ctx : Context} (u : Basic ctx) (st : SSAValue ctx.primCtx) :
    SSAValue ctx.primCtx :=
  .block ctx.stateTy (.let_ "st" st (.ret (.raw u.val)))

/--
  SIMPL guard/condition set as a predicate on the state.
  AC: `L1_set_to_pred S ≡ λs. s ∈ S` — L1Defs.thy:39, applied by
  `set_to_pred` (defined simpl_conv.ML:109–111, applied at :132/:140/:148).
-/
def bexpValue {ctx : Context} (b : BExp ctx) (st : SSAValue ctx.primCtx) :
    SSAValue ctx.primCtx :=
  .block boolTy (.let_ "st" st (.ret (.raw b.val)))

/--
  SIMPL → L1. Mirrors the AC case table in simpl_conv.ML:118–150 one-for-one:

  | SIMPL | AC L1 term (simpl_conv.ML) | AC def |
  | --- | --- | --- |
  | `Skip` | `L1_skip` (:118–120) | L1Defs.thy:18 |
  | `Basic m` | `L1_modify m` (:126–128) | L1Defs.thy:19 |
  | `Guard _ c body` | `L1_seq (L1_guard c) body` (:146–148) | L1Defs.thy:25,17 |
  | `Seq l r` | `L1_seq l r` (:122–124) | L1Defs.thy:17 |
  | `Cond c l r` | `L1_condition c l r` (:130–132) | L1Defs.thy:20 |
  | `While c body` | `L1_while c body` (:138–140) | L1Defs.thy:22 |
  | `Throw` | `L1_throw` (:142–144) | L1Defs.thy:23 |
  | `Catch l r` | `L1_catch l r` (:134–136) | L1Defs.thy:21 |
  | `Call p` | `L1_call …` (:173) | L1Defs.thy:27 — **not ported**, `none` |

  `L1_guard c ≡ liftE (guard c)` *fails* (`snd`) when `c` is false; the flagged
  encoding records that as `fault = true`. NB this is a *divergence*: AC's
  `guard` makes the monad fail (`snd (A s)`), which makes `L1corres` vacuous,
  whereas Zag returns a definite flagged state. See L1Defs.thy:64.
-/
def toSSA? {ctx : Context} {proc : Type u} {fault : Type v}
    [Peano.Types ctx.primCtx] :
    Com ctx proc fault → Option (SSAExpr ctx.primCtx)
  -- L1_skip ≡ returnOk () — L1Defs.thy:18
  | .Skip =>
      some (.ret (packFlagged ctx.stateTy falseB falseB (.var "st")))
  -- L1_modify m ≡ liftE (modify m) — L1Defs.thy:19
  | .Basic u =>
      some <|
        .let_ "st'" (basicUpdate u (.var "st")) <|
        .ret (packFlagged ctx.stateTy falseB falseB (.var "st'"))
  -- L1_seq (L1_guard c) body — L1Defs.thy:25,17; guard failure ↦ fault flag
  | .Guard b c =>
      match toSSA? c with
      | none => none
      | some body =>
          some (.ite (bexpValue b (.var "st")) body
            (.ret (packFlagged ctx.stateTy trueB falseB (.var "st"))))
  -- L1_seq A B ≡ A >>=E (λ_. B) — L1Defs.thy:17; >>=E short-circuits Inl/fail
  | .Seq c1 c2 =>
      match toSSA? c1, toSSA? c2 with
      | some e1, some e2 =>
          let rt := flaggedTy ctx.stateTy
          some <|
            .let_ "r1" (.block rt e1) <|
            .let_ "f1" (projFault ctx.stateTy (.var "r1")) <|
            .let_ "a1" (projAbrupt ctx.stateTy (.var "r1")) <|
            .let_ "s1" (projState ctx.stateTy (.var "r1")) <|
            .ite (.var "f1") (.ret (.var "r1"))
              (.ite (.var "a1") (.ret (.var "r1")) (.let_ "st" (.var "s1") e2))
      | _, _ => none
  -- L1_condition c A B ≡ condition c A B — L1Defs.thy:20
  | .Cond b c1 c2 =>
      match toSSA? c1, toSSA? c2 with
      | some e1, some e2 => some (.ite (bexpValue b (.var "st")) e1 e2)
      | _, _ => none
  -- L1_while c A ≡ whileLoopE (λ_. c) (λ_. A) () — L1Defs.thy:22
  | .While b c =>
      match toSSA? c with
      | none => none
      | some body =>
          -- Loop-carried: [fault, abrupt, st]. `varCtx` length must match outer
          -- free env so `recurse` base points at packed loop state (not outer st).
          -- Outer L1 env is one state var (`lowerEnv`); no fuel — `Term.recurse`.
          let stateVars : List SSAVar := [
            { name := "fault", ty := boolTy },
            { name := "abrupt", ty := boolTy },
            { name := "st", ty := ctx.stateTy }]
          let outerVarCtx : VarCtx := [ctx.stateTy]
          let init : List (SSAValue ctx.primCtx) := [falseB, falseB, .var "st"]
          let rt := flaggedTy ctx.stateTy
          let bodyRun : SSAExpr ctx.primCtx :=
            .let_ "br" (.block rt (.let_ "st" (SSAValue.var "st") body)) <|
            .let_ "bf" (projFault ctx.stateTy (.var "br")) <|
            .let_ "ba" (projAbrupt ctx.stateTy (.var "br")) <|
            .let_ "bs" (projState ctx.stateTy (.var "br")) <|
            .ite (.var "bf")
              (.ret (packFlagged ctx.stateTy trueB falseB (.var "bs")))
              (.ite (.var "ba")
                (.ret (packFlagged ctx.stateTy falseB trueB (.var "bs")))
                (.yield [.var "bf", .var "ba", .var "bs"]))
          let loopBody : SSAExpr ctx.primCtx :=
            .let_ "already" (.op "eq" [SSAValue.var "abrupt", trueB]) <|
            .ite (.var "already")
              (.ret (packFlagged ctx.stateTy
                (SSAValue.var "fault") (SSAValue.var "abrupt") (SSAValue.var "st")))
              (.let_ "cond" (bexpValue b (SSAValue.var "st")) <|
                .ite (.var "cond") bodyRun
                  (.ret (packFlagged ctx.stateTy
                    (SSAValue.var "fault") falseB (SSAValue.var "st"))))
          some (.ret (.loopBody outerVarCtx stateVars init rt loopBody))
  -- L1_throw ≡ throwError () — L1Defs.thy:23
  | .Throw =>
      some (.ret (packFlagged ctx.stateTy falseB trueB (.var "st")))
  -- L1_catch A B ≡ A <handle> (λ_. B) — L1Defs.thy:21; only Inl is handled
  | .Catch c1 c2 =>
      match toSSA? c1, toSSA? c2 with
      | some e1, some e2 =>
          let rt := flaggedTy ctx.stateTy
          some <|
            .let_ "r1" (.block rt e1) <|
            .let_ "f1" (projFault ctx.stateTy (.var "r1")) <|
            .let_ "a1" (projAbrupt ctx.stateTy (.var "r1")) <|
            .let_ "s1" (projState ctx.stateTy (.var "r1")) <|
            .ite (.var "f1") (.ret (.var "r1"))
              (.ite (.var "a1") (.let_ "st" (.var "s1") e2) (.ret (.var "r1")))
      | _, _ => none
  -- L1_call — L1Defs.thy:27, simpl_conv.ML:173. Interprocedural; not ported.
  | .Call _ => none

/-- Ambient `'s` of `L1_monad` bound as de Bruijn 0 (AC state is implicit). -/
def lowerEnv {p : PrimitiveCtx} : LowerCtx p := { vars := [("st", .var 0)] }

/--
  Run an L1 body on a full state. AC's `A s` in `L1corres` (L1Defs.thy:59);
  `some v` here plays the role of `¬ snd (A s)` with result `v`.
-/
def evalL1? {ctx : Context} (expr : SSAExpr ctx.primCtx) (s : Val ctx.primCtx) :
    Option (Val ctx.primCtx) := do
  let t ← SSAExpr.toTerm? expr lowerEnv
  Term.eval ctx.zagCtx [s] t

/-- Encode AC exception outcome as flagged struct (requires `s : stateTy`). -/
def encode {ctx : Context} [Peano.Types ctx.primCtx]
    (fault abrupt : Bool) (s : Val ctx.primCtx) (hs : s.ty = ctx.stateTy) :
    Val ctx.primCtx :=
  let tys : List Ty := [boolTy, boolTy, ctx.stateTy]
  have htys : tys = [boolTy, boolTy, ctx.stateTy] := rfl
  let fields : (idx : Fin tys.length) → Ty.type ctx.primCtx tys[idx] := fun idx =>
    match idx with
    | ⟨0, _⟩ => by
        change Ty.type ctx.primCtx boolTy
        exact Ty.ofBool ctx.primCtx fault
    | ⟨1, _⟩ => by
        change Ty.type ctx.primCtx boolTy
        exact Ty.ofBool ctx.primCtx abrupt
    | ⟨2, _⟩ => by
        change Ty.type ctx.primCtx ctx.stateTy
        exact cast (congrArg (Ty.type ctx.primCtx) hs) s.val
    | ⟨n + 3, h⟩ => by
        have : n + 3 < 3 := h
        omega
  Val.mk (flaggedTy ctx.stateTy) (cast (Ty.type.eq_5 ctx.primCtx tys).symm fields)

/--
  The `case t of` table of `L1corres` — L1Defs.thy:60–64:
  `Normal s' ↦ (Inr (), s')`, `Abrupt s' ↦ (Inl (), s')`, `_ ↦ False`.
  Zag: Fault gets its own flag; `Stuck` has no encoding (the `False` arm).
-/
def encodeOutcome {ctx : Context} {fault : Type v} [Peano.Types ctx.primCtx]
    (o : Outcome ctx fault) : Option (Val ctx.primCtx) :=
  match o with
  | .normal s => if hs : s.ty = ctx.stateTy then some (encode false false s hs) else none
  | .abrupt s => if hs : s.ty = ctx.stateTy then some (encode false true s hs) else none
  | .fault _ s => if hs : s.ty = ctx.stateTy then some (encode true false s hs) else none
  | .stuck => none

/-- L1 output lives in `Dialect.l1Dialect` (flagged state, still packed State ABI). -/
def targetDialect (arity : Nat) : Dialect.Dialect :=
  Dialect.l1Dialect arity

/--
  L1 faithfulness = general `Corres.SimplExceptionFaithful`, i.e. the Zag
  reading of `L1corres check_term Γ A C` — L1Defs.thy:54–65.
-/
def Faithful {ctx : Context} {proc : Type} {fault : Type}
    [Peano.Types ctx.primCtx]
    (Γ : ProcEnv ctx proc fault) (unitFault : fault) : Prop :=
  SimplExceptionFaithful Γ unitFault
    (toSSA? (ctx := ctx) (proc := proc) (fault := fault))
    evalL1?
    encodeOutcome

theorem toSSA_skip {ctx : Context} {proc : Type u} {fault : Type v}
    [Peano.Types ctx.primCtx] :
    toSSA? (ctx := ctx) (proc := proc) (fault := fault) .Skip =
      some (.ret (packFlagged ctx.stateTy falseB falseB (.var "st"))) := rfl

theorem toSSA_throw {ctx : Context} {proc : Type u} {fault : Type v}
    [Peano.Types ctx.primCtx] :
    toSSA? (ctx := ctx) (proc := proc) (fault := fault) .Throw =
      some (.ret (packFlagged ctx.stateTy falseB trueB (.var "st"))) := rfl

theorem toSSA_call {ctx : Context} {proc : Type u} {fault : Type v}
    [Peano.Types ctx.primCtx] (p : proc) :
    toSSA? (ctx := ctx) (proc := proc) (fault := fault) (.Call p) = none := rfl

theorem toSSA_seq_skip_skip {ctx : Context} {proc : Type u} {fault : Type v}
    [Peano.Types ctx.primCtx] :
    (toSSA? (ctx := ctx) (proc := proc) (fault := fault) (.Seq .Skip .Skip)).isSome = true := by
  simp [toSSA?]

theorem toSSA_catch_throw_skip {ctx : Context} {proc : Type u} {fault : Type v}
    [Peano.Types ctx.primCtx] :
    (toSSA? (ctx := ctx) (proc := proc) (fault := fault) (.Catch .Throw .Skip)).isSome = true := by
  simp [toSSA?]

/-- While lowers via SSA `loopBody` → `Term.recurse` (`partial_fixpoint`), not fuel. -/
theorem toSSA_while_skip {ctx : Context} {proc : Type u} {fault : Type v}
    [Peano.Types ctx.primCtx] (b : BExp ctx) :
    (toSSA? (ctx := ctx) (proc := proc) (fault := fault) (.While b .Skip)).isSome = true := by
  simp [toSSA?]

/--
  BigStep Skip is a no-op on outcomes.
  AC: `L1_skip` (L1Defs.thy:18) and `L1corres_skip` (L1Defs.thy:94).
  Encoding of a normal state is the L1 `Inr ()` stand-in.
-/
theorem bigStep_skip_normal {ctx : Context} {proc : Type u} {fault : Type v}
    (Γ : ProcEnv ctx proc fault) (uf : fault) (s : Val ctx.primCtx) :
    BigStep Γ uf .Skip (.normal s) (.normal s) :=
  BigStep.skip _

/-- AC: `L1_throw` (L1Defs.thy:23) and `L1corres_throw` (L1Defs.thy:107). -/
theorem bigStep_throw_abrupt {ctx : Context} {proc : Type u} {fault : Type v}
    (Γ : ProcEnv ctx proc fault) (uf : fault) (s : Val ctx.primCtx) :
    BigStep Γ uf .Throw (.normal s) (.abrupt s) :=
  BigStep.throw (s := s)

/-- encodeOutcome of Normal/Abrupt is always defined when ty matches (L1corres domain). -/
theorem encodeOutcome_normal {ctx : Context} {fault : Type v}
    [Peano.Types ctx.primCtx] (s : Val ctx.primCtx) (hs : s.ty = ctx.stateTy) :
    encodeOutcome (fault := fault) (.normal s) = some (encode false false s hs) := by
  simp [encodeOutcome, hs]

theorem encodeOutcome_abrupt {ctx : Context} {fault : Type v}
    [Peano.Types ctx.primCtx] (s : Val ctx.primCtx) (hs : s.ty = ctx.stateTy) :
    encodeOutcome (fault := fault) (.abrupt s) = some (encode false true s hs) := by
  simp [encodeOutcome, hs]

theorem encodeOutcome_fault {ctx : Context} {fault : Type v}
    [Peano.Types ctx.primCtx] (f : fault) (s : Val ctx.primCtx) (hs : s.ty = ctx.stateTy) :
    encodeOutcome (.fault f s) = some (encode true false s hs) := by
  simp [encodeOutcome, hs]

theorem encodeOutcome_stuck {ctx : Context} {fault : Type v}
    [Peano.Types ctx.primCtx] :
    encodeOutcome (ctx := ctx) (fault := fault) .stuck = none := rfl

/--
  L1corres domain: stuck has no encoding (AC Fault/Stuck ↛ successful L1 value).
  Normal/Abrupt/Fault map to flagged structs when `s.ty = stateTy`.
-/
theorem encodeOutcome_iff_not_stuck {ctx : Context} {fault : Type v}
    [Peano.Types ctx.primCtx] (o : Outcome ctx fault) :
    (encodeOutcome o).isSome → o ≠ .stuck := by
  intro h hs
  subst hs
  simp [encodeOutcome] at h

/-- Skip/Throw-only translator: AC `L1_skip` / `L1_throw` — L1Defs.thy:18,23. -/
def toSSA_exnCore? {ctx : Context} {proc : Type u} {fault : Type v}
    [Peano.Types ctx.primCtx] : Com ctx proc fault → Option (SSAExpr ctx.primCtx)
  | .Skip => some (.ret (packFlagged ctx.stateTy falseB falseB (.var "st")))
  | .Throw => some (.ret (packFlagged ctx.stateTy falseB trueB (.var "st")))
  | _ => none

/--
  Remaining obligation of `L1corres` (L1Defs.thy:54–65) for the Skip/Throw
  fragment: the translated body evaluates to the encoded outcome.
  **Assumed, not discharged.** `Test/L1.lean` executes it at two concrete
  states; nothing instantiates `faithful_exnCore_of`. A `∀`-quantified proof
  needs `Term.eval` lemmas for `mkStruct` (tracked in AC_NOTES).
-/
def ExnCoreEvalOk (ctx : Context) [Peano.Types ctx.primCtx] : Prop :=
  (∀ s (hs : s.ty = ctx.stateTy),
    evalL1? (.ret (packFlagged ctx.stateTy falseB falseB (.var "st"))) s =
      some (encode false false s hs)) ∧
  (∀ s (hs : s.ty = ctx.stateTy),
    evalL1? (.ret (packFlagged ctx.stateTy falseB trueB (.var "st"))) s =
      some (encode false true s hs))

theorem faithful_exnCore_of
    {ctx : Context} {proc : Type} {fault : Type}
    [Peano.Types ctx.primCtx]
    (Γ : ProcEnv ctx proc fault) (unitFault : fault)
    (h : ExnCoreEvalOk ctx) :
    SimplExceptionFaithful Γ unitFault
      (toSSA_exnCore? (ctx := ctx) (proc := proc) (fault := fault))
      evalL1? encodeOutcome := by
  intro cmd expr htrans s o ⟨hty, hbs, hnstuck⟩
  cases cmd with
  | Skip =>
      injection htrans with hE; subst hE
      cases hbs
      · exact ⟨encode false false s hty, h.1 s hty,
          encodeOutcome_normal (fault := fault) s hty⟩
      · simp [Outcome.isNormal] at *
  | Throw =>
      injection htrans with hE; subst hE
      cases hbs
      · exact ⟨encode false true s hty, h.2 s hty,
          encodeOutcome_abrupt (fault := fault) s hty⟩
      · simp [Outcome.isNormal] at *
  | Basic _ | Guard _ _ | Seq _ _ | Cond _ _ _ | While _ _ | Call _ | Catch _ _ =>
      cases htrans

end Lang.Simple.Lift.L1

