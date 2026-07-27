import Lang.Simple.Defs
import Lang.Simple.ABI
import Lang.Simple.Corres
import Lang.Simple.Dialect
import Lang.Simple.Lift.L1
import Lang.SSA

/-!
  # L2 — AutoCorres LocalVarExtract

  Upstream: <https://github.com/seL4/l4v/tree/master/tools/autocorres>
  (`L2Defs.thy`, `local_var_extract.ML`). Line numbers against l4v `master`.

  * `type_synonym ('s,'a,'e) L2_monad = ('s, 'e+'a) nondet_monad` — L2Defs.thy:11
  * `L2_gets f (names : string list) ≡ liftE (gets f)` — L2Defs.thy:15
  * `L2_seq`/`L2_modify`/`L2_condition`/`L2_catch`/`L2_while`/`L2_throw`/
    `L2_guard` — L2Defs.thy:13,14,16,17,18,19,21
  * `L2_skip ≡ L2_gets (λ_. ()) []` — L2Defs.thy:26
  * `L2corres st ret_xf ex_xf P A C ≡ corresXF st (λ_. ret_xf) (λ_. ex_xf) P A C`
    — L2Defs.thy:85–91
  * entry point `LocalVarExtract.translate` — local_var_extract.ML:1607
  * Ambient `'s` after extract = **globals/heap** (`ABI.L2State` / `Globals`);
    locals become monadic return values, so `st` in `L2corres` is the
    full-state → globals projection (`ABI.projectGlobals`)

  Zag: pure path `fromCom?` (Simpl→L2); `fromL1?` unpacks L1 flagged full
  state into named locals + residual heap (LocalVarExtract shape).

  ## Correctness

  * `PureStep` → `BigStep` (proved).
  * Full `Corres.SimplPureFaithful` open; concrete eval demos in tests.
  * Exceptional Com constructors → `none` (L1 first).
-/

namespace Lang.Simple.Lift.L2

open Zag
open Zag.Lang.SSA
open Lang.Simple
open Lang.Simple.ABI
open Lang.Simple.Corres

abbrev SSAValue (p : PrimitiveCtx) := Zag.Lang.SSA.SSAValue p
abbrev SSAExpr (p : PrimitiveCtx) := Zag.Lang.SSA.SSAExpr p

/--
  The variables LocalVarExtract pulls out of the state.
  AC carries them as the `names : string list` argument threaded through
  `L2_gets`/`L2_while`/`L2_throw` (L2Defs.thy:15,18,19), built by
  `var_set_to_isa_list` (local_var_extract.ML:38–43); the Isabelle-level name
  map is `name_map_internal` (local_var_extract.ML:1262–1264).
-/
structure LocalContext where
  vars : List SSAVar
  loopResultName : String := "__simple_loop_state"
  condResultName : String := "__simple_cond_state"

namespace LocalContext

def tys (ctx : LocalContext) : List Ty := SSAVar.tys ctx.vars

def resultTy (ctx : LocalContext) : Ty :=
  match ctx.vars with
  | [v] => v.ty
  | _ => .struct ctx.tys

def currentValues {p : PrimitiveCtx} (ctx : LocalContext) : List (SSAValue p) :=
  ctx.vars.map fun v => .var v.name

def packCurrent {p : PrimitiveCtx} (ctx : LocalContext) : SSAValue p :=
  match ctx.vars with
  | [v] => .var v.name
  | _ => .struct ctx.tys ctx.currentValues

def packSourceState {p : PrimitiveCtx} (ctx : LocalContext) : SSAValue p :=
  .call (.primFunc (statePackName ctx.vars.length)) ctx.currentValues

def inputEnvFrom {p : PrimitiveCtx} : List SSAVar → Nat → List (String × Term p)
  | [], _ => []
  | v :: vs, i => (v.name, .var i) :: inputEnvFrom vs (i + 1)

def inputEnv {p : PrimitiveCtx} (ctx : LocalContext) : List (String × Term p) :=
  inputEnvFrom ctx.vars 0

def hasVarName (ctx : LocalContext) (name : String) : Bool :=
  ctx.vars.any (·.name == name)

def unpackBindings {p : PrimitiveCtx} (ctx : LocalContext) (packed : SSAValue p) :
    List (String × SSAValue p) :=
  match ctx.vars with
  | [] => []
  | [v] => [(v.name, packed)]
  | _ =>
      (List.finRange ctx.vars.length).map fun idx =>
        (ctx.vars[idx].name, .field ctx.tys (SSAVar.tyIndex idx) packed)

end LocalContext

def letBindings {p : PrimitiveCtx}
    (bs : List (String × SSAValue p)) (body : SSAExpr p) : SSAExpr p :=
  match bs with
  | [] => body
  | (n, v) :: bs => .let_ n v (letBindings bs body)

def assignFieldValues {p : PrimitiveCtx} (ctx : LocalContext)
    (fields : List (SSAValue p)) (body : SSAExpr p) : SSAExpr p :=
  letBindings ((ctx.vars.zip fields).map fun b => (b.1.name, b.2)) body

def replaceAt? {α : Type u} : List α → Nat → α → Option (List α)
  | [], _, _ => none
  | _ :: xs, 0, x => some (x :: xs)
  | h :: xs, n + 1, x => do
      let xs' ← replaceAt? xs n x
      some (h :: xs')

def stateGetIndex? (ctx : LocalContext) (name : String) : Option (Fin ctx.vars.length) :=
  (List.finRange ctx.vars.length).find? fun i => stateGetName i.val == name

def stateSetIndex? (ctx : LocalContext) (name : String) : Option (Fin ctx.vars.length) :=
  (List.finRange ctx.vars.length).find? fun i => stateSetName i.val == name

def isStatePackName (ctx : LocalContext) (name : String) : Bool :=
  name == statePackName ctx.vars.length

/-!
  Read a Simpl state term as L2 values.
  AC: the `state.get.i` applications are what local_var_extract.ML:865–867
  turns into `L2_gets` (`liftE (gets f)`, L2Defs.thy:15) with the extracted
  variable as its return set (thm `L2corres_modify_gets`); the `state.set.i`
  applications are what local_var_extract.ML:856 turns into `L2_modify`
  (L2Defs.thy:14) — for a *local* the modify is dropped and the new value is
  rebound to a name instead, which is the extract itself.
-/

mutual

partial def termToSSAValue? {sc : Context}
    (ctx : LocalContext) : Term sc.primCtx → Option (SSAValue sc.primCtx)
  | .prim ty v => some (.raw (.prim ty v))
  | .primFunc n => some (.primFunc n)
  | .var 0 => some ctx.packSourceState
  | .var _ => none
  | .app (.primFunc name) [st] =>
      match stateGetIndex? ctx name with
      | some idx => do
          let fs ← stateTermFields? ctx st
          fs[idx.val]?
      | none => do
          let s ← termToSSAValue? ctx st
          some (.call (.primFunc name) [s])
  | .app f args => do
      let fn ← termToSSAValue? ctx f
      let as ← termsToSSAValues? ctx args
      some (.call fn as)
  | .op n args => do
      let as ← termsToSSAValues? ctx args
      some (.op n as)
  | .mkStruct tys => some (.raw (.mkStruct tys))
  | .structProj tys idx => some (.raw (.structProj tys idx))
  | .recurse _ _ _ => none

partial def termsToSSAValues? {sc : Context}
    (ctx : LocalContext) : List (Term sc.primCtx) → Option (List (SSAValue sc.primCtx))
  | [] => some []
  | t :: ts => do
      let v ← termToSSAValue? ctx t
      let vs ← termsToSSAValues? ctx ts
      some (v :: vs)

partial def stateTermFields? {sc : Context}
    (ctx : LocalContext) : Term sc.primCtx → Option (List (SSAValue sc.primCtx))
  | .var 0 => some ctx.currentValues
  | .app (.primFunc name) fields =>
      if isStatePackName ctx name then
        if fields.length = ctx.vars.length then termsToSSAValues? ctx fields else none
      else
        match stateSetIndex? ctx name, fields with
        | some idx, [st, vt] => do
            let vs ← stateTermFields? ctx st
            let v ← termToSSAValue? ctx vt
            replaceAt? vs idx.val v
        | _, _ => none
  | _ => none

end

def assignFields? {p : PrimitiveCtx} (ctx : LocalContext)
    (fields : List (SSAValue p)) (body : SSAExpr p) : Option (SSAExpr p) :=
  if fields.length = ctx.vars.length then some (assignFieldValues ctx fields body)
  else none

def assignPackedLocals? {p : PrimitiveCtx} (ctx : LocalContext)
    (packedName : String) (packed : SSAValue p) (body : SSAExpr p) : Option (SSAExpr p) :=
  match ctx.vars with
  | [] => some body
  | [_] => some (letBindings (ctx.unpackBindings packed) body)
  | _ =>
      if ctx.hasVarName packedName then none
      else some (.let_ packedName packed
        (letBindings (ctx.unpackBindings (.var packedName)) body))

/--
  Turn a loop body's result into the loop-carried tuple.
  AC: `L2_while c A i names ≡ whileLoopE c A i` (L2Defs.thy:18) — the body `A`
  takes and returns the carried locals `i`, so its tail must `yield` them.
-/
def retToYield {p : PrimitiveCtx} (ctx : LocalContext) :
    SSAExpr p → Option (SSAExpr p)
  | .ret _ => some (.yield ctx.currentValues)
  | .let_ n v b => do let b' ← retToYield ctx b; some (.let_ n v b')
  | .seq a b => do let b' ← retToYield ctx b; some (.seq a b')
  | .ite c t e => do
      let t' ← retToYield ctx t
      let e' ← retToYield ctx e
      some (.ite c t' e')
  | .yield vs => some (.yield vs)

/--
  Pure-fragment lift, straight from SIMPL (AC composes SimplConv then
  LocalVarExtract; this is the fused pure path). Mirrors the L2 combinators:

  | SIMPL | AC L2 | def |
  | --- | --- | --- |
  | `Skip` | `L2_skip ≡ L2_gets (λ_. ()) []` | L2Defs.thy:26,15 |
  | `Basic m` | `L2_gets`/`L2_modify` split by local vs global | L2Defs.thy:15,14 |
  | `Seq` | `L2_seq A B ≡ A >>=E B` | L2Defs.thy:13 |
  | `Cond` | `L2_condition c A B ≡ condition c A B` | L2Defs.thy:16 |
  | `While` | `L2_while c A i names ≡ whileLoopE c A i` | L2Defs.thy:18 |

  `Guard`/`Throw`/`Catch`/`Call` (`L2_guard`/`L2_throw`/`L2_catch`/`L2_call`
  — L2Defs.thy:21,19,17,23) are the exception fragment: `none` here, take the
  L1 path (`fromL1?`) instead.
-/
def fromCom? {sc : Context} {proc : Type u} {fault : Type v}
    (ctx : LocalContext) : Com sc proc fault → Option (SSAExpr sc.primCtx)
  -- L2_skip — L2Defs.thy:26
  | .Skip => some (.ret ctx.packCurrent)
  -- locals: rebind names instead of L2_modify — local_var_extract.ML:836,856
  | .Basic u => do
      let fs ← stateTermFields? ctx u.val
      assignFields? ctx fs (.ret ctx.packCurrent)
  -- L2_guard — L2Defs.thy:21 (exception fragment)
  | .Guard _ _ => none
  -- L2_seq — L2Defs.thy:13
  | .Seq c1 c2 => do
      let a ← fromCom? ctx c1
      let b ← fromCom? ctx c2
      some (SSAExpr.seqLetBindings a b)
  -- L2_condition — L2Defs.thy:16
  | .Cond cond t e => do
      let c ← termToSSAValue? ctx cond.val
      let te ← fromCom? ctx t
      let ee ← fromCom? ctx e
      assignPackedLocals? ctx ctx.condResultName
        (.block ctx.resultTy (.ite c te ee)) (.ret ctx.packCurrent)
  -- L2_while — L2Defs.thy:18 (whileLoopE, no fuel)
  | .While cond body => do
      let c ← termToSSAValue? ctx cond.val
      let be ← fromCom? ctx body
      let by' ← retToYield ctx be
      let lb := SSAExpr.ite c by' (.ret ctx.packCurrent)
      let lv := SSAValue.loopBody ctx.tys ctx.vars ctx.currentValues ctx.resultTy lb
      assignPackedLocals? ctx ctx.loopResultName lv (.ret ctx.packCurrent)
  | .Call _ | .Throw | .Catch _ _ => none

/--
  LocalVarExtract applied to L1 output — the real AC ordering
  (`SimplConv.translate` then `LocalVarExtract.translate`,
  autocorres.ML:586,592; entry point local_var_extract.ML:1607).

  L1 result = `struct [fault, abrupt, FullState]` (L1Defs.thy:16). L2:
  * project the residual globals out of the full state — this is `st` of
    `L2corres` (L2Defs.thy:85–91), here `ABI.projectGlobals`
  * read each local out via `state.get.i` and bind it to its name — AC
    `L2_gets f names` (L2Defs.thy:15), emitted at local_var_extract.ML:865–867
  * return the pack of locals — AC `ret_xf` of `L2corres` (L2Defs.thy:85–91)

  Requires the shared Simpl primCtx with `state.get.*` (same as the L1 live
  path), since the extract must still *mention* the concrete state to read it.
-/
def fromL1? {p : PrimitiveCtx} (lctx : LocalContext) (e : SSAExpr p) :
    Option (SSAExpr p) :=
  let stTy : Ty := .prim "State"
  let flagged : Ty := .struct [.prim "Bool", .prim "Bool", stTy]
  let unpack : SSAExpr p :=
    lctx.vars.zipIdx.foldr
      (fun (v, i) rest =>
        .let_ v.name
          (.call (.primFunc (stateGetName i)) [.var "st"])
          rest)
      (.ret lctx.packCurrent)
  some <|
    .let_ "r1" (.block flagged e) <|
    .let_ "st" (.field [.prim "Bool", .prim "Bool", stTy] ⟨2, by decide⟩ (.var "r1")) <|
    unpack

/--
  Eval L1→L2 extract under full ambient state (AC `st` input).
  Lowering binds outer `st` (same as L1 `lowerEnv`), not local inputEnv.
-/
def evalFromL1? {sc : Context} (lctx : LocalContext)
    (l1 : SSAExpr sc.primCtx) (s : Val sc.primCtx) : Option (Val sc.primCtx) := do
  let l2 ← fromL1? lctx l1
  let t ← SSAExpr.toTerm? l2 { vars := [("st", .var 0)] }
  Term.eval sc.zagCtx [s] t

/-- Locals env of a full State value — the `L2_gets` reads (L2Defs.thy:15). -/
def envOfFullState? (arity : Nat) (s : Val primitiveCtx) :
    Option (List (Val primitiveCtx)) := do
  let full ← State.asFull? s
  let rec go (i : Nat) (acc : List (Val primitiveCtx)) : Option (List (Val primitiveCtx)) :=
    match i with
    | 0 => some acc.reverse
    | i + 1 => do
        let w ← full.getLocal? (arity - 1 - i)
        go i (State.wordVal w :: acc)
  go arity []

def toTermWithLocals? {p : PrimitiveCtx} (ctx : LocalContext) (e : SSAExpr p) :
    Option (Term p) :=
  SSAExpr.toTerm? e { vars := ctx.inputEnv }

def evalSSAWithLocals? {sc : Context} (ctx : LocalContext)
    (env : List (Val sc.primCtx)) (e : SSAExpr sc.primCtx) : Option (Val sc.primCtx) := do
  let t ← toTermWithLocals? ctx e
  Term.eval sc.zagCtx env t

/--
  Pure normal-normal big-step fragment (what `fromCom?` targets): the SIMPL
  subset whose L1 image never takes the `Inl ()`/fail arms of L1Defs.thy:16,
  so `L2corres`'s `ex_xf` (L2Defs.thy:85–91) is vacuous on it.
-/
inductive PureStep {sc : Context} {proc : Type u} {fault : Type v} :
    Com sc proc fault → Val sc.primCtx → Val sc.primCtx → Prop where
  | skip (s : Val sc.primCtx) : PureStep .Skip s s
  | basic {u : Basic sc} {s t : Val sc.primCtx} :
      evalBasic? s u = some t → PureStep (.Basic u) s t
  | seq {c1 c2 : Com sc proc fault} {s m t : Val sc.primCtx} :
      PureStep c1 s m → PureStep c2 m t → PureStep (.Seq c1 c2) s t
  | condTrue {b : BExp sc} {c1 c2 : Com sc proc fault} {s t : Val sc.primCtx} :
      evalBExp? s b = some true → PureStep c1 s t →
      PureStep (.Cond b c1 c2) s t
  | condFalse {b : BExp sc} {c1 c2 : Com sc proc fault} {s t : Val sc.primCtx} :
      evalBExp? s b = some false → PureStep c2 s t →
      PureStep (.Cond b c1 c2) s t
  | whileTrue {b : BExp sc} {c : Com sc proc fault} {s m t : Val sc.primCtx} :
      evalBExp? s b = some true → PureStep c s m → PureStep (.While b c) m t →
      PureStep (.While b c) s t
  | whileFalse {b : BExp sc} {c : Com sc proc fault} {s : Val sc.primCtx} :
      evalBExp? s b = some false → PureStep (.While b c) s s

theorem PureStep.toBigStep {sc : Context} {proc : Type u} {fault : Type v}
    (Γ : ProcEnv sc proc fault) (uf : fault)
    {cmd : Com sc proc fault} {s t : Val sc.primCtx}
    (h : PureStep cmd s t) :
    BigStep Γ uf cmd (.normal s) (.normal t) := by
  induction h with
  | skip s => exact BigStep.skip _
  | basic h => exact BigStep.basic h
  | seq _ _ ih1 ih2 => exact BigStep.seqNormal ih1 ih2
  | condTrue hC _ ih => exact BigStep.condTrue hC ih
  | condFalse hC _ ih => exact BigStep.condFalse hC ih
  | whileTrue hC _ _ ihB ihL => exact BigStep.whileTrue hC ihB ihL
  | whileFalse hC => exact BigStep.whileFalse hC

theorem fromCom_skip {sc : Context} {proc : Type u} {fault : Type v}
    (ctx : LocalContext) :
    fromCom? (sc := sc) (proc := proc) (fault := fault) ctx .Skip =
      some (.ret ctx.packCurrent) := rfl

/--
  Skip faithfulness. AC `L2_skip ≡ L2_gets (λ_. ()) []` — L2Defs.thy:26:
  if Skip translates and `packCurrent` evals to `resultOf s`, PureStep Skip is
  matched.
-/
theorem pureFaithful_skip_eval (sc : Context) (lctx : LocalContext)
    (env : List (Val sc.primCtx)) (r : Val sc.primCtx)
    (heval : evalSSAWithLocals? (sc := sc) lctx env (.ret lctx.packCurrent) = some r) :
    ∃ e, fromCom? (sc := sc) (proc := Empty) (fault := Unit) lctx .Skip = some e ∧
      evalSSAWithLocals? (sc := sc) lctx env e = some r :=
  ⟨.ret lctx.packCurrent, fromCom_skip lctx, heval⟩

/-- Target dialect for successful pure L2 output (arity = `lctx.vars.length`). -/
def targetDialect (lctx : LocalContext) : Dialect.Dialect :=
  Dialect.l2Dialect lctx.vars.length

/--
  AC `L2corres` — L2Defs.thy:85–91:

  ```
  L2corres st ret_xf ex_xf P A C ≡ corresXF st (λ_. ret_xf) (λ_. ex_xf) P A C
  ```

  `C` is the L1 (concrete) body, `A` the L2 (abstract) body, `st` the state
  projection, `P` the precondition. Zag: `st` = full → globals
  (`ABI.projectGlobals`); `ret_xf` = pack of lifted locals, presented as
  `ret_rel` relating the L1 flagged result to the L2 local pack.
-/
def L2corres (sc : Context) (lctx : LocalContext)
    (st : Val sc.primCtx → Option L2State)
    (envOf : Val sc.primCtx → List (Val sc.primCtx))
    (ret_rel : Val sc.primCtx → Val sc.primCtx → Prop)
    (P : Val sc.primCtx → Prop)
    (l2 : SSAExpr sc.primCtx) (l1 : SSAExpr sc.primCtx) : Prop :=
  ∀ (s : Val sc.primCtx),
    P s →
    ∀ v1, L1.evalL1? (ctx := sc) l1 s = some v1 →
      (st s).isSome ∧
      ∃ v2, evalSSAWithLocals? (sc := sc) lctx (envOf s) l2 = some v2 ∧
        ret_rel v1 v2

/--
  The `st` of `L2corres` (L2Defs.thy:85–91) for this ABI: full C-parser record
  → residual globals. This is what makes locals leave the ambient state.
-/
def stOfFull? (s : Val primitiveCtx) : Option L2State := do
  let full ← State.asFull? s
  some (projectGlobals full)

/--
  `L2corres` at the concrete ABI `st = projectGlobals`
  (AC L2Defs.thy:85–91, `st` argument).
-/
def L2corresGlobals (lctx : LocalContext) (sc : Context)
    (hsc : sc.primCtx = primitiveCtx)
    (envOf : Val sc.primCtx → List (Val sc.primCtx))
    (ret_rel : Val sc.primCtx → Val sc.primCtx → Prop)
    (P : Val sc.primCtx → Prop)
    (l2 l1 : SSAExpr sc.primCtx) : Prop :=
  L2corres sc lctx (fun s => stOfFull? (hsc ▸ s)) envOf ret_rel P l2 l1

/-- The `State`-typed `Val` round trip is the identity (ABI packing). -/
theorem toFull_ofFull (s : State) : State.toFull (State.ofFull s) = s := by
  unfold State.toFull State.ofFull
  simp

/--
  `st` is total on `State`-typed values — the `(st s).isSome` side condition of
  `L2corres` (L2Defs.thy:85–91) holds by construction for this ABI, for *every*
  state, not just the ones the tests execute.
-/
theorem stOfFull_isSome (s : State) :
    (stOfFull? (State.valFull s)).isSome = true := by
  simp [stOfFull?, State.asFull?, State.valFull, Val.as?]

/-- `st` keeps the globals and drops the locals — the point of the extract. -/
theorem stOfFull_eq_globals (s : State) :
    stOfFull? (State.valFull s) = some s.globals := by
  simp [stOfFull?, State.asFull?, State.valFull, Val.as?, projectGlobals,
    toFull_ofFull]

/--
  L2 faithfulness = general `Corres.SimplPureFaithful`.
  `envOf` / `resultOf` are ABI-specific (see `Word2`).
-/
def Faithful (sc : Context) (lctx : LocalContext)
    (envOf : Val sc.primCtx → List (Val sc.primCtx))
    (resultOf : Val sc.primCtx → Val sc.primCtx) : Prop :=
  ∀ (proc : Type) (fault : Type),
    SimplPureFaithful (ctx := sc) (proc := proc) (fault := fault)
      (PureStep (sc := sc) (proc := proc) (fault := fault))
      (fromCom? (sc := sc) (proc := proc) (fault := fault) lctx)
      envOf resultOf
      (fun e env => evalSSAWithLocals? (sc := sc) lctx env e)

end Lang.Simple.Lift.L2
