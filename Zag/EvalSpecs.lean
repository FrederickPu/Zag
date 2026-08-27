import Zag.Loop
import Std.Tactic.Do

namespace Zag

namespace EvalTriple

namespace Exact

open scoped Std.Do

attribute [spec] Scope.get?_nil Scope.get?_cons
attribute [spec] List.length_nil List.length_cons
attribute [spec] List.nil_append List.cons_append
attribute [spec] List.drop_nil List.drop_zero List.drop_succ_cons
attribute [spec] List.map_nil List.map_cons List.zip_nil_left List.zip_nil_right List.zip_cons_cons
attribute [spec] List.getElem_cons_zero List.getElem_cons_succ
attribute [spec] List.get_cons_zero List.get_cons_succ List.get_cons_succ'
attribute [spec] somePost_some somePost_none someEqPost_some someEqPost_none

@[spec] theorem Instr.ofTerm_name {primCtx : PrimitiveCtx}
    (name : String) (value : Term primCtx) :
    (Instr.ofTerm name value).name = name := rfl

@[spec] theorem Instr.ofTerm_value {primCtx : PrimitiveCtx}
    (name : String) (value : Term primCtx) :
    (Instr.ofTerm name value).value = value := rfl

@[spec] theorem Block.entryEnv_eq {primCtx : PrimitiveCtx}
    (block : Block primCtx) (args : List (Val primCtx)) :
    block.entryEnv args = (block.params.map Prod.fst).zip args := rfl

@[spec] theorem Option.or_eq {α : Type _} (left right : Option α) :
    left.or right = match left with
    | some value => some value
    | none => right := by
  cases left <;> rfl

@[spec] theorem List.getElem_cons_zero_spec {α : Type _}
    (head : α) (tail : List α) (h : 0 < (head :: tail).length) :
    (head :: tail)[0]'h = head := rfl

@[spec] theorem List.getElem_cons_succ_spec {α : Type _}
    (head : α) (tail : List α) (idx : Nat)
    (h : idx + 1 < (head :: tail).length) :
    (head :: tail)[idx + 1]'h = tail[idx]'(Nat.lt_of_succ_lt_succ h) := rfl

@[spec] theorem BlockCtx.get?_mk {primCtx : PrimitiveCtx}
    (ctx : BlockCtx.Raw primCtx) (h : BlockCtx.Valid ctx) (name : String) :
    BlockCtx.get? ⟨ctx, h⟩ name = ctx.get? name := rfl

@[spec] theorem BlockCtx.Raw.get?_eq {primCtx : PrimitiveCtx}
    (ctx : BlockCtx.Raw primCtx) (name : String) :
    BlockCtx.Raw.get? ctx name = Scope.get? ctx name := rfl

def evalInstrs? (ctx : Ctx) (instrs : List (Instr ctx.primCtx))
    (result : Term ctx.primCtx) (env : Env ctx.primCtx)
    (hM : ctx.M = Id := by first | assumption | rfl) :
    Std.Do.PredTrans .pure (Option (Val ctx.primCtx)) :=
  EvalTriple.total? fun value => Exact.EvaluatesInstrs ctx instrs result env value hM

def evalListPre (ctx : Ctx) (env : Env ctx.primCtx)
    (terms : List (Term ctx.primCtx)) (hM : ctx.M = Id)
    (Q : Std.Do.PostCond (Option (List (Val ctx.primCtx))) .pure) :
    Std.Do.Assertion .pure :=
  match terms with
  | [] => Q.1 (some [])
  | term :: terms =>
      (Std.Do.wp (eval? ctx env term hM)).apply
        (somePost fun value =>
          (Std.Do.wp (evalList? ctx env terms hM)).apply
            (somePost fun values => Q.1 (some (value :: values))))

def evalInstrsPre (ctx : Ctx) (instrs : List (Instr ctx.primCtx))
    (result : Term ctx.primCtx) (env : Env ctx.primCtx) (hM : ctx.M = Id)
    (Q : Std.Do.PostCond (Option (Val ctx.primCtx)) .pure) :
    Std.Do.Assertion .pure :=
  match instrs with
  | [] =>
      (Std.Do.wp (eval? ctx env result hM)).apply
        (somePost fun value => Q.1 (some value))
  | instr :: instrs =>
      (Std.Do.wp (eval? ctx env instr.value hM)).apply
        (somePost fun instrValue =>
          (Std.Do.wp (evalInstrs? ctx instrs result
              (env ++ [(instr.name, instrValue)]) hM)).apply
            (somePost fun value => Q.1 (some value)))

def evalListStep? (ctx : Ctx) (env : Env ctx.primCtx)
    (terms : List (Term ctx.primCtx)) (hM : ctx.M = Id) :
    Std.Do.PredTrans .pure (Option (List (Val ctx.primCtx))) :=
  match terms with
  | [] => pure (some [])
  | .var name :: terms =>
      match Scope.get? env name with
      | some value =>
          evalList? ctx env terms hM >>= fun
          | some values => pure (some (value :: values))
          | none => pure none
      | none =>
          eval? ctx env (.var name) hM >>= fun
          | some value =>
              evalList? ctx env terms hM >>= fun
              | some values => pure (some (value :: values))
              | none => pure none
          | none => pure none
  | .prim ty value :: terms =>
      evalList? ctx env terms hM >>= fun
      | some values => pure (some (.mk ty value :: values))
      | none => pure none
  | term :: terms =>
      eval? ctx env term hM >>= fun
      | some value =>
          evalList? ctx env terms hM >>= fun
          | some values => pure (some (value :: values))
           | none => pure none
       | none => pure none

attribute [irreducible] evalListStep?

@[spec] theorem evalListStep?_nil {ctx : Ctx} {hM : ctx.M = Id}
    (env : Env ctx.primCtx) :
    evalListStep? ctx env [] hM = pure (some []) := by
  unfold evalListStep?
  rfl

@[spec] theorem evalListStep?_cons {ctx : Ctx} {hM : ctx.M = Id}
    (env : Env ctx.primCtx) (term : Term ctx.primCtx)
    (terms : List (Term ctx.primCtx)) :
    evalListStep? ctx env (term :: terms) hM =
      match term with
      | .var name =>
          match Scope.get? env name with
          | some value =>
              evalList? ctx env terms hM >>= fun
              | some values => pure (some (value :: values))
              | none => pure none
          | none =>
              eval? ctx env (.var name) hM >>= fun
              | some value =>
                  evalList? ctx env terms hM >>= fun
                  | some values => pure (some (value :: values))
                  | none => pure none
              | none => pure none
      | .prim ty value =>
          evalList? ctx env terms hM >>= fun
          | some values => pure (some (.mk ty value :: values))
          | none => pure none
      | term =>
          eval? ctx env term hM >>= fun
          | some value =>
              evalList? ctx env terms hM >>= fun
              | some values => pure (some (value :: values))
              | none => pure none
          | none => pure none := by
  unfold evalListStep?
  cases term <;> rfl

@[spec] theorem evalListStep?_eq {ctx : Ctx} {hM : ctx.M = Id}
    (env : Env ctx.primCtx) (terms : List (Term ctx.primCtx)) :
    evalListStep? ctx env terms hM =
      match terms with
      | [] => pure (some [])
      | .var name :: terms =>
          match Scope.get? env name with
          | some value =>
              evalList? ctx env terms hM >>= fun
              | some values => pure (some (value :: values))
              | none => pure none
          | none =>
              eval? ctx env (.var name) hM >>= fun
              | some value =>
                  evalList? ctx env terms hM >>= fun
                  | some values => pure (some (value :: values))
                  | none => pure none
              | none => pure none
      | .prim ty value :: terms =>
          evalList? ctx env terms hM >>= fun
          | some values => pure (some (.mk ty value :: values))
          | none => pure none
       | term :: terms =>
           (eval? ctx env term hM >>= fun
           | some value =>
               evalList? ctx env terms hM >>= fun
               | some values => pure (some (value :: values))
               | none => pure none
           | none => pure none) := by
  unfold evalListStep?
  cases terms with
  | nil => rfl
  | cons term terms => cases term <;> rfl

@[spec 1100] theorem evalListStep?_wp_spec {ctx : Ctx} {hM : ctx.M = Id}
    (env : Env ctx.primCtx) (terms : List (Term ctx.primCtx))
    (Q : Std.Do.PostCond (Option (List (Val ctx.primCtx))) .pure) :
    Std.Do.Triple (evalListStep? ctx env terms hM)
      ((Std.Do.wp
        (match terms with
        | [] => pure (some [])
        | .var name :: terms =>
            match Scope.get? env name with
            | some value =>
                evalList? ctx env terms hM >>= fun
                | some values => pure (some (value :: values))
                | none => pure none
            | none =>
                eval? ctx env (.var name) hM >>= fun
                | some value =>
                    evalList? ctx env terms hM >>= fun
                    | some values => pure (some (value :: values))
                    | none => pure none
                | none => pure none
        | .prim ty value :: terms =>
            evalList? ctx env terms hM >>= fun
            | some values => pure (some (.mk ty value :: values))
            | none => pure none
        | term :: terms =>
            eval? ctx env term hM >>= fun
            | some value =>
                evalList? ctx env terms hM >>= fun
                | some values => pure (some (value :: values))
                | none => pure none
            | none => pure none)).apply Q) Q := by
  rw [Std.Do.Triple.iff]
  intro hpre
  simpa [evalListStep?_eq] using hpre

def evalVarStep? (ctx : Ctx) (env : Env ctx.primCtx) (name : String)
    (_hM : ctx.M = Id) : Std.Do.PredTrans .pure (Option (Val ctx.primCtx)) :=
  match Scope.get? env name with
  | some value => pure (some value)
  | none =>
      match ctx.blockCtx.get? name with
      | some block => pure (some (.blockRef name (block.params.map Prod.snd) block.outTy))
      | none => pure none

@[spec] theorem evalVarStep?_eq {ctx : Ctx} {hM : ctx.M = Id}
    (env : Env ctx.primCtx) (name : String) :
    evalVarStep? ctx env name hM =
      match Scope.get? env name with
      | some value => pure (some value)
      | none =>
          match ctx.blockCtx.get? name with
           | some block => pure (some (.blockRef name (block.params.map Prod.snd) block.outTy))
           | none => pure none := by
  rfl

@[spec 1100] theorem evalVarStep?_wp_spec {ctx : Ctx} {hM : ctx.M = Id}
    (env : Env ctx.primCtx) (name : String)
    (Q : Std.Do.PostCond (Option (Val ctx.primCtx)) .pure) :
    Std.Do.Triple (evalVarStep? ctx env name hM)
      ((Std.Do.wp
        ((match Scope.get? env name with
        | some value => pure (some value)
        | none =>
            match ctx.blockCtx.get? name with
            | some block => pure (some (Val.blockRef name (block.params.map Prod.snd) block.outTy))
            | none => pure none) :
          Std.Do.PredTrans .pure (Option (Val ctx.primCtx)))).apply Q) Q := by
  rw [Std.Do.Triple.iff]
  intro hpre
  simpa [evalVarStep?] using hpre

def evalInstrsStep? (ctx : Ctx) (instrs : List (Instr ctx.primCtx))
    (result : Term ctx.primCtx) (env : Env ctx.primCtx) (hM : ctx.M = Id) :
    Std.Do.PredTrans .pure (Option (Val ctx.primCtx)) :=
  match instrs with
  | [] => eval? ctx env result hM
  | instr :: instrs =>
      eval? ctx env instr.value hM >>= fun
      | some instrValue =>
          evalInstrs? ctx instrs result (env ++ [(instr.name, instrValue)]) hM
      | none => pure none

def callValuesStep? (ctx : Ctx) (name : String) (args : List (Val ctx.primCtx))
    (hM : ctx.M = Id) : Std.Do.PredTrans .pure (Option (Val ctx.primCtx)) :=
  match ctx.blockCtx.get? name with
  | some block =>
      if args.length = block.params.length then
        evalInstrs? ctx block.instrs block.result (block.entryEnv args) hM
      else
        pure none
  | none => pure none

def evalCallStep? (ctx : Ctx) (env : Env ctx.primCtx)
    (name : String) (args : List (Term ctx.primCtx)) (hM : ctx.M = Id) :
    Std.Do.PredTrans .pure (Option (Val ctx.primCtx)) :=
  evalList? ctx env args hM >>= fun
  | some argValues => callValues? ctx name argValues hM
  | none => pure none

@[spec] theorem evalInstrsStep?_nil {ctx : Ctx} {hM : ctx.M = Id}
    (result : Term ctx.primCtx) (env : Env ctx.primCtx) :
    evalInstrsStep? ctx [] result env hM = eval? ctx env result hM := rfl

@[spec] theorem evalInstrsStep?_cons {ctx : Ctx} {hM : ctx.M = Id}
    (instr : Instr ctx.primCtx) (instrs : List (Instr ctx.primCtx))
    (result : Term ctx.primCtx) (env : Env ctx.primCtx) :
    evalInstrsStep? ctx (instr :: instrs) result env hM =
      (eval? ctx env instr.value hM >>= fun
      | some instrValue =>
          evalInstrs? ctx instrs result (env ++ [(instr.name, instrValue)]) hM
      | none => pure none) := rfl

@[spec] theorem evalInstrsStep?_eq {ctx : Ctx} {hM : ctx.M = Id}
    (instrs : List (Instr ctx.primCtx)) (result : Term ctx.primCtx)
    (env : Env ctx.primCtx) :
    evalInstrsStep? ctx instrs result env hM =
      match instrs with
      | [] => eval? ctx env result hM
      | instr :: instrs =>
          eval? ctx env instr.value hM >>= fun
          | some instrValue =>
              evalInstrs? ctx instrs result (env ++ [(instr.name, instrValue)]) hM
           | none => pure none := by
  cases instrs <;> rfl

@[spec 1100] theorem evalInstrsStep?_wp_spec {ctx : Ctx} {hM : ctx.M = Id}
    (instrs : List (Instr ctx.primCtx)) (result : Term ctx.primCtx)
    (env : Env ctx.primCtx)
    (Q : Std.Do.PostCond (Option (Val ctx.primCtx)) .pure) :
    Std.Do.Triple (evalInstrsStep? ctx instrs result env hM)
      ((Std.Do.wp
        (match instrs with
        | [] => eval? ctx env result hM
        | instr :: instrs =>
            eval? ctx env instr.value hM >>= fun
            | some instrValue =>
                evalInstrs? ctx instrs result (env ++ [(instr.name, instrValue)]) hM
            | none => pure none)).apply Q) Q := by
  rw [Std.Do.Triple.iff]
  intro hpre
  simpa [evalInstrsStep?] using hpre

@[spec] theorem callValuesStep?_eq {ctx : Ctx} {hM : ctx.M = Id}
    (name : String) (args : List (Val ctx.primCtx)) :
    callValuesStep? ctx name args hM =
      match ctx.blockCtx.get? name with
      | some block =>
          if args.length = block.params.length then
            evalInstrs? ctx block.instrs block.result (block.entryEnv args) hM
          else
            pure none
      | none => pure none := by
  rfl

@[spec 1100] theorem callValuesStep?_wp_spec {ctx : Ctx} {hM : ctx.M = Id}
    (name : String) (args : List (Val ctx.primCtx))
    (Q : Std.Do.PostCond (Option (Val ctx.primCtx)) .pure) :
    Std.Do.Triple (callValuesStep? ctx name args hM)
      ((Std.Do.wp
        (match ctx.blockCtx.get? name with
        | some block =>
            if args.length = block.params.length then
              evalInstrs? ctx block.instrs block.result (block.entryEnv args) hM
            else
              pure none
        | none => pure none)).apply Q) Q := by
  rw [Std.Do.Triple.iff]
  intro hpre
  simpa [callValuesStep?] using hpre

@[spec] theorem evalCallStep?_eq {ctx : Ctx} {hM : ctx.M = Id}
    (env : Env ctx.primCtx) (name : String) (args : List (Term ctx.primCtx)) :
    evalCallStep? ctx env name args hM =
      (evalList? ctx env args hM >>= fun
      | some argValues => callValues? ctx name argValues hM
      | none => pure none) := by
  rfl

@[spec 1100] theorem evalCallStep?_wp_spec {ctx : Ctx} {hM : ctx.M = Id}
    (env : Env ctx.primCtx) (name : String) (args : List (Term ctx.primCtx))
    (Q : Std.Do.PostCond (Option (Val ctx.primCtx)) .pure) :
    Std.Do.Triple (evalCallStep? ctx env name args hM)
      ((Std.Do.wp
        (evalList? ctx env args hM >>= fun
        | some argValues => callValues? ctx name argValues hM
        | none => pure none)).apply Q) Q := by
  rw [Std.Do.Triple.iff]
  intro hpre
  simpa [evalCallStep?] using hpre

theorem total?_wp_some {α : Type} {R : α → Prop}
    {Q : Std.Do.PostCond (Option α) .pure}
    (h : ((Std.Do.wp (EvalTriple.total? R)).apply Q).down)
    {value : α} (hvalue : R value) : (Q.1 (some value)).down := by
  change ((∀ value, R value → (Q.1 (some value)).down) ∧
    ((∀ value, ¬ R value) → (Q.1 none).down)) at h
  exact h.1 value hvalue

theorem total?_wp_none {α : Type} {R : α → Prop}
    {Q : Std.Do.PostCond (Option α) .pure}
    (h : ((Std.Do.wp (EvalTriple.total? R)).apply Q).down)
    (hnone : ∀ value, ¬ R value) : (Q.1 none).down := by
  change ((∀ value, R value → (Q.1 (some value)).down) ∧
    ((∀ value, ¬ R value) → (Q.1 none).down)) at h
  exact h.2 hnone

theorem eval?_wp_some {ctx : Ctx} {env : Env ctx.primCtx}
    {term : Term ctx.primCtx} {hM : ctx.M = Id}
    {Q : Std.Do.PostCond (Option (Val ctx.primCtx)) .pure}
    (h : ((Std.Do.wp (eval? ctx env term hM)).apply Q).down)
    {value : Val ctx.primCtx} (hvalue : Exact.EvaluatesTo ctx env term value hM) :
    (Q.1 (some value)).down :=
  total?_wp_some (R := fun value => Exact.EvaluatesTo ctx env term value hM) h hvalue

theorem eval?_wp_none {ctx : Ctx} {env : Env ctx.primCtx}
    {term : Term ctx.primCtx} {hM : ctx.M = Id}
    {Q : Std.Do.PostCond (Option (Val ctx.primCtx)) .pure}
    (h : ((Std.Do.wp (eval? ctx env term hM)).apply Q).down)
    (hnone : ∀ value, ¬ Exact.EvaluatesTo ctx env term value hM) :
    (Q.1 none).down :=
  total?_wp_none (R := fun value => Exact.EvaluatesTo ctx env term value hM) h hnone

theorem evalList?_wp_some {ctx : Ctx} {env : Env ctx.primCtx}
    {terms : List (Term ctx.primCtx)} {hM : ctx.M = Id}
    {Q : Std.Do.PostCond (Option (List (Val ctx.primCtx))) .pure}
    (h : ((Std.Do.wp (evalList? ctx env terms hM)).apply Q).down)
    {values : List (Val ctx.primCtx)}
    (hvalues : Exact.EvaluatesList ctx env terms values hM) :
    (Q.1 (some values)).down :=
  total?_wp_some (R := fun values => Exact.EvaluatesList ctx env terms values hM) h hvalues

theorem evalList?_wp_none {ctx : Ctx} {env : Env ctx.primCtx}
    {terms : List (Term ctx.primCtx)} {hM : ctx.M = Id}
    {Q : Std.Do.PostCond (Option (List (Val ctx.primCtx))) .pure}
    (h : ((Std.Do.wp (evalList? ctx env terms hM)).apply Q).down)
    (hnone : ∀ values, ¬ Exact.EvaluatesList ctx env terms values hM) :
    (Q.1 none).down :=
  total?_wp_none (R := fun values => Exact.EvaluatesList ctx env terms values hM) h hnone

theorem evalInstrs?_wp_some {ctx : Ctx} {instrs : List (Instr ctx.primCtx)}
    {result : Term ctx.primCtx} {env : Env ctx.primCtx} {hM : ctx.M = Id}
    {Q : Std.Do.PostCond (Option (Val ctx.primCtx)) .pure}
    (h : ((Std.Do.wp (evalInstrs? ctx instrs result env hM)).apply Q).down)
    {value : Val ctx.primCtx}
    (hvalue : Exact.EvaluatesInstrs ctx instrs result env value hM) :
    (Q.1 (some value)).down :=
  total?_wp_some (R := fun value => Exact.EvaluatesInstrs ctx instrs result env value hM) h hvalue

theorem evalInstrs?_wp_none {ctx : Ctx} {instrs : List (Instr ctx.primCtx)}
    {result : Term ctx.primCtx} {env : Env ctx.primCtx} {hM : ctx.M = Id}
    {Q : Std.Do.PostCond (Option (Val ctx.primCtx)) .pure}
    (h : ((Std.Do.wp (evalInstrs? ctx instrs result env hM)).apply Q).down)
    (hnone : ∀ value, ¬ Exact.EvaluatesInstrs ctx instrs result env value hM) :
    (Q.1 none).down :=
  total?_wp_none (R := fun value => Exact.EvaluatesInstrs ctx instrs result env value hM) h hnone

theorem EvaluatesInstrs.unique {ctx : Ctx} {instrs : List (Instr ctx.primCtx)}
    {result : Term ctx.primCtx} {env : Env ctx.primCtx}
    {value₁ value₂ : Val ctx.primCtx} {hM : ctx.M = Id}
    (h₁ : Exact.EvaluatesInstrs ctx instrs result env value₁ hM)
    (h₂ : Exact.EvaluatesInstrs ctx instrs result env value₂ hM) : value₁ = value₂ := by
  induction h₁ generalizing value₂ with
  | nil hresult₁ =>
      cases h₂ with
      | nil hresult₂ => exact Exact.EvaluatesTo.unique hresult₁ hresult₂
  | cons hinstr₁ hrest₁ ih =>
      cases h₂ with
      | cons hinstr₂ hrest₂ =>
          have hinstr : _ := Exact.EvaluatesTo.unique hinstr₁ hinstr₂
          subst hinstr
          exact ih hrest₂

theorem EvaluatesCallValues.unique {ctx : Ctx} {name : String}
    {args : List (Val ctx.primCtx)} {value₁ value₂ : Val ctx.primCtx}
    {hM : ctx.M = Id}
    (h₁ : Exact.EvaluatesCallValues ctx name args value₁ hM)
    (h₂ : Exact.EvaluatesCallValues ctx name args value₂ hM) : value₁ = value₂ :=
  Exact.EvaluatesApply.unique
    (Exact.EvaluatesApply.blockRef (argTys := args.map Val.ty) (outTy := value₁.ty) h₁)
    (Exact.EvaluatesApply.blockRef (argTys := args.map Val.ty) (outTy := value₁.ty) h₂)

theorem evalInstrs?_some_of_wp {ctx : Ctx} {instrs : List (Instr ctx.primCtx)}
    {result : Term ctx.primCtx} {env : Env ctx.primCtx} {hM : ctx.M = Id}
    {success : Val ctx.primCtx → Std.Do.Assertion .pure}
    (h : ((Std.Do.wp (evalInstrs? ctx instrs result env hM)).apply (somePost success)).down) :
    ∃ value, Exact.EvaluatesInstrs ctx instrs result env value hM ∧ (success value).down := by
  exact EvalTriple.total?_some_of_wp (R := fun value =>
    Exact.EvaluatesInstrs ctx instrs result env value hM) (success := success) h

theorem evaluatesInstrs_of_evalInstrs?_triple {ctx : Ctx}
    {instrs : List (Instr ctx.primCtx)} {result : Term ctx.primCtx}
    {env : Env ctx.primCtx} {hM : ctx.M = Id} {value : Val ctx.primCtx}
    (h : Std.Do.Triple (evalInstrs? ctx instrs result env hM) (Std.Do.SPred.pure True)
      (someEqPost value)) :
    Exact.EvaluatesInstrs ctx instrs result env value hM := by
  have hwp := (Std.Do.Triple.iff.mp h) trivial
  obtain ⟨actual, hactual, heq⟩ := evalInstrs?_some_of_wp hwp
  subst actual
  exact hactual

theorem evalInstrs?_triple_of_evaluatesInstrs {ctx : Ctx}
    {instrs : List (Instr ctx.primCtx)} {result : Term ctx.primCtx}
    {env : Env ctx.primCtx} {hM : ctx.M = Id} {value : Val ctx.primCtx}
    (h : Exact.EvaluatesInstrs ctx instrs result env value hM)
    (Q : Std.Do.PostCond (Option (Val ctx.primCtx)) .pure) :
    Std.Do.Triple (evalInstrs? ctx instrs result env hM) (Q.1 (some value)) Q := by
  change (Q.1 (some value)).down → _
  intro hQ
  dsimp [evalInstrs?, total?]
  constructor
  · intro actual hactual
    have hsame : actual = value := EvaluatesInstrs.unique hactual h
    subst actual
    exact hQ
  · intro hnone
    exact (hnone value h).elim

theorem callValues?_triple_of_evaluatesCallValues {ctx : Ctx} {name : String}
    {args : List (Val ctx.primCtx)} {hM : ctx.M = Id} {value : Val ctx.primCtx}
    (h : Exact.EvaluatesCallValues ctx name args value hM)
    (Q : Std.Do.PostCond (Option (Val ctx.primCtx)) .pure) :
    Std.Do.Triple (callValues? ctx name args hM) (Q.1 (some value)) Q := by
  change (Q.1 (some value)).down → _
  intro hQ
  dsimp [callValues?, total?]
  constructor
  · intro actual hactual
    have hsame : actual = value := EvaluatesCallValues.unique hactual h
    subst actual
    exact hQ
  · intro hnone
    exact (hnone value h).elim

theorem eval?_eq_triple_of_evaluatesTo {ctx : Ctx} {env : Env ctx.primCtx}
    {term : Term ctx.primCtx} {hM : ctx.M = Id} {value : Val ctx.primCtx}
    (h : Exact.EvaluatesTo ctx env term value hM) :
    Std.Do.Triple (eval? ctx env term hM) (Std.Do.SPred.pure True) (someEqPost value) := by
  change True → _
  intro _
  exact (eval?_triple_of_evaluatesTo h (someEqPost value)) rfl

theorem evalList?_eq_triple_of_evaluatesList {ctx : Ctx} {env : Env ctx.primCtx}
    {terms : List (Term ctx.primCtx)} {hM : ctx.M = Id}
    {values : List (Val ctx.primCtx)}
    (h : Exact.EvaluatesList ctx env terms values hM) :
    Std.Do.Triple (evalList? ctx env terms hM) (Std.Do.SPred.pure True) (someEqPost values) := by
  change True → _
  intro _
  exact (evalList?_triple_of_evaluatesList h (someEqPost values)) rfl

theorem apply?_eq_triple_of_evaluatesApply {ctx : Ctx} {fn : Val ctx.primCtx}
    {args : List (Val ctx.primCtx)} {hM : ctx.M = Id} {value : Val ctx.primCtx}
    (h : Exact.EvaluatesApply ctx fn args value hM) :
    Std.Do.Triple (apply? ctx fn args hM) (Std.Do.SPred.pure True) (someEqPost value) := by
  change True → _
  intro _
  exact (apply?_triple_of_evaluatesApply h (someEqPost value)) rfl

theorem callValues?_eq_triple_of_evaluatesCallValues {ctx : Ctx} {name : String}
    {args : List (Val ctx.primCtx)} {hM : ctx.M = Id} {value : Val ctx.primCtx}
    (h : Exact.EvaluatesCallValues ctx name args value hM) :
    Std.Do.Triple (callValues? ctx name args hM) (Std.Do.SPred.pure True) (someEqPost value) := by
  change True → _
  intro _
  exact (callValues?_triple_of_evaluatesCallValues h (someEqPost value)) rfl

theorem evalInstrs?_eq_triple_of_evaluatesInstrs {ctx : Ctx}
    {instrs : List (Instr ctx.primCtx)} {result : Term ctx.primCtx}
    {env : Env ctx.primCtx} {hM : ctx.M = Id} {value : Val ctx.primCtx}
    (h : Exact.EvaluatesInstrs ctx instrs result env value hM) :
    Std.Do.Triple (evalInstrs? ctx instrs result env hM)
      (Std.Do.SPred.pure True) (someEqPost value) := by
  change True → _
  intro _
  exact (evalInstrs?_triple_of_evaluatesInstrs h (someEqPost value)) rfl

theorem evalInstrs?_nil_eq_spec {ctx : Ctx} {hM : ctx.M = Id}
    {result : Term ctx.primCtx} {env : Env ctx.primCtx} {value : Val ctx.primCtx}
    (hresult : Std.Do.Triple (eval? ctx env result hM)
      (Std.Do.SPred.pure True) (someEqPost value)) :
    Std.Do.Triple (evalInstrs? ctx [] result env hM)
      (Std.Do.SPred.pure True) (someEqPost value) :=
  evalInstrs?_eq_triple_of_evaluatesInstrs
    (EvaluatesInstrs.nil (evaluatesTo_of_eval?_triple hresult))

theorem evalInstrs?_cons_eq_spec {ctx : Ctx} {hM : ctx.M = Id}
    {instr : Instr ctx.primCtx} {instrs : List (Instr ctx.primCtx)}
    {result : Term ctx.primCtx} {env : Env ctx.primCtx}
    {instrValue value : Val ctx.primCtx}
    (hinstr : Std.Do.Triple (eval? ctx env instr.value hM)
      (Std.Do.SPred.pure True) (someEqPost instrValue))
    (hrest : Std.Do.Triple (evalInstrs? ctx instrs result
        (env ++ [(instr.name, instrValue)]) hM)
      (Std.Do.SPred.pure True) (someEqPost value)) :
    Std.Do.Triple (evalInstrs? ctx (instr :: instrs) result env hM)
      (Std.Do.SPred.pure True) (someEqPost value) :=
  evalInstrs?_eq_triple_of_evaluatesInstrs
    (EvaluatesInstrs.cons (evaluatesTo_of_eval?_triple hinstr)
      (evaluatesInstrs_of_evalInstrs?_triple hrest))

@[spec] theorem eval?_prim_spec {ctx : Ctx} {hM : ctx.M = Id}
    (env : Env ctx.primCtx) (ty : Ty) (value : Ty.type ctx.primCtx ty)
    (Q : Std.Do.PostCond (Option (Val ctx.primCtx)) .pure) :
    Std.Do.Triple (eval? ctx env (.prim ty value) hM) (Q.1 (some (.mk ty value))) Q := by
  exact eval?_triple_of_evaluatesTo (EvaluatesTo.prim ty value) Q

@[spec 1100] theorem eval?_var_spec {ctx : Ctx} {hM : ctx.M = Id}
    (env : Env ctx.primCtx) (name : String)
    (Q : Std.Do.PostCond (Option (Val ctx.primCtx)) .pure) :
    Std.Do.Triple (eval? ctx env (.var name) hM)
      ((Std.Do.wp (evalVarStep? ctx env name hM)).apply
        (somePost fun value => Q.1 (some value))) Q := by
  change _ → _
  intro hpre
  unfold evalVarStep? at hpre
  cases hlocal : Scope.get? env name with
  | some value =>
      have hQ : (Q.1 (some value)).down := by
        simpa [hlocal, Std.Do.PredTrans.apply_pure] using hpre
      exact (eval?_triple_of_evaluatesTo (EvaluatesTo.var_local hlocal) Q) hQ
  | none =>
      cases hblock : ctx.blockCtx.get? name with
      | some block =>
          have hQ : (Q.1 (some (.blockRef name (block.params.map Prod.snd) block.outTy))).down := by
            simpa [hlocal, hblock, Std.Do.PredTrans.apply_pure] using hpre
          exact (eval?_triple_of_evaluatesTo (EvaluatesTo.var_block hlocal hblock) Q) hQ
      | none =>
          simp [hlocal, hblock] at hpre

@[spec] theorem eval?_var_local_spec {ctx : Ctx} {hM : ctx.M = Id}
    {env : Env ctx.primCtx} {name : String} {value : Val ctx.primCtx}
    (hlocal : Scope.get? env name = some value)
    (Q : Std.Do.PostCond (Option (Val ctx.primCtx)) .pure) :
    Std.Do.Triple (eval? ctx env (.var name) hM) (Q.1 (some value)) Q := by
  exact eval?_triple_of_evaluatesTo (EvaluatesTo.var_local hlocal) Q

@[spec] theorem eval?_var_block_spec {ctx : Ctx} {hM : ctx.M = Id}
    {env : Env ctx.primCtx} {name : String} {block : Block ctx.primCtx}
    (hlocal : Scope.get? env name = none)
    (hblock : ctx.blockCtx.get? name = some block)
    (Q : Std.Do.PostCond (Option (Val ctx.primCtx)) .pure) :
    Std.Do.Triple (eval? ctx env (.var name) hM)
      (Q.1 (some (.blockRef name (block.params.map Prod.snd) block.outTy))) Q := by
  exact eval?_triple_of_evaluatesTo (EvaluatesTo.var_block hlocal hblock) Q

@[spec] theorem evalList?_nil_spec {ctx : Ctx} {hM : ctx.M = Id}
    (env : Env ctx.primCtx)
    (Q : Std.Do.PostCond (Option (List (Val ctx.primCtx))) .pure) :
    Std.Do.Triple (evalList? ctx env [] hM) (Q.1 (some [])) Q := by
  exact evalList?_triple_of_evaluatesList EvaluatesList.nil Q

@[spec] theorem evalList?_cons_spec {ctx : Ctx} {hM : ctx.M = Id}
    (env : Env ctx.primCtx) (term : Term ctx.primCtx) (terms : List (Term ctx.primCtx))
    (Q : Std.Do.PostCond (Option (List (Val ctx.primCtx))) .pure) :
    Std.Do.Triple (evalList? ctx env (term :: terms) hM)
      ((Std.Do.wp (eval? ctx env term hM)).apply
        (somePost fun value =>
          (Std.Do.wp (evalList? ctx env terms hM)).apply
            (somePost fun values => Q.1 (some (value :: values))))) Q := by
  change _ → _
  intro hpre
  obtain ⟨value, hvalue, hrestWp⟩ := eval?_some_of_wp hpre
  obtain ⟨values, hvalues, hQ⟩ := evalList?_some_of_wp hrestWp
  exact (evalList?_triple_of_evaluatesList (EvaluatesList.cons hvalue hvalues) Q) hQ

theorem evalList?_cons_value_step {ctx : Ctx} {hM : ctx.M = Id}
    {env : Env ctx.primCtx} {term : Term ctx.primCtx}
    {terms : List (Term ctx.primCtx)} {value : Val ctx.primCtx}
    (hhead : Exact.EvaluatesTo ctx env term value hM)
    (Q : Std.Do.PostCond (Option (List (Val ctx.primCtx))) .pure) :
    Std.Do.Triple (evalList? ctx env (term :: terms) hM)
      ((Std.Do.wp
        (evalList? ctx env terms hM >>= fun
        | some values => pure (some (value :: values))
        | none => pure none)).apply Q) Q := by
  let listPost : Std.Do.PostCond (Option (List (Val ctx.primCtx))) .pure :=
    (fun result =>
      (Std.Do.wp
        ((match result with
        | some values => pure (some (value :: values))
        | none => pure none) :
          Std.Do.PredTrans .pure (Option (List (Val ctx.primCtx))))).apply Q, Q.2)
  rw [Std.Do.Triple.iff]
  intro hpre
  have htailPre : ((Std.Do.wp (evalList? ctx env terms hM)).apply listPost).down := by
    simpa [listPost, Std.Do.PredTrans.apply_bind] using hpre
  dsimp [evalList?, total?]
  constructor
  · intro values hvalues
    cases hvalues with
    | cons hterm htail =>
        have hsame := Exact.EvaluatesTo.unique hhead hterm
        have hQ := evalList?_wp_some htailPre htail
        simpa [listPost, Std.Do.PredTrans.apply_pure, hsame] using hQ
  · intro hnone
    have htailNone : ∀ values, ¬ Exact.EvaluatesList ctx env terms values hM := by
      intro values htail
      exact hnone (value :: values) (Exact.EvaluatesList.cons hhead htail)
    have hQ := evalList?_wp_none htailPre htailNone
    simpa [listPost, Std.Do.PredTrans.apply_pure] using hQ

theorem evalList?_cons_step {ctx : Ctx} {hM : ctx.M = Id}
    (env : Env ctx.primCtx) (term : Term ctx.primCtx)
    (terms : List (Term ctx.primCtx))
    (Q : Std.Do.PostCond (Option (List (Val ctx.primCtx))) .pure) :
    Std.Do.Triple (evalList? ctx env (term :: terms) hM)
      ((Std.Do.wp
        (eval? ctx env term hM >>= fun
        | some value =>
            evalList? ctx env terms hM >>= fun
            | some values => pure (some (value :: values))
            | none => pure none
        | none => pure none)).apply Q) Q := by
  let termPost : Std.Do.PostCond (Option (Val ctx.primCtx)) .pure :=
    (fun result =>
      (Std.Do.wp
        ((match result with
        | some value =>
            evalList? ctx env terms hM >>= fun
            | some values => pure (some (value :: values))
            | none => pure none
        | none => pure none) :
          Std.Do.PredTrans .pure (Option (List (Val ctx.primCtx))))).apply Q, Q.2)
  let listPost (value : Val ctx.primCtx) :
      Std.Do.PostCond (Option (List (Val ctx.primCtx))) .pure :=
    (fun result =>
      (Std.Do.wp
        ((match result with
        | some values => pure (some (value :: values))
        | none => pure none) :
          Std.Do.PredTrans .pure (Option (List (Val ctx.primCtx))))).apply Q, Q.2)
  rw [Std.Do.Triple.iff]
  intro hpre
  have htermPre : ((Std.Do.wp (eval? ctx env term hM)).apply termPost).down := by
    simpa [termPost, Std.Do.PredTrans.apply_bind,
      Std.Do.PredTrans.apply_pure] using hpre
  dsimp [evalList?, total?]
  constructor
  · intro values hvalues
    cases hvalues with
    | cons hterm htail =>
        have htailPreRaw := eval?_wp_some (Q := termPost) htermPre hterm
        have htailPre := by
          simpa [termPost, listPost, Std.Do.PredTrans.apply_bind,
            Std.Do.PredTrans.apply_pure] using htailPreRaw
        have hQ := evalList?_wp_some htailPre htail
        simpa [listPost, Std.Do.PredTrans.apply_pure] using hQ
  · intro hnone
    by_cases hexists : ∃ value, Exact.EvaluatesTo ctx env term value hM
    · obtain ⟨value, hvalue⟩ := hexists
      have htailPreRaw := eval?_wp_some (Q := termPost) htermPre hvalue
      have htailPre : ((Std.Do.wp (evalList? ctx env terms hM)).apply
          (listPost value)).down := by
        simpa [termPost, listPost, Std.Do.PredTrans.apply_bind,
          Std.Do.PredTrans.apply_pure] using htailPreRaw
      have htailNone : ∀ values, ¬ Exact.EvaluatesList ctx env terms values hM := by
        intro values htail
        exact hnone (value :: values) (Exact.EvaluatesList.cons hvalue htail)
      have hQ := evalList?_wp_none htailPre htailNone
      simpa [listPost, Std.Do.PredTrans.apply_pure] using hQ
    · have hQ := eval?_wp_none (Q := termPost) htermPre
        (fun value hvalue => hexists ⟨value, hvalue⟩)
      simpa [termPost, Std.Do.PredTrans.apply_pure] using hQ

@[spec 1200] theorem evalListStep?_var_local_spec {ctx : Ctx} {hM : ctx.M = Id}
    {env : Env ctx.primCtx} {name : String} {value : Val ctx.primCtx}
    (hlocal : Scope.get? env name = some value)
    (terms : List (Term ctx.primCtx))
    (Q : Std.Do.PostCond (Option (List (Val ctx.primCtx))) .pure) :
    Std.Do.Triple (evalListStep? ctx env (.var name :: terms) hM)
      ((Std.Do.wp (evalList? ctx env terms hM)).apply
        (somePost fun values => Q.1 (some (value :: values)))) Q := by
  rw [Std.Do.Triple.iff]
  intro hpre
  simp only [evalListStep?, hlocal]
  change ((Std.Do.wp (evalList? ctx env terms hM)).apply
    (fun result =>
      (Std.Do.wp
        ((match result with
        | some values => pure (some (value :: values))
        | none => pure none) :
          Std.Do.PredTrans .pure (Option (List (Val ctx.primCtx))))).apply Q,
      Q.2)).down
  dsimp [evalList?, total?]
  constructor
  · intro values hvalues
    have hQ := evalList?_wp_some (Q := somePost fun values =>
      Q.1 (some (value :: values))) hpre hvalues
    simpa [Std.Do.PredTrans.apply_pure, somePost] using hQ
  · intro hnone
    exact (evalList?_wp_none (Q := somePost fun values =>
      Q.1 (some (value :: values))) hpre hnone).elim

@[spec 1200] theorem evalListStep?_prim_spec {ctx : Ctx} {hM : ctx.M = Id}
    {env : Env ctx.primCtx} (ty : Ty) (value : Ty.type ctx.primCtx ty)
    (terms : List (Term ctx.primCtx))
    (Q : Std.Do.PostCond (Option (List (Val ctx.primCtx))) .pure) :
    Std.Do.Triple (evalListStep? ctx env (.prim ty value :: terms) hM)
      ((Std.Do.wp (evalList? ctx env terms hM)).apply
        (somePost fun values => Q.1 (some (.mk ty value :: values)))) Q := by
  rw [Std.Do.Triple.iff]
  intro hpre
  simp only [evalListStep?]
  change ((Std.Do.wp (evalList? ctx env terms hM)).apply
    (fun result =>
      (Std.Do.wp
        ((match result with
        | some values => pure (some (.mk ty value :: values))
        | none => pure none) :
          Std.Do.PredTrans .pure (Option (List (Val ctx.primCtx))))).apply Q,
      Q.2)).down
  dsimp [evalList?, total?]
  constructor
  · intro values hvalues
    have hQ := evalList?_wp_some (Q := somePost fun values =>
      Q.1 (some (.mk ty value :: values))) hpre hvalues
    simpa [Std.Do.PredTrans.apply_pure, somePost] using hQ
  · intro hnone
    exact (evalList?_wp_none (Q := somePost fun values =>
      Q.1 (some (.mk ty value :: values))) hpre hnone).elim

@[spec 1100] theorem evalList?_spec {ctx : Ctx} {hM : ctx.M = Id}
    (env : Env ctx.primCtx) (terms : List (Term ctx.primCtx))
    (Q : Std.Do.PostCond (Option (List (Val ctx.primCtx))) .pure) :
    Std.Do.Triple (evalList? ctx env terms hM)
      ((Std.Do.wp (evalListStep? ctx env terms hM)).apply Q) Q := by
  cases terms with
  | nil =>
      simpa [evalListStep?] using
        (evalList?_triple_of_evaluatesList (ctx := ctx) (env := env)
          (terms := []) (hM := hM) Exact.EvaluatesList.nil Q)
  | cons term terms =>
      rw [Std.Do.Triple.iff]
      intro hpre
      cases term with
      | var name =>
          cases hlocal : Scope.get? env name with
          | some value =>
              exact Std.Do.Triple.iff.mp
                (evalList?_cons_value_step
                  (ctx := ctx) (hM := hM) (env := env)
                  (term := Term.var name) (terms := terms) (value := value)
                  (Exact.EvaluatesTo.var_local hlocal) Q)
                (by simpa [evalListStep?, hlocal] using hpre)
          | none =>
              exact Std.Do.Triple.iff.mp
                (evalList?_cons_step (ctx := ctx) (hM := hM) env (.var name) terms Q)
                (by simpa [evalListStep?, hlocal] using hpre)
      | prim ty value =>
          exact Std.Do.Triple.iff.mp
            (evalList?_cons_value_step
              (ctx := ctx) (hM := hM) (env := env)
              (term := Term.prim ty value) (terms := terms) (value := .mk ty value)
              (Exact.EvaluatesTo.prim ty value) Q)
            (by simpa [evalListStep?] using hpre)
      | app fn args =>
          exact Std.Do.Triple.iff.mp
            (evalList?_cons_step (ctx := ctx) (hM := hM) env (.app fn args) terms Q)
            (by simpa [evalListStep?] using hpre)
      | «op» name args =>
          exact Std.Do.Triple.iff.mp
            (evalList?_cons_step (ctx := ctx) (hM := hM) env (.op name args) terms Q)
            (by simpa [evalListStep?] using hpre)
      | «call» name args =>
          exact Std.Do.Triple.iff.mp
            (evalList?_cons_step (ctx := ctx) (hM := hM) env (.call name args) terms Q)
            (by simpa [evalListStep?] using hpre)
      | «exit» name value =>
          exact Std.Do.Triple.iff.mp
            (evalList?_cons_step (ctx := ctx) (hM := hM) env (.exit name value) terms Q)
            (by simpa [evalListStep?] using hpre)

theorem evalListPre_of_evaluatesList {ctx : Ctx} {hM : ctx.M = Id}
    {env : Env ctx.primCtx} {terms : List (Term ctx.primCtx)}
    {values : List (Val ctx.primCtx)}
    (h : Exact.EvaluatesList ctx env terms values hM)
    {success : List (Val ctx.primCtx) → Std.Do.Assertion .pure}
    (hpost : (success values).down) :
    (evalListPre ctx env terms hM (somePost success)).down := by
  induction h with
  | nil =>
      simpa [evalListPre] using hpost
  | cons hvalue hvalues =>
      simp only [evalListPre]
      exact Std.Do.Triple.iff.mp
        (eval?_triple_of_evaluatesTo hvalue
          (somePost fun value =>
            (Std.Do.wp (evalList? ctx env _ hM)).apply
              (somePost fun values => success (value :: values))))
        (Std.Do.Triple.iff.mp
          (evalList?_triple_of_evaluatesList hvalues
            (somePost fun values => success (_ :: values)))
          hpost)

@[spec] theorem eval?_app_spec {ctx : Ctx} {hM : ctx.M = Id}
    {env : Env ctx.primCtx} {fn : Term ctx.primCtx} {args : List (Term ctx.primCtx)}
    (Q : Std.Do.PostCond (Option (Val ctx.primCtx)) .pure) :
    Std.Do.Triple (eval? ctx env (.app fn args) hM)
      ((Std.Do.wp (eval? ctx env fn hM)).apply
        (somePost fun fnValue =>
          (Std.Do.wp (evalList? ctx env args hM)).apply
            (somePost fun argValues =>
              (Std.Do.wp (apply? ctx fnValue argValues hM)).apply
                (somePost fun value => Q.1 (some value))))) Q := by
  change _ → _
  intro hpre
  obtain ⟨fnValue, hfn, hargsWp⟩ := eval?_some_of_wp hpre
  obtain ⟨argValues, hargs, happlyWp⟩ := evalList?_some_of_wp hargsWp
  obtain ⟨value, happly, hQ⟩ := apply?_some_of_wp happlyWp
  exact (eval?_triple_of_evaluatesTo (EvaluatesTo.app hfn hargs happly) Q) hQ

@[spec] theorem eval?_call_spec {ctx : Ctx} {hM : ctx.M = Id}
    {env : Env ctx.primCtx} {name : String} {args : List (Term ctx.primCtx)}
    {block : Block ctx.primCtx}
    (hblock : ctx.blockCtx.get? name = some block)
    (Q : Std.Do.PostCond (Option (Val ctx.primCtx)) .pure) :
    Std.Do.Triple (eval? ctx env (.call name args) hM)
      ((Std.Do.wp (evalCallStep? ctx env name args hM)).apply
        (somePost fun value => Q.1 (some value))) Q := by
  change _ → _
  intro hpre
  let resultPost : Std.Do.PostCond (Option (Val ctx.primCtx)) .pure :=
    somePost fun value => Q.1 (some value)
  let argsPost : Std.Do.PostCond (Option (List (Val ctx.primCtx))) .pure :=
    (fun result =>
      (Std.Do.wp
        (match result with
        | some argValues => callValues? ctx name argValues hM
        | none => pure none)).apply resultPost, resultPost.2)
  have hargsPre : ((Std.Do.wp (evalList? ctx env args hM)).apply argsPost).down := by
    simpa [evalCallStep?, Std.Do.PredTrans.apply_bind,
      Std.Do.PredTrans.apply_pure, resultPost, argsPost] using hpre
  by_cases hexists : ∃ argValues, Exact.EvaluatesList ctx env args argValues hM
  · obtain ⟨argValues, hargs⟩ := hexists
    have hcallWpRaw := evalList?_wp_some (Q := argsPost) hargsPre hargs
    have hcallWp : ((Std.Do.wp (callValues? ctx name argValues hM)).apply resultPost).down := by
      simpa [argsPost] using hcallWpRaw
    obtain ⟨value, hcall, hQ⟩ := callValues?_some_of_wp hcallWp
    exact (eval?_triple_of_evaluatesTo (EvaluatesTo.call hcall hblock hargs) Q) hQ
  · have hnone := evalList?_wp_none (Q := argsPost) hargsPre
      (fun argValues hargs => hexists ⟨argValues, hargs⟩)
    simp [argsPost, resultPost] at hnone

@[spec 1200] theorem eval?_call_somePost_spec {ctx : Ctx} {hM : ctx.M = Id}
    {env : Env ctx.primCtx} {name : String} {args : List (Term ctx.primCtx)}
    {block : Block ctx.primCtx}
    (hblock : ctx.blockCtx.get? name = some block)
    (success : Val ctx.primCtx → Std.Do.Assertion .pure) :
    Std.Do.Triple (eval? ctx env (.call name args) hM)
      ((Std.Do.wp (evalCallStep? ctx env name args hM)).apply (somePost success))
      (somePost success) := by
  simpa [somePost] using
    (eval?_call_spec (ctx := ctx) (hM := hM) (env := env)
      (name := name) (args := args) (block := block) hblock (somePost success))

@[spec 900] theorem eval?_call_block_somePost_spec {ctx : Ctx} {hM : ctx.M = Id}
    {env : Env ctx.primCtx} {name : String} {args : List (Term ctx.primCtx)}
    {block : Block ctx.primCtx}
    (hblock : ctx.blockCtx.get? name = some block)
    (success : Val ctx.primCtx → Std.Do.Assertion .pure) :
    Std.Do.Triple (eval? ctx env (.call name args) hM)
      ((Std.Do.wp (evalList? ctx env args hM)).apply
        (somePost fun argValues =>
          (Std.Do.wp (callValues? ctx name argValues hM)).apply (somePost success)))
      (somePost success) := by
  rw [Std.Do.Triple.iff]
  intro hpre
  exact Std.Do.Triple.iff.mp
    (eval?_call_somePost_spec (ctx := ctx) (hM := hM) (env := env)
      (name := name) (args := args) (block := block) hblock success)
    (by
      simp only [evalCallStep?]
      change ((Std.Do.wp (evalList? ctx env args hM)).apply
        (fun result =>
          (Std.Do.wp
            ((match result with
            | some argValues => callValues? ctx name argValues hM
            | none => pure none) :
              Std.Do.PredTrans .pure (Option (Val ctx.primCtx)))).apply (somePost success),
          (somePost success).2)).down
      dsimp [evalList?, total?]
      constructor
      · intro argValues hargs
        have hcall := evalList?_wp_some (Q := somePost fun argValues =>
          (Std.Do.wp (callValues? ctx name argValues hM)).apply (somePost success)) hpre hargs
        simpa [Std.Do.PredTrans.apply_pure, somePost] using hcall
      · intro hnone
        exact (evalList?_wp_none (Q := somePost fun argValues =>
          (Std.Do.wp (callValues? ctx name argValues hM)).apply (somePost success))
          hpre hnone).elim)

@[spec] theorem apply?_blockRef_spec {ctx : Ctx} {hM : ctx.M = Id}
    {name : String} {argTys : List Ty} {outTy : Ty} {args : List (Val ctx.primCtx)}
    (Q : Std.Do.PostCond (Option (Val ctx.primCtx)) .pure) :
    Std.Do.Triple (apply? ctx (.blockRef name argTys outTy) args hM)
      ((Std.Do.wp (callValues? ctx name args hM)).apply
        (somePost fun value => Q.1 (some value))) Q := by
  change _ → _
  intro hpre
  obtain ⟨value, hcall, hQ⟩ := callValues?_some_of_wp hpre
  exact (apply?_triple_of_evaluatesApply (EvaluatesApply.blockRef hcall) Q) hQ

@[spec 1100] theorem callValues?_spec {ctx : Ctx} {hM : ctx.M = Id}
    (name : String) (args : List (Val ctx.primCtx))
    (Q : Std.Do.PostCond (Option (Val ctx.primCtx)) .pure) :
    Std.Do.Triple (callValues? ctx name args hM)
      ((Std.Do.wp (callValuesStep? ctx name args hM)).apply
        (somePost fun value => Q.1 (some value))) Q := by
  rw [Std.Do.Triple.iff]
  intro hpre
  unfold callValuesStep? at hpre
  cases hblock : ctx.blockCtx.get? name with
  | none =>
      simp [hblock] at hpre
  | some block =>
      by_cases hargs : args.length = block.params.length
      · have hbodyPre : ((Std.Do.wp
            (evalInstrs? ctx block.instrs block.result (block.entryEnv args) hM)).apply
            (somePost fun value => Q.1 (some value))).down := by
          simpa [hblock, hargs] using hpre
        obtain ⟨value, hbody, hQ⟩ := evalInstrs?_some_of_wp hbodyPre
        exact (callValues?_triple_of_evaluatesCallValues
          (EvaluatesCallValues.of_evaluatesInstrs hblock hargs hbody) Q) hQ
      · simp [hblock, hargs] at hpre

@[spec 1200] theorem callValues?_somePost_spec {ctx : Ctx} {hM : ctx.M = Id}
    (name : String) (args : List (Val ctx.primCtx))
    (success : Val ctx.primCtx → Std.Do.Assertion .pure) :
    Std.Do.Triple (callValues? ctx name args hM)
      ((Std.Do.wp (callValuesStep? ctx name args hM)).apply (somePost success))
      (somePost success) := by
  simpa [somePost] using
    (callValues?_spec (ctx := ctx) (hM := hM) name args (somePost success))

@[spec] theorem callValues?_block_spec {ctx : Ctx} {hM : ctx.M = Id}
    {name : String} {args : List (Val ctx.primCtx)} {block : Block ctx.primCtx}
    (hblock : ctx.blockCtx.get? name = some block)
    (hargs : args.length = block.params.length)
    (Q : Std.Do.PostCond (Option (Val ctx.primCtx)) .pure) :
    Std.Do.Triple (callValues? ctx name args hM)
      ((Std.Do.wp (evalInstrs? ctx block.instrs block.result (block.entryEnv args) hM)).apply
        (somePost fun value => Q.1 (some value))) Q := by
  change _ → _
  intro hpre
  obtain ⟨value, hbody, hQ⟩ := evalInstrs?_some_of_wp hpre
  exact (callValues?_triple_of_evaluatesCallValues
    (EvaluatesCallValues.of_evaluatesInstrs hblock hargs hbody) Q) hQ

@[spec 900] theorem callValues?_block_somePost_spec {ctx : Ctx} {hM : ctx.M = Id}
    {name : String} {args : List (Val ctx.primCtx)} {block : Block ctx.primCtx}
    (hblock : ctx.blockCtx.get? name = some block)
    (hargs : args.length = block.params.length)
    (success : Val ctx.primCtx → Std.Do.Assertion .pure) :
    Std.Do.Triple (callValues? ctx name args hM)
      ((Std.Do.wp (evalInstrs? ctx block.instrs block.result (block.entryEnv args) hM)).apply
        (somePost success))
      (somePost success) := by
  simpa [somePost] using
    (callValues?_block_spec (ctx := ctx) (hM := hM) (name := name)
      (args := args) (block := block) hblock hargs (somePost success))

@[spec] theorem evalInstrs?_nil_spec {ctx : Ctx} {hM : ctx.M = Id}
    {result : Term ctx.primCtx} {env : Env ctx.primCtx}
    (Q : Std.Do.PostCond (Option (Val ctx.primCtx)) .pure) :
    Std.Do.Triple (evalInstrs? ctx [] result env hM)
      ((Std.Do.wp (eval? ctx env result hM)).apply
        (somePost fun value => Q.1 (some value))) Q := by
  change _ → _
  intro hpre
  obtain ⟨value, hresult, hQ⟩ := eval?_some_of_wp hpre
  exact (evalInstrs?_triple_of_evaluatesInstrs (EvaluatesInstrs.nil hresult) Q) hQ

@[spec 1100] theorem evalInstrs?_nil_somePost_spec {ctx : Ctx} {hM : ctx.M = Id}
    {result : Term ctx.primCtx} {env : Env ctx.primCtx}
    (success : Val ctx.primCtx → Std.Do.Assertion .pure) :
    Std.Do.Triple (evalInstrs? ctx [] result env hM)
      ((Std.Do.wp (eval? ctx env result hM)).apply (somePost success))
      (somePost success) := by
  simpa [somePost] using
    (evalInstrs?_nil_spec (ctx := ctx) (hM := hM)
      (result := result) (env := env) (somePost success))

@[spec] theorem evalInstrs?_cons_spec {ctx : Ctx} {hM : ctx.M = Id}
    {instr : Instr ctx.primCtx} {instrs : List (Instr ctx.primCtx)}
    {result : Term ctx.primCtx} {env : Env ctx.primCtx}
    (Q : Std.Do.PostCond (Option (Val ctx.primCtx)) .pure) :
    Std.Do.Triple (evalInstrs? ctx (instr :: instrs) result env hM)
      ((Std.Do.wp (eval? ctx env instr.value hM)).apply
        (somePost fun instrValue =>
          (Std.Do.wp (evalInstrs? ctx instrs result
              (env ++ [(instr.name, instrValue)]) hM)).apply
            (somePost fun value => Q.1 (some value)))) Q := by
  change _ → _
  intro hpre
  obtain ⟨instrValue, hinstr, hrestWp⟩ := eval?_some_of_wp hpre
  obtain ⟨value, hrest, hQ⟩ := evalInstrs?_some_of_wp hrestWp
  exact (evalInstrs?_triple_of_evaluatesInstrs (EvaluatesInstrs.cons hinstr hrest) Q) hQ

@[spec 1100] theorem evalInstrs?_spec {ctx : Ctx} {hM : ctx.M = Id}
    (instrs : List (Instr ctx.primCtx)) (result : Term ctx.primCtx)
    (env : Env ctx.primCtx)
    (Q : Std.Do.PostCond (Option (Val ctx.primCtx)) .pure) :
    Std.Do.Triple (evalInstrs? ctx instrs result env hM)
      ((Std.Do.wp (evalInstrsStep? ctx instrs result env hM)).apply Q) Q := by
  cases instrs with
  | nil =>
      rw [Std.Do.Triple.iff]
      intro hpre
      dsimp [evalInstrs?, total?]
      constructor
      · intro value hvalue
        cases hvalue with
        | nil hresult =>
            exact eval?_wp_some (by simpa [evalInstrsStep?] using hpre) hresult
      · intro hnone
        exact eval?_wp_none (by simpa [evalInstrsStep?] using hpre)
          (fun value hresult => hnone value (Exact.EvaluatesInstrs.nil hresult))
  | cons instr instrs =>
      let instrPost : Std.Do.PostCond (Option (Val ctx.primCtx)) .pure :=
        (fun instrResult =>
          (Std.Do.wp
            ((match instrResult with
            | some instrValue =>
                evalInstrs? ctx instrs result (env ++ [(instr.name, instrValue)]) hM
            | none => pure none) :
              Std.Do.PredTrans .pure (Option (Val ctx.primCtx)))).apply Q, Q.2)
      rw [Std.Do.Triple.iff]
      intro hpre
      have hinstrPre : ((Std.Do.wp (eval? ctx env instr.value hM)).apply instrPost).down := by
        simpa [evalInstrsStep?, instrPost, Std.Do.PredTrans.apply_bind,
          Std.Do.PredTrans.apply_pure] using hpre
      dsimp [evalInstrs?, total?]
      constructor
      · intro value hvalue
        cases hvalue with
        | cons hinstr hrest =>
            have hrestPreRaw := eval?_wp_some (Q := instrPost) hinstrPre hinstr
            have hrestPre := by simpa [instrPost] using hrestPreRaw
            exact evalInstrs?_wp_some hrestPre hrest
      · intro hnone
        by_cases hexists : ∃ instrValue, Exact.EvaluatesTo ctx env instr.value instrValue hM
        · obtain ⟨instrValue, hinstr⟩ := hexists
          have hrestPreRaw := eval?_wp_some (Q := instrPost) hinstrPre hinstr
          have hrestPre : ((Std.Do.wp (evalInstrs? ctx instrs result
              (env ++ [(instr.name, instrValue)]) hM)).apply Q).down := by
            simpa [instrPost] using hrestPreRaw
          have hrestNone : ∀ value,
              ¬ Exact.EvaluatesInstrs ctx instrs result
                (env ++ [(instr.name, instrValue)]) value hM := by
            intro value hvalue
            exact hnone value (Exact.EvaluatesInstrs.cons hinstr hvalue)
          exact evalInstrs?_wp_none hrestPre hrestNone
        · have hQ := eval?_wp_none (Q := instrPost) hinstrPre
            (fun instrValue hinstr => hexists ⟨instrValue, hinstr⟩)
          simpa [instrPost, Std.Do.PredTrans.apply_pure] using hQ

end Exact

namespace State

open scoped Std.Do

def somePost {σ α : Type} (success : α → Std.Do.Assertion (.arg σ .pure)) :
    Std.Do.PostCond (Option α) (.arg σ .pure) :=
  Std.Do.PostCond.noThrow fun
    | some value => success value
    | none => fun _ => Std.Do.SPred.pure False

def someEqPost {σ α : Type} (expected : α) (expectedFinal : σ) :
    Std.Do.PostCond (Option α) (.arg σ .pure) :=
  somePost fun actual actualFinal =>
    Std.Do.SPred.pure (actual = expected ∧ actualFinal = expectedFinal)

@[simp] theorem somePost_some {σ α : Type}
    (success : α → Std.Do.Assertion (.arg σ .pure)) (value : α) :
    (somePost success).1 (some value) = success value := rfl

@[simp] theorem somePost_none {σ α : Type}
    (success : α → Std.Do.Assertion (.arg σ .pure)) :
    (somePost success).1 none = fun _ => Std.Do.SPred.pure False := rfl

@[simp] theorem someEqPost_some {σ α : Type} (expected actual : α)
    (expectedFinal : σ) :
    (someEqPost expected expectedFinal).1 (some actual) =
      fun actualFinal => Std.Do.SPred.pure
        (actual = expected ∧ actualFinal = expectedFinal) := rfl

@[simp] theorem someEqPost_none {σ α : Type} (expected : α) (expectedFinal : σ) :
    (someEqPost expected expectedFinal).1 none = fun _ => Std.Do.SPred.pure False := rfl

def total? {σ α : Type} (R : σ → α → σ → Prop) :
    Std.Do.PredTrans (.arg σ .pure) (Option α) where
  trans Q := fun initial => ULift.up
    ((∀ value final, R initial value final → (Q.1 (some value) final).down) ∧
      ((∀ value final, ¬ R initial value final) → (Q.1 none initial).down))
  conjunctiveRaw := by
    intro Q₁ Q₂ initial
    dsimp [Std.Do.PredTrans.apply, Std.Do.SPred.bientails, Std.Do.SPred.and]
    constructor
    · intro h
      exact ⟨⟨fun value final hvalue => (h.1 value final hvalue).1,
          fun hnone => (h.2 hnone).1⟩,
        ⟨fun value final hvalue => (h.1 value final hvalue).2,
          fun hnone => (h.2 hnone).2⟩⟩
    · intro h
      exact ⟨fun value final hvalue =>
          ⟨h.1.1 value final hvalue, h.2.1 value final hvalue⟩,
        fun hnone => ⟨h.1.2 hnone, h.2.2 hnone⟩⟩

theorem total?_some_of_wp {σ α : Type} {R : σ → α → σ → Prop}
    {success : α → Std.Do.Assertion (.arg σ .pure)} {initial : σ}
    (h : ((Std.Do.wp (total? R)).apply (somePost success) initial).down) :
    ∃ value final, R initial value final ∧ (success value final).down := by
  change ((∀ value final, R initial value final →
      ((somePost success).1 (some value) final).down) ∧
    ((∀ value final, ¬ R initial value final) →
      ((somePost success).1 none initial).down)) at h
  by_cases hexists : ∃ value final, R initial value final
  · obtain ⟨value, final, hvalue⟩ := hexists
    exact ⟨value, final, hvalue, h.1 value final hvalue⟩
  · exact (h.2 (fun value final hvalue => hexists ⟨value, final, hvalue⟩)).elim

theorem total?_triple_of_unique {σ α : Type} {R : σ → α → σ → Prop}
    {initial final : σ} {value : α}
    (h : R initial value final)
    (hunique : ∀ {actual actualFinal}, R initial actual actualFinal →
      actual = value ∧ actualFinal = final)
    (Q : Std.Do.PostCond (Option α) (.arg σ .pure)) :
    Std.Do.Triple (total? R)
      (fun state => Std.Do.SPred.pure
        (state = initial ∧ (Q.1 (some value) final).down)) Q := by
  rw [Std.Do.Triple.iff, Std.Do.SPred.entails_1]
  intro state hpre
  change state = initial ∧ (Q.1 (some value) final).down at hpre
  rcases hpre with ⟨hstate, hQ⟩
  subst state
  change ((∀ actual actualFinal, R initial actual actualFinal →
      (Q.1 (some actual) actualFinal).down) ∧
    ((∀ actual actualFinal, ¬ R initial actual actualFinal) →
      (Q.1 none initial).down))
  constructor
  · intro actual actualFinal hactual
    obtain ⟨hvalue, hfinal⟩ := hunique hactual
    subst actual
    subst actualFinal
    exact hQ
  · intro hnone
    exact (hnone value final h).elim

inductive EvaluatesList (primCtx : PrimitiveCtx) (opCtx : OpCtx primCtx (StateM σ))
    (blockCtx : BlockCtx primCtx) (env : Env primCtx) :
    List (Term primCtx) → σ → List (Val primCtx) → σ → Prop where
| nil {state} : EvaluatesList primCtx opCtx blockCtx env [] state [] state
| cons {term terms initial middle final value values} :
    State.EvaluatesToK primCtx opCtx blockCtx env term initial value middle →
    EvaluatesList primCtx opCtx blockCtx env terms middle values final →
    EvaluatesList primCtx opCtx blockCtx env (term :: terms) initial (value :: values) final

attribute [zspec] EvaluatesList.nil EvaluatesList.cons

inductive EvaluatesInstrs (primCtx : PrimitiveCtx) (opCtx : OpCtx primCtx (StateM σ))
    (blockCtx : BlockCtx primCtx) :
    List (Instr primCtx) → Term primCtx → Env primCtx → σ → Val primCtx → σ → Prop where
| nil {result env initial final value} :
    State.EvaluatesToK primCtx opCtx blockCtx env result initial value final →
    EvaluatesInstrs primCtx opCtx blockCtx [] result env initial value final
| cons {instr instrs result env initial middle final instrValue value} :
    State.EvaluatesToK primCtx opCtx blockCtx env instr.value initial instrValue middle →
    EvaluatesInstrs primCtx opCtx blockCtx instrs result
      (env ++ [(instr.name, instrValue)]) middle value final →
    EvaluatesInstrs primCtx opCtx blockCtx (instr :: instrs) result env initial value final

attribute [zspec] EvaluatesInstrs.nil EvaluatesInstrs.cons

inductive EvaluatesBody (primCtx : PrimitiveCtx) (opCtx : OpCtx primCtx (StateM σ))
    (blockCtx : BlockCtx primCtx) (env : Env primCtx) :
    Op.Body primCtx → List (Op.Arg primCtx) → σ → Val primCtx → σ → Prop where
| done {result state rest} :
    EvaluatesBody primCtx opCtx blockCtx env (.done result) rest state result state
| nextTerm {term rest resume initial middle final termValue result} :
    State.EvaluatesToK primCtx opCtx blockCtx env term initial termValue middle →
    EvaluatesBody primCtx opCtx blockCtx env (resume (some termValue)) rest
      middle result final →
    EvaluatesBody primCtx opCtx blockCtx env (.next true resume) (.inl term :: rest)
      initial result final
| nextValue {value rest resume initial final result} :
    EvaluatesBody primCtx opCtx blockCtx env (resume (some value)) rest
      initial result final →
    EvaluatesBody primCtx opCtx blockCtx env (.next true resume) (.inr value :: rest)
      initial result final
| skip {arg rest resume initial final result} :
    EvaluatesBody primCtx opCtx blockCtx env (resume none) rest initial result final →
    EvaluatesBody primCtx opCtx blockCtx env (.next false resume) (arg :: rest)
      initial result final
| apply {fn args resume rest initial middle final applied result} :
    State.EvaluatesApply primCtx opCtx blockCtx fn args initial applied middle →
    EvaluatesBody primCtx opCtx blockCtx env (resume applied) rest middle result final →
    EvaluatesBody primCtx opCtx blockCtx env (.apply fn args resume) rest initial result final

attribute [zspec] EvaluatesBody.done EvaluatesBody.nextTerm EvaluatesBody.nextValue
  EvaluatesBody.skip EvaluatesBody.apply

def evalList? (primCtx : PrimitiveCtx) (opCtx : OpCtx primCtx (StateM σ))
    (blockCtx : BlockCtx primCtx) (env : Env primCtx) (terms : List (Term primCtx)) :
    Std.Do.PredTrans (.arg σ .pure) (Option (List (Val primCtx))) :=
  total? fun initial values final => EvaluatesList primCtx opCtx blockCtx env terms initial values final

def apply? (primCtx : PrimitiveCtx) (opCtx : OpCtx primCtx (StateM σ))
    (blockCtx : BlockCtx primCtx) (fn : Val primCtx) (args : List (Val primCtx)) :
    Std.Do.PredTrans (.arg σ .pure) (Option (Val primCtx)) :=
  total? fun initial value final => State.EvaluatesApply primCtx opCtx blockCtx fn args initial value final

def callValues? (primCtx : PrimitiveCtx) (opCtx : OpCtx primCtx (StateM σ))
    (blockCtx : BlockCtx primCtx) (name : String) (args : List (Val primCtx)) :
    Std.Do.PredTrans (.arg σ .pure) (Option (Val primCtx)) :=
  total? fun initial value final =>
    State.EvaluatesCallValues primCtx opCtx blockCtx name args initial value final

def evalInstrs? (primCtx : PrimitiveCtx) (opCtx : OpCtx primCtx (StateM σ))
    (blockCtx : BlockCtx primCtx) (instrs : List (Instr primCtx))
    (result : Term primCtx) (env : Env primCtx) :
    Std.Do.PredTrans (.arg σ .pure) (Option (Val primCtx)) :=
  total? fun initial value final =>
    EvaluatesInstrs primCtx opCtx blockCtx instrs result env initial value final

def evalListPre (primCtx : PrimitiveCtx) (opCtx : OpCtx primCtx (StateM σ))
    (blockCtx : BlockCtx primCtx) (env : Env primCtx) (terms : List (Term primCtx))
    (Q : Std.Do.PostCond (Option (List (Val primCtx))) (.arg σ .pure)) :
    Std.Do.Assertion (.arg σ .pure) :=
  match terms with
  | [] => Q.1 (some [])
  | term :: terms =>
      (Std.Do.wp (State.eval? primCtx opCtx blockCtx env term)).apply
        (somePost fun value =>
          (Std.Do.wp (evalList? primCtx opCtx blockCtx env terms)).apply
            (somePost fun values => Q.1 (some (value :: values))))

def evalInstrsPre (primCtx : PrimitiveCtx) (opCtx : OpCtx primCtx (StateM σ))
    (blockCtx : BlockCtx primCtx) (instrs : List (Instr primCtx))
    (result : Term primCtx) (env : Env primCtx)
    (Q : Std.Do.PostCond (Option (Val primCtx)) (.arg σ .pure)) :
    Std.Do.Assertion (.arg σ .pure) :=
  match instrs with
  | [] =>
      (Std.Do.wp (State.eval? primCtx opCtx blockCtx env result)).apply
        (somePost fun value => Q.1 (some value))
  | instr :: instrs =>
      (Std.Do.wp (State.eval? primCtx opCtx blockCtx env instr.value)).apply
        (somePost fun instrValue =>
          (Std.Do.wp (evalInstrs? primCtx opCtx blockCtx instrs result
              (env ++ [(instr.name, instrValue)]))).apply
            (somePost fun value => Q.1 (some value)))

theorem eval?_some_of_wp {primCtx : PrimitiveCtx}
    {opCtx : OpCtx primCtx (StateM σ)} {blockCtx : BlockCtx primCtx}
    {env : Env primCtx} {term : Term primCtx}
    {success : Val primCtx → Std.Do.Assertion (.arg σ .pure)} {initial : σ}
    (h : ((Std.Do.wp (State.eval? primCtx opCtx blockCtx env term)).apply
      (somePost success) initial).down) :
    ∃ value final, State.EvaluatesToK primCtx opCtx blockCtx env term initial value final ∧
      (success value final).down := by
  change ((∀ value final,
      State.EvaluatesToK primCtx opCtx blockCtx env term initial value final →
        ((somePost success).1 (some value) final).down) ∧
    ((∀ value final,
      ¬ State.EvaluatesToK primCtx opCtx blockCtx env term initial value final) →
        ((somePost success).1 none initial).down)) at h
  by_cases hexists : ∃ value final,
      State.EvaluatesToK primCtx opCtx blockCtx env term initial value final
  · obtain ⟨value, final, hvalue⟩ := hexists
    exact ⟨value, final, hvalue, h.1 value final hvalue⟩
  · exact (h.2 (fun value final hvalue => hexists ⟨value, final, hvalue⟩)).elim

theorem evalList?_some_of_wp {primCtx : PrimitiveCtx}
    {opCtx : OpCtx primCtx (StateM σ)} {blockCtx : BlockCtx primCtx}
    {env : Env primCtx} {terms : List (Term primCtx)}
    {success : List (Val primCtx) → Std.Do.Assertion (.arg σ .pure)} {initial : σ}
    (h : ((Std.Do.wp (evalList? primCtx opCtx blockCtx env terms)).apply
      (somePost success) initial).down) :
    ∃ values final, EvaluatesList primCtx opCtx blockCtx env terms initial values final ∧
      (success values final).down := by
  exact total?_some_of_wp (R := fun initial values final =>
    EvaluatesList primCtx opCtx blockCtx env terms initial values final) h

theorem apply?_some_of_wp {primCtx : PrimitiveCtx}
    {opCtx : OpCtx primCtx (StateM σ)} {blockCtx : BlockCtx primCtx}
    {fn : Val primCtx} {args : List (Val primCtx)}
    {success : Val primCtx → Std.Do.Assertion (.arg σ .pure)} {initial : σ}
    (h : ((Std.Do.wp (apply? primCtx opCtx blockCtx fn args)).apply
      (somePost success) initial).down) :
    ∃ value final, State.EvaluatesApply primCtx opCtx blockCtx fn args initial value final ∧
      (success value final).down := by
  exact total?_some_of_wp (R := fun initial value final =>
    State.EvaluatesApply primCtx opCtx blockCtx fn args initial value final) h

theorem callValues?_some_of_wp {primCtx : PrimitiveCtx}
    {opCtx : OpCtx primCtx (StateM σ)} {blockCtx : BlockCtx primCtx}
    {name : String} {args : List (Val primCtx)}
    {success : Val primCtx → Std.Do.Assertion (.arg σ .pure)} {initial : σ}
    (h : ((Std.Do.wp (callValues? primCtx opCtx blockCtx name args)).apply
      (somePost success) initial).down) :
    ∃ value final,
      State.EvaluatesCallValues primCtx opCtx blockCtx name args initial value final ∧
      (success value final).down := by
  exact total?_some_of_wp (R := fun initial value final =>
    State.EvaluatesCallValues primCtx opCtx blockCtx name args initial value final) h

theorem evalInstrs?_some_of_wp {primCtx : PrimitiveCtx}
    {opCtx : OpCtx primCtx (StateM σ)} {blockCtx : BlockCtx primCtx}
    {instrs : List (Instr primCtx)} {result : Term primCtx} {env : Env primCtx}
    {success : Val primCtx → Std.Do.Assertion (.arg σ .pure)} {initial : σ}
    (h : ((Std.Do.wp (evalInstrs? primCtx opCtx blockCtx instrs result env)).apply
      (somePost success) initial).down) :
    ∃ value final,
      EvaluatesInstrs primCtx opCtx blockCtx instrs result env initial value final ∧
      (success value final).down := by
  exact total?_some_of_wp (R := fun initial value final =>
    EvaluatesInstrs primCtx opCtx blockCtx instrs result env initial value final) h

namespace EvaluatesBody

theorem toEvaluatesFrom {primCtx : PrimitiveCtx} {opCtx : OpCtx primCtx (StateM σ)}
    {blockCtx : BlockCtx primCtx} {env : Env primCtx}
    {body : Op.Body primCtx} {rest : List (Op.Arg primCtx)}
    {initial final : σ} {result : Val primCtx}
    (h : EvaluatesBody primCtx opCtx blockCtx env body rest initial result final) :
    ∀ stack : List (Frame primCtx), ∃ state,
      Machine.driveOp body rest env stack = some state ∧
        State.EvaluatesFrom primCtx opCtx blockCtx state initial result final stack := by
  induction h with
  | @done result state rest =>
      intro stack
      exact ⟨⟨.ret result, env, stack⟩, by simp [Machine.driveOp],
        State.EvaluatesFrom.done⟩
  | @nextTerm term rest resume initial middle final termValue result hterm hrest ih =>
      intro stack
      obtain ⟨state, hdrive, hfrom⟩ := ih stack
      let frame := Frame.opBody resume rest env
      refine ⟨⟨.eval term, env, frame :: stack⟩, ?_, ?_⟩
      · simp [Machine.driveOp, frame]
      · apply State.EvaluatesFrom.bind (hterm (frame :: stack))
        intro scope
        apply State.EvaluatesFrom.step (next := state) (middle := middle)
        · simp [Machine.step, Machine.ofOption, Machine.resumeFrame, hdrive, frame]
          rfl
        exact hfrom
  | @nextValue value rest resume initial final result hrest ih =>
      intro stack
      obtain ⟨state, hdrive, hfrom⟩ := ih stack
      exact ⟨state, by simpa [Machine.driveOp] using hdrive, hfrom⟩
  | @skip arg rest resume initial final result hrest ih =>
      intro stack
      obtain ⟨state, hdrive, hfrom⟩ := ih stack
      exact ⟨state, by cases arg <;> simpa [Machine.driveOp] using hdrive, hfrom⟩
  | @apply fn args resume rest initial middle final applied result happly hrest ih =>
      intro stack
      obtain ⟨state, hdrive, hfrom⟩ := ih stack
      let frame := Frame.opBody (fun | some value => resume value | none => .fail) rest env
      refine ⟨⟨.apply fn args, env, frame :: stack⟩, ?_, ?_⟩
      · simp [Machine.driveOp, frame]
        funext input
        cases input <;> rfl
      · apply State.EvaluatesFrom.bind (happly env (frame :: stack))
        intro scope
        apply State.EvaluatesFrom.step (next := state) (middle := middle)
        · simp [Machine.step, Machine.ofOption, Machine.resumeFrame, hdrive, frame]
          rfl
        exact hfrom

end EvaluatesBody

namespace EvaluatesList

theorem length_eq {primCtx : PrimitiveCtx} {opCtx : OpCtx primCtx (StateM σ)}
    {blockCtx : BlockCtx primCtx} {env : Env primCtx}
    {terms : List (Term primCtx)} {initial final : σ} {values : List (Val primCtx)}
    (h : EvaluatesList primCtx opCtx blockCtx env terms initial values final) :
    terms.length = values.length := by
  induction h <;> simp_all

theorem unique {primCtx : PrimitiveCtx} {opCtx : OpCtx primCtx (StateM σ)}
    {blockCtx : BlockCtx primCtx} {env : Env primCtx}
    {terms : List (Term primCtx)} {initial final₁ final₂ : σ}
    {values₁ values₂ : List (Val primCtx)}
    (h₁ : EvaluatesList primCtx opCtx blockCtx env terms initial values₁ final₁)
    (h₂ : EvaluatesList primCtx opCtx blockCtx env terms initial values₂ final₂) :
    values₁ = values₂ ∧ final₁ = final₂ := by
  induction h₁ generalizing values₂ final₂ with
  | nil =>
      cases h₂
      exact ⟨rfl, rfl⟩
  | cons hterm₁ hrest₁ ih =>
      cases h₂ with
      | cons hterm₂ hrest₂ =>
          obtain ⟨hvalue, hmiddle⟩ := State.EvaluatesToK.unique hterm₁ hterm₂
          subst hvalue
          subst hmiddle
          obtain ⟨hvalues, hfinal⟩ := ih hrest₂
          subst hvalues
          subst hfinal
          exact ⟨rfl, rfl⟩

theorem collectApply {primCtx : PrimitiveCtx} {opCtx : OpCtx primCtx (StateM σ)}
    {blockCtx : BlockCtx primCtx} {env scope : Env primCtx}
    {fn current result : Val primCtx} {prior values : List (Val primCtx)}
    {terms : List (Term primCtx)} {stack : List (Frame primCtx)}
    {initial middle final : σ}
    (hterms : EvaluatesList primCtx opCtx blockCtx env terms initial values middle)
    (happly : State.EvaluatesApply primCtx opCtx blockCtx fn (prior ++ current :: values)
      middle result final) :
    State.EvaluatesFrom primCtx opCtx blockCtx
      ⟨.ret current, scope, .args .apply (fn :: prior) terms env :: stack⟩
      initial result final stack := by
  induction hterms generalizing prior current scope with
  | nil =>
      rename_i state
      apply State.EvaluatesFrom.step
        (next := ⟨.apply fn (prior ++ [current]), env, stack⟩) (middle := state)
      · simp [Machine.step, Machine.ofOption, Machine.resumeFrame]
        rfl
      simpa using happly env stack
  | cons hterm hrest ih =>
      rename_i term terms initial middle restFinal termValue termValues
      apply State.EvaluatesFrom.step
        (next := ⟨.eval term, env,
          .args .apply (fn :: prior ++ [current]) terms env :: stack⟩)
        (middle := initial)
      · simp [Machine.step, Machine.ofOption, Machine.resumeFrame]
        rfl
      apply State.EvaluatesFrom.bind
        (hterm (.args .apply (fn :: prior ++ [current]) terms env :: stack))
      intro nextScope
      apply ih (prior := prior ++ [current])
      simpa [List.append_assoc] using happly

end EvaluatesList

namespace EvaluatesInstrs

theorem unique {primCtx : PrimitiveCtx} {opCtx : OpCtx primCtx (StateM σ)}
    {blockCtx : BlockCtx primCtx} {instrs : List (Instr primCtx)}
    {result : Term primCtx} {env : Env primCtx} {initial final₁ final₂ : σ}
    {value₁ value₂ : Val primCtx}
    (h₁ : EvaluatesInstrs primCtx opCtx blockCtx instrs result env initial value₁ final₁)
    (h₂ : EvaluatesInstrs primCtx opCtx blockCtx instrs result env initial value₂ final₂) :
    value₁ = value₂ ∧ final₁ = final₂ := by
  induction h₁ generalizing value₂ final₂ with
  | nil hresult₁ =>
      cases h₂ with
      | nil hresult₂ => exact State.EvaluatesToK.unique hresult₁ hresult₂
  | cons hinstr₁ hrest₁ ih =>
      cases h₂ with
      | cons hinstr₂ hrest₂ =>
          obtain ⟨hinstr, hmiddle⟩ := State.EvaluatesToK.unique hinstr₁ hinstr₂
          subst hinstr
          subst hmiddle
          exact ih hrest₂

theorem toEvaluatesFrom {primCtx : PrimitiveCtx} {opCtx : OpCtx primCtx (StateM σ)}
    {blockCtx : BlockCtx primCtx} {instrs : List (Instr primCtx)}
    {result : Term primCtx} {env callerEnv : Env primCtx}
    {initial final : σ} {value : Val primCtx} {name : String}
    {base : List (Frame primCtx)}
    (h : EvaluatesInstrs primCtx opCtx blockCtx instrs result env initial value final) :
    State.EvaluatesFrom primCtx opCtx blockCtx
      (Machine.enterInstrs instrs result env (.call name callerEnv :: base))
      initial value final base := by
  induction h with
  | nil hresult =>
      apply State.EvaluatesFrom.bind (hresult (.call name callerEnv :: base))
      intro scope
      exact State.EvaluatesFrom.return_to_call
  | @cons instr instrs result env initial middle final instrValue value hinstr hrest ih =>
      apply State.EvaluatesFrom.bind
        (hinstr (.instrs instr.name instrs result env :: .call name callerEnv :: base))
      intro scope
      apply State.EvaluatesFrom.step (middle := middle)
      · rfl
      exact ih

end EvaluatesInstrs

namespace EvaluatesToK

theorem prim {primCtx : PrimitiveCtx} {opCtx : OpCtx primCtx (StateM σ)}
    {blockCtx : BlockCtx primCtx} {env : Env primCtx} (ty : Ty)
    (value : Ty.type primCtx ty) (state : σ) :
    State.EvaluatesToK primCtx opCtx blockCtx env (.prim ty value) state (.mk ty value) state := by
  intro base
  apply State.EvaluatesFrom.step
    (next := ⟨.ret (.mk ty value), env, base⟩) (middle := state)
  · rfl
  exact State.EvaluatesFrom.done

theorem var_local {primCtx : PrimitiveCtx} {opCtx : OpCtx primCtx (StateM σ)}
    {blockCtx : BlockCtx primCtx} {env : Env primCtx} {name : String}
    {value : Val primCtx} (hlocal : Scope.get? env name = some value) (state : σ) :
    State.EvaluatesToK primCtx opCtx blockCtx env (.var name) state value state := by
  intro base
  apply State.EvaluatesFrom.step
    (next := ⟨.ret value, env, base⟩) (middle := state)
  · simp [Machine.step, Machine.evalTerm, Machine.evalTermImmediate,
      Machine.ofOption, hlocal]
    rfl
  exact State.EvaluatesFrom.done

theorem var_block {primCtx : PrimitiveCtx} {opCtx : OpCtx primCtx (StateM σ)}
    {blockCtx : BlockCtx primCtx} {env : Env primCtx} {name : String}
    {block : Block primCtx} (hlocal : Scope.get? env name = none)
    (hblock : blockCtx.get? name = some block) (state : σ) :
    State.EvaluatesToK primCtx opCtx blockCtx env (.var name) state
      (.blockRef name (block.params.map Prod.snd) block.outTy) state := by
  intro base
  apply State.EvaluatesFrom.step
    (next := ⟨.ret (.blockRef name (block.params.map Prod.snd) block.outTy), env, base⟩)
    (middle := state)
  · simp [Machine.step, Machine.evalTerm, Machine.evalTermImmediate,
      Machine.ofOption, hlocal, hblock]
    rfl
  exact State.EvaluatesFrom.done

theorem op {primCtx : PrimitiveCtx} {opCtx : OpCtx primCtx (StateM σ)}
    {blockCtx : BlockCtx primCtx} {env : Env primCtx} {name : String}
    {args : List (Term primCtx)} {oper : Op primCtx (StateM σ)}
    {body : Op.Body primCtx} {initial final : σ} {value : Val primCtx}
    (hop : opCtx.get? name = some oper)
    (hbody : oper.body name args.length = some body)
    (hbodyEval : EvaluatesBody primCtx opCtx blockCtx env body (Op.Arg.ofTerms args)
      initial value final) :
    State.EvaluatesToK primCtx opCtx blockCtx env (.op name args) initial value final := by
  intro stack
  obtain ⟨state, hdrive, hfrom⟩ := hbodyEval.toEvaluatesFrom stack
  apply State.EvaluatesFrom.step (next := state) (middle := initial)
  · simp [Machine.step, Machine.evalTerm, Machine.driveSelectedOp, Machine.ofOption,
      hop, hbody, hdrive]
    rfl
  exact hfrom

theorem app {primCtx : PrimitiveCtx} {opCtx : OpCtx primCtx (StateM σ)}
    {blockCtx : BlockCtx primCtx} {fn : Term primCtx} {args : List (Term primCtx)}
    {fnValue : Val primCtx} {argValues : List (Val primCtx)}
    {value : Val primCtx} {env : Env primCtx} {initial fnFinal argsFinal final : σ}
    (hfn : State.EvaluatesToK primCtx opCtx blockCtx env fn initial fnValue fnFinal)
    (hargs : EvaluatesList primCtx opCtx blockCtx env args fnFinal argValues argsFinal)
    (happly : State.EvaluatesApply primCtx opCtx blockCtx fnValue argValues
      argsFinal value final) :
    State.EvaluatesToK primCtx opCtx blockCtx env (.app fn args) initial value final := by
  intro stack
  apply State.EvaluatesFrom.step
    (next := ⟨.eval fn, env, .args .apply [] args env :: stack⟩) (middle := initial)
  · rfl
  apply State.EvaluatesFrom.bind (hfn (.args .apply [] args env :: stack))
  intro scope
  cases hargs with
  | nil =>
      apply State.EvaluatesFrom.step
        (next := ⟨.apply fnValue [], env, stack⟩) (middle := fnFinal)
      · simp [Machine.step, Machine.ofOption, Machine.resumeFrame]
        rfl
      exact happly env stack
  | cons harg hrest =>
      rename_i arg rest argFinal argValue restValues
      apply State.EvaluatesFrom.step
        (next := ⟨.eval arg, env, .args .apply [fnValue] rest env :: stack⟩)
        (middle := fnFinal)
      · simp [Machine.step, Machine.ofOption, Machine.resumeFrame]
        rfl
      apply State.EvaluatesFrom.bind (harg (.args .apply [fnValue] rest env :: stack))
      intro argScope
      exact hrest.collectApply (prior := []) happly

theorem call {primCtx : PrimitiveCtx} {opCtx : OpCtx primCtx (StateM σ)}
    {blockCtx : BlockCtx primCtx} {name : String} {args : List (Term primCtx)}
    {argValues : List (Val primCtx)} {value : Val primCtx}
    {env : Env primCtx} {block : Block primCtx} {initial argsFinal final : σ}
    (hcall : State.EvaluatesCallValues primCtx opCtx blockCtx name argValues
      argsFinal value final)
    (hblock : blockCtx.get? name = some block)
    (hargs : EvaluatesList primCtx opCtx blockCtx env args initial argValues argsFinal) :
    State.EvaluatesToK primCtx opCtx blockCtx env (.call name args) initial value final := by
  let fnValue : Val primCtx := .blockRef name (block.params.map Prod.snd) block.outTy
  have happly : State.EvaluatesApply primCtx opCtx blockCtx fnValue argValues
      argsFinal value final := by
    exact EvalTriple.EvaluatesApply.blockRef hcall
  intro stack
  cases hargs with
  | nil =>
      apply State.EvaluatesFrom.step
        (next := ⟨.apply fnValue [], env, stack⟩) (middle := initial)
      · simp [Machine.step, Machine.evalTerm, Machine.evalTermImmediate,
          Machine.ofOption, hblock]
        rfl
      exact happly env stack
  | cons harg hrest =>
      rename_i arg rest argFinal argValue restValues
      apply State.EvaluatesFrom.step
        (next := ⟨.eval arg, env, .args .apply [fnValue] rest env :: stack⟩)
        (middle := initial)
      · simp [Machine.step, Machine.evalTerm, Machine.evalTermImmediate,
          Machine.ofOption, hblock]
        rfl
      apply State.EvaluatesFrom.bind (harg (.args .apply [fnValue] rest env :: stack))
      intro argScope
      exact hrest.collectApply (prior := []) happly

end EvaluatesToK

namespace EvaluatesCallValues

theorem of_evaluatesInstrs {primCtx : PrimitiveCtx} {opCtx : OpCtx primCtx (StateM σ)}
    {blockCtx : BlockCtx primCtx} {name : String} {vargs : List (Val primCtx)}
    {initial final : σ} {value : Val primCtx} {block : Block primCtx}
    (hblock : blockCtx.get? name = some block)
    (hargs : vargs.length = block.params.length)
    (hbody : EvaluatesInstrs primCtx opCtx blockCtx block.instrs block.result
      (block.entryEnv vargs) initial value final) :
    State.EvaluatesCallValues primCtx opCtx blockCtx name vargs initial value final := by
  intro callerEnv base
  refine ⟨block,
    Machine.enterInstrs block.instrs block.result (block.entryEnv vargs)
      (.call name callerEnv :: base), hblock, ?_, hbody.toEvaluatesFrom⟩
  simp [Machine.enterBlock, hargs]

end EvaluatesCallValues

theorem evalList?_triple_of_evaluatesList {primCtx : PrimitiveCtx}
    {opCtx : OpCtx primCtx (StateM σ)} {blockCtx : BlockCtx primCtx}
    {env : Env primCtx} {terms : List (Term primCtx)} {initial final : σ}
    {values : List (Val primCtx)}
    (h : EvaluatesList primCtx opCtx blockCtx env terms initial values final)
    (Q : Std.Do.PostCond (Option (List (Val primCtx))) (.arg σ .pure)) :
    Std.Do.Triple (evalList? primCtx opCtx blockCtx env terms)
      (fun state => Std.Do.SPred.pure
        (state = initial ∧ (Q.1 (some values) final).down)) Q :=
  total?_triple_of_unique h (fun hactual => EvaluatesList.unique hactual h) Q

theorem apply?_triple_of_evaluatesApply {primCtx : PrimitiveCtx}
    {opCtx : OpCtx primCtx (StateM σ)} {blockCtx : BlockCtx primCtx}
    {fn : Val primCtx} {args : List (Val primCtx)} {initial final : σ}
    {value : Val primCtx}
    (h : State.EvaluatesApply primCtx opCtx blockCtx fn args initial value final)
    (Q : Std.Do.PostCond (Option (Val primCtx)) (.arg σ .pure)) :
    Std.Do.Triple (apply? primCtx opCtx blockCtx fn args)
      (fun state => Std.Do.SPred.pure
        (state = initial ∧ (Q.1 (some value) final).down)) Q :=
  total?_triple_of_unique h (fun hactual => State.EvaluatesApply.unique hactual h) Q

theorem callValues?_triple_of_evaluatesCallValues {primCtx : PrimitiveCtx}
    {opCtx : OpCtx primCtx (StateM σ)} {blockCtx : BlockCtx primCtx}
    {name : String} {args : List (Val primCtx)} {initial final : σ}
    {value : Val primCtx}
    (h : State.EvaluatesCallValues primCtx opCtx blockCtx name args initial value final)
    (Q : Std.Do.PostCond (Option (Val primCtx)) (.arg σ .pure)) :
    Std.Do.Triple (callValues? primCtx opCtx blockCtx name args)
      (fun state => Std.Do.SPred.pure
        (state = initial ∧ (Q.1 (some value) final).down)) Q :=
  total?_triple_of_unique h (fun hactual => State.EvaluatesCallValues.unique hactual h) Q

theorem evalInstrs?_triple_of_evaluatesInstrs {primCtx : PrimitiveCtx}
    {opCtx : OpCtx primCtx (StateM σ)} {blockCtx : BlockCtx primCtx}
    {instrs : List (Instr primCtx)} {result : Term primCtx} {env : Env primCtx}
    {initial final : σ} {value : Val primCtx}
    (h : EvaluatesInstrs primCtx opCtx blockCtx instrs result env initial value final)
    (Q : Std.Do.PostCond (Option (Val primCtx)) (.arg σ .pure)) :
    Std.Do.Triple (evalInstrs? primCtx opCtx blockCtx instrs result env)
      (fun state => Std.Do.SPred.pure
        (state = initial ∧ (Q.1 (some value) final).down)) Q :=
  total?_triple_of_unique h (fun hactual => EvaluatesInstrs.unique hactual h) Q

theorem evaluatesTo_of_eval?_triple {primCtx : PrimitiveCtx}
    {opCtx : OpCtx primCtx (StateM σ)} {blockCtx : BlockCtx primCtx}
    {env : Env primCtx} {term : Term primCtx} {initial final : σ}
    {value : Val primCtx}
    (h : Std.Do.Triple (State.eval? primCtx opCtx blockCtx env term)
      (EvalTriple.Singleton.statePre initial) (someEqPost value final)) :
    State.EvaluatesToK primCtx opCtx blockCtx env term initial value final := by
  have hwp := (Std.Do.Triple.iff.mp h) initial rfl
  obtain ⟨actual, actualFinal, hactual, heq⟩ := eval?_some_of_wp hwp
  rcases heq with ⟨rfl, rfl⟩
  exact hactual

theorem evaluatesList_of_evalList?_triple {primCtx : PrimitiveCtx}
    {opCtx : OpCtx primCtx (StateM σ)} {blockCtx : BlockCtx primCtx}
    {env : Env primCtx} {terms : List (Term primCtx)} {initial final : σ}
    {values : List (Val primCtx)}
    (h : Std.Do.Triple (evalList? primCtx opCtx blockCtx env terms)
      (EvalTriple.Singleton.statePre initial) (someEqPost values final)) :
    EvaluatesList primCtx opCtx blockCtx env terms initial values final := by
  have hwp := (Std.Do.Triple.iff.mp h) initial rfl
  obtain ⟨actual, actualFinal, hactual, heq⟩ := evalList?_some_of_wp hwp
  rcases heq with ⟨rfl, rfl⟩
  exact hactual

theorem evaluatesApply_of_apply?_triple {primCtx : PrimitiveCtx}
    {opCtx : OpCtx primCtx (StateM σ)} {blockCtx : BlockCtx primCtx}
    {fn : Val primCtx} {args : List (Val primCtx)} {initial final : σ}
    {value : Val primCtx}
    (h : Std.Do.Triple (apply? primCtx opCtx blockCtx fn args)
      (EvalTriple.Singleton.statePre initial) (someEqPost value final)) :
    State.EvaluatesApply primCtx opCtx blockCtx fn args initial value final := by
  have hwp := (Std.Do.Triple.iff.mp h) initial rfl
  obtain ⟨actual, actualFinal, hactual, heq⟩ := apply?_some_of_wp hwp
  rcases heq with ⟨rfl, rfl⟩
  exact hactual

theorem evaluatesCallValues_of_callValues?_triple {primCtx : PrimitiveCtx}
    {opCtx : OpCtx primCtx (StateM σ)} {blockCtx : BlockCtx primCtx}
    {name : String} {args : List (Val primCtx)} {initial final : σ}
    {value : Val primCtx}
    (h : Std.Do.Triple (callValues? primCtx opCtx blockCtx name args)
      (EvalTriple.Singleton.statePre initial) (someEqPost value final)) :
    State.EvaluatesCallValues primCtx opCtx blockCtx name args initial value final := by
  have hwp := (Std.Do.Triple.iff.mp h) initial rfl
  obtain ⟨actual, actualFinal, hactual, heq⟩ := callValues?_some_of_wp hwp
  rcases heq with ⟨rfl, rfl⟩
  exact hactual

theorem evaluatesInstrs_of_evalInstrs?_triple {primCtx : PrimitiveCtx}
    {opCtx : OpCtx primCtx (StateM σ)} {blockCtx : BlockCtx primCtx}
    {instrs : List (Instr primCtx)} {result : Term primCtx} {env : Env primCtx}
    {initial final : σ} {value : Val primCtx}
    (h : Std.Do.Triple (evalInstrs? primCtx opCtx blockCtx instrs result env)
      (EvalTriple.Singleton.statePre initial) (someEqPost value final)) :
    EvaluatesInstrs primCtx opCtx blockCtx instrs result env initial value final := by
  have hwp := (Std.Do.Triple.iff.mp h) initial rfl
  obtain ⟨actual, actualFinal, hactual, heq⟩ := evalInstrs?_some_of_wp hwp
  rcases heq with ⟨rfl, rfl⟩
  exact hactual

theorem eval?_eq_triple_of_evaluatesTo {primCtx : PrimitiveCtx}
    {opCtx : OpCtx primCtx (StateM σ)} {blockCtx : BlockCtx primCtx}
    {env : Env primCtx} {term : Term primCtx} {initial final : σ}
    {value : Val primCtx}
    (h : State.EvaluatesToK primCtx opCtx blockCtx env term initial value final) :
    Std.Do.Triple (State.eval? primCtx opCtx blockCtx env term)
      (EvalTriple.Singleton.statePre initial) (someEqPost value final) := by
  rw [Std.Do.Triple.iff, Std.Do.SPred.entails_1]
  intro state hstate
  exact (Std.Do.Triple.iff.mp
    (State.eval?_triple_of_evaluatesTo h (someEqPost value final))) state
      ⟨hstate, by simp [someEqPost, somePost]⟩

theorem evalList?_eq_triple_of_evaluatesList {primCtx : PrimitiveCtx}
    {opCtx : OpCtx primCtx (StateM σ)} {blockCtx : BlockCtx primCtx}
    {env : Env primCtx} {terms : List (Term primCtx)} {initial final : σ}
    {values : List (Val primCtx)}
    (h : EvaluatesList primCtx opCtx blockCtx env terms initial values final) :
    Std.Do.Triple (evalList? primCtx opCtx blockCtx env terms)
      (EvalTriple.Singleton.statePre initial) (someEqPost values final) := by
  rw [Std.Do.Triple.iff, Std.Do.SPred.entails_1]
  intro state hstate
  exact (Std.Do.Triple.iff.mp
    (evalList?_triple_of_evaluatesList h (someEqPost values final))) state
      ⟨hstate, by simp [someEqPost, somePost]⟩

theorem apply?_eq_triple_of_evaluatesApply {primCtx : PrimitiveCtx}
    {opCtx : OpCtx primCtx (StateM σ)} {blockCtx : BlockCtx primCtx}
    {fn : Val primCtx} {args : List (Val primCtx)} {initial final : σ}
    {value : Val primCtx}
    (h : State.EvaluatesApply primCtx opCtx blockCtx fn args initial value final) :
    Std.Do.Triple (apply? primCtx opCtx blockCtx fn args)
      (EvalTriple.Singleton.statePre initial) (someEqPost value final) := by
  rw [Std.Do.Triple.iff, Std.Do.SPred.entails_1]
  intro state hstate
  exact (Std.Do.Triple.iff.mp
    (apply?_triple_of_evaluatesApply h (someEqPost value final))) state
      ⟨hstate, by simp [someEqPost, somePost]⟩

theorem callValues?_eq_triple_of_evaluatesCallValues {primCtx : PrimitiveCtx}
    {opCtx : OpCtx primCtx (StateM σ)} {blockCtx : BlockCtx primCtx}
    {name : String} {args : List (Val primCtx)} {initial final : σ}
    {value : Val primCtx}
    (h : State.EvaluatesCallValues primCtx opCtx blockCtx name args initial value final) :
    Std.Do.Triple (callValues? primCtx opCtx blockCtx name args)
      (EvalTriple.Singleton.statePre initial) (someEqPost value final) := by
  rw [Std.Do.Triple.iff, Std.Do.SPred.entails_1]
  intro state hstate
  exact (Std.Do.Triple.iff.mp
    (callValues?_triple_of_evaluatesCallValues h (someEqPost value final))) state
      ⟨hstate, by simp [someEqPost, somePost]⟩

theorem evalInstrs?_eq_triple_of_evaluatesInstrs {primCtx : PrimitiveCtx}
    {opCtx : OpCtx primCtx (StateM σ)} {blockCtx : BlockCtx primCtx}
    {instrs : List (Instr primCtx)} {result : Term primCtx} {env : Env primCtx}
    {initial final : σ} {value : Val primCtx}
    (h : EvaluatesInstrs primCtx opCtx blockCtx instrs result env initial value final) :
    Std.Do.Triple (evalInstrs? primCtx opCtx blockCtx instrs result env)
      (EvalTriple.Singleton.statePre initial) (someEqPost value final) := by
  rw [Std.Do.Triple.iff, Std.Do.SPred.entails_1]
  intro state hstate
  exact (Std.Do.Triple.iff.mp
    (evalInstrs?_triple_of_evaluatesInstrs h (someEqPost value final))) state
      ⟨hstate, by simp [someEqPost, somePost]⟩

theorem evalInstrs?_nil_eq_spec {primCtx : PrimitiveCtx}
    {opCtx : OpCtx primCtx (StateM σ)} {blockCtx : BlockCtx primCtx}
    {result : Term primCtx} {env : Env primCtx} {initial final : σ}
    {value : Val primCtx}
    (hresult : Std.Do.Triple (State.eval? primCtx opCtx blockCtx env result)
      (EvalTriple.Singleton.statePre initial) (someEqPost value final)) :
    Std.Do.Triple (evalInstrs? primCtx opCtx blockCtx [] result env)
      (EvalTriple.Singleton.statePre initial) (someEqPost value final) :=
  evalInstrs?_eq_triple_of_evaluatesInstrs
    (EvaluatesInstrs.nil (evaluatesTo_of_eval?_triple hresult))

theorem evalInstrs?_cons_eq_spec {primCtx : PrimitiveCtx}
    {opCtx : OpCtx primCtx (StateM σ)} {blockCtx : BlockCtx primCtx}
    {instr : Instr primCtx} {instrs : List (Instr primCtx)}
    {result : Term primCtx} {env : Env primCtx}
    {initial middle final : σ} {instrValue value : Val primCtx}
    (hinstr : Std.Do.Triple (State.eval? primCtx opCtx blockCtx env instr.value)
      (EvalTriple.Singleton.statePre initial) (someEqPost instrValue middle))
    (hrest : Std.Do.Triple (evalInstrs? primCtx opCtx blockCtx instrs result
        (env ++ [(instr.name, instrValue)]))
      (EvalTriple.Singleton.statePre middle) (someEqPost value final)) :
    Std.Do.Triple (evalInstrs? primCtx opCtx blockCtx (instr :: instrs) result env)
      (EvalTriple.Singleton.statePre initial) (someEqPost value final) :=
  evalInstrs?_eq_triple_of_evaluatesInstrs
    (EvaluatesInstrs.cons (evaluatesTo_of_eval?_triple hinstr)
      (evaluatesInstrs_of_evalInstrs?_triple hrest))

@[spec] theorem evalList?_nil_spec {primCtx : PrimitiveCtx}
    {opCtx : OpCtx primCtx (StateM σ)} {blockCtx : BlockCtx primCtx}
    (env : Env primCtx)
    (Q : Std.Do.PostCond (Option (List (Val primCtx))) (.arg σ .pure)) :
    Std.Do.Triple (evalList? primCtx opCtx blockCtx env []) (Q.1 (some [])) Q := by
  rw [Std.Do.Triple.iff, Std.Do.SPred.entails_1]
  intro state hQ
  exact (Std.Do.Triple.iff.mp
    (evalList?_triple_of_evaluatesList (EvaluatesList.nil (state := state)) Q)) state
      ⟨rfl, hQ⟩

@[spec] theorem evalList?_cons_spec {primCtx : PrimitiveCtx}
    {opCtx : OpCtx primCtx (StateM σ)} {blockCtx : BlockCtx primCtx}
    (env : Env primCtx) (term : Term primCtx) (terms : List (Term primCtx))
    (Q : Std.Do.PostCond (Option (List (Val primCtx))) (.arg σ .pure)) :
    Std.Do.Triple (evalList? primCtx opCtx blockCtx env (term :: terms))
      ((Std.Do.wp (State.eval? primCtx opCtx blockCtx env term)).apply
        (somePost fun value =>
          (Std.Do.wp (evalList? primCtx opCtx blockCtx env terms)).apply
            (somePost fun values => Q.1 (some (value :: values))))) Q := by
  rw [Std.Do.Triple.iff, Std.Do.SPred.entails_1]
  intro initial hpre
  obtain ⟨value, middle, hvalue, hrestWp⟩ := eval?_some_of_wp hpre
  obtain ⟨values, final, hvalues, hQ⟩ := evalList?_some_of_wp hrestWp
  exact (Std.Do.Triple.iff.mp
    (evalList?_triple_of_evaluatesList (EvaluatesList.cons hvalue hvalues) Q)) initial
      ⟨rfl, hQ⟩

@[spec 1100] theorem evalList?_spec {primCtx : PrimitiveCtx}
    {opCtx : OpCtx primCtx (StateM σ)} {blockCtx : BlockCtx primCtx}
    (env : Env primCtx) (terms : List (Term primCtx))
    (Q : Std.Do.PostCond (Option (List (Val primCtx))) (.arg σ .pure)) :
    Std.Do.Triple (evalList? primCtx opCtx blockCtx env terms)
      (evalListPre primCtx opCtx blockCtx env terms Q) Q := by
  cases terms with
  | nil => exact evalList?_nil_spec env Q
  | cons term terms => exact evalList?_cons_spec env term terms Q

@[spec] theorem eval?_app_spec {primCtx : PrimitiveCtx}
    {opCtx : OpCtx primCtx (StateM σ)} {blockCtx : BlockCtx primCtx}
    {env : Env primCtx} {fn : Term primCtx} {args : List (Term primCtx)}
    (Q : Std.Do.PostCond (Option (Val primCtx)) (.arg σ .pure)) :
    Std.Do.Triple (State.eval? primCtx opCtx blockCtx env (.app fn args))
      ((Std.Do.wp (State.eval? primCtx opCtx blockCtx env fn)).apply
        (somePost fun fnValue =>
          (Std.Do.wp (evalList? primCtx opCtx blockCtx env args)).apply
            (somePost fun argValues =>
              (Std.Do.wp (apply? primCtx opCtx blockCtx fnValue argValues)).apply
                (somePost fun value => Q.1 (some value))))) Q := by
  rw [Std.Do.Triple.iff, Std.Do.SPred.entails_1]
  intro initial hpre
  obtain ⟨fnValue, fnFinal, hfn, hargsWp⟩ := eval?_some_of_wp hpre
  obtain ⟨argValues, argsFinal, hargs, happlyWp⟩ := evalList?_some_of_wp hargsWp
  obtain ⟨value, final, happly, hQ⟩ := apply?_some_of_wp happlyWp
  exact (Std.Do.Triple.iff.mp
    (State.eval?_triple_of_evaluatesTo (EvaluatesToK.app hfn hargs happly) Q)) initial
      ⟨rfl, hQ⟩

@[spec] theorem eval?_call_spec {primCtx : PrimitiveCtx}
    {opCtx : OpCtx primCtx (StateM σ)} {blockCtx : BlockCtx primCtx}
    {env : Env primCtx} {name : String} {args : List (Term primCtx)}
    {block : Block primCtx}
    (hblock : blockCtx.get? name = some block)
    (Q : Std.Do.PostCond (Option (Val primCtx)) (.arg σ .pure)) :
    Std.Do.Triple (State.eval? primCtx opCtx blockCtx env (.call name args))
      ((Std.Do.wp (evalList? primCtx opCtx blockCtx env args)).apply
        (somePost fun argValues =>
          (Std.Do.wp (callValues? primCtx opCtx blockCtx name argValues)).apply
            (somePost fun value => Q.1 (some value)))) Q := by
  rw [Std.Do.Triple.iff, Std.Do.SPred.entails_1]
  intro initial hpre
  obtain ⟨argValues, argsFinal, hargs, hcallWp⟩ := evalList?_some_of_wp hpre
  obtain ⟨value, final, hcall, hQ⟩ := callValues?_some_of_wp hcallWp
  exact (Std.Do.Triple.iff.mp
    (State.eval?_triple_of_evaluatesTo (EvaluatesToK.call hcall hblock hargs) Q)) initial
      ⟨rfl, hQ⟩

@[spec] theorem apply?_blockRef_spec {primCtx : PrimitiveCtx}
    {opCtx : OpCtx primCtx (StateM σ)} {blockCtx : BlockCtx primCtx}
    {name : String} {argTys : List Ty} {outTy : Ty} {args : List (Val primCtx)}
    (Q : Std.Do.PostCond (Option (Val primCtx)) (.arg σ .pure)) :
    Std.Do.Triple (apply? primCtx opCtx blockCtx (.blockRef name argTys outTy) args)
      ((Std.Do.wp (callValues? primCtx opCtx blockCtx name args)).apply
        (somePost fun value => Q.1 (some value))) Q := by
  rw [Std.Do.Triple.iff, Std.Do.SPred.entails_1]
  intro initial hpre
  obtain ⟨value, final, hcall, hQ⟩ := callValues?_some_of_wp hpre
  exact (Std.Do.Triple.iff.mp
    (apply?_triple_of_evaluatesApply (EvalTriple.EvaluatesApply.blockRef hcall) Q)) initial
      ⟨rfl, hQ⟩

@[spec] theorem callValues?_block_spec {primCtx : PrimitiveCtx}
    {opCtx : OpCtx primCtx (StateM σ)} {blockCtx : BlockCtx primCtx}
    {name : String} {args : List (Val primCtx)} {block : Block primCtx}
    (hblock : blockCtx.get? name = some block)
    (hargs : args.length = block.params.length)
    (Q : Std.Do.PostCond (Option (Val primCtx)) (.arg σ .pure)) :
    Std.Do.Triple (callValues? primCtx opCtx blockCtx name args)
      ((Std.Do.wp (evalInstrs? primCtx opCtx blockCtx block.instrs block.result
          (block.entryEnv args))).apply
        (somePost fun value => Q.1 (some value))) Q := by
  rw [Std.Do.Triple.iff, Std.Do.SPred.entails_1]
  intro initial hpre
  obtain ⟨value, final, hbody, hQ⟩ := evalInstrs?_some_of_wp hpre
  exact (Std.Do.Triple.iff.mp
    (callValues?_triple_of_evaluatesCallValues
      (EvaluatesCallValues.of_evaluatesInstrs hblock hargs hbody) Q)) initial
      ⟨rfl, hQ⟩

@[spec] theorem evalInstrs?_nil_spec {primCtx : PrimitiveCtx}
    {opCtx : OpCtx primCtx (StateM σ)} {blockCtx : BlockCtx primCtx}
    {result : Term primCtx} {env : Env primCtx}
    (Q : Std.Do.PostCond (Option (Val primCtx)) (.arg σ .pure)) :
    Std.Do.Triple (evalInstrs? primCtx opCtx blockCtx [] result env)
      ((Std.Do.wp (State.eval? primCtx opCtx blockCtx env result)).apply
        (somePost fun value => Q.1 (some value))) Q := by
  rw [Std.Do.Triple.iff, Std.Do.SPred.entails_1]
  intro initial hpre
  obtain ⟨value, final, hresult, hQ⟩ := eval?_some_of_wp hpre
  exact (Std.Do.Triple.iff.mp
    (evalInstrs?_triple_of_evaluatesInstrs (EvaluatesInstrs.nil hresult) Q)) initial
      ⟨rfl, hQ⟩

@[spec] theorem evalInstrs?_cons_spec {primCtx : PrimitiveCtx}
    {opCtx : OpCtx primCtx (StateM σ)} {blockCtx : BlockCtx primCtx}
    {instr : Instr primCtx} {instrs : List (Instr primCtx)}
    {result : Term primCtx} {env : Env primCtx}
    (Q : Std.Do.PostCond (Option (Val primCtx)) (.arg σ .pure)) :
    Std.Do.Triple (evalInstrs? primCtx opCtx blockCtx (instr :: instrs) result env)
      ((Std.Do.wp (State.eval? primCtx opCtx blockCtx env instr.value)).apply
        (somePost fun instrValue =>
          (Std.Do.wp (evalInstrs? primCtx opCtx blockCtx instrs result
              (env ++ [(instr.name, instrValue)]))).apply
            (somePost fun value => Q.1 (some value)))) Q := by
  rw [Std.Do.Triple.iff, Std.Do.SPred.entails_1]
  intro initial hpre
  obtain ⟨instrValue, middle, hinstr, hrestWp⟩ := eval?_some_of_wp hpre
  obtain ⟨value, final, hrest, hQ⟩ := evalInstrs?_some_of_wp hrestWp
  exact (Std.Do.Triple.iff.mp
    (evalInstrs?_triple_of_evaluatesInstrs (EvaluatesInstrs.cons hinstr hrest) Q)) initial
      ⟨rfl, hQ⟩

@[spec 1100] theorem evalInstrs?_spec {primCtx : PrimitiveCtx}
    {opCtx : OpCtx primCtx (StateM σ)} {blockCtx : BlockCtx primCtx}
    (instrs : List (Instr primCtx)) (result : Term primCtx) (env : Env primCtx)
    (Q : Std.Do.PostCond (Option (Val primCtx)) (.arg σ .pure)) :
    Std.Do.Triple (evalInstrs? primCtx opCtx blockCtx instrs result env)
      (evalInstrsPre primCtx opCtx blockCtx instrs result env Q) Q := by
  cases instrs with
  | nil => exact evalInstrs?_nil_spec Q
  | cons instr instrs => exact evalInstrs?_cons_spec Q

end State

end EvalTriple

end Zag
