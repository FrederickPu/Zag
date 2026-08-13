import Test.Autocorres.Examples.Common

namespace Zag.Test.Autocorres.Examples

open Zag Zag.Lib.PeanoHeap

@[simp] theorem evalOutcome_nat {ctx : Ctx} [Peano.Types ctx.primCtx]
    (env : Env ctx.primCtx) (n : Nat) :
    Term.evalOutcome ctx env (Term.nat n) = some (.ok (Val.nat n)) := by
  rw [Term.evalOutcome.eq_def]
  rfl

@[simp] theorem evalOutcome_bool {ctx : Ctx} [Peano.Types ctx.primCtx]
    (env : Env ctx.primCtx) (b : Bool) :
    Term.evalOutcome ctx env (Term.bool b) = some (.ok (Val.bool b)) := by
  rw [Term.evalOutcome.eq_def]
  rfl

theorem evalListOutcome_cons_ok {ctx : Ctx} {env : Env ctx.primCtx}
    {t : Term ctx.primCtx} {ts : List (Term ctx.primCtx)} {v : Val ctx.primCtx}
    {vs : List (Val ctx.primCtx)}
    (ht : Term.evalOutcome ctx env t = some (.ok v))
    (hrest : Term.evalListOutcome ctx env ts = some (.ok vs)) :
    Term.evalListOutcome ctx env (t :: ts) = some (.ok (v :: vs)) := by
  rw [Term.evalListOutcome.eq_def]
  simp [ht, hrest]

@[simp] theorem evalListOutcome_nil {ctx : Ctx} (env : Env ctx.primCtx) :
    Term.evalListOutcome ctx env [] = some (.ok []) := by
  rw [Term.evalListOutcome.eq_def]

theorem evalListOutcome_two_nat {ctx : Ctx} [Peano.Types ctx.primCtx]
    (env : Env ctx.primCtx) (a b : Nat) :
    Term.evalListOutcome ctx env [Term.nat a, Term.nat b] =
      some (.ok [Val.nat a, Val.nat b]) :=
  evalListOutcome_cons_ok (evalOutcome_nat env a)
    (evalListOutcome_cons_ok (evalOutcome_nat env b) (evalListOutcome_nil env))

theorem evalBlock_noInstr_ok {ctx : Ctx} {env : Env ctx.primCtx} {name : String}
    {params : VarCtx} {outTy : Ty} {result : Term ctx.primCtx} {value : Val ctx.primCtx}
    (hresult : Term.evalOutcome ctx env result = some (.ok value)) :
    Term.evalBlock ctx name env { params := params, instrs := [], outTy := outTy, result := result } =
      some (.ok value) := by
  rw [Term.evalBlock.eq_def, Term.evalInstrs.eq_def]
  simp [hresult]

theorem evalOutcome_ok_of_eval {ctx : Ctx} {env : Env ctx.primCtx} {term : Term ctx.primCtx}
    {value : Val ctx.primCtx} (h : Term.eval ctx env term = some value) :
    Term.evalOutcome ctx env term = some (.ok value) := by
  set_option linter.unnecessarySimpa false in
  unfold Term.eval Term.evalGo at h
  cases hterm : Term.evalOutcome ctx env term with
  | none => simp [hterm] at h
  | some outcome =>
      cases outcome <;> simp [hterm, Outcome.ok?] at h
      case ok value' =>
        simpa [h] using hterm

theorem evalBlock_noInstr_eval {ctx : Ctx} {env : Env ctx.primCtx} {name : String}
    {params : VarCtx} {outTy : Ty} {result : Term ctx.primCtx} {value : Val ctx.primCtx}
    (hresult : Term.eval ctx env result = some value) :
    Term.evalBlock ctx name env { params := params, instrs := [], outTy := outTy, result := result } =
      some (.ok value) :=
  evalBlock_noInstr_ok (evalOutcome_ok_of_eval hresult)

theorem evalInstrs_cons_ok {ctx : Ctx} {env out : Env ctx.primCtx}
    {instr : Instr ctx.primCtx} {instrs : List (Instr ctx.primCtx)} {value : Val ctx.primCtx}
    (hvalue : Term.evalOutcome ctx env instr.value = some (.ok value))
    (hrest : Term.evalInstrs ctx (env ++ [(instr.name, value)]) instrs = some (.ok out)) :
    Term.evalInstrs ctx env (instr :: instrs) = some (.ok out) := by
  rw [Term.evalInstrs.eq_def]
  simp [hvalue, hrest]

theorem evalBlock_oneInstr_eval {ctx : Ctx} {env : Env ctx.primCtx} {name : String}
    {params : VarCtx} {outTy : Ty} {instr : Instr ctx.primCtx} {result : Term ctx.primCtx}
    {instrValue value : Val ctx.primCtx}
    (hinstr : Term.eval ctx env instr.value = some instrValue)
    (hresult : Term.eval ctx (env ++ [(instr.name, instrValue)]) result = some value) :
    Term.evalBlock ctx name env
        { params := params, instrs := [instr], outTy := outTy, result := result } =
      some (.ok value) := by
  rw [Term.evalBlock.eq_def]
  rw [evalInstrs_cons_ok (evalOutcome_ok_of_eval hinstr) (by rw [Term.evalInstrs.eq_def])]
  simp [evalOutcome_ok_of_eval hresult]

theorem eval_call_ok {ctx : Ctx} {env : Env ctx.primCtx} {name : String}
    {args : List (Term ctx.primCtx)} {block : Block ctx.primCtx} {vargs : List (Val ctx.primCtx)}
    {value : Val ctx.primCtx}
    (hblock : ctx.blockCtx.get? name = some block)
    (hargs : Term.evalListOutcome ctx env args = some (.ok vargs))
    (hlen : vargs.length = block.params.length)
    (hbody : Term.evalBlock ctx name (block.entryEnv vargs) block = some (.ok value)) :
    Term.eval ctx env (.call name args) = some value := by
  simp only [Term.eval, Term.evalGo, Term.evalOutcome.eq_def]
  rw [hblock, hargs]
  simp [hlen, hbody, Outcome.ok?]

theorem applyVals_natUnary {primCtx : PrimitiveCtx} [Peano.Types primCtx]
    (f : Nat -> Nat) (a : Nat) :
    Op.applyVals (Op.natUnary (primCtx := primCtx) f) [Val.nat a] =
      some (Val.nat (f a)) := by
  rw [Op.applyVals]
  simp only [Op.natUnary, Op.ofVals, List.length_cons, List.length_nil, Nat.reduceAdd,
    if_true]
  rw [eager_one]
  have htys : List.map Val.ty [Val.nat (primCtx := primCtx) a] = [Peano.NatTy] := rfl
  rw [if_pos htys]
  simp [Val.asNat?_nat, Val.as?_nat]
where
  eager_one {primCtx : PrimitiveCtx} (run : List (Val primCtx) -> Option (Val primCtx))
      (a : Val primCtx) :
      Op.Body.applyVals (Op.Body.eager run 1 []) [a] = run [a] := by
    unfold Op.Body.eager
    change Op.Body.applyVals (Op.Body.next true (fun
      | some value => Op.Body.eager run 0 ([] ++ [value])
      | none => Op.Body.fail)) [a] = run [a]
    rw [Op.Body.applyVals.eq_def]
    change Op.Body.applyVals (Op.Body.eager run 0 ([] ++ [a])) [] = run [a]
    unfold Op.Body.eager
    simp
    cases run [a] <;> simp [Op.Body.applyVals]

theorem evalBody_natUnary {ctx : Ctx} [Peano.Types ctx.primCtx]
    {env : Env ctx.primCtx} {a : Term ctx.primCtx} {m : Nat} {f : Nat -> Nat}
    (ha : Term.eval ctx env a = some (Val.nat m)) :
    Term.evalBody ctx env [a] (Op.natUnary (primCtx := ctx.primCtx) f).body =
      some (Val.nat (f m)) := by
  change Term.evalBody ctx env [a] (Op.Body.eager _ 1 []) = some (Val.nat (f m))
  rw [Term.evalBody_eager_one ctx env _ a (Val.nat m) ha]
  exact applyVals_natUnary f m

theorem eval_nat_unary_op {ctx : Ctx} [Peano.Types ctx.primCtx]
    {env : Env ctx.primCtx} {name : String} {a : Term ctx.primCtx} {m : Nat}
    {f : Nat -> Nat}
    (hop : ctx.opCtx.get? name = some (Op.natUnary (primCtx := ctx.primCtx) f))
    (ha : Term.eval ctx env a = some (Val.nat m)) :
    Term.eval ctx env (.op name [a]) = some (Val.nat (f m)) := by
  rw [Term.eval, Term.evalGo_op, hop]
  change (if [a].length = (Op.natUnary (primCtx := ctx.primCtx) f).arity then
    Term.evalBody ctx env [a] (Op.natUnary (primCtx := ctx.primCtx) f).body else none) = _
  have hlen : [a].length = (Op.natUnary (primCtx := ctx.primCtx) f).arity := rfl
  rw [if_pos hlen]
  exact evalBody_natUnary ha

theorem applyVals_natBinary {primCtx : PrimitiveCtx} [Peano.Types primCtx]
    (f : Nat -> Nat -> Nat) (a b : Nat) :
    Op.applyVals (Op.natBinary (primCtx := primCtx) f) [Val.nat a, Val.nat b] =
      some (Val.nat (f a b)) := by
  rw [Op.applyVals]
  simp only [Op.natBinary, Op.ofVals, List.length_cons, List.length_nil, Nat.reduceAdd, if_true]
  rw [eager_two]
  have htys : List.map Val.ty [Val.nat (primCtx := primCtx) a, Val.nat b] =
      [Peano.NatTy, Peano.NatTy] := rfl
  rw [if_pos htys]
  simp [Val.asNat?_nat, Val.as?_nat]
where
  eager_two {primCtx : PrimitiveCtx} (run : List (Val primCtx) -> Option (Val primCtx))
      (a b : Val primCtx) :
      Op.Body.applyVals (Op.Body.eager run 2 []) [a, b] = run [a, b] := by
    unfold Op.Body.eager
    change Op.Body.applyVals (Op.Body.next true (fun
      | some value => Op.Body.eager run 1 ([] ++ [value])
      | none => Op.Body.fail)) [a, b] = run [a, b]
    rw [Op.Body.applyVals.eq_def]
    change Op.Body.applyVals (Op.Body.eager run 1 ([] ++ [a])) [b] = run [a, b]
    unfold Op.Body.eager
    change Op.Body.applyVals (Op.Body.next true (fun
      | some value => Op.Body.eager run 0 ([] ++ [a] ++ [value])
      | none => Op.Body.fail)) [b] = run [a, b]
    rw [Op.Body.applyVals.eq_def]
    change Op.Body.applyVals (Op.Body.eager run 0 ([] ++ [a] ++ [b])) [] = run [a, b]
    unfold Op.Body.eager
    simp
    cases run [a, b] <;> simp [Op.Body.applyVals]

theorem evalBody_natBinary {ctx : Ctx} [Peano.Types ctx.primCtx]
    {env : Env ctx.primCtx} {a b : Term ctx.primCtx} {m n : Nat} {f : Nat -> Nat -> Nat}
    (ha : Term.eval ctx env a = some (Val.nat m))
    (hb : Term.eval ctx env b = some (Val.nat n)) :
    Term.evalBody ctx env [a, b] (Op.natBinary (primCtx := ctx.primCtx) f).body =
      some (Val.nat (f m n)) := by
  change Term.evalBody ctx env [a, b] (Op.Body.eager _ 2 []) = some (Val.nat (f m n))
  rw [Term.evalBody_eager_two ctx env _ a b (Val.nat m) (Val.nat n) ha hb]
  exact applyVals_natBinary f m n

theorem eval_nat_binary_op {ctx : Ctx} [Peano.Types ctx.primCtx]
    {env : Env ctx.primCtx} {name : String} {a b : Term ctx.primCtx} {m n : Nat}
    {f : Nat -> Nat -> Nat}
    (hop : ctx.opCtx.get? name = some (Op.natBinary (primCtx := ctx.primCtx) f))
    (ha : Term.eval ctx env a = some (Val.nat m))
    (hb : Term.eval ctx env b = some (Val.nat n)) :
    Term.eval ctx env (.op name [a, b]) = some (Val.nat (f m n)) := by
  rw [Term.eval, Term.evalGo_op, hop]
  change (if [a, b].length = (Op.natBinary (primCtx := ctx.primCtx) f).arity then
    Term.evalBody ctx env [a, b] (Op.natBinary (primCtx := ctx.primCtx) f).body else none) = _
  have hlen : [a, b].length = (Op.natBinary (primCtx := ctx.primCtx) f).arity := rfl
  rw [if_pos hlen]
  exact evalBody_natBinary ha hb

theorem eval_nat_eq_op {ctx : Ctx} [Peano.Model ctx]
    {env : Env ctx.primCtx} {a b : Term ctx.primCtx} {m n : Nat}
    (ha : Term.eval ctx env a = some (Val.nat m))
    (hb : Term.eval ctx env b = some (Val.nat n)) :
    Term.eval ctx env (.op "eq" [a, b]) = some (Val.bool (decide (m = n))) := by
  have h := Term.evalGo_op_compare (ctx := ctx) (env := env) (name := "eq")
    (cmp := Val.primEq?) (a := a) (b := b) (va := Val.nat m) (vb := Val.nat n)
    (by rw [Peano.Model.eqOp]; rfl) ha hb rfl
  rw [Term.eval]
  rw [h]
  simp [Val.primEq?]

theorem eval_ite_true {ctx : Ctx} [Peano.Model ctx]
    {env : Env ctx.primCtx} {cond thenTerm elseTerm : Term ctx.primCtx}
    (hcond : Term.eval ctx env cond = some (Val.bool true)) :
    Term.eval ctx env (Term.ite cond thenTerm elseTerm) = Term.eval ctx env thenTerm := by
  have hcondGo : Term.evalGo ctx env cond = some (Val.bool true) := hcond
  rw [Term.eval, Term.evalGo_ite]
  simp [hcondGo, Val.as?_bool, Ty.toBool_ofBool]
  rfl

theorem eval_ite_false {ctx : Ctx} [Peano.Model ctx]
    {env : Env ctx.primCtx} {cond thenTerm elseTerm : Term ctx.primCtx}
    (hcond : Term.eval ctx env cond = some (Val.bool false)) :
    Term.eval ctx env (Term.ite cond thenTerm elseTerm) = Term.eval ctx env elseTerm := by
  have hcondGo : Term.evalGo ctx env cond = some (Val.bool false) := hcond
  rw [Term.eval, Term.evalGo_ite]
  simp [hcondGo, Val.as?_bool, Ty.toBool_ofBool]
  rfl

end Zag.Test.Autocorres.Examples
