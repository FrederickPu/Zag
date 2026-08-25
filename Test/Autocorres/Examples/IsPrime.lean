import Test.Autocorres.Examples.Common

/-!
Upstream Isabelle theory:
[`IsPrime.thy`](https://github.com/seL4/l4v/blob/master/tools/autocorres/tests/examples/IsPrime.thy).

The two C trial-division loops are modeled over unbounded `Nat`, including the faster loop's
`65536` bound. Multiplication and increment do not wrap; correspondence with the unsigned C result
for the faster function is consequently stated only in its original 32-bit input range. There is
no typed-memory behavior because the source functions are pure. Each increasing `for` loop carries
an internal decreasing count; this is an extensional current-model encoding of exactly the same
candidate sequence and exit tests, used to expose structural termination to Lean.
-/

namespace Zag.Test.Autocorres.Examples

open Zag Zag.Lib.PeanoHeap
open Zag.EvalTriple
open Zag.EvalTriple.Exact
open scoped Std.Do

private abbrev heapOpCtx := pureHeapOpCtx

abbrev isPrimeBlocks : BlockCtx.Raw heapCtx :=
  blocks% [
    isPrimeLinear(n : Nat) : Bool {
      small := op "lt"[n, nat(2)];
      ret if small { bool(false) }
        else { call isPrimeLinearLoop [n, nat(2), op "sub"[n, nat(2)]] }
    },
    isPrimeLinearLoop(n : Nat, div : Nat, remaining : Nat) : Bool {
      done := primEq remaining nat(0);
      remainder := op "mod"[n, div];
      divides := primEq remainder nat(0);
      ret if done { bool(true) } else {
        if divides { bool(false) }
          else { call isPrimeLinearLoop
            [n, op "add"[div, nat(1)], op "sub"[remaining, nat(1)]] }
      }
    },
    isPrime(n : Nat) : Bool {
      small := op "lt"[n, nat(2)];
      ret if small { bool(false) } else { call isPrimeLoop [n, nat(2), nat(65534)] }
    },
    isPrimeLoop(n : Nat, div : Nat, remaining : Nat) : Bool {
      atLimit := primEq remaining nat(0);
      square := op "mul"[div, div];
      pastSquare := op "lt"[n, square];
      remainder := op "mod"[n, div];
      divides := primEq remainder nat(0);
      ret if atLimit { bool(true) } else {
        if pastSquare { bool(true) } else {
          if divides { bool(false) }
            else { call isPrimeLoop
              [n, op "add"[div, nat(1)], op "sub"[remaining, nat(1)]] }
        }
      }
    }
  ]

theorem isPrimeBlocksValid : BlockCtx.Valid isPrimeBlocks := by
  valid_blocks [isPrimeBlocks]

abbrev isPrimeCtx : Ctx := mkPureCtx isPrimeBlocks isPrimeBlocksValid

theorem isPrimeCtx_wellTyped : Ctx.WellTyped isPrimeCtx := by
  typecheck_ctx

@[eval_semantic] theorem isPrime_evaluates_mod {env : Env heapCtx}
    {lhsTerm rhsTerm : Term heapCtx} {lhs rhs : Nat}
    (hlhs : EvaluatesTo isPrimeCtx env lhsTerm (Val.nat lhs))
    (hrhs : EvaluatesTo isPrimeCtx env rhsTerm (Val.nat rhs)) :
    EvaluatesTo isPrimeCtx env (.op "mod" [lhsTerm, rhsTerm]) (Val.nat (lhs % rhs)) := by
  refine EvaluatesTo.op_applyVals (oper := binaryNatOp Nat.mod) rfl
    (EvaluatesList.cons hlhs (EvaluatesList.cons hrhs EvaluatesList.nil)) ?_
  simp [Op.applyValsAt, Op.fixed, binaryNatOp, Op.ofVals, Op.Body.applyVals, Op.Body.eager]
  rfl

theorem isPrime_evaluates_ite_true {env : Env heapCtx}
    {conditionTerm thenTerm elseTerm : Term heapCtx} {value elseValue : Val heapCtx}
    (hcondition : EvaluatesTo isPrimeCtx env conditionTerm (Val.bool true))
    (hthen : EvaluatesTo isPrimeCtx env thenTerm value)
    (helse : EvaluatesTo isPrimeCtx env elseTerm elseValue) :
    EvaluatesTo isPrimeCtx env (Term.ite conditionTerm thenTerm elseTerm) value := by
  refine EvaluatesTo.op_applyVals (oper := Op.ite) Peano.Model.iteOp
    (EvaluatesList.cons hcondition
      (EvaluatesList.cons hthen (EvaluatesList.cons helse EvaluatesList.nil))) ?_
  simp [Op.applyValsAt, Op.ite, Op.fixed, Op.Body.applyVals]

theorem isPrime_evaluates_ite_false {env : Env heapCtx}
    {conditionTerm thenTerm elseTerm : Term heapCtx} {thenValue value : Val heapCtx}
    (hcondition : EvaluatesTo isPrimeCtx env conditionTerm (Val.bool false))
    (hthen : EvaluatesTo isPrimeCtx env thenTerm thenValue)
    (helse : EvaluatesTo isPrimeCtx env elseTerm value) :
    EvaluatesTo isPrimeCtx env (Term.ite conditionTerm thenTerm elseTerm) value := by
  refine EvaluatesTo.op_applyVals (oper := Op.ite) Peano.Model.iteOp
    (EvaluatesList.cons hcondition
      (EvaluatesList.cons hthen (EvaluatesList.cons helse EvaluatesList.nil))) ?_
  simp [Op.applyValsAt, Op.ite, Op.fixed, Op.Body.applyVals]

theorem isPrime_evaluates_next_args {env : Env heapCtx} {n div remaining : Nat}
    (hn : env.get? "n" = some (Val.nat n))
    (hdiv : env.get? "div" = some (Val.nat div))
    (hremaining : env.get? "remaining" = some (Val.nat remaining)) :
    EvaluatesList isPrimeCtx env
      [Term.var "n", Term.op "add" [Term.var "div", Term.nat 1],
        Term.op "sub" [Term.var "remaining", Term.nat 1]]
      [Val.nat n, Val.nat (div + 1), Val.nat (remaining - 1)] := by
  exact EvaluatesList.cons (EvaluatesTo.var_local hn)
    (EvaluatesList.cons
      (evaluates_add_nat (ctx := isPrimeCtx) (hM := rfl)
        (EvaluatesTo.var_local hdiv) (evaluates_nat (ctx := isPrimeCtx) (hM := rfl) env 1))
      (EvaluatesList.cons
        (evaluates_sub_nat (ctx := isPrimeCtx) (hM := rfl)
          (EvaluatesTo.var_local hremaining) (evaluates_nat (ctx := isPrimeCtx) (hM := rfl) env 1))
        EvaluatesList.nil))

theorem isPrime_evaluates_remaining_succ_ne_zero {env : Env heapCtx} {count : Nat}
    (hremaining : env.get? "remaining" = some (Val.nat (count + 1))) :
    EvaluatesTo isPrimeCtx env (Term.op "eq" [Term.var "remaining", Term.nat 0])
      (Val.bool false) := by
  simpa using
    (evaluates_eq_nat (ctx := isPrimeCtx) (hM := rfl)
      (EvaluatesTo.var_local hremaining)
      (evaluates_nat (ctx := isPrimeCtx) (hM := rfl) env 0))

/-- Check `count` consecutive candidate divisors starting at `div`. This is a pure semantic model
of the exact linear loop state, not the mathematical definition of primality. -/
def trialDivision (n : Nat) : Nat → Nat → Bool
| _, 0 => true
| div, count + 1 =>
    if n % div = 0 then false else trialDivision n (div + 1) count

/-- Pure semantic model of the bounded square-root loop. -/
def trialDivisionSqrt (n : Nat) : Nat → Nat → Bool
| _, 0 => true
| div, count + 1 =>
    if n < div * div then true
    else if n % div = 0 then false
    else trialDivisionSqrt n (div + 1) count

def isPrimeLinearSpec (n : Nat) : Bool :=
  if n < 2 then false else trialDivision n 2 (n - 2)

def isPrimeSpec (n : Nat) : Bool :=
  if n < 2 then false else trialDivisionSqrt n 2 65534

set_option maxRecDepth 100000 in
private theorem isPrimeLinearLoop_eval_exact (n div count : Nat) :
    Exact.EvaluatesCallValues isPrimeCtx "isPrimeLinearLoop"
      ([Val.nat n, Val.nat div, Val.nat count] : List (Val heapCtx))
      (Val.bool (trialDivision n div count)) := by
  induction count generalizing div with
  | zero =>
      change Exact.EvaluatesCallValues isPrimeCtx "isPrimeLinearLoop"
        ([Val.nat n, Val.nat div, Val.nat 0] : List (Val heapCtx)) (Val.bool true)
      apply EvaluatesCallValues.of_evaluatesInstrs (block := isPrimeBlocks[1].2) <;> try rfl
      refine EvaluatesInstrs.cons (instrValue := Val.bool true) ?_ ?_
      · evaluates 100 [heapOpCtx, Op.fixed, isPrimeBlocks]
      refine EvaluatesInstrs.cons (instrValue := Val.nat (n % div)) ?_ ?_
      · exact isPrime_evaluates_mod (EvaluatesTo.var_local (by rfl))
          (EvaluatesTo.var_local (by rfl))
      refine EvaluatesInstrs.cons (instrValue := Val.bool (decide (n % div = 0))) ?_ ?_
      · evaluates 100 [heapOpCtx, Op.fixed, isPrimeBlocks]
      apply EvaluatesInstrs.nil
      evaluates 100 [heapOpCtx, Op.fixed, isPrimeBlocks]
  | succ count ih =>
      by_cases hdiv : n % div = 0
      · simp only [trialDivision, hdiv, ↓reduceIte]
        apply EvaluatesCallValues.of_evaluatesInstrs (block := isPrimeBlocks[1].2) <;> try rfl
        refine EvaluatesInstrs.cons (instrValue := Val.bool false) ?_ ?_
        · exact isPrime_evaluates_remaining_succ_ne_zero (count := count) rfl
        refine EvaluatesInstrs.cons (instrValue := Val.nat (n % div)) ?_ ?_
        · exact isPrime_evaluates_mod (EvaluatesTo.var_local (by rfl))
            (EvaluatesTo.var_local (by rfl))
        refine EvaluatesInstrs.cons (instrValue := Val.bool true) ?_ ?_
        · evaluates 100 [heapOpCtx, Op.fixed, isPrimeBlocks, hdiv]
        apply EvaluatesInstrs.nil
        apply isPrime_evaluates_ite_false
        · exact EvaluatesTo.var_local (name := "done") (value := Val.bool false) (by rfl)
        · exact evaluates_bool _ true
        apply isPrime_evaluates_ite_true
        · exact EvaluatesTo.var_local (name := "divides") (value := Val.bool true) (by rfl)
        · exact evaluates_bool _ false
        apply EvaluatesTo.call (ih (div + 1)) rfl
        exact isPrime_evaluates_next_args (n := n) (div := div) (remaining := count + 1)
          rfl rfl rfl
      · simp only [trialDivision, hdiv, ↓reduceIte]
        apply EvaluatesCallValues.of_evaluatesInstrs (block := isPrimeBlocks[1].2) <;> try rfl
        refine EvaluatesInstrs.cons (instrValue := Val.bool false) ?_ ?_
        · exact isPrime_evaluates_remaining_succ_ne_zero (count := count) rfl
        refine EvaluatesInstrs.cons (instrValue := Val.nat (n % div)) ?_ ?_
        · exact isPrime_evaluates_mod (EvaluatesTo.var_local (by rfl))
            (EvaluatesTo.var_local (by rfl))
        refine EvaluatesInstrs.cons (instrValue := Val.bool false) ?_ ?_
        · simpa [hdiv] using
            (evaluates_eq_nat (ctx := isPrimeCtx) (hM := rfl)
              (EvaluatesTo.var_local (name := "remainder") (value := Val.nat (n % div)) (by rfl))
              (evaluates_nat (ctx := isPrimeCtx) (hM := rfl) _ 0))
        apply EvaluatesInstrs.nil
        apply isPrime_evaluates_ite_false
        · exact EvaluatesTo.var_local (name := "done") (value := Val.bool false) (by rfl)
        · exact evaluates_bool _ true
        apply isPrime_evaluates_ite_false
        · exact EvaluatesTo.var_local (name := "divides") (value := Val.bool false) (by rfl)
        · exact evaluates_bool _ false
        apply EvaluatesTo.call (ih (div + 1)) rfl
        exact isPrime_evaluates_next_args (n := n) (div := div) (remaining := count + 1)
          rfl rfl rfl

theorem isPrimeLinearLoop_eval (n div count : Nat) :
    Zag.EvaluatesCallValues isPrimeCtx "isPrimeLinearLoop"
      ([Val.nat n, Val.nat div, Val.nat count] : List (Val heapCtx))
      (Singleton.idPre True)
      (Singleton.idPost (· = Val.bool (trialDivision n div count))) := by
  simpa [Exact.EvaluatesCallValues, Exact.pre, Exact.post, Singleton.idPre, Singleton.idPost]
    using isPrimeLinearLoop_eval_exact n div count

private theorem isPrimeLinear_eval_exact (n : Nat) :
    Exact.EvaluatesCallValues isPrimeCtx "isPrimeLinear" ([Val.nat n] : List (Val heapCtx))
      (Val.bool (isPrimeLinearSpec n)) := by
  unfold isPrimeLinearSpec
  by_cases hsmall : n < 2
  · simp only [hsmall, ↓reduceIte]
    apply EvaluatesCallValues.of_evaluatesInstrs (block := isPrimeBlocks[0].2) <;> try rfl
    refine EvaluatesInstrs.cons (instrValue := Val.bool true) ?_ ?_
    · evaluates 100 [heapOpCtx, Op.fixed, isPrimeBlocks, hsmall]
    apply EvaluatesInstrs.nil
    apply isPrime_evaluates_ite_true
    · exact EvaluatesTo.var_local (name := "small") (value := Val.bool true) (by rfl)
    · exact evaluates_bool _ false
    apply EvaluatesTo.call (isPrimeLinearLoop_eval_exact n 2 (n - 2)) rfl
    evaluates_to_all 100 [heapOpCtx, Op.fixed, isPrimeBlocks]
  · simp only [hsmall, ↓reduceIte]
    apply EvaluatesCallValues.of_evaluatesInstrs (block := isPrimeBlocks[0].2) <;> try rfl
    refine EvaluatesInstrs.cons (instrValue := Val.bool false) ?_ ?_
    · evaluates 100 [heapOpCtx, Op.fixed, isPrimeBlocks, hsmall]
    apply EvaluatesInstrs.nil
    apply isPrime_evaluates_ite_false
    · exact EvaluatesTo.var_local (name := "small") (value := Val.bool false) (by rfl)
    · exact evaluates_bool _ false
    apply EvaluatesTo.call (isPrimeLinearLoop_eval_exact n 2 (n - 2)) rfl
    evaluates_to_all 100 [heapOpCtx, Op.fixed, isPrimeBlocks]

theorem isPrimeLinear_eval (n : Nat) :
    Zag.EvaluatesCallValues isPrimeCtx "isPrimeLinear" ([Val.nat n] : List (Val heapCtx))
      (Singleton.idPre True)
      (Singleton.idPost (· = Val.bool (isPrimeLinearSpec n))) := by
  simpa [Exact.EvaluatesCallValues, Exact.pre, Exact.post, Singleton.idPre, Singleton.idPost]
    using isPrimeLinear_eval_exact n

set_option maxRecDepth 100000 in
private theorem isPrimeLoop_eval_exact (n div count : Nat) :
    Exact.EvaluatesCallValues isPrimeCtx "isPrimeLoop"
      ([Val.nat n, Val.nat div, Val.nat count] : List (Val heapCtx))
      (Val.bool (trialDivisionSqrt n div count)) := by
  induction count generalizing div with
  | zero =>
      change Exact.EvaluatesCallValues isPrimeCtx "isPrimeLoop"
        ([Val.nat n, Val.nat div, Val.nat 0] : List (Val heapCtx)) (Val.bool true)
      apply EvaluatesCallValues.of_evaluatesInstrs (block := isPrimeBlocks[3].2) <;> try rfl
      refine EvaluatesInstrs.cons (instrValue := Val.bool true) ?_ ?_
      · evaluates 100 [heapOpCtx, Op.fixed, isPrimeBlocks]
      refine EvaluatesInstrs.cons (instrValue := Val.nat (div * div)) ?_ ?_
      · evaluates 100 [heapOpCtx, Op.fixed, isPrimeBlocks]
      refine EvaluatesInstrs.cons (instrValue := Val.bool (decide (n < div * div))) ?_ ?_
      · evaluates 100 [heapOpCtx, Op.fixed, isPrimeBlocks]
      refine EvaluatesInstrs.cons (instrValue := Val.nat (n % div)) ?_ ?_
      · exact isPrime_evaluates_mod (EvaluatesTo.var_local (by rfl))
          (EvaluatesTo.var_local (by rfl))
      refine EvaluatesInstrs.cons (instrValue := Val.bool (decide (n % div = 0))) ?_ ?_
      · evaluates 100 [heapOpCtx, Op.fixed, isPrimeBlocks]
      apply EvaluatesInstrs.nil
      evaluates 100 [heapOpCtx, Op.fixed, isPrimeBlocks]
  | succ count ih =>
      by_cases hsquare : n < div * div
      · simp only [trialDivisionSqrt, hsquare, ↓reduceIte]
        apply EvaluatesCallValues.of_evaluatesInstrs (block := isPrimeBlocks[3].2) <;> try rfl
        refine EvaluatesInstrs.cons (instrValue := Val.bool false) ?_ ?_
        · exact isPrime_evaluates_remaining_succ_ne_zero (count := count) rfl
        refine EvaluatesInstrs.cons (instrValue := Val.nat (div * div)) ?_ ?_
        · exact evaluates_mul_nat (hM := rfl)
            (EvaluatesTo.var_local (name := "div") (value := Val.nat div) (by rfl))
            (EvaluatesTo.var_local (name := "div") (value := Val.nat div) (by rfl))
        refine EvaluatesInstrs.cons (instrValue := Val.bool true) ?_ ?_
        · simpa [hsquare] using
            (evaluates_lt_nat (ctx := isPrimeCtx) (hM := rfl)
              (EvaluatesTo.var_local (name := "n") (value := Val.nat n) (by rfl))
              (EvaluatesTo.var_local (name := "square") (value := Val.nat (div * div)) (by rfl)))
        refine EvaluatesInstrs.cons (instrValue := Val.nat (n % div)) ?_ ?_
        · exact isPrime_evaluates_mod (EvaluatesTo.var_local (by rfl))
            (EvaluatesTo.var_local (by rfl))
        refine EvaluatesInstrs.cons (instrValue := Val.bool (decide (n % div = 0))) ?_ ?_
        · exact evaluates_eq_nat (hM := rfl)
            (EvaluatesTo.var_local (name := "remainder") (value := Val.nat (n % div)) (by rfl))
            (evaluates_nat (ctx := isPrimeCtx) (hM := rfl) _ 0)
        apply EvaluatesInstrs.nil
        apply isPrime_evaluates_ite_false
        · exact EvaluatesTo.var_local (name := "atLimit") (value := Val.bool false) (by rfl)
        · exact evaluates_bool _ true
        refine isPrime_evaluates_ite_true
          (elseValue := Val.bool (if n % div = 0 then false
            else trialDivisionSqrt n (div + 1) count)) ?_ ?_ ?_
        · exact EvaluatesTo.var_local (name := "pastSquare") (value := Val.bool true) (by rfl)
        · exact evaluates_bool _ true
        by_cases hdiv : n % div = 0
        · simp only [hdiv, ↓reduceIte]
          refine isPrime_evaluates_ite_true
            (elseValue := Val.bool (trialDivisionSqrt n (div + 1) count)) ?_ ?_ ?_
          · exact EvaluatesTo.var_local (name := "divides") (value := Val.bool true) (by rfl)
          · exact evaluates_bool _ false
          apply EvaluatesTo.call (ih (div + 1)) rfl
          exact isPrime_evaluates_next_args (n := n) (div := div) (remaining := count + 1)
            rfl rfl rfl
        · simp only [hdiv, ↓reduceIte]
          refine isPrime_evaluates_ite_false
            (thenValue := Val.bool false)
            (value := Val.bool (trialDivisionSqrt n (div + 1) count)) ?_ ?_ ?_
          · exact EvaluatesTo.var_local (name := "divides") (value := Val.bool false) (by rfl)
          · exact evaluates_bool _ false
          apply EvaluatesTo.call (ih (div + 1)) rfl
          exact isPrime_evaluates_next_args (n := n) (div := div) (remaining := count + 1)
            rfl rfl rfl
      · by_cases hdiv : n % div = 0
        · simp only [trialDivisionSqrt, hsquare, hdiv, ↓reduceIte]
          apply EvaluatesCallValues.of_evaluatesInstrs (block := isPrimeBlocks[3].2) <;> try rfl
          refine EvaluatesInstrs.cons (instrValue := Val.bool false) ?_ ?_
          · exact isPrime_evaluates_remaining_succ_ne_zero (count := count) rfl
          refine EvaluatesInstrs.cons (instrValue := Val.nat (div * div)) ?_ ?_
          · exact evaluates_mul_nat (hM := rfl)
              (EvaluatesTo.var_local (name := "div") (value := Val.nat div) (by rfl))
              (EvaluatesTo.var_local (name := "div") (value := Val.nat div) (by rfl))
          refine EvaluatesInstrs.cons (instrValue := Val.bool false) ?_ ?_
          · simpa [hsquare] using
              (evaluates_lt_nat (ctx := isPrimeCtx) (hM := rfl)
                (EvaluatesTo.var_local (name := "n") (value := Val.nat n) (by rfl))
                (EvaluatesTo.var_local (name := "square") (value := Val.nat (div * div)) (by rfl)))
          refine EvaluatesInstrs.cons (instrValue := Val.nat (n % div)) ?_ ?_
          · exact isPrime_evaluates_mod (EvaluatesTo.var_local (by rfl))
              (EvaluatesTo.var_local (by rfl))
          refine EvaluatesInstrs.cons (instrValue := Val.bool true) ?_ ?_
          · rw [hdiv]
            exact evaluates_eq_nat (hM := rfl)
              (EvaluatesTo.var_local (name := "remainder") (value := Val.nat 0) (by rfl))
              (evaluates_nat (ctx := isPrimeCtx) (hM := rfl) _ 0)
          apply EvaluatesInstrs.nil
          apply isPrime_evaluates_ite_false
          · exact EvaluatesTo.var_local (name := "atLimit") (value := Val.bool false) (by rfl)
          · exact evaluates_bool _ true
          apply isPrime_evaluates_ite_false
          · exact EvaluatesTo.var_local (name := "pastSquare") (value := Val.bool false) (by rfl)
          · exact evaluates_bool _ true
          apply isPrime_evaluates_ite_true
          · exact EvaluatesTo.var_local (name := "divides") (value := Val.bool true) (by rfl)
          · exact evaluates_bool _ false
          apply EvaluatesTo.call (ih (div + 1)) rfl
          exact isPrime_evaluates_next_args (n := n) (div := div) (remaining := count + 1)
            rfl rfl rfl
        · simp only [trialDivisionSqrt, hsquare, hdiv, ↓reduceIte]
          apply EvaluatesCallValues.of_evaluatesInstrs (block := isPrimeBlocks[3].2) <;> try rfl
          refine EvaluatesInstrs.cons (instrValue := Val.bool false) ?_ ?_
          · exact isPrime_evaluates_remaining_succ_ne_zero (count := count) rfl
          refine EvaluatesInstrs.cons (instrValue := Val.nat (div * div)) ?_ ?_
          · exact evaluates_mul_nat (hM := rfl)
              (EvaluatesTo.var_local (name := "div") (value := Val.nat div) (by rfl))
              (EvaluatesTo.var_local (name := "div") (value := Val.nat div) (by rfl))
          refine EvaluatesInstrs.cons (instrValue := Val.bool false) ?_ ?_
          · simpa [hsquare] using
              (evaluates_lt_nat (ctx := isPrimeCtx) (hM := rfl)
                (EvaluatesTo.var_local (name := "n") (value := Val.nat n) (by rfl))
                (EvaluatesTo.var_local (name := "square") (value := Val.nat (div * div)) (by rfl)))
          refine EvaluatesInstrs.cons (instrValue := Val.nat (n % div)) ?_ ?_
          · exact isPrime_evaluates_mod (EvaluatesTo.var_local (by rfl))
              (EvaluatesTo.var_local (by rfl))
          refine EvaluatesInstrs.cons (instrValue := Val.bool false) ?_ ?_
          · simpa [hdiv] using
              (evaluates_eq_nat (ctx := isPrimeCtx) (hM := rfl)
                (EvaluatesTo.var_local (name := "remainder") (value := Val.nat (n % div)) (by rfl))
                (evaluates_nat (ctx := isPrimeCtx) (hM := rfl) _ 0))
          apply EvaluatesInstrs.nil
          apply isPrime_evaluates_ite_false
          · exact EvaluatesTo.var_local (name := "atLimit") (value := Val.bool false) (by rfl)
          · exact evaluates_bool _ true
          apply isPrime_evaluates_ite_false
          · exact EvaluatesTo.var_local (name := "pastSquare") (value := Val.bool false) (by rfl)
          · exact evaluates_bool _ true
          apply isPrime_evaluates_ite_false
          · exact EvaluatesTo.var_local (name := "divides") (value := Val.bool false) (by rfl)
          · exact evaluates_bool _ false
          apply EvaluatesTo.call (ih (div + 1)) rfl
          exact isPrime_evaluates_next_args (n := n) (div := div) (remaining := count + 1)
            rfl rfl rfl

theorem isPrimeLoop_eval (n div count : Nat) :
    Zag.EvaluatesCallValues isPrimeCtx "isPrimeLoop"
      ([Val.nat n, Val.nat div, Val.nat count] : List (Val heapCtx))
      (Singleton.idPre True)
      (Singleton.idPost (· = Val.bool (trialDivisionSqrt n div count))) := by
  simpa [Exact.EvaluatesCallValues, Exact.pre, Exact.post, Singleton.idPre, Singleton.idPost]
    using isPrimeLoop_eval_exact n div count

private theorem isPrime_eval_exact (n : Nat) :
    Exact.EvaluatesCallValues isPrimeCtx "isPrime" ([Val.nat n] : List (Val heapCtx))
      (Val.bool (isPrimeSpec n)) := by
  unfold isPrimeSpec
  by_cases hsmall : n < 2
  · simp only [hsmall, ↓reduceIte]
    apply EvaluatesCallValues.of_evaluatesInstrs (block := isPrimeBlocks[2].2) <;> try rfl
    refine EvaluatesInstrs.cons (instrValue := Val.bool true) ?_ ?_
    · evaluates 100 [heapOpCtx, Op.fixed, isPrimeBlocks, hsmall]
    apply EvaluatesInstrs.nil
    apply isPrime_evaluates_ite_true
    · exact EvaluatesTo.var_local (name := "small") (value := Val.bool true) (by rfl)
    · exact evaluates_bool _ false
    apply EvaluatesTo.call (isPrimeLoop_eval_exact n 2 65534) rfl
    evaluates_to_all 100 [heapOpCtx, Op.fixed, isPrimeBlocks]
  · simp only [hsmall, ↓reduceIte]
    apply EvaluatesCallValues.of_evaluatesInstrs (block := isPrimeBlocks[2].2) <;> try rfl
    refine EvaluatesInstrs.cons (instrValue := Val.bool false) ?_ ?_
    · evaluates 100 [heapOpCtx, Op.fixed, isPrimeBlocks, hsmall]
    apply EvaluatesInstrs.nil
    apply isPrime_evaluates_ite_false
    · exact EvaluatesTo.var_local (name := "small") (value := Val.bool false) (by rfl)
    · exact evaluates_bool _ false
    apply EvaluatesTo.call (isPrimeLoop_eval_exact n 2 65534) rfl
    evaluates_to_all 100 [heapOpCtx, Op.fixed, isPrimeBlocks]

theorem isPrime_eval (n : Nat) :
    Zag.EvaluatesCallValues isPrimeCtx "isPrime" ([Val.nat n] : List (Val heapCtx))
      (Singleton.idPre True)
      (Singleton.idPost (· = Val.bool (isPrimeSpec n))) := by
  simpa [Exact.EvaluatesCallValues, Exact.pre, Exact.post, Singleton.idPre, Singleton.idPost]
    using isPrime_eval_exact n

/-- Standard bounded-divisor characterization of primality over `Nat`. -/
def NatPrime (n : Nat) : Prop :=
  2 ≤ n ∧ ∀ d, 2 ≤ d → d < n → n % d ≠ 0

theorem trialDivision_eq_true (n start count : Nat) :
    trialDivision n start count = true ↔
      ∀ d, start ≤ d → d < start + count → n % d ≠ 0 := by
  induction count generalizing start with
  | zero =>
      constructor
      · intro _ d hd hlt
        omega
      · intro _
        simp [trialDivision]
  | succ count ih =>
      rw [trialDivision]
      by_cases hz : n % start = 0
      · simp only [hz, ↓reduceIte, Bool.false_eq_true, false_iff]
        intro h
        exact (h start (by omega) (by omega)) hz
      · simp only [hz, ↓reduceIte]
        rw [ih]
        constructor
        · intro h d hd hlt
          by_cases heq : d = start
          · simpa [heq] using hz
          · exact h d (by omega) (by omega)
        · intro h d hd hlt
          exact h d (by omega) (by omega)

/-- The exact linear source algorithm decides the independent primality predicate. -/
theorem isPrimeLinearSpec_correct (n : Nat) :
    isPrimeLinearSpec n = true ↔ NatPrime n := by
  by_cases hsmall : n < 2
  · simp [isPrimeLinearSpec, NatPrime, hsmall]
  · rw [isPrimeLinearSpec]
    simp only [hsmall, ↓reduceIte, trialDivision_eq_true, NatPrime]
    constructor
    · intro h
      constructor
      · omega
      · intro d hd hdn
        exact h d hd (by omega)
    · intro h d hd hbound
      exact h.2 d hd (by omega)

/-- The executable linear block decides mathematical primality. -/
theorem isPrimeLinear_correct (n : Nat) :
    ∃ result, Zag.EvaluatesCallValues isPrimeCtx "isPrimeLinear"
        ([Val.nat n] : List (Val heapCtx))
        (Singleton.idPre True)
        (Singleton.idPost (· = Val.bool result)) ∧
      (result = true ↔ NatPrime n) := by
  exact ⟨isPrimeLinearSpec n, isPrimeLinear_eval n, isPrimeLinearSpec_correct n⟩

/-- Independent square-root trial-division characterization used by the faster algorithm. -/
def SqrtPrime (n : Nat) : Prop :=
  2 ≤ n ∧ ∀ d, 2 ≤ d → d * d ≤ n → n % d ≠ 0

theorem trialDivisionSqrt_eq_true (n start count : Nat) :
    trialDivisionSqrt n start count = true ↔
      ∀ d, start ≤ d → d < start + count → d * d ≤ n → n % d ≠ 0 := by
  induction count generalizing start with
  | zero =>
      constructor
      · intro _ d hd hlt
        omega
      · intro _
        simp [trialDivisionSqrt]
  | succ count ih =>
      rw [trialDivisionSqrt]
      by_cases hsquare : n < start * start
      · simp only [hsquare, ↓reduceIte, true_iff]
        intro d hd hlt hsq
        by_cases heq : d = start
        · subst d
          omega
        · have hle : start ≤ d := hd
          have hmul := Nat.mul_le_mul hle hle
          omega
      · simp only [hsquare, ↓reduceIte]
        by_cases hz : n % start = 0
        · simp only [hz, ↓reduceIte, Bool.false_eq_true, false_iff]
          intro h
          exact (h start (by omega) (by omega) (by omega)) hz
        · simp only [hz, ↓reduceIte]
          rw [ih]
          constructor
          · intro h d hd hlt hsq
            by_cases heq : d = start
            · simpa [heq] using hz
            · exact h d (by omega) (by omega) hsq
          · intro h d hd hlt hsq
            exact h d (by omega) (by omega) hsq

/-- In the original 32-bit input range, the faster source algorithm decides square-root
trial-division primality; `65536` is therefore beyond every candidate with `d*d ≤ n`. -/
theorem isPrimeSpec_correct (n : Nat) (h32 : n < 65536 * 65536) :
    isPrimeSpec n = true ↔ SqrtPrime n := by
  by_cases hsmall : n < 2
  · simp [isPrimeSpec, SqrtPrime, hsmall]
  · rw [isPrimeSpec]
    simp only [hsmall, ↓reduceIte, trialDivisionSqrt_eq_true, SqrtPrime]
    constructor
    · intro h
      constructor
      · omega
      · intro d hd hsq
        exact h d hd (by
          have hlt : d < 65536 := by
            by_cases hge : 65536 ≤ d
            · have hmul := Nat.mul_le_mul hge hge
              omega
            · omega
          omega) hsq
    · intro h d hd hbound hsq
      exact h.2 d hd hsq

theorem sqrtPrime_iff_natPrime (n : Nat) : SqrtPrime n ↔ NatPrime n := by
  constructor
  · rintro ⟨hn, hsqrt⟩
    refine ⟨hn, ?_⟩
    intro d hd hdn hdiv
    let q := n / d
    have hdpos : 0 < d := by omega
    have hn_eq : n = d * q := by
      rw [Nat.mul_div_cancel' (Nat.dvd_of_mod_eq_zero hdiv)]
    have hqpos : 0 < q := Nat.div_pos (Nat.le_of_lt hdn) hdpos
    by_cases hdq : d ≤ q
    · have hsq : d * d ≤ n := by
        rw [hn_eq]
        exact Nat.mul_le_mul_left d hdq
      exact hsqrt d hd hsq hdiv
    · have hqd : q < d := by omega
      have hq2 : 2 ≤ q := by
        by_cases hq1 : q = 1
        · rw [hq1, Nat.mul_one] at hn_eq
          omega
        · omega
      have hsq : q * q ≤ n := by
        rw [hn_eq]
        exact Nat.mul_le_mul_right q (Nat.le_of_lt hqd)
      have hqdiv : n % q = 0 := by
        rw [hn_eq, Nat.mul_mod_left]
      exact hsqrt q hq2 hsq hqdiv
  · rintro ⟨hn, hprime⟩
    exact ⟨hn, fun d hd hsq => hprime d hd (by
      have hdouble : d * 2 ≤ d * d := Nat.mul_le_mul_left d hd
      omega)⟩

/-- In the bounded source domain, the executable faster block decides the same independent
mathematical primality predicate as the linear block. -/
theorem isPrime_correct (n : Nat) (hbound : n < 65536 * 65536) :
    ∃ result, Zag.EvaluatesCallValues isPrimeCtx "isPrime" ([Val.nat n] : List (Val heapCtx))
        (Singleton.idPre True)
        (Singleton.idPost (· = Val.bool result)) ∧
      (result = true ↔ NatPrime n) := by
  refine ⟨isPrimeSpec n, isPrime_eval n, ?_⟩
  exact (isPrimeSpec_correct n hbound).trans (sqrtPrime_iff_natPrime n)

end Zag.Test.Autocorres.Examples
