import Test.Autocorres.Examples.Common

/-!
Upstream Isabelle theory:
[`Str2Long.thy`](https://github.com/seL4/l4v/blob/master/tools/autocorres/tests/examples/Str2Long.thy).

The result array is `[error, negative, magnitude]`. The final two cells encode the mathematical
integer `magnitude` when `negative = 0` and `-magnitude` when `negative = 1`; in particular, the C
failure result `-1` is `[1, 1, 1]`. Successful conversion preserves the incoming global `error`
value, while failure sets it to `1`. Array exhaustion acts as an implicit trailing NUL.

**Unsupported:** fixed-width `long` overflow and underflow. Magnitudes use unbounded `Nat`, so the
correctness theorem covers the source parser and persistent error state but not its machine bounds.
-/

namespace Zag.Test.Autocorres.Examples

open Zag Zag.Lib.PeanoHeap
open Zag.EvalTriple
open Zag.EvalTriple.Exact
open scoped Std.Do

private abbrev heapOpCtx := pureHeapOpCtx

abbrev str2longBlocks : BlockCtx.Raw heapCtx :=
  blocks% [
    str2long(chars : Array[Nat], error : Nat) : Array[Nat] {
      len := op "arrayLen"[chars];
      empty := primEq len nat(0);
      ch0 := op "arrayGet"[chars, nat(0)];
      minus := primEq ch0 nat(45);
      remaining := op "sub"[len, nat(1)];
      noDigit := primEq remaining nat(0);
      ch1 := op "arrayGet"[chars, nat(1)];
      nul1 := primEq ch1 nat(0);
      nul0 := primEq ch0 nat(0);
      ret if empty { call parseResult [nat(1), nat(1), nat(1)] }
        else {
          if minus {
            if noDigit {
              call parseResult [nat(1), nat(1), nat(1)]
            } else {
              if nul1 {
                call parseResult [nat(1), nat(1), nat(1)]
              } else {
                call str2longLoop
                  [chars, remaining, nat(1), nat(0), nat(1), error]
              }
            }
          } else {
            if nul0 {
              call parseResult [nat(1), nat(1), nat(1)]
            } else {
              call str2longLoop [chars, len, nat(0), nat(0), nat(0), error]
            }
          }
        }
    },
    str2longLoop(chars : Array[Nat], remaining : Nat, idx : Nat, acc : Nat,
        negative : Nat, error : Nat) : Array[Nat] {
      done := primEq remaining nat(0);
      ch := op "arrayGet"[chars, idx];
      nul := primEq ch nat(0);
      digitOk := op "isDigit"[ch];
      digit := op "digit"[ch];
      ret if done { call parseResult [error, negative, acc] } else {
        if nul {
          call parseResult [error, negative, acc]
        } else {
          if digitOk {
            call str2longLoop [chars, op "sub"[remaining, nat(1)],
              op "add"[idx, nat(1)],
              op "add"[op "mul"[acc, nat(10)], digit], negative, error]
          } else { call parseResult [nat(1), nat(1), nat(1)] }
        }
      }
    },
    parseResult(error : Nat, negative : Nat, magnitude : Nat) : Array[Nat] {
      withError := op "arraySet"[raw(termArray [0, 0, 0]), nat(0), error];
      withSign := op "arraySet"[withError, nat(1), negative];
      ret op "arraySet"[withSign, nat(2), magnitude]
    }
  ]

theorem str2longBlocksValid : BlockCtx.Valid str2longBlocks := by
  valid_blocks [str2longBlocks]

abbrev str2longCtx : Ctx := mkPureCtx str2longBlocks str2longBlocksValid

theorem str2longCtx_wellTyped : Ctx.WellTyped str2longCtx := by
  typecheck_ctx

def parseResultSpec (error negative magnitude : Nat) : HeapArray :=
  [error, negative, magnitude]

def str2longLoopSpec (chars : HeapArray) : Nat → Nat → Nat → Nat → Nat → HeapArray
| 0, _idx, acc, negative, error => parseResultSpec error negative acc
| remaining + 1, idx, acc, negative, error =>
    let ch := HeapArray.get chars idx
    if ch = 0 then parseResultSpec error negative acc
    else if isDigit ch then
      str2longLoopSpec chars remaining (idx + 1)
        (acc * 10 + parseDigit ch) negative error
    else parseResultSpec 1 1 1

def str2longSpec (chars : HeapArray) (error : Nat) : HeapArray :=
  let len := chars.length
  if len = 0 then parseResultSpec 1 1 1
  else
    let ch := HeapArray.get chars 0
    if ch = 45 then
      let remaining := len - 1
      if remaining = 0 ∨ HeapArray.get chars 1 = 0 then parseResultSpec 1 1 1
      else str2longLoopSpec chars remaining 1 0 1 error
    else if ch = 0 then parseResultSpec 1 1 1
    else str2longLoopSpec chars len 0 0 0 error

theorem parsed_digit_lt_ten (code : Nat) (h : isDigit code = true) : parseDigit code < 10 := by
  simp [isDigit] at h
  simp [parseDigit]
  omega

@[simp] theorem str2long_toArray_ofArray (chars : HeapArray) :
    toArray (ofArray chars) = chars := by
  simp [toArray, ofArray, PrimitiveCtx.toPrimitiveValue]

@[eval_semantic] theorem str2long_evaluates_arrayGet {env : Env heapCtx}
    {arrayTerm idxTerm : Term heapCtx} {chars : HeapArray} {idx : Nat}
    (harray : EvaluatesTo str2longCtx env arrayTerm (valArray chars))
    (hidx : EvaluatesTo str2longCtx env idxTerm (Val.nat idx)) :
    EvaluatesTo str2longCtx env (.op "arrayGet" [arrayTerm, idxTerm])
      (Val.nat (HeapArray.get chars idx)) := by
  refine EvaluatesTo.op_applyVals (oper := arrayGetOp) rfl
    (EvaluatesList.cons harray (EvaluatesList.cons hidx EvaluatesList.nil)) ?_
  simp [Op.applyValsAt, Op.fixed, arrayGetOp, Op.ofVals, Op.Body.applyVals, Op.Body.eager,
    asArray?, valArray]

@[eval_semantic] theorem str2long_evaluates_arrayLen {env : Env heapCtx}
    {arrayTerm : Term heapCtx} {chars : HeapArray}
    (harray : EvaluatesTo str2longCtx env arrayTerm (valArray chars)) :
    EvaluatesTo str2longCtx env (.op "arrayLen" [arrayTerm]) (Val.nat chars.length) := by
  refine EvaluatesTo.op_applyVals (oper := arrayLenOp) rfl
    (EvaluatesList.cons harray EvaluatesList.nil) ?_
  simp [Op.applyValsAt, Op.fixed, arrayLenOp, Op.ofVals, Op.Body.applyVals, Op.Body.eager,
    asArray?, valArray]

@[eval_semantic] theorem str2long_evaluates_arraySet {env : Env heapCtx}
    {arrayTerm idxTerm valueTerm : Term heapCtx} {chars : HeapArray} {idx value : Nat}
    (harray : EvaluatesTo str2longCtx env arrayTerm (valArray chars))
    (hidx : EvaluatesTo str2longCtx env idxTerm (Val.nat idx))
    (hvalue : EvaluatesTo str2longCtx env valueTerm (Val.nat value)) :
    EvaluatesTo str2longCtx env (.op "arraySet" [arrayTerm, idxTerm, valueTerm])
      (valArray (HeapArray.set chars idx value)) := by
  refine EvaluatesTo.op_applyVals (oper := arraySetOp) rfl
    (EvaluatesList.cons harray (EvaluatesList.cons hidx
      (EvaluatesList.cons hvalue EvaluatesList.nil))) ?_
  simp [Op.applyValsAt, Op.fixed, arraySetOp, Op.ofVals, Op.Body.applyVals, Op.Body.eager,
    asArray?, valArray]

@[eval_semantic] theorem str2long_evaluates_isDigit {env : Env heapCtx}
    {term : Term heapCtx} {code : Nat}
    (hterm : EvaluatesTo str2longCtx env term (Val.nat code)) :
    EvaluatesTo str2longCtx env (.op "isDigit" [term]) (Val.bool (isDigit code)) := by
  refine EvaluatesTo.op_applyVals rfl (EvaluatesList.cons hterm EvaluatesList.nil) ?_
  simp [Op.applyValsAt, Op.fixed, Op.ofVals, Op.Body.applyVals, Op.Body.eager]

@[eval_semantic] theorem str2long_evaluates_digit {env : Env heapCtx}
    {term : Term heapCtx} {code : Nat}
    (hterm : EvaluatesTo str2longCtx env term (Val.nat code)) :
    EvaluatesTo str2longCtx env (.op "digit" [term]) (Val.nat (parseDigit code)) := by
  refine EvaluatesTo.op_applyVals rfl (EvaluatesList.cons hterm EvaluatesList.nil) ?_
  simp [Op.applyValsAt, Op.fixed, unaryNatOp, Op.ofVals, Op.Body.applyVals,
    Op.Body.eager]

private theorem parseResult_eval_exact (error negative magnitude : Nat) :
    Exact.EvaluatesCallValues str2longCtx "parseResult"
      ([Val.nat error, Val.nat negative, Val.nat magnitude] : List (Val heapCtx))
      (valArray (parseResultSpec error negative magnitude)) := by
  evaluates_call 500
    [heapOpCtx, Op.fixed, str2longBlocks, parseResultSpec, arraySetOp, Op.ofVals,
      Op.Body.eager, asArray?, valArray, ofArray]

theorem parseResult_eval (error negative magnitude : Nat) :
    Zag.EvaluatesCallValues str2longCtx "parseResult"
      ([Val.nat error, Val.nat negative, Val.nat magnitude] : List (Val heapCtx))
      (Singleton.idPre True)
      (Singleton.idPost (· = valArray (parseResultSpec error negative magnitude))) := by
  simpa [Exact.EvaluatesCallValues, Exact.pre, Exact.post, Singleton.idPre, Singleton.idPost]
    using parseResult_eval_exact error negative magnitude

local macro "prove_str2long_instrs" "(" chars:term ")" : tactic => `(tactic| (
  apply EvaluatesCallValues.of_evaluatesInstrs (block := str2longBlocks[0].2) <;> try rfl
  refine EvaluatesInstrs.cons (instrValue := Val.nat ($chars).length) ?_ ?_
  · exact str2long_evaluates_arrayLen (EvaluatesTo.var_local (name := "chars") (by rfl))
  refine EvaluatesInstrs.cons (instrValue := Val.bool (decide (($chars).length = 0))) ?_ ?_
  · evaluates 100 [heapOpCtx, Op.fixed, str2longBlocks]
  refine EvaluatesInstrs.cons (instrValue := Val.nat (HeapArray.get $chars 0)) ?_ ?_
  · exact str2long_evaluates_arrayGet
      (EvaluatesTo.var_local (name := "chars") (by rfl)) (evaluates_nat _ 0)
  refine EvaluatesInstrs.cons
      (instrValue := Val.bool (decide (HeapArray.get $chars 0 = 45))) ?_ ?_
  · evaluates 100 [heapOpCtx, Op.fixed, str2longBlocks]
  refine EvaluatesInstrs.cons (instrValue := Val.nat (($chars).length - 1)) ?_ ?_
  · evaluates 100 [heapOpCtx, Op.fixed, str2longBlocks]
  refine EvaluatesInstrs.cons
      (instrValue := Val.bool (decide (($chars).length - 1 = 0))) ?_ ?_
  · evaluates 100 [heapOpCtx, Op.fixed, str2longBlocks]
  refine EvaluatesInstrs.cons (instrValue := Val.nat (HeapArray.get $chars 1)) ?_ ?_
  · exact str2long_evaluates_arrayGet
      (EvaluatesTo.var_local (name := "chars") (by rfl)) (evaluates_nat _ 1)
  refine EvaluatesInstrs.cons
      (instrValue := Val.bool (decide (HeapArray.get $chars 1 = 0))) ?_ ?_
  · evaluates 100 [heapOpCtx, Op.fixed, str2longBlocks]
  refine EvaluatesInstrs.cons
      (instrValue := Val.bool (decide (HeapArray.get $chars 0 = 0))) ?_ ?_
  · evaluates 100 [heapOpCtx, Op.fixed, str2longBlocks]
  apply EvaluatesInstrs.nil))

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem str2longLoop_eval_exact (chars : HeapArray)
    (remaining idx acc negative error : Nat) :
    Exact.EvaluatesCallValues str2longCtx "str2longLoop"
      ([valArray chars, Val.nat remaining, Val.nat idx, Val.nat acc, Val.nat negative,
        Val.nat error] : List (Val heapCtx))
      (valArray (str2longLoopSpec chars remaining idx acc negative error)) := by
  induction remaining generalizing idx acc with
  | zero =>
      change Exact.EvaluatesCallValues str2longCtx "str2longLoop"
        ([valArray chars, Val.nat 0, Val.nat idx, Val.nat acc, Val.nat negative,
          Val.nat error] : List (Val heapCtx))
        (valArray (parseResultSpec error negative acc))
      apply EvaluatesCallValues.of_evaluatesInstrs (block := str2longBlocks[1].2) <;> try rfl
      dsimp [str2longBlocks, Block.entryEnv]
      refine EvaluatesInstrs.cons (instrValue := Val.bool true) ?_ ?_
      · evaluates 100 [heapOpCtx, Op.fixed, str2longBlocks]
      refine EvaluatesInstrs.cons
        (instrValue := Val.nat (HeapArray.get chars idx)) ?_ ?_
      · exact str2long_evaluates_arrayGet
          (EvaluatesTo.var_local (name := "chars") (by rfl))
          (EvaluatesTo.var_local (name := "idx") (by rfl))
      refine EvaluatesInstrs.cons
        (instrValue := Val.bool (decide (HeapArray.get chars idx = 0))) ?_ ?_
      · evaluates 100 [heapOpCtx, Op.fixed, str2longBlocks]
      refine EvaluatesInstrs.cons
        (instrValue := Val.bool (isDigit (HeapArray.get chars idx))) ?_ ?_
      · exact str2long_evaluates_isDigit (EvaluatesTo.var_local (name := "ch") (by rfl))
      refine EvaluatesInstrs.cons
        (instrValue := Val.nat (parseDigit (HeapArray.get chars idx))) ?_ ?_
      · exact str2long_evaluates_digit (EvaluatesTo.var_local (name := "ch") (by rfl))
      apply EvaluatesInstrs.nil
      evaluates 300 [heapOpCtx, Op.fixed, str2longBlocks]
      zspec_call 300 [heapOpCtx, Op.fixed, str2longBlocks]
        (parseResult_eval_exact error negative acc)
  | succ remaining ih =>
      by_cases hnul : HeapArray.get chars idx = 0
      · simp only [str2longLoopSpec, hnul, ↓reduceIte]
        apply EvaluatesCallValues.of_evaluatesInstrs (block := str2longBlocks[1].2) <;> try rfl
        dsimp [str2longBlocks, Block.entryEnv]
        refine EvaluatesInstrs.cons (instrValue := Val.bool false) ?_ ?_
        · evaluates 100 [heapOpCtx, Op.fixed, str2longBlocks]
        refine EvaluatesInstrs.cons
          (instrValue := Val.nat (HeapArray.get chars idx)) ?_ ?_
        · exact str2long_evaluates_arrayGet
            (EvaluatesTo.var_local (name := "chars") (by rfl))
            (EvaluatesTo.var_local (name := "idx") (by rfl))
        refine EvaluatesInstrs.cons (instrValue := Val.bool true) ?_ ?_
        · evaluates 100 [heapOpCtx, Op.fixed, str2longBlocks, hnul]
        refine EvaluatesInstrs.cons
          (instrValue := Val.bool (isDigit (HeapArray.get chars idx))) ?_ ?_
        · exact str2long_evaluates_isDigit (EvaluatesTo.var_local (name := "ch") (by rfl))
        refine EvaluatesInstrs.cons
          (instrValue := Val.nat (parseDigit (HeapArray.get chars idx))) ?_ ?_
        · exact str2long_evaluates_digit (EvaluatesTo.var_local (name := "ch") (by rfl))
        apply EvaluatesInstrs.nil
        evaluates 300 [heapOpCtx, Op.fixed, str2longBlocks, hnul]
        zspec_call 300 [heapOpCtx, Op.fixed, str2longBlocks]
          (parseResult_eval_exact error negative acc)
      · by_cases hdigit : isDigit (HeapArray.get chars idx) = true
        · simp only [str2longLoopSpec, hnul, hdigit, ↓reduceIte]
          have hmul : 10 * acc = acc * 10 := Nat.mul_comm 10 acc
          have hrecursive :=
            ih (idx + 1) (10 * acc + parseDigit (HeapArray.get chars idx))
          have hrecursive' :
              Exact.EvaluatesCallValues str2longCtx "str2longLoop"
                ([valArray chars, Val.nat remaining, Val.nat (idx + 1),
                  Val.nat (10 * acc + parseDigit (HeapArray.get chars idx)), Val.nat negative,
                  Val.nat error] : List (Val heapCtx))
                (valArray (str2longLoopSpec chars remaining (idx + 1)
                  (acc * 10 + parseDigit (HeapArray.get chars idx)) negative error)) := by
            apply EvaluatesCallValues.of_eq hrecursive
            rw [hmul]
          apply EvaluatesCallValues.of_evaluatesInstrs (block := str2longBlocks[1].2) <;> try rfl
          dsimp [str2longBlocks, Block.entryEnv]
          refine EvaluatesInstrs.cons (instrValue := Val.bool false) ?_ ?_
          · evaluates 100 [heapOpCtx, Op.fixed, str2longBlocks]
          refine EvaluatesInstrs.cons
            (instrValue := Val.nat (HeapArray.get chars idx)) ?_ ?_
          · exact str2long_evaluates_arrayGet
              (EvaluatesTo.var_local (name := "chars") (by rfl))
              (EvaluatesTo.var_local (name := "idx") (by rfl))
          refine EvaluatesInstrs.cons (instrValue := Val.bool false) ?_ ?_
          · evaluates 100 [heapOpCtx, Op.fixed, str2longBlocks, hnul]
          refine EvaluatesInstrs.cons (instrValue := Val.bool true) ?_ ?_
          · simpa [hdigit] using
              str2long_evaluates_isDigit
                (EvaluatesTo.var_local (ctx := str2longCtx) (hM := rfl) (name := "ch")
                  (value := Val.nat (HeapArray.get chars idx)) (by rfl))
          refine EvaluatesInstrs.cons
            (instrValue := Val.nat (parseDigit (HeapArray.get chars idx))) ?_ ?_
          · exact str2long_evaluates_digit (EvaluatesTo.var_local (name := "ch") (by rfl))
          apply EvaluatesInstrs.nil
          evaluates 300 [heapOpCtx, Op.fixed, str2longBlocks, hnul, hdigit]
          zspec_call 300 [heapOpCtx, Op.fixed, str2longBlocks, hnul, hdigit] hrecursive'
        · have hdigitFalse : isDigit (HeapArray.get chars idx) = false := by
            cases hvalue : isDigit (HeapArray.get chars idx) <;> simp_all
          simp only [str2longLoopSpec, hnul, hdigitFalse, ↓reduceIte]
          apply EvaluatesCallValues.of_evaluatesInstrs (block := str2longBlocks[1].2) <;> try rfl
          dsimp [str2longBlocks, Block.entryEnv]
          refine EvaluatesInstrs.cons (instrValue := Val.bool false) ?_ ?_
          · evaluates 100 [heapOpCtx, Op.fixed, str2longBlocks]
          refine EvaluatesInstrs.cons
            (instrValue := Val.nat (HeapArray.get chars idx)) ?_ ?_
          · exact str2long_evaluates_arrayGet
              (EvaluatesTo.var_local (name := "chars") (by rfl))
              (EvaluatesTo.var_local (name := "idx") (by rfl))
          refine EvaluatesInstrs.cons (instrValue := Val.bool false) ?_ ?_
          · evaluates 100 [heapOpCtx, Op.fixed, str2longBlocks, hnul]
          refine EvaluatesInstrs.cons (instrValue := Val.bool false) ?_ ?_
          · simpa [hdigitFalse] using
              str2long_evaluates_isDigit
                (EvaluatesTo.var_local (ctx := str2longCtx) (hM := rfl) (name := "ch")
                  (value := Val.nat (HeapArray.get chars idx)) (by rfl))
          refine EvaluatesInstrs.cons
            (instrValue := Val.nat (parseDigit (HeapArray.get chars idx))) ?_ ?_
          · exact str2long_evaluates_digit (EvaluatesTo.var_local (name := "ch") (by rfl))
          apply EvaluatesInstrs.nil
          evaluates 300 [heapOpCtx, Op.fixed, str2longBlocks, hnul, hdigitFalse]
          zspec_call 300 [heapOpCtx, Op.fixed, str2longBlocks] (parseResult_eval_exact 1 1 1)

theorem str2longLoop_eval (chars : HeapArray) (remaining idx acc negative error : Nat) :
    Zag.EvaluatesCallValues str2longCtx "str2longLoop"
      ([valArray chars, Val.nat remaining, Val.nat idx, Val.nat acc, Val.nat negative,
        Val.nat error] : List (Val heapCtx))
      (Singleton.idPre True)
      (Singleton.idPost
        (· = valArray (str2longLoopSpec chars remaining idx acc negative error))) := by
  simpa [Exact.EvaluatesCallValues, Exact.pre, Exact.post, Singleton.idPre, Singleton.idPost]
    using str2longLoop_eval_exact chars remaining idx acc negative error

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem str2long_eval_exact (chars : HeapArray) (error : Nat) :
    Exact.EvaluatesCallValues str2longCtx "str2long"
      ([valArray chars, Val.nat error] : List (Val heapCtx))
      (valArray (str2longSpec chars error)) := by
  by_cases hempty : chars.length = 0
  · simp only [str2longSpec, hempty, ↓reduceIte]
    prove_str2long_instrs (chars)
    evaluates 300 [heapOpCtx, Op.fixed, str2longBlocks, hempty]
    zspec_call 300 [heapOpCtx, Op.fixed, str2longBlocks] (parseResult_eval_exact 1 1 1)
  · by_cases hminus : HeapArray.get chars 0 = 45
    · by_cases hremaining : chars.length - 1 = 0
      · simp only [str2longSpec, hempty, hminus, hremaining, true_or, ↓reduceIte]
        prove_str2long_instrs (chars)
        evaluates 300 [heapOpCtx, Op.fixed, str2longBlocks, hempty, hminus, hremaining]
        zspec_call 300 [heapOpCtx, Op.fixed, str2longBlocks] (parseResult_eval_exact 1 1 1)
      · by_cases hnul : HeapArray.get chars 1 = 0
        · simp only [str2longSpec, hempty, hminus, hremaining, hnul, or_true,
            ↓reduceIte]
          prove_str2long_instrs (chars)
          evaluates 300
            [heapOpCtx, Op.fixed, str2longBlocks, hempty, hminus, hremaining, hnul]
          zspec_call 300 [heapOpCtx, Op.fixed, str2longBlocks] (parseResult_eval_exact 1 1 1)
        · simp only [str2longSpec, hempty, hminus, hremaining, hnul, or_false,
            ↓reduceIte]
          prove_str2long_instrs (chars)
          evaluates 300
            [heapOpCtx, Op.fixed, str2longBlocks, hempty, hminus, hremaining, hnul]
          zspec_call 300 [heapOpCtx, Op.fixed, str2longBlocks]
            (str2longLoop_eval_exact chars (chars.length - 1) 1 0 1 error)
    · have hminusFalse : decide (HeapArray.get chars 0 = 45) = false :=
        decide_eq_false hminus
      by_cases hnul : HeapArray.get chars 0 = 0
      · simp only [str2longSpec, hempty, hnul, ↓reduceIte]
        prove_str2long_instrs (chars)
        evaluates 300 [heapOpCtx, Op.fixed, str2longBlocks, hempty, hminusFalse, hnul]
        zspec_call 300 [heapOpCtx, Op.fixed, str2longBlocks] (parseResult_eval_exact 1 1 1)
      · simp only [str2longSpec, hempty, hminus, hnul, ↓reduceIte]
        have hnulFalse : decide (HeapArray.get chars 0 = 0) = false := decide_eq_false hnul
        prove_str2long_instrs (chars)
        evaluates 300
          [heapOpCtx, Op.fixed, str2longBlocks, hempty, hminusFalse, hnulFalse]
        zspec_call 300 [heapOpCtx, Op.fixed, str2longBlocks]
          (str2longLoop_eval_exact chars chars.length 0 0 0 error)

theorem str2long_eval (chars : HeapArray) (error : Nat) :
    Zag.EvaluatesCallValues str2longCtx "str2long"
      ([valArray chars, Val.nat error] : List (Val heapCtx))
      (Singleton.idPre True)
      (Singleton.idPost (· = valArray (str2longSpec chars error))) := by
  simpa [Exact.EvaluatesCallValues, Exact.pre, Exact.post, Singleton.idPre, Singleton.idPost]
    using str2long_eval_exact chars error

def runStr2Long (chars : HeapArray) (error : Nat) : Option HeapArray :=
  (Machine.evalFuel str2longCtx 10000 []
    (.call "str2long" [termArray chars, .nat error])).run.bind asArray?

#guard runStr2Long [] 0 = some [1, 1, 1]
#guard runStr2Long [0] 4 = some [1, 1, 1]
#guard runStr2Long [45, 0] 4 = some [1, 1, 1]
#guard runStr2Long [45, 49, 50, 0] 7 = some [7, 1, 12]
#guard runStr2Long [49, 120, 0] 7 = some [1, 1, 1]
#guard runStr2Long [52, 50, 0, 57] 3 = some [3, 0, 42]
#guard runStr2Long [49, 50] 9 = some [9, 0, 12]

end Zag.Test.Autocorres.Examples
