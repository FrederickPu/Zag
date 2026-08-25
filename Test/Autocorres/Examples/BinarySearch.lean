import Test.Autocorres.Examples.Common

/-!
Upstream Isabelle theory:
[`BinarySearch.thy`](https://github.com/seL4/l4v/blob/master/tools/autocorres/tests/examples/BinarySearch.thy).

This module models the lifted algorithm over `Nat` and a functional `List Nat` array. Arithmetic
does not wrap, and array access is total with zero outside the list; all semantic theorems below
therefore assume the in-bounds interval established by `binarySearch`. It does not model C words,
pointers, validity predicates, or typed memory.
-/

namespace Zag.Test.Autocorres.Examples

open Zag Zag.Lib.PeanoHeap
open Zag.EvalTriple
open Zag.EvalTriple.Exact
open scoped Std.Do

private abbrev heapOpCtx := pureHeapOpCtx

abbrev binarySearchBlocks : BlockCtx.Raw heapCtx :=
  blocks% [
    binarySearch(xs : Array[Nat], needle : Nat) : Bool {
      len := op "arrayLen"[xs];
      ret call binarySearchLoop [xs, needle, nat(0), len]
    },
    binarySearchLoop(xs : Array[Nat], needle : Nat, low : Nat, high : Nat) : Bool {
      empty := op "le"[high, low];
      ret if empty { bool(false) }
        else { call binarySearchStep [xs, needle, low, high] }
    },
    binarySearchStep(xs : Array[Nat], needle : Nat, low : Nat, high : Nat) : Bool {
      mid := op "div"[op "add"[low, high], nat(2)];
      value := op "arrayGet"[xs, mid];
      found := primEq value needle;
      goRight := op "lt"[value, needle];
      ret if found { bool(true) } else {
        if goRight { call binarySearchLoop [xs, needle, op "add"[mid, nat(1)], high] }
        else { call binarySearchLoop [xs, needle, low, mid] }
      }
    }
  ]

theorem binarySearchBlocksValid : BlockCtx.Valid binarySearchBlocks := by
  valid_blocks [binarySearchBlocks]

abbrev binarySearchCtx : Ctx := mkPureCtx binarySearchBlocks binarySearchBlocksValid

theorem binarySearchCtx_wellTyped : Ctx.WellTyped binarySearchCtx := by
  typecheck_ctx

@[simp] theorem binarySearch_toArray_ofArray (xs : HeapArray) :
    toArray (ofArray xs) = xs := by
  simp [toArray, ofArray, PrimitiveCtx.toPrimitiveValue]

@[eval_semantic] theorem binarySearch_evaluates_arrayGet {env : Env heapCtx}
    {arrayTerm idxTerm : Term heapCtx} {xs : HeapArray} {idx : Nat}
    (harray : EvaluatesTo binarySearchCtx env arrayTerm (valArray xs))
    (hidx : EvaluatesTo binarySearchCtx env idxTerm (Val.nat idx)) :
    EvaluatesTo binarySearchCtx env (.op "arrayGet" [arrayTerm, idxTerm])
      (Val.nat (HeapArray.get xs idx)) := by
  refine EvaluatesTo.op_applyVals (oper := arrayGetOp) rfl
    (EvaluatesList.cons harray (EvaluatesList.cons hidx EvaluatesList.nil)) ?_
  simp [Op.applyValsAt, Op.fixed, arrayGetOp, Op.ofVals, Op.Body.applyVals, Op.Body.eager,
    asArray?, valArray]

@[eval_semantic] theorem binarySearch_evaluates_arrayLen {env : Env heapCtx}
    {arrayTerm : Term heapCtx} {xs : HeapArray}
    (harray : EvaluatesTo binarySearchCtx env arrayTerm (valArray xs)) :
    EvaluatesTo binarySearchCtx env (.op "arrayLen" [arrayTerm]) (Val.nat xs.length) := by
  refine EvaluatesTo.op_applyVals (oper := arrayLenOp) rfl
    (EvaluatesList.cons harray EvaluatesList.nil) ?_
  simp [Op.applyValsAt, Op.fixed, arrayLenOp, Op.ofVals, Op.Body.applyVals, Op.Body.eager,
    asArray?, valArray]

@[eval_semantic] theorem binarySearch_evaluates_le {env : Env heapCtx}
    {lhsTerm rhsTerm : Term heapCtx} {lhs rhs : Nat}
    (hlhs : EvaluatesTo binarySearchCtx env lhsTerm (Val.nat lhs))
    (hrhs : EvaluatesTo binarySearchCtx env rhsTerm (Val.nat rhs)) :
    EvaluatesTo binarySearchCtx env (.op "le" [lhsTerm, rhsTerm])
      (Val.bool (decide (lhs ≤ rhs))) := by
  refine EvaluatesTo.op_applyVals (oper := binaryNatBoolOp fun a b => decide (a ≤ b)) rfl
    (EvaluatesList.cons hlhs (EvaluatesList.cons hrhs EvaluatesList.nil)) ?_
  simp [Op.applyValsAt, Op.fixed, binaryNatBoolOp, Op.ofVals, Op.Body.applyVals,
    Op.Body.eager]

theorem binarySearch_evaluates_ite_true {env : Env heapCtx}
    {conditionTerm thenTerm elseTerm : Term heapCtx} {value elseValue : Val heapCtx}
    (hcondition : EvaluatesTo binarySearchCtx env conditionTerm (Val.bool true))
    (hthen : EvaluatesTo binarySearchCtx env thenTerm value)
    (helse : EvaluatesTo binarySearchCtx env elseTerm elseValue) :
    EvaluatesTo binarySearchCtx env (Term.ite conditionTerm thenTerm elseTerm) value := by
  refine EvaluatesTo.op_applyVals (oper := Op.ite) Peano.Model.iteOp
    (EvaluatesList.cons hcondition
      (EvaluatesList.cons hthen (EvaluatesList.cons helse EvaluatesList.nil))) ?_
  simp [Op.applyValsAt, Op.ite, Op.fixed, Op.Body.applyVals]

theorem binarySearch_evaluates_ite_false {env : Env heapCtx}
    {conditionTerm thenTerm elseTerm : Term heapCtx} {thenValue value : Val heapCtx}
    (hcondition : EvaluatesTo binarySearchCtx env conditionTerm (Val.bool false))
    (hthen : EvaluatesTo binarySearchCtx env thenTerm thenValue)
    (helse : EvaluatesTo binarySearchCtx env elseTerm value) :
    EvaluatesTo binarySearchCtx env (Term.ite conditionTerm thenTerm elseTerm) value := by
  refine EvaluatesTo.op_applyVals (oper := Op.ite) Peano.Model.iteOp
    (EvaluatesList.cons hcondition
      (EvaluatesList.cons hthen (EvaluatesList.cons helse EvaluatesList.nil))) ?_
  simp [Op.applyValsAt, Op.ite, Op.fixed, Op.Body.applyVals]

/-- Index-based sortedness for the functional array model. -/
def SortedArray (xs : HeapArray) : Prop :=
  ∀ i j, i ≤ j → j < xs.length → HeapArray.get xs i ≤ HeapArray.get xs j

def InArrayRange (xs : HeapArray) (needle low high : Nat) : Prop :=
  ∃ i, low ≤ i ∧ i < high ∧ HeapArray.get xs i = needle

/-- Pure big-step semantics of the source loop. It is separate from both membership and sortedness,
so the correctness theorem below does not define success to mean its desired postcondition. -/
inductive BinarySearchResult (xs : HeapArray) (needle : Nat) : Nat → Nat → Bool → Prop
| empty {low high} (h : high ≤ low) : BinarySearchResult xs needle low high false
| found {low high} (h : low < high)
    (heq : HeapArray.get xs ((low + high) / 2) = needle) :
    BinarySearchResult xs needle low high true
| right {low high} (h : low < high)
    (hlt : HeapArray.get xs ((low + high) / 2) < needle)
    (next : BinarySearchResult xs needle ((low + high) / 2 + 1) high result) :
    BinarySearchResult xs needle low high result
| left {low high} (h : low < high)
    (hlt : needle < HeapArray.get xs ((low + high) / 2))
    (next : BinarySearchResult xs needle low ((low + high) / 2) result) :
    BinarySearchResult xs needle low high result

local macro "prove_binary_loop_instrs" "(" high:term "," low:term ")" : tactic => `(tactic| (
  apply EvaluatesCallValues.of_evaluatesInstrs (block := binarySearchBlocks[1].2) <;> try rfl
  refine EvaluatesInstrs.cons (instrValue := Val.bool (decide ($high ≤ $low))) ?_ ?_
  · exact binarySearch_evaluates_le
      (EvaluatesTo.var_local (name := "high") (by rfl))
      (EvaluatesTo.var_local (name := "low") (by rfl))
  apply EvaluatesInstrs.nil))

local macro "prove_binary_step_instrs" "(" xs:term "," needle:term "," low:term "," high:term ")" : tactic => `(tactic| (
  apply EvaluatesCallValues.of_evaluatesInstrs (block := binarySearchBlocks[2].2) <;> try rfl
  refine EvaluatesInstrs.cons (instrValue := Val.nat (($low + $high) / 2)) ?_ ?_
  · evaluates 100 [heapOpCtx, Op.fixed, binarySearchBlocks]
  refine EvaluatesInstrs.cons
      (instrValue := Val.nat (HeapArray.get $xs (($low + $high) / 2))) ?_ ?_
  · exact binarySearch_evaluates_arrayGet
      (EvaluatesTo.var_local (name := "xs") (by rfl))
      (EvaluatesTo.var_local (name := "mid") (by rfl))
  refine EvaluatesInstrs.cons
      (instrValue := Val.bool (decide (HeapArray.get $xs (($low + $high) / 2) = $needle))) ?_ ?_
  · evaluates 100 [heapOpCtx, Op.fixed, binarySearchBlocks]
  refine EvaluatesInstrs.cons
      (instrValue := Val.bool (decide (HeapArray.get $xs (($low + $high) / 2) < $needle))) ?_ ?_
  · evaluates 100 [heapOpCtx, Op.fixed, binarySearchBlocks]
  apply EvaluatesInstrs.nil
  refine EvaluatesTo.ofEvaluatesFrom ?_))

set_option maxRecDepth 10000 in
set_option maxHeartbeats 1000000 in
/-- Private Exact spine for the fuel induction. -/
private theorem binarySearchLoop_result_exact (fuel : Nat) (xs : HeapArray) (needle low high : Nat)
    (hhigh : high ≤ xs.length) (hfuel : high - low ≤ fuel) :
    ∃ result, BinarySearchResult xs needle low high result ∧
      Exact.EvaluatesCallValues binarySearchCtx "binarySearchLoop"
        ([valArray xs, Val.nat needle, Val.nat low, Val.nat high] : List (Val heapCtx))
        (Val.bool result) := by
  induction fuel generalizing low high with
  | zero =>
      have hempty : high ≤ low := by omega
      refine ⟨false, .empty hempty, ?_⟩
      prove_binary_loop_instrs (high, low)
      evaluates 100 [heapOpCtx, Op.fixed, binarySearchBlocks, hempty]
  | succ fuel ih =>
      by_cases hempty : high ≤ low
      · refine ⟨false, .empty hempty, ?_⟩
        prove_binary_loop_instrs (high, low)
        evaluates 100 [heapOpCtx, Op.fixed, binarySearchBlocks, hempty]
      · have hnonempty : low < high := by omega
        let mid := (low + high) / 2
        have hmidLow : low ≤ mid := by
          dsimp [mid]
          omega
        have hmidHigh : mid < high := by
          dsimp [mid]
          omega
        have hrightFuel : high - (mid + 1) ≤ fuel := by omega
        obtain ⟨rightResult, hrightResult, hrightEval⟩ :=
          ih (mid + 1) high hhigh hrightFuel
        have hleftFuel : mid - low ≤ fuel := by omega
        obtain ⟨leftResult, hleftResult, hleftEval⟩ :=
          ih low mid (Nat.le_trans (Nat.le_of_lt hmidHigh) hhigh) hleftFuel
        by_cases hfound : HeapArray.get xs mid = needle
        · have hstep : Exact.EvaluatesCallValues binarySearchCtx "binarySearchStep"
              ([valArray xs, Val.nat needle, Val.nat low, Val.nat high] :
                List (Val heapCtx)) (Val.bool true) := by
            prove_binary_step_instrs (xs, needle, low, high)
            apply binarySearch_evaluates_ite_true
            · evaluates 100 [heapOpCtx, Op.fixed, binarySearchBlocks, mid, hfound]
            · exact evaluates_bool _ true
            apply binarySearch_evaluates_ite_false
            · evaluates 100 [heapOpCtx, Op.fixed, binarySearchBlocks, mid, hfound]
            · zspec_call 100 [heapOpCtx, Op.fixed, binarySearchBlocks, mid] hrightEval
            · zspec_call 100 [heapOpCtx, Op.fixed, binarySearchBlocks, mid] hleftEval
          refine ⟨true, .found hnonempty (by simpa [mid] using hfound), ?_⟩
          prove_binary_loop_instrs (high, low)
          apply binarySearch_evaluates_ite_false
          · evaluates 100 [heapOpCtx, Op.fixed, binarySearchBlocks, hempty]
          · exact evaluates_bool _ false
          · zspec_call 100 [heapOpCtx, Op.fixed, binarySearchBlocks] hstep
        · by_cases hright : HeapArray.get xs mid < needle
          · have hstep : Exact.EvaluatesCallValues binarySearchCtx "binarySearchStep"
                ([valArray xs, Val.nat needle, Val.nat low, Val.nat high] :
                  List (Val heapCtx)) (Val.bool rightResult) := by
              prove_binary_step_instrs (xs, needle, low, high)
              apply binarySearch_evaluates_ite_false
              · evaluates 100 [heapOpCtx, Op.fixed, binarySearchBlocks, mid, hfound]
              · exact evaluates_bool _ true
              apply binarySearch_evaluates_ite_true
              · evaluates 100 [heapOpCtx, Op.fixed, binarySearchBlocks, mid, hright]
              · zspec_call 100 [heapOpCtx, Op.fixed, binarySearchBlocks, mid] hrightEval
              · zspec_call 100 [heapOpCtx, Op.fixed, binarySearchBlocks, mid] hleftEval
            refine ⟨rightResult,
              .right hnonempty (by simpa [mid] using hright) hrightResult, ?_⟩
            prove_binary_loop_instrs (high, low)
            apply binarySearch_evaluates_ite_false
            · evaluates 100 [heapOpCtx, Op.fixed, binarySearchBlocks, hempty]
            · exact evaluates_bool _ false
            · zspec_call 100 [heapOpCtx, Op.fixed, binarySearchBlocks] hstep
          · have hleft : needle < HeapArray.get xs mid := by omega
            have hstep : Exact.EvaluatesCallValues binarySearchCtx "binarySearchStep"
                ([valArray xs, Val.nat needle, Val.nat low, Val.nat high] :
                  List (Val heapCtx)) (Val.bool leftResult) := by
              prove_binary_step_instrs (xs, needle, low, high)
              apply binarySearch_evaluates_ite_false
              · evaluates 100 [heapOpCtx, Op.fixed, binarySearchBlocks, mid, hfound]
              · exact evaluates_bool _ true
              apply binarySearch_evaluates_ite_false
              · evaluates 100 [heapOpCtx, Op.fixed, binarySearchBlocks, mid, hright]
              · zspec_call 100 [heapOpCtx, Op.fixed, binarySearchBlocks, mid] hrightEval
              · zspec_call 100 [heapOpCtx, Op.fixed, binarySearchBlocks, mid] hleftEval
            refine ⟨leftResult,
              .left hnonempty (by simpa [mid] using hleft) hleftResult, ?_⟩
            prove_binary_loop_instrs (high, low)
            apply binarySearch_evaluates_ite_false
            · evaluates 100 [heapOpCtx, Op.fixed, binarySearchBlocks, hempty]
            · exact evaluates_bool _ false
            · zspec_call 100 [heapOpCtx, Op.fixed, binarySearchBlocks] hstep

theorem binarySearchLoop_result (fuel : Nat) (xs : HeapArray) (needle low high : Nat)
    (hhigh : high ≤ xs.length) (hfuel : high - low ≤ fuel) :
    ∃ result, BinarySearchResult xs needle low high result ∧
      Zag.EvaluatesCallValues binarySearchCtx "binarySearchLoop"
        ([valArray xs, Val.nat needle, Val.nat low, Val.nat high] : List (Val heapCtx))
        (Singleton.idPre True)
        (Singleton.idPost (· = Val.bool result)) := by
  obtain ⟨result, hresult, heval⟩ :=
    binarySearchLoop_result_exact fuel xs needle low high hhigh hfuel
  refine ⟨result, hresult, ?_⟩
  simpa [Exact.EvaluatesCallValues, Exact.pre, Exact.post, Singleton.idPre, Singleton.idPost]
    using heval

/-- Private Exact spine for the entry block. -/
private theorem binarySearch_result_exact (xs : HeapArray) (needle : Nat) :
    ∃ result, BinarySearchResult xs needle 0 xs.length result ∧
      Exact.EvaluatesCallValues binarySearchCtx "binarySearch"
        ([valArray xs, Val.nat needle] : List (Val heapCtx)) (Val.bool result) := by
  obtain ⟨result, hresult, hloop⟩ :=
    binarySearchLoop_result_exact xs.length xs needle 0 xs.length (Nat.le_refl _) (by omega)
  refine ⟨result, hresult, ?_⟩
  evaluates_call 300
    [heapOpCtx, Op.fixed, binarySearchBlocks, arrayLenOp, Op.ofVals, Op.Body.eager,
      asArray?, valArray]
  zspec_call 100 [heapOpCtx, Op.fixed, binarySearchBlocks] hloop

theorem binarySearch_result (xs : HeapArray) (needle : Nat) :
    ∃ result, BinarySearchResult xs needle 0 xs.length result ∧
      Zag.EvaluatesCallValues binarySearchCtx "binarySearch"
        ([valArray xs, Val.nat needle] : List (Val heapCtx))
        (Singleton.idPre True)
        (Singleton.idPost (· = Val.bool result)) := by
  obtain ⟨result, hresult, heval⟩ := binarySearch_result_exact xs needle
  refine ⟨result, hresult, ?_⟩
  simpa [Exact.EvaluatesCallValues, Exact.pre, Exact.post, Singleton.idPre, Singleton.idPost]
    using heval

/-- On an in-bounds sorted interval, the modeled binary-search control flow returns true exactly
when the needle occurs in that interval. -/
theorem binarySearch_membership {xs : HeapArray} {needle low high : Nat} {result : Bool}
    (hsorted : SortedArray xs) (hhigh : high ≤ xs.length)
    (run : BinarySearchResult xs needle low high result) :
    result = true ↔ InArrayRange xs needle low high := by
  induction run with
  | @empty low high h =>
      simp only [Bool.false_eq_true, false_iff, InArrayRange]
      intro hm
      rcases hm with ⟨i, hlo, hhi, _⟩
      omega
  | @found low high h heq =>
      simp only [InArrayRange, true_iff]
      refine ⟨(low + high) / 2, ?_, ?_, heq⟩ <;> omega
  | @right result low high h hlt next ih =>
      rw [ih hhigh]
      constructor
      · intro hm
        rcases hm with ⟨i, hlo, hhi, heq⟩
        exact ⟨i, by omega, hhi, heq⟩
      · intro hm
        rcases hm with ⟨i, hlo, hhi, heq⟩
        by_cases hi : (low + high) / 2 + 1 ≤ i
        · exact ⟨i, hi, hhi, heq⟩
        · have hle : i ≤ (low + high) / 2 := by omega
          have hmid : (low + high) / 2 < xs.length := by omega
          have horder := hsorted i ((low + high) / 2) hle hmid
          omega
  | @left result low high h hlt next ih =>
      have hmid : (low + high) / 2 ≤ xs.length := by omega
      rw [ih hmid]
      constructor
      · intro hm
        rcases hm with ⟨i, hlo, hhi, heq⟩
        exact ⟨i, hlo, by omega, heq⟩
      · intro hm
        rcases hm with ⟨i, hlo, hhi, heq⟩
        refine ⟨i, hlo, ?_, heq⟩
        by_cases hi : i < (low + high) / 2
        · exact hi
        · have hle : (low + high) / 2 ≤ i := by omega
          have horder := hsorted ((low + high) / 2) i hle (by omega)
          omega

/-- The executable entry block returns true exactly when the sorted input contains the needle. -/
theorem binarySearch_correct (xs : HeapArray) (needle : Nat) (hsorted : SortedArray xs) :
    ∃ result, Zag.EvaluatesCallValues binarySearchCtx "binarySearch"
        ([valArray xs, Val.nat needle] : List (Val heapCtx))
        (Singleton.idPre True)
        (Singleton.idPost (· = Val.bool result)) ∧
      (result = true ↔ InArrayRange xs needle 0 xs.length) := by
  obtain ⟨result, hresult, heval⟩ := binarySearch_result xs needle
  exact ⟨result, heval, binarySearch_membership hsorted (Nat.le_refl _) hresult⟩

end Zag.Test.Autocorres.Examples
