import Test.Autocorres.Examples.Common

/-!
Upstream Isabelle theory:
[`WordAbs.thy`](https://github.com/seL4/l4v/blob/master/tools/autocorres/tests/examples/WordAbs.thy).

This module covers only the source operations whose successful abstraction is expressible with
unbounded `Nat`: arithmetic, unsigned bitwise binary operators, and nonnegative shifts. The block
names carry `Nat` to prevent them being mistaken for 32-bit C operations. In particular,
subtraction is truncated, shifts have no width guard, and division/modulo are total at zero.

**Unsupported:** signed integers, 32-bit wraparound and complements/negation, mixed signedness,
overflow and invalid-shift failure, and the AutoCorres per-function word-abstraction selection.
No theorem below claims behavior outside the corresponding successful Nat path.
-/

namespace Zag.Test.Autocorres.Examples

open Zag Zag.Lib.PeanoHeap
open Zag.EvalTriple
open Zag.EvalTriple.Exact
open scoped Std.Do

private abbrev heapOpCtx := pureHeapOpCtx

abbrev wordAbsBlocks : BlockCtx.Raw heapCtx :=
  blocks% [
    ver366Nat(x : Nat) : Nat {
      zero := primEq x nat(0);
      ret if zero { nat(0) } else { op "sub"[x, nat(1)] }
    },
    uAddNat(x : Nat, y : Nat) : Nat {
      ret op "add"[x, y]
    },
    uSubNat(x : Nat, y : Nat) : Nat {
      ret op "sub"[x, y]
    },
    uMulNat(x : Nat, y : Nat) : Nat {
      ret op "mul"[x, y]
    },
    uDivNat(x : Nat, y : Nat) : Nat {
      ret op "div"[x, y]
    },
    uModNat(x : Nat, y : Nat) : Nat {
      ret op "mod"[x, y]
    },
    uAndNat(x : Nat, y : Nat) : Nat {
      ret op "bitAnd"[x, y]
    },
    uOrNat(x : Nat, y : Nat) : Nat {
      ret op "bitOr"[x, y]
    },
    uXorNat(x : Nat, y : Nat) : Nat {
      ret op "bitXor"[x, y]
    },
    uShiftlNat(x : Nat, shift : Nat) : Nat {
      ret op "shl"[x, shift]
    },
    uShiftrNat(x : Nat, shift : Nat) : Nat {
      ret op "shr"[x, shift]
    }
  ]

theorem wordAbsBlocksValid : BlockCtx.Valid wordAbsBlocks := by
  valid_blocks [wordAbsBlocks]

abbrev wordAbsCtx : Ctx := mkPureCtx wordAbsBlocks wordAbsBlocksValid

theorem wordAbsCtx_wellTyped : Ctx.WellTyped wordAbsCtx := by
  typecheck_ctx

def ver366NatSpec (x : Nat) : Nat := if x = 0 then 0 else x - 1

theorem word_evaluates_binary {env : Env heapCtx} {name : String} {f : Nat → Nat → Nat}
    {lhs rhs : Term heapCtx} {x y : Nat}
    (hop : wordAbsCtx.opCtx.get? name = some (binaryNatOp f))
    (hlhs : EvaluatesTo wordAbsCtx env lhs (Val.nat x))
    (hrhs : EvaluatesTo wordAbsCtx env rhs (Val.nat y)) :
    EvaluatesTo wordAbsCtx env (.op name [lhs, rhs]) (Val.nat (f x y)) := by
  refine EvaluatesTo.op_applyVals (oper := binaryNatOp f) hop
    (EvaluatesList.cons hlhs (EvaluatesList.cons hrhs EvaluatesList.nil)) ?_
  simp [Op.applyValsAt, Op.fixed, binaryNatOp, Op.ofVals, Op.Body.applyVals, Op.Body.eager]

@[eval_semantic] theorem word_evaluates_mod {env : Env heapCtx} {lhs rhs : Term heapCtx}
    {x y : Nat} (hlhs : EvaluatesTo wordAbsCtx env lhs (Val.nat x))
    (hrhs : EvaluatesTo wordAbsCtx env rhs (Val.nat y)) :
    EvaluatesTo wordAbsCtx env (.op "mod" [lhs, rhs]) (Val.nat (x % y)) :=
  word_evaluates_binary rfl hlhs hrhs

@[eval_semantic] theorem word_evaluates_bitAnd {env : Env heapCtx} {lhs rhs : Term heapCtx}
    {x y : Nat} (hlhs : EvaluatesTo wordAbsCtx env lhs (Val.nat x))
    (hrhs : EvaluatesTo wordAbsCtx env rhs (Val.nat y)) :
    EvaluatesTo wordAbsCtx env (.op "bitAnd" [lhs, rhs]) (Val.nat (bitAnd x y)) :=
  word_evaluates_binary rfl hlhs hrhs

@[eval_semantic] theorem word_evaluates_bitOr {env : Env heapCtx} {lhs rhs : Term heapCtx}
    {x y : Nat} (hlhs : EvaluatesTo wordAbsCtx env lhs (Val.nat x))
    (hrhs : EvaluatesTo wordAbsCtx env rhs (Val.nat y)) :
    EvaluatesTo wordAbsCtx env (.op "bitOr" [lhs, rhs]) (Val.nat (bitOr x y)) :=
  word_evaluates_binary rfl hlhs hrhs

@[eval_semantic] theorem word_evaluates_bitXor {env : Env heapCtx} {lhs rhs : Term heapCtx}
    {x y : Nat} (hlhs : EvaluatesTo wordAbsCtx env lhs (Val.nat x))
    (hrhs : EvaluatesTo wordAbsCtx env rhs (Val.nat y)) :
    EvaluatesTo wordAbsCtx env (.op "bitXor" [lhs, rhs]) (Val.nat (bitXor x y)) :=
  word_evaluates_binary rfl hlhs hrhs

@[eval_semantic] theorem word_evaluates_shl {env : Env heapCtx} {lhs rhs : Term heapCtx}
    {x y : Nat} (hlhs : EvaluatesTo wordAbsCtx env lhs (Val.nat x))
    (hrhs : EvaluatesTo wordAbsCtx env rhs (Val.nat y)) :
    EvaluatesTo wordAbsCtx env (.op "shl" [lhs, rhs]) (Val.nat (x * pow2 y)) :=
  word_evaluates_binary (f := fun a b => a * pow2 b) rfl hlhs hrhs

@[eval_semantic] theorem word_evaluates_shr {env : Env heapCtx} {lhs rhs : Term heapCtx}
    {x y : Nat} (hlhs : EvaluatesTo wordAbsCtx env lhs (Val.nat x))
    (hrhs : EvaluatesTo wordAbsCtx env rhs (Val.nat y)) :
    EvaluatesTo wordAbsCtx env (.op "shr" [lhs, rhs]) (Val.nat (x / pow2 y)) :=
  word_evaluates_binary (f := fun a b => a / pow2 b) rfl hlhs hrhs

private theorem ver366Nat_eval_exact (x : Nat) :
    Exact.EvaluatesCallValues wordAbsCtx "ver366Nat" ([Val.nat x] : List (Val heapCtx))
      (Val.nat (ver366NatSpec x)) := by
  by_cases h : x = 0
  · subst x
    evaluates_call 100 [heapOpCtx, Op.fixed, wordAbsBlocks, ver366NatSpec]
  · simp only [ver366NatSpec, h, ↓reduceIte]
    evaluates_call 100 [heapOpCtx, Op.fixed, wordAbsBlocks, h]

theorem ver366Nat_eval (x : Nat) :
    Zag.EvaluatesCallValues wordAbsCtx "ver366Nat" ([Val.nat x] : List (Val heapCtx))
      (Singleton.idPre True)
      (Singleton.idPost (· = Val.nat (ver366NatSpec x))) := by
  simpa [Exact.EvaluatesCallValues, Exact.pre, Exact.post, Singleton.idPre, Singleton.idPost]
    using ver366Nat_eval_exact x

private theorem uAddNat_eval_exact (x y : Nat) :
    Exact.EvaluatesCallValues wordAbsCtx "uAddNat" ([Val.nat x, Val.nat y] : List (Val heapCtx))
      (Val.nat (x + y)) := by
  evaluates_call [heapOpCtx, Op.fixed, wordAbsBlocks]

theorem uAddNat_eval (x y : Nat) :
    Zag.EvaluatesCallValues wordAbsCtx "uAddNat" ([Val.nat x, Val.nat y] : List (Val heapCtx))
      (Singleton.idPre True)
      (Singleton.idPost (· = Val.nat (x + y))) := by
  simpa [Exact.EvaluatesCallValues, Exact.pre, Exact.post, Singleton.idPre, Singleton.idPost]
    using uAddNat_eval_exact x y

private theorem uSubNat_eval_exact (x y : Nat) :
    Exact.EvaluatesCallValues wordAbsCtx "uSubNat" ([Val.nat x, Val.nat y] : List (Val heapCtx))
      (Val.nat (x - y)) := by
  evaluates_call [heapOpCtx, Op.fixed, wordAbsBlocks]

theorem uSubNat_eval (x y : Nat) :
    Zag.EvaluatesCallValues wordAbsCtx "uSubNat" ([Val.nat x, Val.nat y] : List (Val heapCtx))
      (Singleton.idPre True)
      (Singleton.idPost (· = Val.nat (x - y))) := by
  simpa [Exact.EvaluatesCallValues, Exact.pre, Exact.post, Singleton.idPre, Singleton.idPost]
    using uSubNat_eval_exact x y

private theorem uMulNat_eval_exact (x y : Nat) :
    Exact.EvaluatesCallValues wordAbsCtx "uMulNat" ([Val.nat x, Val.nat y] : List (Val heapCtx))
      (Val.nat (x * y)) := by
  evaluates_call [heapOpCtx, Op.fixed, wordAbsBlocks]

theorem uMulNat_eval (x y : Nat) :
    Zag.EvaluatesCallValues wordAbsCtx "uMulNat" ([Val.nat x, Val.nat y] : List (Val heapCtx))
      (Singleton.idPre True)
      (Singleton.idPost (· = Val.nat (x * y))) := by
  simpa [Exact.EvaluatesCallValues, Exact.pre, Exact.post, Singleton.idPre, Singleton.idPost]
    using uMulNat_eval_exact x y

private theorem uDivNat_eval_exact (x y : Nat) :
    Exact.EvaluatesCallValues wordAbsCtx "uDivNat" ([Val.nat x, Val.nat y] : List (Val heapCtx))
      (Val.nat (x / y)) := by
  evaluates_call [heapOpCtx, Op.fixed, wordAbsBlocks]

theorem uDivNat_eval (x y : Nat) :
    Zag.EvaluatesCallValues wordAbsCtx "uDivNat" ([Val.nat x, Val.nat y] : List (Val heapCtx))
      (Singleton.idPre True)
      (Singleton.idPost (· = Val.nat (x / y))) := by
  simpa [Exact.EvaluatesCallValues, Exact.pre, Exact.post, Singleton.idPre, Singleton.idPost]
    using uDivNat_eval_exact x y

private theorem uModNat_eval_exact (x y : Nat) :
    Exact.EvaluatesCallValues wordAbsCtx "uModNat" ([Val.nat x, Val.nat y] : List (Val heapCtx))
      (Val.nat (x % y)) := by
  evaluates_call 300
    [heapOpCtx, Op.fixed, wordAbsBlocks, binaryNatOp, Op.ofVals, Op.Body.eager]

theorem uModNat_eval (x y : Nat) :
    Zag.EvaluatesCallValues wordAbsCtx "uModNat" ([Val.nat x, Val.nat y] : List (Val heapCtx))
      (Singleton.idPre True)
      (Singleton.idPost (· = Val.nat (x % y))) := by
  simpa [Exact.EvaluatesCallValues, Exact.pre, Exact.post, Singleton.idPre, Singleton.idPost]
    using uModNat_eval_exact x y

private theorem uAndNat_eval_exact (x y : Nat) :
    Exact.EvaluatesCallValues wordAbsCtx "uAndNat" ([Val.nat x, Val.nat y] : List (Val heapCtx))
      (Val.nat (bitAnd x y)) := by
  evaluates_call 300
    [heapOpCtx, Op.fixed, wordAbsBlocks, binaryNatOp, Op.ofVals, Op.Body.eager]

theorem uAndNat_eval (x y : Nat) :
    Zag.EvaluatesCallValues wordAbsCtx "uAndNat" ([Val.nat x, Val.nat y] : List (Val heapCtx))
      (Singleton.idPre True)
      (Singleton.idPost (· = Val.nat (bitAnd x y))) := by
  simpa [Exact.EvaluatesCallValues, Exact.pre, Exact.post, Singleton.idPre, Singleton.idPost]
    using uAndNat_eval_exact x y

private theorem uOrNat_eval_exact (x y : Nat) :
    Exact.EvaluatesCallValues wordAbsCtx "uOrNat" ([Val.nat x, Val.nat y] : List (Val heapCtx))
      (Val.nat (bitOr x y)) := by
  evaluates_call 300
    [heapOpCtx, Op.fixed, wordAbsBlocks, binaryNatOp, Op.ofVals, Op.Body.eager]

theorem uOrNat_eval (x y : Nat) :
    Zag.EvaluatesCallValues wordAbsCtx "uOrNat" ([Val.nat x, Val.nat y] : List (Val heapCtx))
      (Singleton.idPre True)
      (Singleton.idPost (· = Val.nat (bitOr x y))) := by
  simpa [Exact.EvaluatesCallValues, Exact.pre, Exact.post, Singleton.idPre, Singleton.idPost]
    using uOrNat_eval_exact x y

private theorem uXorNat_eval_exact (x y : Nat) :
    Exact.EvaluatesCallValues wordAbsCtx "uXorNat" ([Val.nat x, Val.nat y] : List (Val heapCtx))
      (Val.nat (bitXor x y)) := by
  evaluates_call 300
    [heapOpCtx, Op.fixed, wordAbsBlocks, binaryNatOp, Op.ofVals, Op.Body.eager]

theorem uXorNat_eval (x y : Nat) :
    Zag.EvaluatesCallValues wordAbsCtx "uXorNat" ([Val.nat x, Val.nat y] : List (Val heapCtx))
      (Singleton.idPre True)
      (Singleton.idPost (· = Val.nat (bitXor x y))) := by
  simpa [Exact.EvaluatesCallValues, Exact.pre, Exact.post, Singleton.idPre, Singleton.idPost]
    using uXorNat_eval_exact x y

private theorem uShiftlNat_eval_exact (x shift : Nat) :
    Exact.EvaluatesCallValues wordAbsCtx "uShiftlNat"
      ([Val.nat x, Val.nat shift] : List (Val heapCtx)) (Val.nat (x * pow2 shift)) := by
  evaluates_call 300
    [heapOpCtx, Op.fixed, wordAbsBlocks, binaryNatOp, Op.ofVals, Op.Body.eager]

theorem uShiftlNat_eval (x shift : Nat) :
    Zag.EvaluatesCallValues wordAbsCtx "uShiftlNat"
      ([Val.nat x, Val.nat shift] : List (Val heapCtx))
      (Singleton.idPre True)
      (Singleton.idPost (· = Val.nat (x * pow2 shift))) := by
  simpa [Exact.EvaluatesCallValues, Exact.pre, Exact.post, Singleton.idPre, Singleton.idPost]
    using uShiftlNat_eval_exact x shift

private theorem uShiftrNat_eval_exact (x shift : Nat) :
    Exact.EvaluatesCallValues wordAbsCtx "uShiftrNat"
      ([Val.nat x, Val.nat shift] : List (Val heapCtx)) (Val.nat (x / pow2 shift)) := by
  evaluates_call 300
    [heapOpCtx, Op.fixed, wordAbsBlocks, binaryNatOp, Op.ofVals, Op.Body.eager]

theorem uShiftrNat_eval (x shift : Nat) :
    Zag.EvaluatesCallValues wordAbsCtx "uShiftrNat"
      ([Val.nat x, Val.nat shift] : List (Val heapCtx))
      (Singleton.idPre True)
      (Singleton.idPost (· = Val.nat (x / pow2 shift))) := by
  simpa [Exact.EvaluatesCallValues, Exact.pre, Exact.post, Singleton.idPre, Singleton.idPost]
    using uShiftrNat_eval_exact x shift

theorem nat_shift_round_trip (x shift : Nat) :
    (x * pow2 shift) / pow2 shift = x := by
  simpa [pow2, Nat.mul_comm] using Nat.mul_div_right x (Nat.two_pow_pos shift)

end Zag.Test.Autocorres.Examples
