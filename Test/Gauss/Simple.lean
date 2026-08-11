import Lang.AutoCorres.CParser.Frontend
import Test.Gauss.SSA

/-!
# Gauss through the current C frontend and SSA semantics

The C frontend and verified SSA program are intentionally kept as separate
stages until C-to-SIMPL lowering is implemented. The frontend test preserves
the imperative loop, while the SSA theorem proves the same summation algorithm
for every natural input rather than only checking sample outputs.
-/

namespace Zag.Test.Gauss.Simple

open Zag.Lang.AutoCorres.CParser
open Zag.Test.Gauss.Rec
open Zag.Lib.Peano

private def source : String := "
unsigned gauss(unsigned n)
{
    unsigned i = n;
    unsigned acc = 0;
    while (0 < i) {
        acc = acc + i;
        i = i - 1;
    }
    return acc;
}
"

def frontendResult := Frontend.analyzeSource .arm "gauss.c" source

theorem frontend_succeeds : frontendResult.isSuccess := by native_decide

theorem frontend_has_gauss_function :
    frontendResult.program.map (fun program =>
      (program.symbolsNamed "gauss").length) = some 1 := by
  native_decide

theorem frontend_has_no_calls :
    frontendResult.program.map (fun program => program.calls.length) = some 0 := by
  native_decide

mutual
  private def statementAny (predicate : Statement → Bool) (statement : Statement) : Bool :=
    predicate statement || match statement with
    | .stmt ⟨.block items, _⟩ => blockAny predicate items
    | .stmt ⟨.whileStmt _ _ body, _⟩ | .stmt ⟨.trap _ body, _⟩ =>
        statementAny predicate body
    | .stmt ⟨.ifStmt _ thenBranch elseBranch, _⟩ =>
        statementAny predicate thenBranch || statementAny predicate elseBranch
    | .stmt ⟨.switch _ cases, _⟩ => casesAny predicate cases
    | .stmt ⟨.spec (_, statements, _), _⟩ => statementsAny predicate statements
    | _ => false
  termination_by sizeOf statement
  decreasing_by all_goals simp_wf <;> decreasing_trivial

  private def blockAny (predicate : Statement → Bool) : List BlockItem → Bool
    | [] => false
    | .statement statement :: rest =>
        statementAny predicate statement || blockAny predicate rest
    | .declaration _ :: rest => blockAny predicate rest
  termination_by items => sizeOf items
  decreasing_by all_goals simp_wf <;> decreasing_trivial

  private def casesAny (predicate : Statement → Bool) :
      List (List (Option Expr) × List BlockItem) → Bool
    | [] => false
    | (_, body) :: rest => blockAny predicate body || casesAny predicate rest
  termination_by cases => sizeOf cases
  decreasing_by all_goals simp_wf <;> decreasing_trivial

  private def statementsAny (predicate : Statement → Bool) : List Statement → Bool
    | [] => false
    | statement :: rest =>
        statementAny predicate statement || statementsAny predicate rest
  termination_by statements => sizeOf statements
  decreasing_by all_goals simp_wf <;> decreasing_trivial
end

private def isVar (expected : String) : Expr → Bool
  | .e ⟨.var name _, _⟩ => name == expected
  | _ => false

private def isLiteral (expected : Int) : Expr → Bool
  | .e ⟨.constant ⟨.numConst info, _⟩, _⟩ => info.value == expected
  | _ => false

private def isAccUpdate : Statement → Bool
  | .stmt ⟨.assign left (.e ⟨.binOp .plus first second, _⟩), _⟩ =>
      isVar "acc" left && isVar "acc" first && isVar "i" second
  | _ => false

private def isIUpdate : Statement → Bool
  | .stmt ⟨.assign left (.e ⟨.binOp .minus first second, _⟩), _⟩ =>
      isVar "i" left && isVar "i" first && isLiteral 1 second
  | _ => false

private def isExpectedLoop : Statement → Bool
  | .stmt ⟨.whileStmt (.e ⟨.binOp .lt zero index, _⟩) _ body, _⟩ =>
      isLiteral 0 zero && isVar "i" index &&
        statementAny isAccUpdate body && statementAny isIUpdate body
  | _ => false

private def isReturnAcc : Statement → Bool
  | .stmt ⟨.returnStmt (some value), _⟩ => isVar "acc" value
  | _ => false

private def externalHasGaussBody : ExternalDeclaration → Bool
  | .functionDefinition (_, name) _ _ _ body =>
      name.value == "gauss" && blockAny isExpectedLoop body.value &&
        blockAny isReturnAcc body.value
  | .declaration _ => false

theorem frontend_preserves_imperative_algorithm :
    frontendResult.program.map (fun program =>
      program.translationUnit.any externalHasGaussBody &&
        (program.symbolsNamed "i").length == 1 &&
        (program.symbolsNamed "acc").length == 1) = some true := by
  native_decide

def gaussProgram := Zag.Test.Gauss.SSA.lhsProgram

theorem gauss_program_is_typed (n : Nat) :
    Term.hasType peanoCtx [] (gaussProgram n) NatTy :=
  Zag.Test.Gauss.SSA.lhsProgram_hasType n

theorem gauss_program_correct (n : Nat) :
    Term.eval peanoCtx [] (gaussProgram n) =
      some (Val.nat (n * (n + 1) / 2)) :=
  Zag.Test.Gauss.SSA.lhsProgram_eval_rhs n

theorem gauss_eval_5 :
    Term.eval peanoCtx [] (gaussProgram 5) = some (Val.nat 15) := by
  simpa using gauss_program_correct 5

theorem gauss_eval_10 :
    Term.eval peanoCtx [] (gaussProgram 10) = some (Val.nat 55) := by
  simpa using gauss_program_correct 10

end Zag.Test.Gauss.Simple
