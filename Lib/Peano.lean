import Lib.Peano.Eval
import Meta.Induction

namespace Zag.Lib.Peano

open Zag
open Zag.Pr.Induction

def succName : String := "succ"

theorem succ_spec : SuccSpec peanoCtx succName where
  hasType_op := fun _ _ ht =>
    Term.hasType.unOp (by rfl) ht
  eval_succ := fun _ _ _ ht => by
    simpa [succName, Nat.succ_eq_add_one] using
      (evaluates_natUnary (ctx := peanoCtx) (name := "succ") (f := Nat.succ)
        (Peano.Model.succOp (ctx := peanoCtx)) ht)

theorem hsucc (env : Env natCtx) (m : Nat) :
    EvaluatesTo peanoCtx env (.op succName [Term.nat m]) (Val.nat (m + 1)) :=
  succ_spec.eval_succ env (Term.nat m) m (Pr.Induction.eval_natLit (ctx := peanoCtx) env m)

end Zag.Lib.Peano
