import Lib.Peano
import Meta.Abbrev
import Meta.UnifyType

namespace Zag.Test.Abbrev

open Zag
open Lib.Peano

private abbrev NatTy : Ty := .prim "Nat"

private def typeAbbrevs : TypeAbbrevCtx :=
  ⟨[("Identity", { typeArity := 1, body := .var 0 }),
    ("NatAlias", { typeArity := 0, body := .«abbrev» "Identity" [NatTy] })], by decide⟩

private def identity : String × TermAbbrev natCtx :=
  termAbbrev% identity[A](x : A) : A := x

private def recursive : String × TermAbbrev natCtx :=
  ("recursive", {
    typeArity := 0
    varCtx := []
    outTy := NatTy
    body := .«abbrev» "recursive" [] []
  })

private def illTyped : String × TermAbbrev natCtx :=
  ("illTyped", {
    typeArity := 0
    varCtx := [NatTy]
    outTy := .option NatTy
    body := .var 0
  })

private def genericPrimitive : String × TermAbbrev natCtx :=
  ("genericPrimitive", {
    typeArity := 1
    varCtx := []
    outTy := .option (.var 0)
    body := .prim (.option (.var 0))
      (cast (Ty.type.eq_3 natCtx (.var 0)).symm none)
  })

private def applySecond : String × TermAbbrev natCtx :=
  termAbbrev% applySecond(x : Nat, f : func[Nat] => Nat) : Nat := call f [x]

private def useIdentity : String × TermAbbrev natCtx :=
  termAbbrev% useIdentity[A](x : A) : A := abbrev "identity" [A] [x]

private def forwardReference : String × TermAbbrev natCtx :=
  termAbbrev% forwardReference(x : Nat) : Nat := abbrev "later" [] [x]

private def later : String × TermAbbrev natCtx :=
  termAbbrev% later(x : Nat) : Nat := x

private def constantNat : String × TermAbbrev natCtx :=
  termAbbrev% constantNat(x : Nat) : Nat := term(Term.nat 1)

private def aliasTypedIdentity : String × TermAbbrev natCtx :=
  termAbbrev% aliasTypedIdentity(
    x : abbrev "Identity" [Nat]) : abbrev "Identity" [Nat] := x

private def aliasOut : String × TermAbbrev natCtx :=
  termAbbrev% aliasOut() : abbrev "NatAlias" [] := term(Term.nat 13)

private def forwardMotive : String × TermAbbrev natCtx :=
  termAbbrev% forwardMotive(f : func[Bool] => Nat) : func[Bool] => Nat := f

private def ignoreFunction : Op natCtx where
  arity := 1
  out := fun _ => some NatTy
  body := .next true fun
    | none => .fail
    | some _ => .done (Val.nat 7)

private def base : BaseCtx where
  primCtx := natCtx
  primFuncCtx := natFuncCtx
  opCtx := natOpCtx
  tyAbbrevCtx := typeAbbrevs

private def abbrevCtx : Ctx where
  primCtx := natCtx
  primFuncCtx := natFuncCtx
  opCtx := natOpCtx
  tyAbbrevCtx := typeAbbrevs
  termAbbrevCtx := ⟨[identity], by native_decide⟩

private instance : Peano.Types abbrevCtx.primCtx := by
  change Peano.Types natCtx
  infer_instance

private instance : Peano.Model abbrevCtx where
  natType := by rfl
  boolType := by rfl
  eqOp := by rfl
  ltOp := by rfl
  gtOp := by rfl
  iteOp := by rfl

private def natAlias : Ty := .«abbrev» "NatAlias" []

private def natAliasSyntax : Ty := ty% { abbrev "NatAlias" [] }

private def identitySeven : Term natCtx :=
  term% { abbrev "identity" [Nat] [term(Term.nat 7)] }

private def identityAliasSeven : Term natCtx :=
  .«abbrev» "identity" [natAlias] [Term.nat 7]

private def aliasOutCall : Term natCtx :=
  .«abbrev» "aliasOut" [] []

private def motiveCtx : Ctx where
  primCtx := natCtx
  primFuncCtx := natFuncCtx
  opCtx := natOpCtx
  termAbbrevCtx := ⟨[applySecond], by native_decide⟩

private instance : Peano.Types motiveCtx.primCtx := by
  change Peano.Types natCtx
  infer_instance

private def applyInsideRecurse : Term natCtx :=
  .recurse NatTy (Term.nat 0)
    (.«abbrev» "applySecond" [] [Term.nat 7, .primFunc "succ"])

private def eagerCtx : Ctx where
  primCtx := natCtx
  primFuncCtx := natFuncCtx
  opCtx := natOpCtx
  termAbbrevCtx := ⟨[constantNat], by native_decide⟩

private def priorCtx : Ctx where
  primCtx := natCtx
  primFuncCtx := natFuncCtx
  opCtx := natOpCtx
  termAbbrevCtx := ⟨[identity, useIdentity], by native_decide⟩

private def recursorCtx : Ctx where
  primCtx := natCtx
  primFuncCtx := natFuncCtx
  opCtx := ("ignoreFunction", ignoreFunction) :: natOpCtx

private def recursorAbbrevCtx : Ctx where
  primCtx := natCtx
  primFuncCtx := natFuncCtx
  opCtx := ("ignoreFunction", ignoreFunction) :: natOpCtx
  termAbbrevCtx := ⟨[identity], by native_decide⟩

private def aliasCtx : Ctx where
  primCtx := natCtx
  primFuncCtx := natFuncCtx
  opCtx := natOpCtx
  tyAbbrevCtx := typeAbbrevs
  termAbbrevCtx := ⟨[aliasTypedIdentity], by native_decide⟩

private def aliasOutCtx : Ctx where
  primCtx := natCtx
  primFuncCtx := natFuncCtx
  opCtx := natOpCtx
  tyAbbrevCtx := typeAbbrevs
  termAbbrevCtx := ⟨[aliasOut], by native_decide⟩

private def forwardingCtx : Ctx where
  primCtx := natCtx
  primFuncCtx := natFuncCtx
  opCtx := natOpCtx
  termAbbrevCtx := ⟨[forwardMotive], by native_decide⟩

private instance : Peano.Types priorCtx.primCtx := by
  change Peano.Types natCtx
  infer_instance

private instance : Peano.Model priorCtx where
  natType := by rfl
  boolType := by rfl
  eqOp := by rfl
  ltOp := by rfl
  gtOp := by rfl
  iteOp := by rfl

private instance : Peano.Types recursorCtx.primCtx := by
  change Peano.Types natCtx
  infer_instance

private instance : Peano.Types recursorAbbrevCtx.primCtx := by
  change Peano.Types natCtx
  infer_instance

private instance : Peano.Types eagerCtx.primCtx := by
  change Peano.Types natCtx
  infer_instance

private instance : Peano.Types aliasCtx.primCtx := by
  change Peano.Types natCtx
  infer_instance

private instance : Peano.Types aliasOutCtx.primCtx := by
  change Peano.Types natCtx
  infer_instance

private instance : Peano.Model aliasOutCtx where
  natType := by rfl
  boolType := by rfl
  eqOp := by rfl
  ltOp := by rfl
  gtOp := by rfl
  iteOp := by rfl

private instance : Peano.Types forwardingCtx.primCtx := by
  change Peano.Types natCtx
  infer_instance

private def unusedFailingArgument : Term natCtx :=
  .«abbrev» "constantNat" [] [.primFunc "missing"]

private def nestedForwarding : Term natCtx :=
  .recurse NatTy (Term.bool false)
    (Term.ite (.var 0) (Term.nat 7)
      (.recurse NatTy (Term.bool false)
        (.app (.«abbrev» "forwardMotive" [] [.var 1]) [Term.bool true])))

private def ignoredMotiveRecurse : Term natCtx :=
  .recurse NatTy (Term.nat 0) (.op "ignoreFunction" [.var 1])

example : identity.2.typeArity = 1 := rfl
example : identity.2.varCtx = [.var 0] := rfl
example : identity.2.outTy = .var 0 := rfl
example : identity.2.body = .var 0 := rfl
example : aliasTypedIdentity.2.varCtx = [.«abbrev» "Identity" [NatTy]] := rfl
example : aliasTypedIdentity.2.outTy = .«abbrev» "Identity" [NatTy] := rfl
example : ¬ TermAbbrevCtx.Valid [recursive] := by native_decide
example : TermAbbrevCtx.Valid [illTyped] := by native_decide
example : TermAbbrevCtx.Valid [genericPrimitive] := by native_decide
example : TermAbbrevCtx.Valid [identity, useIdentity] := by native_decide
example : ¬ TermAbbrevCtx.Valid [forwardReference, later] := by native_decide

example : ¬ TypeAbbrevCtx.Valid
    [("Duplicate", { typeArity := 0, body := NatTy }),
     ("Duplicate", { typeArity := 0, body := NatTy })] := by decide

example : ¬ TermAbbrevCtx.Valid [identity, identity] := by native_decide
example : natAliasSyntax = natAlias := rfl

example : TermAbbrevCtx.check base [identity] = true := by native_decide
example : TermAbbrevCtx.check base [identity, identity] = false := by native_decide
example : TermAbbrevCtx.check base [recursive] = false := by native_decide
example : TermAbbrevCtx.check base [illTyped] = false := by native_decide
example : TermAbbrevCtx.check base [genericPrimitive] = false := by native_decide
example : TermAbbrevCtx.check base [identity, useIdentity] = true := by native_decide
example : TermAbbrevCtx.check base [forwardReference, later] = false := by native_decide
example : TermAbbrevCtx.check base [aliasTypedIdentity] = true := by native_decide
example : (TypeAbbrevCtx.ofRaw? typeAbbrevs.val).isSome := by native_decide
example : (CheckedTermAbbrevCtx.ofRaw? base [identity, useIdentity]).isSome := by
  native_decide
example : (CheckedTermAbbrevCtx.ofRaw? base [illTyped]).isNone := by native_decide
example : TermAbbrevCtx.check base [aliasOut] = true := by native_decide

example : aliasOut.2.body.inferType? base [] aliasOut.2.typeArity aliasOut.2.varCtx =
    some (aliasOut.2.outTy.normalizeAbbrev typeAbbrevs) := by
  exact CheckedTermAbbrevCtx.getWithPrefix?_bodyInferType
    (ctx := aliasOutCtx.termAbbrevCtx) (name := "aliasOut")
    (prior := []) (definition := aliasOut.2) rfl

example : Term.instantiateTy? typeAbbrevs [NatTy] genericPrimitive.2.body = none := by
  native_decide

example : Term.hasType abbrevCtx [] identitySeven NatTy := by
  let model : Peano.Model abbrevCtx := inferInstance
  dsimp [abbrevCtx, identitySeven, identity] at model ⊢
  letI := model
  has_type

example : Term.hasType abbrevCtx [] identityAliasSeven NatTy := by
  let model : Peano.Model abbrevCtx := inferInstance
  dsimp [abbrevCtx, identityAliasSeven, identity, natAlias, typeAbbrevs] at model ⊢
  letI := model
  has_type

example : Term.inferType? base [aliasOut] 0 [] aliasOutCall = some NatTy := by
  native_decide

example : Term.inferType? base [identity] 0 [] identityAliasSeven = some NatTy := by
  native_decide

example : Term.inferType? base [identity] 1 [.var 0]
    (.«abbrev» "identity" [.var 0] [.var 0]) = some (.var 0) := by
  native_decide

example : Term.inferType? base [identity] 0 [.var 0]
    (.«abbrev» "identity" [.var 0] [.var 0]) = none := by
  native_decide

example : Term.hasType aliasOutCtx [] aliasOutCall NatTy := by
  let model : Peano.Model aliasOutCtx := inferInstance
  dsimp [aliasOutCtx, aliasOutCall, aliasOut, natAlias, typeAbbrevs] at model ⊢
  letI := model
  has_type

example : Term.hasType priorCtx []
    (.«abbrev» "useIdentity" [NatTy] [Term.nat 9]) NatTy := by
  let model : Peano.Model priorCtx := inferInstance
  dsimp [priorCtx, useIdentity, identity] at model ⊢
  letI := model
  has_type

example : ¬ Term.hasType priorCtx [.var 0]
    (.«abbrev» "useIdentity" [.var 0] [.var 0]) (.var 0) := by
  intro h
  have htypeArgs := h.abbrev_typeArgs_valid
  exact (by native_decide :
    Ty.validListIn priorCtx.tyAbbrevCtx.val 0 [.var 0] ≠ true) htypeArgs

example : ¬ Term.hasType aliasOutCtx [] aliasOutCall natAlias := by
  intro h
  obtain ⟨definition, prior, hget, hresult⟩ := h.abbrev_result
  have hdefinition : definition = aliasOut.2 := by
    symm
    simpa [aliasOutCtx, aliasOut, CheckedTermAbbrevCtx.getWithPrefix?,
      TermAbbrevCtx.Raw.getWithPrefix?] using congrArg (Option.map Prod.snd) hget
  subst definition
  have hnormalize :
      (Ty.subst [] aliasOut.2.outTy).normalizeAbbrev aliasOutCtx.tyAbbrevCtx = NatTy := by
    native_decide
  rw [hnormalize] at hresult
  exact (by native_decide : natAlias ≠ NatTy) hresult

example : Ty.normalizeAbbrev typeAbbrevs natAlias = NatTy := by
  expand_abbrev

example : (1 : Nat) = 1 := by
  fail_if_success expand_abbrev
  rfl

example : Term.eval abbrevCtx [] (.«abbrev» "identity" [] [Term.nat 7]) = none := by
  native_decide

example : Term.eval abbrevCtx [] (.«abbrev» "identity" [NatTy] []) = none := by
  native_decide

example : (Term.eval abbrevCtx [] identitySeven).bind Val.asNat? = some 7 := by
  native_decide

example : (Term.eval abbrevCtx [] identityAliasSeven).map Val.ty = some NatTy := by
  native_decide

example : Term.eval abbrevCtx []
    (.«abbrev» "identity" [.var 0] [Term.nat 7]) = none := by
  native_decide

example : (Term.eval motiveCtx [] applyInsideRecurse).bind Val.asNat? = some 8 := by
  native_decide

example : Term.eval eagerCtx [] unusedFailingArgument = none := by
  native_decide

example : (Term.eval priorCtx []
    (.«abbrev» "useIdentity" [NatTy] [Term.nat 9])).bind Val.asNat? = some 9 := by
  native_decide

example : Term.eval priorCtx [] (.«abbrev» "useIdentity" [] [Term.nat 9]) = none := by
  native_decide

example : Term.eval priorCtx []
    (.«abbrev» "useIdentity" [NatTy, NatTy] [Term.nat 9]) = none := by
  native_decide

example : Term.eval eagerCtx [] (.«abbrev» "constantNat" [] [Term.bool true]) = none := by
  native_decide

example : (Term.eval aliasCtx []
    (.«abbrev» "aliasTypedIdentity" [] [Term.nat 11])).map Val.ty = some NatTy := by
  native_decide

example : (Term.eval aliasOutCtx [] aliasOutCall).map Val.ty = some NatTy := by
  native_decide

example : (Term.eval aliasOutCtx [] aliasOutCall).map Val.ty ≠ some natAlias := by
  native_decide

example : (Term.eval forwardingCtx [] nestedForwarding).bind Val.asNat? = some 7 := by
  native_decide

example : (Term.eval recursorCtx [] ignoredMotiveRecurse).bind Val.asNat? =
    (Term.eval recursorAbbrevCtx [] ignoredMotiveRecurse).bind Val.asNat? := by
  native_decide

example : (Term.eval recursorAbbrevCtx [] ignoredMotiveRecurse).bind Val.asNat? = some 7 := by
  native_decide

end Zag.Test.Abbrev
