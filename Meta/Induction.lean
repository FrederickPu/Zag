import Zag.Meta

namespace Zag

namespace Pr

namespace Induction

def instantiateTermInTerm {primCtx : PrimitiveCtx} (idx : Nat) (replacement : Term primCtx) :
    Term primCtx → Term primCtx
| .prim ty val => .prim ty val
| .primFunc name => .primFunc name
| .var varIdx =>
    if varIdx = idx then
      replacement
    else if idx < varIdx then
      .var (varIdx - 1)
    else
      .var varIdx
| .app f args => .app (instantiateTermInTerm idx replacement f) (args.map (instantiateTermInTerm idx replacement))
| .op name args => .op name (args.map (instantiateTermInTerm idx replacement))
| .mkStruct tys => .mkStruct tys
| .structProj tys fieldIdx => .structProj tys fieldIdx
| .ite cond thenTerm elseTerm =>
    .ite (instantiateTermInTerm idx replacement cond)
      (instantiateTermInTerm idx replacement thenTerm)
      (instantiateTermInTerm idx replacement elseTerm)
| .recurse resultTy init body =>
    .recurse resultTy (instantiateTermInTerm idx replacement init)
      (instantiateTermInTerm idx replacement body)

def instantiateTermAt {primCtx : PrimitiveCtx} (idx : Nat) (body : Pr (Term primCtx)) (term : Term primCtx) : Pr (Term primCtx) :=
  match body with
  | .eq ctx ty lhs rhs => .eq ctx ty (instantiateTermInTerm idx term lhs) (instantiateTermInTerm idx term rhs)
  | .hasType ctx t ty => .hasType ctx (instantiateTermInTerm idx term t) ty
  | .and p q => .and (instantiateTermAt idx p term) (instantiateTermAt idx q term)
  | .or p q => .or (instantiateTermAt idx p term) (instantiateTermAt idx q term)
  | .implies p q => .implies (instantiateTermAt idx p term) (instantiateTermAt idx q term)
  | .forallTy p => .forallTy (instantiateTermAt idx p term)
  | .forallTerm p => .forallTerm (instantiateTermAt idx p term)

abbrev instantiateTerm {primCtx : PrimitiveCtx} (body : Pr (Term primCtx)) (term : Term primCtx) : Pr (Term primCtx) :=
  instantiateTermAt 0 body term

@[simp] theorem instantiateTermInTerm_nat {primCtx : PrimitiveCtx}
    (idx n : Nat) (replacement : Term primCtx) :
    instantiateTermInTerm idx replacement (Term.nat (primCtx := primCtx) n) = Term.nat n := by
  simp [instantiateTermInTerm, Term.nat]

def weakenTermAt {primCtx : PrimitiveCtx} (idx : Nat) : Term primCtx → Term primCtx
| .prim ty val => .prim ty val
| .primFunc name => .primFunc name
| .var varIdx => if idx ≤ varIdx then .var (varIdx + 1) else .var varIdx
| .app f args => .app (weakenTermAt idx f) (args.map (weakenTermAt idx))
| .op name args => .op name (args.map (weakenTermAt idx))
| .mkStruct tys => .mkStruct tys
| .structProj tys fieldIdx => .structProj tys fieldIdx
| .ite cond thenTerm elseTerm =>
    .ite (weakenTermAt idx cond) (weakenTermAt idx thenTerm) (weakenTermAt idx elseTerm)
| .recurse resultTy init body =>
    .recurse resultTy (weakenTermAt idx init) (weakenTermAt idx body)

def weaken {primCtx : PrimitiveCtx} (idx : Nat) : Pr (Term primCtx) → Pr (Term primCtx)
| .eq ctx ty lhs rhs => .eq ctx ty (weakenTermAt idx lhs) (weakenTermAt idx rhs)
| .hasType ctx t ty => .hasType ctx (weakenTermAt idx t) ty
| .and p q => .and (weaken idx p) (weaken idx q)
| .or p q => .or (weaken idx p) (weaken idx q)
| .implies p q => .implies (weaken idx p) (weaken idx q)
| .forallTy p => .forallTy (weaken idx p)
| .forallTerm p => .forallTerm (weaken idx p)

@[simp] theorem weakenTermAt_nat {primCtx : PrimitiveCtx} (idx n : Nat) :
    weakenTermAt idx (Term.nat (primCtx := primCtx) n) = Term.nat n := by
  simp [weakenTermAt, Term.nat]

mutual

theorem instantiateTermInTerm_weakenTermAt {primCtx : PrimitiveCtx}
    (idx : Nat) (replacement term : Term primCtx) :
    instantiateTermInTerm idx replacement (weakenTermAt idx term) = term := by
  cases term with
  | prim ty val => simp [weakenTermAt, instantiateTermInTerm]
  | primFunc name => simp [weakenTermAt, instantiateTermInTerm]
  | var varIdx =>
      by_cases hle : idx ≤ varIdx
      · have hne : ¬ varIdx + 1 = idx := by omega
        have hlt : idx < varIdx + 1 := by omega
        simp [weakenTermAt, instantiateTermInTerm, hle, hne, hlt]
      · have hne : ¬ varIdx = idx := by omega
        have hnlt : ¬ idx < varIdx := by omega
        simp [weakenTermAt, instantiateTermInTerm, hle, hne, hnlt]
  | app f args =>
      simp [weakenTermAt, instantiateTermInTerm,
        instantiateTermInTerm_weakenTermAt idx replacement f,
        instantiateTermInTerm_weakenTermAtList idx replacement args]
  | «op» name args =>
      simp [weakenTermAt, instantiateTermInTerm,
        instantiateTermInTerm_weakenTermAtList idx replacement args]
  | mkStruct tys => simp [weakenTermAt, instantiateTermInTerm]
  | structProj tys fieldIdx => simp [weakenTermAt, instantiateTermInTerm]
  | ite cond thenTerm elseTerm =>
      simp [weakenTermAt, instantiateTermInTerm,
        instantiateTermInTerm_weakenTermAt idx replacement cond,
        instantiateTermInTerm_weakenTermAt idx replacement thenTerm,
        instantiateTermInTerm_weakenTermAt idx replacement elseTerm]
  | «recurse» resultTy init body =>
      simp [weakenTermAt, instantiateTermInTerm,
        instantiateTermInTerm_weakenTermAt idx replacement init,
        instantiateTermInTerm_weakenTermAt idx replacement body]

theorem instantiateTermInTerm_weakenTermAtList {primCtx : PrimitiveCtx}
    (idx : Nat) (replacement : Term primCtx) (terms : List (Term primCtx)) :
    (terms.map (weakenTermAt idx)).map (instantiateTermInTerm idx replacement) = terms := by
  cases terms with
  | nil => simp
  | cons head tail =>
      simp [instantiateTermInTerm_weakenTermAt idx replacement head,
        instantiateTermInTerm_weakenTermAtList idx replacement tail]

end

theorem instantiateTermAt_weaken {primCtx : PrimitiveCtx}
    (idx : Nat) (replacement : Term primCtx) (body : Pr (Term primCtx)) :
    instantiateTermAt idx (weaken idx body) replacement = body := by
  induction body with
  | eq ctx ty lhs rhs =>
      simp [weaken, instantiateTermAt, instantiateTermInTerm_weakenTermAt]
  | hasType ctx term ty =>
      simp [weaken, instantiateTermAt, instantiateTermInTerm_weakenTermAt]
  | and p q ihp ihq => simp [weaken, instantiateTermAt, ihp, ihq]
  | or p q ihp ihq => simp [weaken, instantiateTermAt, ihp, ihq]
  | implies p q ihp ihq => simp [weaken, instantiateTermAt, ihp, ihq]
  | forallTy p ih => simp [weaken, instantiateTermAt, ih]
  | forallTerm p ih => simp [weaken, instantiateTermAt, ih]

mutual

theorem subst_instantiateTermInTerm {primCtx : PrimitiveCtx}
    (ctxTerm : List (Term primCtx)) (t u : Term primCtx) :
    Term.subst ctxTerm (instantiateTermInTerm ctxTerm.length t u) =
      Term.subst (ctxTerm ++ [Term.subst ctxTerm t]) u := by
  cases u with
  | prim ty val => simp [instantiateTermInTerm]
  | primFunc name => simp [instantiateTermInTerm]
  | var varIdx =>
      by_cases heq : varIdx = ctxTerm.length
      · subst heq
        simp [instantiateTermInTerm, Nat.lt_add_one]
      · by_cases hlt : ctxTerm.length < varIdx
        · have h1 : ¬ varIdx - 1 < ctxTerm.length := by omega
          have h2 : ¬ varIdx < ctxTerm.length + 1 := by omega
          have h3 : varIdx - 1 - ctxTerm.length = varIdx - (ctxTerm.length + 1) := by omega
          simp [instantiateTermInTerm, heq, hlt, h1, h2, h3]
        · have hvlt : varIdx < ctxTerm.length := by omega
          have h2 : varIdx < ctxTerm.length + 1 := by omega
          simp [instantiateTermInTerm, heq, hlt, hvlt, h2]
  | app f args =>
      have hargs : List.map (Term.subst ctxTerm ∘ instantiateTermInTerm ctxTerm.length t) args =
          List.map (Term.subst (ctxTerm ++ [Term.subst ctxTerm t])) args := by
        simpa [List.map_map, Function.comp_def] using
          subst_instantiateTermInTermList ctxTerm t args
      simp [instantiateTermInTerm, subst_instantiateTermInTerm ctxTerm t f, hargs]
  | «op» name args =>
      have hargs : List.map (Term.subst ctxTerm ∘ instantiateTermInTerm ctxTerm.length t) args =
          List.map (Term.subst (ctxTerm ++ [Term.subst ctxTerm t])) args := by
        simpa [List.map_map, Function.comp_def] using
          subst_instantiateTermInTermList ctxTerm t args
      simp [instantiateTermInTerm, hargs]
  | mkStruct tys => simp [instantiateTermInTerm]
  | structProj tys fieldIdx => simp [instantiateTermInTerm]
  | ite cond thenTerm elseTerm =>
      simp [instantiateTermInTerm, subst_instantiateTermInTerm ctxTerm t cond,
        subst_instantiateTermInTerm ctxTerm t thenTerm,
        subst_instantiateTermInTerm ctxTerm t elseTerm]
  | «recurse» resultTy init body =>
      simp [instantiateTermInTerm, subst_instantiateTermInTerm ctxTerm t init,
        subst_instantiateTermInTerm ctxTerm t body]

theorem subst_instantiateTermInTermList {primCtx : PrimitiveCtx}
    (ctxTerm : List (Term primCtx)) (t : Term primCtx) (terms : List (Term primCtx)) :
    (terms.map (instantiateTermInTerm ctxTerm.length t)).map (Term.subst ctxTerm) =
      terms.map (Term.subst (ctxTerm ++ [Term.subst ctxTerm t])) := by
  cases terms with
  | nil => simp
  | cons head tail =>
      simp [subst_instantiateTermInTerm ctxTerm t head,
        subst_instantiateTermInTermList ctxTerm t tail]

end

def quantifierFree {primCtx : PrimitiveCtx} : Pr (Term primCtx) → Bool
| .eq _ _ _ _ => true
| .hasType _ _ _ => true
| .and p q => quantifierFree p && quantifierFree q
| .or p q => quantifierFree p && quantifierFree q
| .implies p q => quantifierFree p && quantifierFree q
| .forallTy _ => false
| .forallTerm _ => false

theorem interp_instantiateTermAt {ctx : Ctx}
    (ctxTy : List Ty) (ctxTerm : List (Term ctx.primCtx)) (t : Term ctx.primCtx)
    (body : Pr (Term ctx.primCtx)) (hqf : quantifierFree body = true) :
    Pr.interp ctx ctxTy ctxTerm (instantiateTermAt ctxTerm.length body t) ↔
      Pr.interp ctx ctxTy (ctxTerm ++ [Term.subst ctxTerm t]) body := by
  induction body with
  | eq ctx ty lhs rhs =>
      simp [instantiateTermAt, Pr.interp, subst_instantiateTermInTerm]
  | hasType ctx term ty =>
      simp [instantiateTermAt, Pr.interp, subst_instantiateTermInTerm]
  | and p q ihp ihq =>
      simp [quantifierFree] at hqf
      simp [instantiateTermAt, Pr.interp, ihp hqf.1, ihq hqf.2]
  | or p q ihp ihq =>
      simp [quantifierFree] at hqf
      simp [instantiateTermAt, Pr.interp, ihp hqf.1, ihq hqf.2]
  | implies p q ihp ihq =>
      simp [quantifierFree] at hqf
      simp [instantiateTermAt, Pr.interp, ihp hqf.1, ihq hqf.2]
  | forallTy p ih => simp [quantifierFree] at hqf
  | forallTerm p ih => simp [quantifierFree] at hqf

mutual

theorem subst_weakenTermAt_concat {primCtx : PrimitiveCtx}
    (ctxTerm : List (Term primCtx)) (y u : Term primCtx) :
    Term.subst (ctxTerm ++ [y]) (weakenTermAt ctxTerm.length u) = Term.subst ctxTerm u := by
  cases u with
  | prim ty val => simp [weakenTermAt]
  | primFunc name => simp [weakenTermAt]
  | var varIdx =>
      by_cases hlt : varIdx < ctxTerm.length
      · have hle : ¬ ctxTerm.length ≤ varIdx := by omega
        have h2 : varIdx < ctxTerm.length + 1 := by omega
        simp [weakenTermAt, hle, h2, List.getElem_append_left, hlt]
      · have hle : ctxTerm.length ≤ varIdx := by omega
        have h2 : ¬ varIdx + 1 < ctxTerm.length + 1 := by omega
        have h3 : varIdx + 1 - (ctxTerm.length + 1) = varIdx - ctxTerm.length := by omega
        simp [weakenTermAt, hlt, hle, h2, h3]
  | app f args =>
      have hargs : List.map (Term.subst (ctxTerm ++ [y]) ∘ weakenTermAt ctxTerm.length) args =
          List.map (Term.subst ctxTerm) args := by
        simpa [List.map_map, Function.comp_def] using
          subst_weakenTermAt_concatList ctxTerm y args
      simp [weakenTermAt, subst_weakenTermAt_concat ctxTerm y f, hargs]
  | «op» name args =>
      have hargs : List.map (Term.subst (ctxTerm ++ [y]) ∘ weakenTermAt ctxTerm.length) args =
          List.map (Term.subst ctxTerm) args := by
        simpa [List.map_map, Function.comp_def] using
          subst_weakenTermAt_concatList ctxTerm y args
      simp [weakenTermAt, hargs]
  | mkStruct tys => simp [weakenTermAt]
  | structProj tys fieldIdx => simp [weakenTermAt]
  | ite cond thenTerm elseTerm =>
      simp [weakenTermAt, subst_weakenTermAt_concat ctxTerm y cond,
        subst_weakenTermAt_concat ctxTerm y thenTerm,
        subst_weakenTermAt_concat ctxTerm y elseTerm]
  | «recurse» resultTy init body =>
      simp [weakenTermAt, subst_weakenTermAt_concat ctxTerm y init,
        subst_weakenTermAt_concat ctxTerm y body]

theorem subst_weakenTermAt_concatList {primCtx : PrimitiveCtx}
    (ctxTerm : List (Term primCtx)) (y : Term primCtx) (terms : List (Term primCtx)) :
    (terms.map (weakenTermAt ctxTerm.length)).map (Term.subst (ctxTerm ++ [y])) =
      terms.map (Term.subst ctxTerm) := by
  cases terms with
  | nil => simp
  | cons head tail =>
      simp [subst_weakenTermAt_concat ctxTerm y head,
        subst_weakenTermAt_concatList ctxTerm y tail]

end

private theorem subst_var_lt {primCtx : PrimitiveCtx} {ctxTerm : List (Term primCtx)} {idx : Nat}
    (h : idx < ctxTerm.length) :
    Term.subst ctxTerm (.var idx) = (ctxTerm[idx]?).getD (.var idx) := by
  simp [h]

private theorem subst_var_ge {primCtx : PrimitiveCtx} {ctxTerm : List (Term primCtx)} {idx : Nat}
    (h : ¬ idx < ctxTerm.length) :
    Term.subst ctxTerm (.var idx) = .var (idx - ctxTerm.length) := by
  simp [h]

private theorem weakenTermAt_var_lt {primCtx : PrimitiveCtx} {wIdx varIdx : Nat}
    (h : varIdx < wIdx) :
    weakenTermAt (primCtx := primCtx) wIdx (.var varIdx) = .var varIdx := by
  simp [weakenTermAt]; omega

private theorem weakenTermAt_var_ge {primCtx : PrimitiveCtx} {wIdx varIdx : Nat}
    (h : wIdx ≤ varIdx) :
    weakenTermAt (primCtx := primCtx) wIdx (.var varIdx) = .var (varIdx + 1) := by
  simp [weakenTermAt, h]

mutual

theorem subst_weakenTermAt_middle {primCtx : PrimitiveCtx}
    (ctxTerm : List (Term primCtx)) (x y u : Term primCtx) :
    Term.subst (ctxTerm ++ [x, y]) (weakenTermAt ctxTerm.length u) =
      Term.subst (ctxTerm ++ [y]) u := by
  cases u with
  | prim ty val => simp [weakenTermAt]
  | primFunc name => simp [weakenTermAt]
  | var varIdx =>
      by_cases hlt : varIdx < ctxTerm.length
      · rw [weakenTermAt_var_lt hlt,
          subst_var_lt (by simp; omega : varIdx < (ctxTerm ++ [x, y]).length),
          subst_var_lt (by simp; omega : varIdx < (ctxTerm ++ [y]).length),
          List.getElem?_append_left hlt, List.getElem?_append_left hlt]
      · have hle : ctxTerm.length ≤ varIdx := by omega
        by_cases heq : varIdx = ctxTerm.length
        · subst heq
          have e1 : (ctxTerm ++ [x, y])[ctxTerm.length + 1]? = some y := by
            rw [show ctxTerm ++ [x, y] = (ctxTerm ++ [x]) ++ [y] by simp,
              show ctxTerm.length + 1 = (ctxTerm ++ [x]).length by simp]
            exact List.getElem?_concat_length
          have e2 : (ctxTerm ++ [y])[ctxTerm.length]? = some y :=
            List.getElem?_concat_length
          have hLHS := subst_var_lt (ctxTerm := ctxTerm ++ [x, y]) (idx := ctxTerm.length + 1)
            (by simp)
          have hRHS := subst_var_lt (ctxTerm := ctxTerm ++ [y]) (idx := ctxTerm.length)
            (by simp)
          rw [weakenTermAt_var_ge (Nat.le_refl _), hLHS, hRHS, e1, e2]
          rfl
        · rw [weakenTermAt_var_ge hle,
            subst_var_ge (by simp; omega : ¬ varIdx + 1 < (ctxTerm ++ [x, y]).length),
            subst_var_ge (by simp; omega : ¬ varIdx < (ctxTerm ++ [y]).length)]
          congr 1
          simp
  | app f args =>
      have hargs : List.map (Term.subst (ctxTerm ++ [x, y]) ∘ weakenTermAt ctxTerm.length)
            args = List.map (Term.subst (ctxTerm ++ [y])) args := by
        simpa [List.map_map, Function.comp_def] using
          subst_weakenTermAt_middleList ctxTerm x y args
      simp [weakenTermAt, subst_weakenTermAt_middle ctxTerm x y f, hargs]
  | «op» name args =>
      have hargs : List.map (Term.subst (ctxTerm ++ [x, y]) ∘ weakenTermAt ctxTerm.length)
            args = List.map (Term.subst (ctxTerm ++ [y])) args := by
        simpa [List.map_map, Function.comp_def] using
          subst_weakenTermAt_middleList ctxTerm x y args
      simp [weakenTermAt, hargs]
  | mkStruct tys => simp [weakenTermAt]
  | structProj tys fieldIdx => simp [weakenTermAt]
  | ite cond thenTerm elseTerm =>
      simp [weakenTermAt, subst_weakenTermAt_middle ctxTerm x y cond,
        subst_weakenTermAt_middle ctxTerm x y thenTerm,
        subst_weakenTermAt_middle ctxTerm x y elseTerm]
  | «recurse» resultTy init body =>
      simp [weakenTermAt, subst_weakenTermAt_middle ctxTerm x y init,
        subst_weakenTermAt_middle ctxTerm x y body]

theorem subst_weakenTermAt_middleList {primCtx : PrimitiveCtx}
    (ctxTerm : List (Term primCtx)) (x y : Term primCtx) (terms : List (Term primCtx)) :
    (terms.map (weakenTermAt ctxTerm.length)).map (Term.subst (ctxTerm ++ [x, y])) =
      terms.map (Term.subst (ctxTerm ++ [y])) := by
  cases terms with
  | nil => simp
  | cons head tail =>
      simp [subst_weakenTermAt_middle ctxTerm x y head,
        subst_weakenTermAt_middleList ctxTerm x y tail]

end

theorem interp_weaken_concat {ctx : Ctx}
    (ctxTy : List Ty) (ctxTerm : List (Term ctx.primCtx)) (y : Term ctx.primCtx)
    (body : Pr (Term ctx.primCtx)) (hqf : quantifierFree body = true) :
    Pr.interp ctx ctxTy (ctxTerm ++ [y]) (weaken ctxTerm.length body) ↔
      Pr.interp ctx ctxTy ctxTerm body := by
  induction body with
  | eq ctx ty lhs rhs =>
      simp [weaken, Pr.interp, subst_weakenTermAt_concat]
  | hasType ctx term ty =>
      simp [weaken, Pr.interp, subst_weakenTermAt_concat]
  | and p q ihp ihq =>
      simp [quantifierFree] at hqf
      simp [weaken, Pr.interp, ihp hqf.1, ihq hqf.2]
  | or p q ihp ihq =>
      simp [quantifierFree] at hqf
      simp [weaken, Pr.interp, ihp hqf.1, ihq hqf.2]
  | implies p q ihp ihq =>
      simp [quantifierFree] at hqf
      simp [weaken, Pr.interp, ihp hqf.1, ihq hqf.2]
  | forallTy p ih => simp [quantifierFree] at hqf
  | forallTerm p ih => simp [quantifierFree] at hqf

theorem interp_weaken_middle {ctx : Ctx}
    (ctxTy : List Ty) (ctxTerm : List (Term ctx.primCtx)) (x y : Term ctx.primCtx)
    (body : Pr (Term ctx.primCtx)) (hqf : quantifierFree body = true) :
    Pr.interp ctx ctxTy (ctxTerm ++ [x] ++ [y]) (weaken ctxTerm.length body) ↔
      Pr.interp ctx ctxTy (ctxTerm ++ [y]) body := by
  induction body with
  | eq ctx ty lhs rhs =>
      simp [weaken, Pr.interp, subst_weakenTermAt_middle]
  | hasType ctx term ty =>
      simp [weaken, Pr.interp, subst_weakenTermAt_middle]
  | and p q ihp ihq =>
      simp [quantifierFree] at hqf
      simp only [List.append_assoc, List.singleton_append] at ihp ihq
      simp [weaken, Pr.interp, ihp hqf.1, ihq hqf.2]
  | or p q ihp ihq =>
      simp [quantifierFree] at hqf
      simp only [List.append_assoc, List.singleton_append] at ihp ihq
      simp [weaken, Pr.interp, ihp hqf.1, ihq hqf.2]
  | implies p q ihp ihq =>
      simp [quantifierFree] at hqf
      simp only [List.append_assoc, List.singleton_append] at ihp ihq
      simp [weaken, Pr.interp, ihp hqf.1, ihq hqf.2]
  | forallTy p ih => simp [quantifierFree] at hqf
  | forallTerm p ih => simp [quantifierFree] at hqf

structure TermRecurseMatch {primCtx : PrimitiveCtx} (idx : Nat) (term : Term primCtx) where
  init : Term primCtx
  predicateTerm : Term primCtx
  property : instantiateTermInTerm idx init predicateTerm = term

structure TermListRecurseMatch {primCtx : PrimitiveCtx} (idx : Nat) (terms : List (Term primCtx)) where
  init : Term primCtx
  predicateTerms : List (Term primCtx)
  property : predicateTerms.map (instantiateTermInTerm idx init) = terms

mutual

def findRecurseInTerm {primCtx : PrimitiveCtx} (idx : Nat) :
    (term : Term primCtx) → Option (TermRecurseMatch idx term)
| .prim _ _ => none
| .primFunc _ => none
| .var _ => none
| .app f args =>
    match findRecurseInTerm idx f with
    | some found =>
        some
          { init := found.init
            predicateTerm := .app found.predicateTerm (args.map (weakenTermAt idx))
            property := by
              have hargs : List.map (instantiateTermInTerm idx found.init ∘ weakenTermAt idx) args = args := by
                simpa [List.map_map, Function.comp_def] using
                  instantiateTermInTerm_weakenTermAtList idx found.init args
              simp [instantiateTermInTerm, found.property,
                hargs] }
    | none =>
        match findRecurseInTermList idx args with
        | some found =>
            some
              { init := found.init
                predicateTerm := .app (weakenTermAt idx f) found.predicateTerms
                property := by
                  simp [instantiateTermInTerm, found.property,
                    instantiateTermInTerm_weakenTermAt] }
        | none => none
| .op name args =>
    match findRecurseInTermList idx args with
    | some found =>
        some
          { init := found.init
            predicateTerm := .op name found.predicateTerms
            property := by simp [instantiateTermInTerm, found.property] }
    | none => none
| .mkStruct _ => none
| .structProj _ _ => none
| .ite cond thenTerm elseTerm =>
    match findRecurseInTerm idx cond with
    | some found =>
        some
          { init := found.init
            predicateTerm := .ite found.predicateTerm (weakenTermAt idx thenTerm) (weakenTermAt idx elseTerm)
            property := by simp [instantiateTermInTerm, found.property, instantiateTermInTerm_weakenTermAt] }
    | none =>
        match findRecurseInTerm idx thenTerm with
        | some found =>
            some
              { init := found.init
                predicateTerm := .ite (weakenTermAt idx cond) found.predicateTerm (weakenTermAt idx elseTerm)
                property := by simp [instantiateTermInTerm, found.property, instantiateTermInTerm_weakenTermAt] }
        | none =>
            match findRecurseInTerm idx elseTerm with
            | some found =>
                some
                  { init := found.init
                    predicateTerm := .ite (weakenTermAt idx cond) (weakenTermAt idx thenTerm) found.predicateTerm
                    property := by simp [instantiateTermInTerm, found.property, instantiateTermInTerm_weakenTermAt] }
            | none => none
| .recurse resultTy init body =>
    some
      { init := init
        predicateTerm := .recurse resultTy (.var idx) (weakenTermAt idx body)
        property := by simp [instantiateTermInTerm, instantiateTermInTerm_weakenTermAt] }

def findRecurseInTermList {primCtx : PrimitiveCtx} (idx : Nat) :
    (terms : List (Term primCtx)) → Option (TermListRecurseMatch idx terms)
| [] => none
| head :: tail =>
    match findRecurseInTerm idx head with
    | some found =>
        some
          { init := found.init
            predicateTerms := found.predicateTerm :: tail.map (weakenTermAt idx)
            property := by
              have htail : List.map (instantiateTermInTerm idx found.init ∘ weakenTermAt idx) tail = tail := by
                simpa [List.map_map, Function.comp_def] using
                  instantiateTermInTerm_weakenTermAtList idx found.init tail
              simp [found.property, htail] }
    | none =>
        match findRecurseInTermList idx tail with
        | some found =>
            some
              { init := found.init
                predicateTerms := weakenTermAt idx head :: found.predicateTerms
                property := by
                  simp [found.property, instantiateTermInTerm_weakenTermAt] }
        | none => none

end

structure PrRecurseMatch {primCtx : PrimitiveCtx} (idx : Nat) (goal : Pr (Term primCtx)) where
  init : Term primCtx
  predicate : Pr (Term primCtx)
  property : goal = instantiateTermAt idx predicate init

def findRecurseInPr {primCtx : PrimitiveCtx} (idx : Nat) :
    (goal : Pr (Term primCtx)) → Option (PrRecurseMatch idx goal)
| .eq ctx ty lhs rhs =>
    match findRecurseInTerm idx lhs with
    | some found =>
        some
          { init := found.init
            predicate := .eq ctx ty found.predicateTerm (weakenTermAt idx rhs)
            property := by simp [instantiateTermAt, found.property, instantiateTermInTerm_weakenTermAt] }
    | none =>
        match findRecurseInTerm idx rhs with
        | some found =>
            some
              { init := found.init
                predicate := .eq ctx ty (weakenTermAt idx lhs) found.predicateTerm
                property := by simp [instantiateTermAt, found.property, instantiateTermInTerm_weakenTermAt] }
        | none => none
| .hasType ctx term ty =>
    match findRecurseInTerm idx term with
    | some found =>
        some
          { init := found.init
            predicate := .hasType ctx found.predicateTerm ty
            property := by simp [instantiateTermAt, found.property] }
    | none => none
| .and p q =>
    match findRecurseInPr idx p with
    | some found =>
        some
          { init := found.init
            predicate := .and found.predicate (weaken idx q)
            property := by simp [instantiateTermAt, found.property, instantiateTermAt_weaken] }
    | none =>
        match findRecurseInPr idx q with
        | some found =>
            some
              { init := found.init
                predicate := .and (weaken idx p) found.predicate
                property := by simp [instantiateTermAt, found.property, instantiateTermAt_weaken] }
        | none => none
| .or p q =>
    match findRecurseInPr idx p with
    | some found =>
        some
          { init := found.init
            predicate := .or found.predicate (weaken idx q)
            property := by simp [instantiateTermAt, found.property, instantiateTermAt_weaken] }
    | none =>
        match findRecurseInPr idx q with
        | some found =>
            some
              { init := found.init
                predicate := .or (weaken idx p) found.predicate
                property := by simp [instantiateTermAt, found.property, instantiateTermAt_weaken] }
        | none => none
| .implies p q =>
    match findRecurseInPr idx p with
    | some found =>
        some
          { init := found.init
            predicate := .implies found.predicate (weaken idx q)
            property := by simp [instantiateTermAt, found.property, instantiateTermAt_weaken] }
    | none =>
        match findRecurseInPr idx q with
        | some found =>
            some
              { init := found.init
                predicate := .implies (weaken idx p) found.predicate
                property := by simp [instantiateTermAt, found.property, instantiateTermAt_weaken] }
        | none => none
| .forallTy p =>
    match findRecurseInPr idx p with
    | some found =>
        some
          { init := found.init
            predicate := .forallTy found.predicate
            property := by simp [instantiateTermAt, found.property] }
    | none => none
| .forallTerm p =>
    match findRecurseInPr idx p with
    | some found =>
        some
          { init := found.init
            predicate := .forallTerm found.predicate
            property := by simp [instantiateTermAt, found.property] }
    | none => none

def sameKnownTerm? {primCtx : PrimitiveCtx} (term init : Term primCtx) :
    Option { _witness : Unit // term = init } :=
  match term, init with
  | .var termIdx, .var initIdx =>
      if h : termIdx = initIdx then some ⟨(), by rw [h]⟩ else none
  | term, init =>
      match term.natLit?, init.natLit? with
      | some ⟨termN, hterm⟩, some ⟨initN, hinit⟩ =>
          if h : termN = initN then
            some ⟨(), by
              calc
                term = Term.nat termN := hterm
                _ = Term.nat initN := by rw [h]
                _ = init := hinit.symm⟩
          else none
      | _, _ => none

structure TermAbstract {primCtx : PrimitiveCtx} (idx : Nat) (init term : Term primCtx) where
  predicateTerm : Term primCtx
  property : instantiateTermInTerm idx init predicateTerm = term

structure TermListAbstract {primCtx : PrimitiveCtx} (idx : Nat) (init : Term primCtx)
    (terms : List (Term primCtx)) where
  predicateTerms : List (Term primCtx)
  property : predicateTerms.map (instantiateTermInTerm idx init) = terms

mutual

def abstractInitInTerm {primCtx : PrimitiveCtx} (idx : Nat) (init : Term primCtx) :
    (term : Term primCtx) → TermAbstract idx init term
| .prim ty val =>
    match sameKnownTerm? (.prim ty val) init with
    | some h =>
        { predicateTerm := .var idx
          property := by rw [h.property]; simp [instantiateTermInTerm] }
    | none =>
        { predicateTerm := weakenTermAt idx (.prim ty val)
          property := instantiateTermInTerm_weakenTermAt idx init (.prim ty val) }
| .primFunc name =>
    match sameKnownTerm? (.primFunc name) init with
    | some h =>
        { predicateTerm := .var idx
          property := by rw [h.property]; simp [instantiateTermInTerm] }
    | none =>
        { predicateTerm := weakenTermAt idx (.primFunc name)
          property := instantiateTermInTerm_weakenTermAt idx init (.primFunc name) }
| .var varIdx =>
    match sameKnownTerm? (.var varIdx) init with
    | some h =>
        { predicateTerm := .var idx
          property := by rw [h.property]; simp [instantiateTermInTerm] }
    | none =>
        { predicateTerm := weakenTermAt idx (.var varIdx)
          property := instantiateTermInTerm_weakenTermAt idx init (.var varIdx) }
| .app f args =>
    match sameKnownTerm? (.app f args) init with
    | some h =>
        { predicateTerm := .var idx
          property := by rw [h.property]; simp [instantiateTermInTerm] }
    | none =>
        let abstractF := abstractInitInTerm idx init f
        let abstractArgs := abstractInitInTermList idx init args
        { predicateTerm := .app abstractF.predicateTerm abstractArgs.predicateTerms
          property := by simp [instantiateTermInTerm, abstractF.property, abstractArgs.property] }
| .op name args =>
    match sameKnownTerm? (.op name args) init with
    | some h =>
        { predicateTerm := .var idx
          property := by rw [h.property]; simp [instantiateTermInTerm] }
    | none =>
        let abstractArgs := abstractInitInTermList idx init args
        { predicateTerm := .op name abstractArgs.predicateTerms
          property := by simp [instantiateTermInTerm, abstractArgs.property] }
| .mkStruct tys =>
    match sameKnownTerm? (.mkStruct tys) init with
    | some h =>
        { predicateTerm := .var idx
          property := by rw [h.property]; simp [instantiateTermInTerm] }
    | none =>
        { predicateTerm := weakenTermAt idx (.mkStruct tys)
          property := instantiateTermInTerm_weakenTermAt idx init (.mkStruct tys) }
| .structProj tys fieldIdx =>
    match sameKnownTerm? (.structProj tys fieldIdx) init with
    | some h =>
        { predicateTerm := .var idx
          property := by rw [h.property]; simp [instantiateTermInTerm] }
    | none =>
        { predicateTerm := weakenTermAt idx (.structProj tys fieldIdx)
          property := instantiateTermInTerm_weakenTermAt idx init (.structProj tys fieldIdx) }
| .ite cond thenTerm elseTerm =>
    match sameKnownTerm? (.ite cond thenTerm elseTerm) init with
    | some h =>
        { predicateTerm := .var idx
          property := by rw [h.property]; simp [instantiateTermInTerm] }
    | none =>
        let abstractCond := abstractInitInTerm idx init cond
        let abstractThen := abstractInitInTerm idx init thenTerm
        let abstractElse := abstractInitInTerm idx init elseTerm
        { predicateTerm := .ite abstractCond.predicateTerm abstractThen.predicateTerm abstractElse.predicateTerm
          property := by
            simp [instantiateTermInTerm, abstractCond.property, abstractThen.property,
              abstractElse.property] }
| .recurse resultTy recInit body =>
    match sameKnownTerm? (.recurse resultTy recInit body) init with
    | some h =>
        { predicateTerm := .var idx
          property := by rw [h.property]; simp [instantiateTermInTerm] }
    | none =>
        let abstractInit := abstractInitInTerm idx init recInit
        { predicateTerm := .recurse resultTy abstractInit.predicateTerm (weakenTermAt idx body)
          property := by
            simp [instantiateTermInTerm, abstractInit.property,
              instantiateTermInTerm_weakenTermAt] }

def abstractInitInTermList {primCtx : PrimitiveCtx} (idx : Nat) (init : Term primCtx) :
    (terms : List (Term primCtx)) → TermListAbstract idx init terms
| [] =>
    { predicateTerms := []
      property := by simp }
| head :: tail =>
    let abstractHead := abstractInitInTerm idx init head
    let abstractTail := abstractInitInTermList idx init tail
    { predicateTerms := abstractHead.predicateTerm :: abstractTail.predicateTerms
      property := by simp [abstractHead.property, abstractTail.property] }

end

@[simp] theorem abstractInitInTerm_nat_self {primCtx : PrimitiveCtx} (idx n : Nat) :
    (abstractInitInTerm idx (Term.nat (primCtx := primCtx) n) (Term.nat n)).predicateTerm =
      .var idx := by
  simp [abstractInitInTerm, sameKnownTerm?, Term.natLit?, Term.nat, Ty.ofNat, Ty.toNat]

@[simp] theorem abstractInitInTerm_nat_ne {primCtx : PrimitiveCtx} (idx m n : Nat)
    (hne : ¬ m = n) :
    (abstractInitInTerm idx (Term.nat (primCtx := primCtx) n) (Term.nat m)).predicateTerm =
      Term.nat m := by
  simp [abstractInitInTerm, sameKnownTerm?, weakenTermAt, Term.natLit?, Term.nat,
    Ty.ofNat, Ty.toNat, hne]

structure PrAbstract {primCtx : PrimitiveCtx} (idx : Nat) (init : Term primCtx)
    (goal : Pr (Term primCtx)) where
  predicate : Pr (Term primCtx)
  property : goal = instantiateTermAt idx predicate init

def abstractInitInPr {primCtx : PrimitiveCtx} (idx : Nat) (init : Term primCtx) :
    (goal : Pr (Term primCtx)) → PrAbstract idx init goal
| .eq ctx ty lhs rhs =>
    let abstractLhs := abstractInitInTerm idx init lhs
    let abstractRhs := abstractInitInTerm idx init rhs
    { predicate := .eq ctx ty abstractLhs.predicateTerm abstractRhs.predicateTerm
      property := by simp [instantiateTermAt, abstractLhs.property, abstractRhs.property] }
| .hasType ctx term ty =>
    let abstractTerm := abstractInitInTerm idx init term
    { predicate := .hasType ctx abstractTerm.predicateTerm ty
      property := by simp [instantiateTermAt, abstractTerm.property] }
| .and p q =>
    let abstractP := abstractInitInPr idx init p
    let abstractQ := abstractInitInPr idx init q
    { predicate := .and abstractP.predicate abstractQ.predicate
      property := by simp [instantiateTermAt, abstractP.property, abstractQ.property] }
| .or p q =>
    let abstractP := abstractInitInPr idx init p
    let abstractQ := abstractInitInPr idx init q
    { predicate := .or abstractP.predicate abstractQ.predicate
      property := by simp [instantiateTermAt, abstractP.property, abstractQ.property] }
| .implies p q =>
    let abstractP := abstractInitInPr idx init p
    let abstractQ := abstractInitInPr idx init q
    { predicate := .implies abstractP.predicate abstractQ.predicate
      property := by simp [instantiateTermAt, abstractP.property, abstractQ.property] }
| .forallTy p =>
    let abstractP := abstractInitInPr idx init p
    { predicate := .forallTy abstractP.predicate
      property := by simp [instantiateTermAt, abstractP.property] }
| .forallTerm p =>
    let abstractP := abstractInitInPr idx init p
    { predicate := .forallTerm abstractP.predicate
      property := by simp [instantiateTermAt, abstractP.property] }

/-- `(succ x == y) = true`. The built-in `eq` operator forces both sides to evaluate to equal
  values (the same termination trick `lt` previously provided). -/
def succEq {primCtx : PrimitiveCtx} (idx : Nat) (succName : String) : Pr (Term primCtx) :=
  .eq [] (.prim "Bool")
    (.op "eq" [.app (.primFunc succName) [.var idx], .var (idx + 1)])
    (Term.bool true)

def natStepGoal {primCtx : PrimitiveCtx} (idx : Nat) (succName : String) (body : Pr (Term primCtx)) :
    Pr (Term primCtx) :=
  .forallNat idx (.forallNat (idx + 1)
    (.implies (succEq idx succName)
      (.implies (weaken (idx + 1) body) (weaken idx body))))

def natInductionGoals {primCtx : PrimitiveCtx} (idx : Nat) (succName : String)
    (body : Pr (Term primCtx)) : List (Pr (Term primCtx)) :=
  [instantiateTermAt idx body (Term.nat 0), natStepGoal idx succName body]

/-- `succName` is a successor primfunc: types as `Nat → Nat`, maps value `m` to `m+1`,
  and inverts whenever the application evaluates. -/
structure SuccSpec (ctx : Ctx) (succName : String) : Prop where
  hasType_app : ∀ (varCtx : VarCtx) (t : Term ctx.primCtx),
    Term.hasType ctx varCtx t (.prim "Nat") →
    Term.hasType ctx varCtx (.app (.primFunc succName) [t]) (.prim "Nat")
  eval_succ : ∀ (t : Term ctx.primCtx) (m : Nat),
    Term.eval ctx [] t = some (Val.nat m) →
    Term.eval ctx [] (.app (.primFunc succName) [t]) = some (Val.nat (m + 1))
  eval_succ_inv : ∀ (t : Term ctx.primCtx) (v : Val ctx.primCtx),
    Term.eval ctx [] (.app (.primFunc succName) [t]) = some v →
    ∃ m : Nat, Term.eval ctx [] t = some (Val.nat m) ∧ v = Val.nat (m + 1)

private theorem natLit_hasType {ctx : Ctx} (varCtx : VarCtx) (n : Nat) :
    Term.hasType ctx varCtx (Term.nat n) (.prim "Nat") :=
  Term.hasType.prim (Ty.ofNat ctx.primCtx n)

private theorem boolLit_hasType {ctx : Ctx} (varCtx : VarCtx) (b : Bool) :
    Term.hasType ctx varCtx (Term.bool b) (.prim "Bool") :=
  Term.hasType.prim (Ty.ofBool ctx.primCtx b)

private theorem eval_natLit {ctx : Ctx} (n : Nat) :
    Term.eval ctx [] (Term.nat n) = some (Val.nat n) := by
  simp [Term.eval, Term.evalGo, Term.nat]

private theorem op_eq_hasType {ctx : Ctx} {varCtx : VarCtx} {a b : Term ctx.primCtx} {ty : Ty}
    (ha : Term.hasType ctx varCtx a ty) (hb : Term.hasType ctx varCtx b ty) :
    Term.hasType ctx varCtx (.op "eq" [a, b]) (.prim "Bool") := by
  refine Term.hasType.op (name := "eq") (args := [a, b]) (tys := [ty, ty]) rfl ?_ ?_
  · intro idx
    match idx with
    | ⟨0, _⟩ => simpa using ha
    | ⟨1, _⟩ => simpa using hb
    | ⟨n + 2, h⟩ =>
        simp at h
        omega
  · simp [OpCtx.outTy?]

private theorem valBool_inj {primCtx : PrimitiveCtx} {a b : Bool}
    (h : (Val.bool (primCtx := primCtx) a) = Val.bool b) : a = b := by
  have := congrArg Val.asBool? h
  simpa using this

private theorem asNat?_eq_some {primCtx : PrimitiveCtx} {v : Val primCtx} {k : Nat}
    (h : v.asNat? = some k) : v = Val.nat k := by
  unfold Val.asNat? Val.as? at h
  by_cases hty : v.ty = .prim "Nat"
  · simp [hty] at h
    cases v with
    | mk ty val =>
        simp at hty
        subst hty
        rw [← Val.mk_ofNat]
        congr 1
        rw [← h]
        simp [Ty.ofNat, Ty.toNat]
  · simp [hty] at h

private theorem eval_op_eq_bool {ctx : Ctx} {a b : Term ctx.primCtx} {c : Bool}
    (h : Term.eq ctx [] (.prim "Bool") (.op "eq" [a, b]) (Term.bool c)) :
    ∃ va vb, Term.eval ctx [] a = some va ∧ Term.eval ctx [] b = some vb ∧
      Val.primEq? va vb = some c ∧ va.ty = vb.ty := by
  have heval := h.eq [] rfl
  simp only [Term.eval] at heval
  cases ha : Term.evalGo ctx [] [] a with
  | none =>
      simp [Term.evalGo, Term.evalList, OpCtx.get?, Op.eq, ha, Term.bool] at heval
  | some va =>
      cases hb : Term.evalGo ctx [] [] b with
      | none =>
          simp [Term.evalGo, Term.evalList, OpCtx.get?, Op.eq, ha, hb, Term.bool] at heval
      | some vb =>
          -- heval : evalGo (op eq [a,b]) = evalGo (bool c) = some (Val.bool c)
          have hrhs : Term.evalGo ctx [] [] (Term.bool c) = some (Val.bool c) := by
            simp [Term.evalGo, Term.bool]
          rw [hrhs] at heval
          -- Need va.ty = vb.ty for applyVals_compare. Derive by cases: if unequal, LHS is none.
          by_cases hty : va.ty = vb.ty
          · have hcmp_form := Term.evalGo_op_compare
              (ctx := ctx) (motives := []) (env := []) (name := "eq")
              (cmp := Val.primEq?) (va := va) (vb := vb)
              (by simp [OpCtx.get?, Op.eq]) ha hb hty
            rw [hcmp_form] at heval
            cases hcmp : Val.primEq? va vb with
            | none => simp [hcmp] at heval
            | some c' =>
                simp [hcmp] at heval
                exact ⟨va, vb, ha, hb, by rw [hcmp, valBool_inj heval], hty⟩
          · have hform :
                Term.evalGo ctx [] [] (.op "eq" [a, b]) =
                  Op.applyVals (Op.eq (primCtx := ctx.primCtx)) [va, vb] := by
              simp [Term.evalGo, Term.evalList, OpCtx.get?, Op.eq, ha, hb]
            rw [hform] at heval
            have hnone : Op.applyVals (Op.eq (primCtx := ctx.primCtx)) [va, vb] = none := by
              dsimp [Op.applyVals, Op.eq, Op.compare]
              rw [if_neg hty]
            simp [hnone] at heval

/-- From `succEq` holding of `(x, y)`, extract `x ↝ nat k` and `y ↝ nat (k + 1)`. -/
theorem succEq_extract {ctx : Ctx} {ctxTy : List Ty} {ctxTerm : List (Term ctx.primCtx)}
    {x y : Term ctx.primCtx} {succName : String}
    (hspec : SuccSpec ctx succName)
    (hsucc : Pr.interp ctx ctxTy (ctxTerm ++ [x, y]) (succEq ctxTerm.length succName)) :
    ∃ k : Nat, Term.eval ctx [] x = some (Val.nat k) ∧
      Term.eval ctx [] y = some (Val.nat (k + 1)) := by
  have heq : Term.eq ctx [] (.prim "Bool")
      (.op "eq" [.app (.primFunc succName) [x], y]) (Term.bool true) := by
    simpa [Pr.interp, succEq, Ty.subst, Term.bool, Term.subst, Nat.lt_add_one] using hsucc
  obtain ⟨va, vb, hva, hvb, hcmp, _hty⟩ := eval_op_eq_bool heq
  obtain ⟨m, hx, rfl⟩ := hspec.eval_succ_inv x va hva
  have hna : (Val.nat (primCtx := ctx.primCtx) (m + 1)).asNat? = some (m + 1) := by
    simp [Val.asNat?, Val.as?, Val.nat, Ty.toNat, Ty.ofNat]
  cases hnb : vb.asNat? with
  | none =>
      unfold Val.primEq? at hcmp
      rw [hna, hnb] at hcmp
      have hba : (Val.nat (primCtx := ctx.primCtx) (m + 1)).asBool? = none := rfl
      simp [hba] at hcmp
  | some m' =>
      unfold Val.primEq? at hcmp
      rw [hna, hnb] at hcmp
      have hm' : m' = m + 1 := by
        have : decide (m + 1 = m') = true := Option.some.inj hcmp
        exact (of_decide_eq_true this).symm
      have hvbeq : vb = Val.nat (m + 1) := by
        rw [hm'] at hnb
        exact asNat?_eq_some hnb
      exact ⟨m, hx, hvbeq ▸ hvb⟩

private theorem succEq_natLit {ctx : Ctx} {succName : String} (hspec : SuccSpec ctx succName)
    (k : Nat) :
    Term.eq ctx [] (.prim "Bool")
      (.op "eq" [.app (.primFunc succName) [Term.nat k], Term.nat (k + 1)])
      (Term.bool true) := by
  have hs := hspec.eval_succ (Term.nat k) k (eval_natLit k)
  refine Term.eq.mk
    (op_eq_hasType (hspec.hasType_app [] (Term.nat k) (natLit_hasType [] k))
      (natLit_hasType [] (k + 1)))
    (boolLit_hasType [] true)
    (by
      intro env henv
      have hnil : env = [] := List.eq_nil_of_length_eq_zero henv
      subst hnil
      have hs' : Term.evalGo ctx [] [] (.app (.primFunc succName) [Term.nat k]) =
          some (Val.nat (k + 1)) := hs
      have hy : Term.evalGo ctx [] [] (Term.nat (k + 1)) = some (Val.nat (k + 1)) := by
        simp [Term.evalGo, Term.nat]
      simp only [Term.eval]
      have hgo := Term.evalGo_op_compare
        (ctx := ctx) (motives := []) (env := []) (name := "eq")
        (cmp := Val.primEq?) (va := Val.nat (k + 1)) (vb := Val.nat (k + 1))
        (by simp [OpCtx.get?, Op.eq]) hs' hy rfl
      have hpe : Val.primEq? (Val.nat (primCtx := ctx.primCtx) (k + 1)) (Val.nat (k + 1)) =
          some true := by
        simp [Val.primEq?, Val.asNat?, Val.as?, Val.nat, Ty.toNat, Ty.ofNat]
      rw [hgo, hpe]
      -- RHS is evalGo (bool true) = some (Val.bool true)
      change some (Val.bool true) = Term.evalGo ctx [] [] (Term.bool true)
      simp [Term.evalGo, Term.bool])

/-- Builds the term-quantified step goal `natStepGoal 0 succName predicate` from a step
  function indexed by literal `Nat`s. -/
theorem natStepGoal_of_literal_step {ctx : Ctx} {ctxTy : List Ty}
    {predicate : Pr (Term ctx.primCtx)} {succName : String}
    (hspec : SuccSpec ctx succName)
    (hqf : quantifierFree predicate = true)
    (hcongr : ∀ (t : Term ctx.primCtx) (k : Nat),
      Term.hasType ctx [] t (.prim "Nat") →
      Term.eval ctx [] t = some (Val.nat k) →
      (Pr.Provable ctx ctxTy [] (instantiateTermAt 0 predicate t) ↔
        Pr.Provable ctx ctxTy [] (instantiateTermAt 0 predicate (Term.nat k))))
    (hstep : ∀ k : Nat,
      Pr.Provable ctx ctxTy [] (instantiateTermAt 0 predicate (Term.nat k)) →
      Pr.Provable ctx ctxTy [] (instantiateTermAt 0 predicate (Term.nat (k + 1)))) :
    Pr.Provable ctx ctxTy [] (natStepGoal 0 succName predicate) := by
  refine Pr.Provable.ofProof ?_
  intro x hxtyRaw y hytyRaw hsuccRaw hbodyRaw
  have hxty : Term.hasType ctx [] x (.prim "Nat") := by
    simpa [Pr.interp, Ty.subst] using hxtyRaw
  have hyty : Term.hasType ctx [] y (.prim "Nat") := by
    simpa [Pr.interp, Ty.subst] using hytyRaw
  have hsuccInterp : Pr.interp ctx ctxTy (([] : List (Term ctx.primCtx)) ++ [x, y])
      (succEq 0 succName) := hsuccRaw
  obtain ⟨k, hxe, hye⟩ := succEq_extract hspec hsuccInterp
  have hwkPrev := interp_weaken_concat ctxTy [x] y predicate hqf
  have hbodyPrev : Pr.interp ctx ctxTy ([x] ++ [y])
      (weaken ([x] : List (Term ctx.primCtx)).length predicate) := hbodyRaw
  have hprevInterp : Pr.interp ctx ctxTy [x] predicate := hwkPrev.mp hbodyPrev
  have hbridgePrev := interp_instantiateTermAt ctxTy
    ([] : List (Term ctx.primCtx)) x predicate hqf
  simp only [Term.subst_nil, List.length_nil] at hbridgePrev
  have hprevProvX : Pr.Provable ctx ctxTy [] (instantiateTermAt 0 predicate x) :=
    Pr.Provable.ofProof (hbridgePrev.mpr (by simpa using hprevInterp))
  have hprevProvK : Pr.Provable ctx ctxTy [] (instantiateTermAt 0 predicate (Term.nat k)) :=
    (hcongr x k hxty hxe).mp hprevProvX
  have hnextProvK := hstep k hprevProvK
  have hnextProvY : Pr.Provable ctx ctxTy [] (instantiateTermAt 0 predicate y) :=
    (hcongr y (k + 1) hyty hye).mpr hnextProvK
  cases hnextProvY with
  | ofProof hnextInterp =>
      have hbridgeNext := interp_instantiateTermAt ctxTy
        ([] : List (Term ctx.primCtx)) y predicate hqf
      simp only [Term.subst_nil, List.length_nil] at hbridgeNext
      have hyInterp : Pr.interp ctx ctxTy ([] ++ [y]) predicate :=
        hbridgeNext.mp hnextInterp
      have hwkNext := interp_weaken_middle ctxTy
        ([] : List (Term ctx.primCtx)) x y predicate hqf
      exact hwkNext.mpr (by simpa using hyInterp)

theorem natInductionChain {ctx : Ctx} {ctxTy : List Ty}
    {ctxTerm : List (Term ctx.primCtx)} {body : Pr (Term ctx.primCtx)} {succName : String}
    (hspec : SuccSpec ctx succName)
    (hqf : quantifierFree body = true)
    (hbase : Pr.Provable ctx ctxTy ctxTerm
      (instantiateTermAt ctxTerm.length body (Term.nat 0)))
    (hstep : Pr.Provable ctx ctxTy ctxTerm
      (natStepGoal ctxTerm.length succName body)) :
    ∀ n, Pr.Provable ctx ctxTy ctxTerm
      (instantiateTermAt ctxTerm.length body (Term.nat n)) := by
  cases hstep with
  | ofProof hstepProof =>
      intro n
      induction n with
      | zero => exact hbase
      | succ k ih =>
          cases ih with
          | ofProof ihProof =>
              refine Pr.Provable.ofProof ?_
              have hvarx : Term.subst (ctxTerm ++ [Term.nat k]) (.var ctxTerm.length) =
                  Term.nat k := by
                simp [Nat.lt_add_one]
              have hguardx : Pr.interp ctx ctxTy (ctxTerm ++ [Term.nat k])
                  (.hasType [] (.var ctxTerm.length) (.prim "Nat")) := by
                simpa [Pr.interp, hvarx, Ty.subst] using natLit_hasType (ctx := ctx) [] k
              have hy := hstepProof (Term.nat k) hguardx
              have hvary : Term.subst (ctxTerm ++ [Term.nat k] ++ [Term.nat (k + 1)])
                  (.var (ctxTerm.length + 1)) = Term.nat (k + 1) := by
                have e : (ctxTerm ++ [Term.nat k] ++
                    [Term.nat (k + 1)])[ctxTerm.length + 1]? = some (Term.nat (k + 1)) := by
                  rw [show ctxTerm.length + 1 = (ctxTerm ++ [Term.nat k]).length by simp]
                  exact List.getElem?_concat_length
                have hc : ctxTerm.length + 1 < ctxTerm.length + 1 + 1 := by omega
                simp [e, hc]
              have hguardy : Pr.interp ctx ctxTy
                  (ctxTerm ++ [Term.nat k] ++ [Term.nat (k + 1)])
                  (.hasType [] (.var (ctxTerm.length + 1)) (.prim "Nat")) := by
                simpa [Pr.interp, hvary, Ty.subst] using
                  natLit_hasType (ctx := ctx) [] (k + 1)
              have h1 := hy (Term.nat (k + 1)) hguardy
              have hvarx2 : Term.subst (ctxTerm ++ [Term.nat k] ++ [Term.nat (k + 1)])
                  (.var ctxTerm.length) = Term.nat k := by
                have e : (ctxTerm ++ [Term.nat k] ++
                    [Term.nat (k + 1)])[ctxTerm.length]? = some (Term.nat k) := by
                  rw [List.getElem?_append_left (by simp)]
                  exact List.getElem?_concat_length
                have hc : ctxTerm.length < ctxTerm.length + 1 + 1 := by omega
                simp [e, hc]
              have hsuccGoal : Pr.interp ctx ctxTy
                  (ctxTerm ++ [Term.nat k] ++ [Term.nat (k + 1)])
                  (succEq ctxTerm.length succName) := by
                have hlit := succEq_natLit hspec k
                simpa [succEq, Pr.interp, hvarx2, hvary, Ty.subst, Term.bool, Term.subst]
                  using hlit
              have h2 := h1 hsuccGoal
              have hlen1 : (ctxTerm ++ [Term.nat k]).length = ctxTerm.length + 1 := by simp
              have hwk1 := interp_weaken_concat ctxTy
                (ctxTerm ++ [Term.nat k]) (Term.nat (k + 1)) body hqf
              rw [hlen1] at hwk1
              have hbx := hwk1.mpr (by
                have h' := (interp_instantiateTermAt ctxTy ctxTerm (Term.nat k) body hqf).mp
                  ihProof
                rwa [show Term.subst ctxTerm (Term.nat k) = Term.nat k by simp [Term.nat]] at h')
              have h3 := h2 hbx
              have hwk2 := interp_weaken_middle ctxTy ctxTerm
                (Term.nat k) (Term.nat (k + 1)) body hqf
              have hfin := hwk2.mp h3
              refine (interp_instantiateTermAt ctxTy ctxTerm (Term.nat (k + 1)) body hqf).mpr ?_
              rwa [show Term.subst ctxTerm (Term.nat (k + 1)) = Term.nat (k + 1) by
                simp [Term.nat]]

def natInductionWithPredicate {ctx : Ctx}
    {ctxTy : List Ty} {ctxTerm : List (Term ctx.primCtx)}
    (succName : String) (hspec : SuccSpec ctx succName)
    (goal : Pr (Term ctx.primCtx)) (predicate : Pr (Term ctx.primCtx)) (target : Nat)
    (hinst : goal = instantiateTermAt ctxTerm.length predicate (Term.nat target))
    (hqf : quantifierFree predicate = true) :
    Refinement ctx ctxTy ctxTerm goal :=
  { goals := natInductionGoals ctxTerm.length succName predicate
    prove := by
      intro proveSubgoals
      simp only [Language.Provable_term] at proveSubgoals ⊢
      have hbase := proveSubgoals (instantiateTermAt ctxTerm.length predicate (Term.nat 0))
        (by simp [natInductionGoals])
      have hstep := proveSubgoals (natStepGoal ctxTerm.length succName predicate)
        (by simp [natInductionGoals])
      rw [hinst]
      exact natInductionChain hspec hqf hbase hstep target }

def simpleInduction {ctx : Ctx}
    {ctxTy : List Ty} {ctxTerm : List (Term ctx.primCtx)}
    (succName : String) (hspec : SuccSpec ctx succName) :
    Tactic? ctx ctxTy ctxTerm (Term ctx.primCtx)
| goal =>
    match findRecurseInPr ctxTerm.length goal with
    | some found =>
        match found.init.natLit? with
        | some target =>
            let abstracted := abstractInitInPr ctxTerm.length found.init goal
            let body := abstracted.predicate
            if hqf : quantifierFree body then
              have hgoalEq :
                  instantiateTermAt ctxTerm.length body (Term.nat target.val) = goal := by
                dsimp [body]
                calc
                  instantiateTermAt ctxTerm.length abstracted.predicate (Term.nat target.val)
                      = instantiateTermAt ctxTerm.length abstracted.predicate found.init := by
                        rw [← target.property]
                  _ = goal := abstracted.property.symm
              some (natInductionWithPredicate succName hspec goal body target.val hgoalEq.symm hqf)
            else
              none
        | none =>
            let abstracted := abstractInitInPr ctxTerm.length found.init goal
            if hqf : quantifierFree abstracted.predicate then
              let refinement : Refinement ctx ctxTy ctxTerm goal :=
                { goals :=
                  [ .hasType [] found.init (.prim "Nat")
                  , Pr.forallNat ctxTerm.length abstracted.predicate ]
                  prove := by
                    intro proveSubgoals
                    simp only [Language.Provable_term] at proveSubgoals ⊢
                    have htype : Pr.Provable ctx ctxTy ctxTerm
                        (.hasType [] found.init (.prim "Nat")) :=
                      proveSubgoals (.hasType [] found.init (.prim "Nat")) (by simp)
                    have hforall : Pr.Provable ctx ctxTy ctxTerm
                        (.forallNat ctxTerm.length abstracted.predicate) :=
                      proveSubgoals
                        (.forallNat ctxTerm.length abstracted.predicate) (by simp)
                    cases htype with
                    | ofProof htypeProof =>
                        cases hforall with
                        | ofProof hforallProof =>
                            refine Pr.Provable.ofProof ?_
                            have hx := hforallProof (Term.subst ctxTerm found.init)
                            have hvar : Term.subst (ctxTerm ++ [Term.subst ctxTerm found.init])
                                (.var ctxTerm.length) = Term.subst ctxTerm found.init := by
                              simp [Nat.lt_add_one]
                            have hpremise : Pr.interp ctx ctxTy
                                (ctxTerm ++ [Term.subst ctxTerm found.init])
                                (.hasType [] (.var ctxTerm.length) (.prim "Nat")) := by
                              simpa [Pr.interp, hvar, Ty.subst] using htypeProof
                            have hbody := hx hpremise
                            show Pr.interp ctx ctxTy ctxTerm goal
                            rw [abstracted.property]
                            exact (interp_instantiateTermAt ctxTy ctxTerm found.init
                              abstracted.predicate hqf).mpr hbody }
              some refinement
            else
              none
    | none =>
        none

end Induction

end Pr

end Zag
