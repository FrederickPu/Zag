import Zag.Meta

namespace Zag

namespace Pr

namespace MetaProgram

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
| .primEq lhs rhs => .primEq (instantiateTermInTerm idx replacement lhs) (instantiateTermInTerm idx replacement rhs)
| .primLt lhs rhs => .primLt (instantiateTermInTerm idx replacement lhs) (instantiateTermInTerm idx replacement rhs)
| .primGt lhs rhs => .primGt (instantiateTermInTerm idx replacement lhs) (instantiateTermInTerm idx replacement rhs)
| .mkStruct tys => .mkStruct tys
| .structProj tys fieldIdx => .structProj tys fieldIdx
| .ite cond thenTerm elseTerm =>
    .ite (instantiateTermInTerm idx replacement cond)
      (instantiateTermInTerm idx replacement thenTerm)
      (instantiateTermInTerm idx replacement elseTerm)
| .recurse resultTy init body =>
    .recurse resultTy (instantiateTermInTerm idx replacement init)
      (instantiateTermInTerm idx replacement body)

def instantiateTermAt {primCtx : PrimitiveCtx} (idx : Nat) (body : Pr primCtx) (term : Term primCtx) : Pr primCtx :=
  match body with
  | .eq ctx ty lhs rhs => .eq ctx ty (instantiateTermInTerm idx term lhs) (instantiateTermInTerm idx term rhs)
  | .hasType ctx t ty => .hasType ctx (instantiateTermInTerm idx term t) ty
  | .and p q => .and (instantiateTermAt idx p term) (instantiateTermAt idx q term)
  | .or p q => .or (instantiateTermAt idx p term) (instantiateTermAt idx q term)
  | .implies p q => .implies (instantiateTermAt idx p term) (instantiateTermAt idx q term)
  | .forallTy p => .forallTy (instantiateTermAt idx p term)
  | .forallTerm p => .forallTerm (instantiateTermAt idx p term)

abbrev instantiateTerm {primCtx : PrimitiveCtx} (body : Pr primCtx) (term : Term primCtx) : Pr primCtx :=
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
| .primEq lhs rhs => .primEq (weakenTermAt idx lhs) (weakenTermAt idx rhs)
| .primLt lhs rhs => .primLt (weakenTermAt idx lhs) (weakenTermAt idx rhs)
| .primGt lhs rhs => .primGt (weakenTermAt idx lhs) (weakenTermAt idx rhs)
| .mkStruct tys => .mkStruct tys
| .structProj tys fieldIdx => .structProj tys fieldIdx
| .ite cond thenTerm elseTerm =>
    .ite (weakenTermAt idx cond) (weakenTermAt idx thenTerm) (weakenTermAt idx elseTerm)
| .recurse resultTy init body =>
    .recurse resultTy (weakenTermAt idx init) (weakenTermAt idx body)

def weaken {primCtx : PrimitiveCtx} (idx : Nat) : Pr primCtx → Pr primCtx
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
  | «primEq» lhs rhs =>
      simp [weakenTermAt, instantiateTermInTerm,
        instantiateTermInTerm_weakenTermAt idx replacement lhs,
        instantiateTermInTerm_weakenTermAt idx replacement rhs]
  | «primLt» lhs rhs =>
      simp [weakenTermAt, instantiateTermInTerm,
        instantiateTermInTerm_weakenTermAt idx replacement lhs,
        instantiateTermInTerm_weakenTermAt idx replacement rhs]
  | «primGt» lhs rhs =>
      simp [weakenTermAt, instantiateTermInTerm,
        instantiateTermInTerm_weakenTermAt idx replacement lhs,
        instantiateTermInTerm_weakenTermAt idx replacement rhs]
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
    (idx : Nat) (replacement : Term primCtx) (body : Pr primCtx) :
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
  | «primEq» lhs rhs =>
      simp [instantiateTermInTerm, subst_instantiateTermInTerm ctxTerm t lhs,
        subst_instantiateTermInTerm ctxTerm t rhs]
  | «primLt» lhs rhs =>
      simp [instantiateTermInTerm, subst_instantiateTermInTerm ctxTerm t lhs,
        subst_instantiateTermInTerm ctxTerm t rhs]
  | «primGt» lhs rhs =>
      simp [instantiateTermInTerm, subst_instantiateTermInTerm ctxTerm t lhs,
        subst_instantiateTermInTerm ctxTerm t rhs]
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

def quantifierFree {primCtx : PrimitiveCtx} : Pr primCtx → Bool
| .eq _ _ _ _ => true
| .hasType _ _ _ => true
| .and p q => quantifierFree p && quantifierFree q
| .or p q => quantifierFree p && quantifierFree q
| .implies p q => quantifierFree p && quantifierFree q
| .forallTy _ => false
| .forallTerm _ => false

theorem interp_instantiateTermAt {primCtx : PrimitiveCtx} {primFuncCtx : PrimFuncCtx primCtx}
    (ctxTy : List Ty) (ctxTerm : List (Term primCtx)) (t : Term primCtx)
    (body : Pr primCtx) (hqf : quantifierFree body = true) :
    Pr.interp primCtx primFuncCtx ctxTy ctxTerm (instantiateTermAt ctxTerm.length body t) ↔
      Pr.interp primCtx primFuncCtx ctxTy (ctxTerm ++ [Term.subst ctxTerm t]) body := by
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
  | «primEq» lhs rhs =>
      simp [weakenTermAt, subst_weakenTermAt_concat ctxTerm y lhs,
        subst_weakenTermAt_concat ctxTerm y rhs]
  | «primLt» lhs rhs =>
      simp [weakenTermAt, subst_weakenTermAt_concat ctxTerm y lhs,
        subst_weakenTermAt_concat ctxTerm y rhs]
  | «primGt» lhs rhs =>
      simp [weakenTermAt, subst_weakenTermAt_concat ctxTerm y lhs,
        subst_weakenTermAt_concat ctxTerm y rhs]
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
  | «primEq» lhs rhs =>
      simp [weakenTermAt, subst_weakenTermAt_middle ctxTerm x y lhs,
        subst_weakenTermAt_middle ctxTerm x y rhs]
  | «primLt» lhs rhs =>
      simp [weakenTermAt, subst_weakenTermAt_middle ctxTerm x y lhs,
        subst_weakenTermAt_middle ctxTerm x y rhs]
  | «primGt» lhs rhs =>
      simp [weakenTermAt, subst_weakenTermAt_middle ctxTerm x y lhs,
        subst_weakenTermAt_middle ctxTerm x y rhs]
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

theorem interp_weaken_concat {primCtx : PrimitiveCtx} {primFuncCtx : PrimFuncCtx primCtx}
    (ctxTy : List Ty) (ctxTerm : List (Term primCtx)) (y : Term primCtx)
    (body : Pr primCtx) (hqf : quantifierFree body = true) :
    Pr.interp primCtx primFuncCtx ctxTy (ctxTerm ++ [y]) (weaken ctxTerm.length body) ↔
      Pr.interp primCtx primFuncCtx ctxTy ctxTerm body := by
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

theorem interp_weaken_middle {primCtx : PrimitiveCtx} {primFuncCtx : PrimFuncCtx primCtx}
    (ctxTy : List Ty) (ctxTerm : List (Term primCtx)) (x y : Term primCtx)
    (body : Pr primCtx) (hqf : quantifierFree body = true) :
    Pr.interp primCtx primFuncCtx ctxTy (ctxTerm ++ [x] ++ [y]) (weaken ctxTerm.length body) ↔
      Pr.interp primCtx primFuncCtx ctxTy (ctxTerm ++ [y]) body := by
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
| .primEq lhs rhs =>
    match findRecurseInTerm idx lhs with
    | some found =>
        some
          { init := found.init
            predicateTerm := .primEq found.predicateTerm (weakenTermAt idx rhs)
            property := by simp [instantiateTermInTerm, found.property, instantiateTermInTerm_weakenTermAt] }
    | none =>
        match findRecurseInTerm idx rhs with
        | some found =>
            some
              { init := found.init
                predicateTerm := .primEq (weakenTermAt idx lhs) found.predicateTerm
                property := by simp [instantiateTermInTerm, found.property, instantiateTermInTerm_weakenTermAt] }
        | none => none
| .primLt lhs rhs =>
    match findRecurseInTerm idx lhs with
    | some found =>
        some
          { init := found.init
            predicateTerm := .primLt found.predicateTerm (weakenTermAt idx rhs)
            property := by simp [instantiateTermInTerm, found.property, instantiateTermInTerm_weakenTermAt] }
    | none =>
        match findRecurseInTerm idx rhs with
        | some found =>
            some
              { init := found.init
                predicateTerm := .primLt (weakenTermAt idx lhs) found.predicateTerm
                property := by simp [instantiateTermInTerm, found.property, instantiateTermInTerm_weakenTermAt] }
        | none => none
| .primGt lhs rhs =>
    match findRecurseInTerm idx lhs with
    | some found =>
        some
          { init := found.init
            predicateTerm := .primGt found.predicateTerm (weakenTermAt idx rhs)
            property := by simp [instantiateTermInTerm, found.property, instantiateTermInTerm_weakenTermAt] }
    | none =>
        match findRecurseInTerm idx rhs with
        | some found =>
            some
              { init := found.init
                predicateTerm := .primGt (weakenTermAt idx lhs) found.predicateTerm
                property := by simp [instantiateTermInTerm, found.property, instantiateTermInTerm_weakenTermAt] }
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

structure PrRecurseMatch {primCtx : PrimitiveCtx} (idx : Nat) (goal : Pr primCtx) where
  init : Term primCtx
  predicate : Pr primCtx
  property : goal = instantiateTermAt idx predicate init

def findRecurseInPr {primCtx : PrimitiveCtx} (idx : Nat) :
    (goal : Pr primCtx) → Option (PrRecurseMatch idx goal)
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
| .primEq lhs rhs =>
    match sameKnownTerm? (.primEq lhs rhs) init with
    | some h =>
        { predicateTerm := .var idx
          property := by rw [h.property]; simp [instantiateTermInTerm] }
    | none =>
        let abstractLhs := abstractInitInTerm idx init lhs
        let abstractRhs := abstractInitInTerm idx init rhs
        { predicateTerm := .primEq abstractLhs.predicateTerm abstractRhs.predicateTerm
          property := by simp [instantiateTermInTerm, abstractLhs.property, abstractRhs.property] }
| .primLt lhs rhs =>
    match sameKnownTerm? (.primLt lhs rhs) init with
    | some h =>
        { predicateTerm := .var idx
          property := by rw [h.property]; simp [instantiateTermInTerm] }
    | none =>
        let abstractLhs := abstractInitInTerm idx init lhs
        let abstractRhs := abstractInitInTerm idx init rhs
        { predicateTerm := .primLt abstractLhs.predicateTerm abstractRhs.predicateTerm
          property := by simp [instantiateTermInTerm, abstractLhs.property, abstractRhs.property] }
| .primGt lhs rhs =>
    match sameKnownTerm? (.primGt lhs rhs) init with
    | some h =>
        { predicateTerm := .var idx
          property := by rw [h.property]; simp [instantiateTermInTerm] }
    | none =>
        let abstractLhs := abstractInitInTerm idx init lhs
        let abstractRhs := abstractInitInTerm idx init rhs
        { predicateTerm := .primGt abstractLhs.predicateTerm abstractRhs.predicateTerm
          property := by simp [instantiateTermInTerm, abstractLhs.property, abstractRhs.property] }
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
    (goal : Pr primCtx) where
  predicate : Pr primCtx
  property : goal = instantiateTermAt idx predicate init

def abstractInitInPr {primCtx : PrimitiveCtx} (idx : Nat) (init : Term primCtx) :
    (goal : Pr primCtx) → PrAbstract idx init goal
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

def falsePr {primCtx : PrimitiveCtx} : Pr primCtx :=
  .eq [] (.prim "Bool") (Term.bool true) (Term.bool false)

def primLtIs {primCtx : PrimitiveCtx} (lhs rhs : Term primCtx) (c : Bool) : Pr primCtx :=
  .eq [] (.prim "Bool") (.primLt lhs rhs) (Term.bool c)

def isSuccPr {primCtx : PrimitiveCtx} (idx : Nat) : Pr primCtx :=
  .and (primLtIs (.var idx) (Term.nat 0) false)
    (.and (primLtIs (.var idx) (.var (idx + 1)) true)
      (.forallNat (idx + 2)
        (.implies
          (.and (primLtIs (.var idx) (.var (idx + 2)) true)
            (primLtIs (.var (idx + 2)) (.var (idx + 1)) true))
          falsePr)))

def natStepGoal {primCtx : PrimitiveCtx} (idx : Nat) (body : Pr primCtx) : Pr primCtx :=
  .forallNat idx (.forallNat (idx + 1)
    (.implies (isSuccPr idx)
      (.implies (weaken (idx + 1) body) (weaken idx body))))

def natInductionGoals {primCtx : PrimitiveCtx} (idx : Nat) (body : Pr primCtx) :
    List (Pr primCtx) :=
  [instantiateTermAt idx body (Term.nat 0), natStepGoal idx body]

private theorem natLit_hasType {primCtx : PrimitiveCtx} {primFuncCtx : PrimFuncCtx primCtx}
    (varCtx : VarCtx) (n : Nat) :
    Term.hasType primCtx primFuncCtx varCtx (Term.nat n) (.prim "Nat") :=
  Term.hasType.prim (Ty.ofNat primCtx n)

private theorem boolLit_hasType {primCtx : PrimitiveCtx} {primFuncCtx : PrimFuncCtx primCtx}
    (varCtx : VarCtx) (b : Bool) :
    Term.hasType primCtx primFuncCtx varCtx (Term.bool b) (.prim "Bool") :=
  Term.hasType.prim (Ty.ofBool primCtx b)

private theorem eval_natLit {primCtx : PrimitiveCtx} (primFuncCtx : PrimFuncCtx primCtx)
    (n : Nat) :
    Term.eval primCtx primFuncCtx [] (Term.nat n) = some (Val.nat n) := by
  simp [Term.eval, Term.evalGo, Term.nat]

private theorem primLt_natLit_eq {primCtx : PrimitiveCtx} {primFuncCtx : PrimFuncCtx primCtx}
    (a b : Nat) :
    Term.eq primCtx primFuncCtx [] (.prim "Bool")
      (.primLt (Term.nat a) (Term.nat b)) (Term.bool (decide (a < b))) :=
  Term.eq.mk
    (Term.hasType.primLt (natLit_hasType [] a) (natLit_hasType [] b))
    (boolLit_hasType [] (decide (a < b)))
    (by
      intro env henv
      have hnil : env = [] := List.eq_nil_of_length_eq_zero henv
      subst hnil
      simp [Term.eval, Term.evalGo, Term.nat, Term.bool, Val.primLt?])

private theorem asBool?_natVal {primCtx : PrimitiveCtx} (n : Nat) :
    (Val.nat (primCtx := primCtx) n).asBool? = none := by
  have hty : (Val.nat (primCtx := primCtx) n).ty = .prim "Nat" := rfl
  simp [Val.asBool?, Val.as?, hty]

private theorem valBool_inj {primCtx : PrimitiveCtx} {a b : Bool}
    (h : (Val.bool (primCtx := primCtx) a) = Val.bool b) : a = b := by
  have := congrArg Val.asBool? h
  simpa using this

private theorem eval_primLt_bool {primCtx : PrimitiveCtx} {primFuncCtx : PrimFuncCtx primCtx}
    {a b : Term primCtx} {c : Bool}
    (h : Term.eq primCtx primFuncCtx [] (.prim "Bool") (.primLt a b) (Term.bool c)) :
    ∃ va vb, Term.evalGo primCtx primFuncCtx none [] a = some va ∧
      Term.evalGo primCtx primFuncCtx none [] b = some vb ∧
      Val.primLt? va vb = some c := by
  have heval := h.eq [] rfl
  simp only [Term.eval, Term.evalGo, Term.bool, Val.mk_ofBool] at heval
  cases hva : Term.evalGo primCtx primFuncCtx none [] a with
  | none => rw [hva] at heval; simp at heval
  | some va =>
      rw [hva] at heval
      cases hvb : Term.evalGo primCtx primFuncCtx none [] b with
      | none => rw [hvb] at heval; simp at heval
      | some vb =>
          rw [hvb] at heval
          cases hlt : Val.primLt? va vb with
          | none => simp [hlt] at heval
          | some c' =>
              simp [hlt] at heval
              exact ⟨va, vb, rfl, rfl, by rw [hlt, valBool_inj heval]⟩

private theorem primLt?_natLeft {primCtx : PrimitiveCtx} {v : Val primCtx} {k : Nat} {c : Bool}
    (h : Val.primLt? (Val.nat k) v = some c) :
    ∃ m, v.asNat? = some m ∧ c = decide (k < m) := by
  unfold Val.primLt? at h
  cases hm : v.asNat? with
  | some m =>
      simp [hm] at h
      exact ⟨m, rfl, h.symm⟩
  | none =>
      simp [hm, asBool?_natVal] at h

private theorem primLt?_natRight {primCtx : PrimitiveCtx} {v : Val primCtx} {m : Nat} {c : Bool}
    (h : Val.primLt? v (Val.nat m) = some c) :
    ∃ j, v.asNat? = some j ∧ c = decide (j < m) := by
  unfold Val.primLt? at h
  cases hj : v.asNat? with
  | some j =>
      simp [hj] at h
      exact ⟨j, rfl, h.symm⟩
  | none =>
      simp [hj, asBool?_natVal] at h

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

private theorem primLt_eq_of_eval {primCtx : PrimitiveCtx} {primFuncCtx : PrimFuncCtx primCtx}
    {a b : Term primCtx} {ka kb : Nat}
    (hta : Term.hasType primCtx primFuncCtx [] a (.prim "Nat"))
    (htb : Term.hasType primCtx primFuncCtx [] b (.prim "Nat"))
    (ha : Term.eval primCtx primFuncCtx [] a = some (Val.nat ka))
    (hb : Term.eval primCtx primFuncCtx [] b = some (Val.nat kb)) :
    Term.eq primCtx primFuncCtx [] (.prim "Bool") (.primLt a b) (Term.bool (decide (ka < kb))) :=
  Term.eq.mk
    (Term.hasType.primLt hta htb)
    (boolLit_hasType [] (decide (ka < kb)))
    (by
      intro env henv
      have hnil : env = [] := List.eq_nil_of_length_eq_zero henv
      subst hnil
      simp only [Term.eval] at ha hb ⊢
      simp [Term.evalGo, ha, hb, Term.bool, Val.primLt?])

/-- From `isSuccPr` holding of a term pair `(x, y)`, extract that `x` and `y` evaluate to
  consecutive nat literals: `x ↝ k`, `y ↝ k + 1`. -/
theorem isSuccPr_extract {primCtx : PrimitiveCtx} {primFuncCtx : PrimFuncCtx primCtx}
    {ctxTy : List Ty} {ctxTerm : List (Term primCtx)} {x y : Term primCtx}
    (hxty : Term.hasType primCtx primFuncCtx [] x (.prim "Nat"))
    (hyty : Term.hasType primCtx primFuncCtx [] y (.prim "Nat"))
    (hsucc : Pr.interp primCtx primFuncCtx ctxTy (ctxTerm ++ [x, y]) (isSuccPr ctxTerm.length)) :
    ∃ k : Nat, Term.eval primCtx primFuncCtx [] x = some (Val.nat k) ∧
      Term.eval primCtx primFuncCtx [] y = some (Val.nat (k + 1)) := by
  obtain ⟨hA, hB, hC⟩ := hsucc
  have hA' : Term.eq primCtx primFuncCtx [] (.prim "Bool") (.primLt x (Term.nat 0)) (Term.bool false) := by
    simpa [Pr.interp, primLtIs, Ty.subst, Term.nat, Term.bool] using hA
  have hB' : Term.eq primCtx primFuncCtx [] (.prim "Bool") (.primLt x y) (Term.bool true) := by
    simpa [Pr.interp, primLtIs, Ty.subst, Term.nat, Term.bool] using hB
  obtain ⟨va, v0, hva, hv0, hpltA⟩ := eval_primLt_bool hA'
  have hv0' : v0 = Val.nat 0 := by
    have hev := eval_natLit primFuncCtx 0
    simp only [Term.eval] at hev
    rw [hev] at hv0
    exact (Option.some.inj hv0).symm
  subst hv0'
  have hkxOpt : ∃ kx, va.asNat? = some kx := by
    cases hna : va.asNat? with
    | some kx => exact ⟨kx, rfl⟩
    | none =>
        exfalso
        unfold Val.primLt? at hpltA
        simp [hna, asBool?_natVal] at hpltA
  obtain ⟨kx, hkx⟩ := hkxOpt
  have hvaEq : va = Val.nat kx := asNat?_eq_some hkx
  subst hvaEq
  obtain ⟨vb, hvb, hpltB⟩ : ∃ vb, Term.evalGo primCtx primFuncCtx none [] y = some vb ∧
      Val.primLt? (Val.nat kx) vb = some true := by
    obtain ⟨va', vb, hva', hvb, hplt⟩ := eval_primLt_bool hB'
    have : va' = Val.nat kx := by
      have hxx : Term.eval primCtx primFuncCtx [] x = some va' := hva'
      have hxx2 : Term.eval primCtx primFuncCtx [] x = some (Val.nat kx) := hva
      rw [hxx] at hxx2
      exact Option.some.inj hxx2
    subst this
    exact ⟨vb, hvb, hplt⟩
  have hkyOpt : ∃ ky, vb.asNat? = some ky := by
    cases hnb : vb.asNat? with
    | some ky => exact ⟨ky, rfl⟩
    | none =>
        exfalso
        unfold Val.primLt? at hpltB
        simp [hnb, asBool?_natVal] at hpltB
  obtain ⟨ky, hky⟩ := hkyOpt
  have hvbEq : vb = Val.nat ky := asNat?_eq_some hky
  subst hvbEq
  have hkxky : kx < ky := by
    unfold Val.primLt? at hpltB
    simp at hpltB
    exact hpltB
  have hkyEq : ky = kx + 1 := by
    by_cases hne : ky = kx + 1
    · exact hne
    exfalso
    have hgt : kx + 1 < ky := by omega
    have htz : Term.hasType primCtx primFuncCtx [] (Term.nat (kx + 1)) (.prim "Nat") :=
      natLit_hasType (primCtx := primCtx) (primFuncCtx := primFuncCtx) [] (kx + 1)
    have hlt1 : Term.eq primCtx primFuncCtx [] (.prim "Bool")
        (.primLt x (Term.nat (kx + 1))) (Term.bool true) := by
      have := primLt_eq_of_eval (primCtx := primCtx) (primFuncCtx := primFuncCtx)
        hxty htz hva (eval_natLit primFuncCtx (kx + 1))
      simpa using this
    have hlt2 : Term.eq primCtx primFuncCtx [] (.prim "Bool")
        (.primLt (Term.nat (kx + 1)) y) (Term.bool true) := by
      have := primLt_eq_of_eval (primCtx := primCtx) (primFuncCtx := primFuncCtx)
        htz hyty (eval_natLit primFuncCtx (kx + 1)) hvb
      simpa [hgt] using this
    have hzty : Pr.interp primCtx primFuncCtx ctxTy (ctxTerm ++ [x, y] ++ [Term.nat (kx + 1)])
        (.hasType [] (.var (ctxTerm.length + 2)) (.prim "Nat")) := by
      simp [Pr.interp, Ty.subst, Nat.lt_add_one]
      exact htz
    have hpair : Pr.interp primCtx primFuncCtx ctxTy
        (ctxTerm ++ [x, y] ++ [Term.nat (kx + 1)])
        (.and (primLtIs (.var ctxTerm.length) (.var (ctxTerm.length + 2)) true)
          (primLtIs (.var (ctxTerm.length + 2)) (.var (ctxTerm.length + 1)) true)) := by
      constructor
      · simpa [primLtIs, Pr.interp, Ty.subst, Nat.lt_add_one, Term.nat, Term.bool] using hlt1
      · simpa [primLtIs, Pr.interp, Ty.subst, Nat.lt_add_one, Term.nat, Term.bool] using hlt2
    have hfalse := hC (Term.nat (kx + 1)) hzty hpair
    simp only [falsePr, Pr.interp, Ty.subst] at hfalse
    have hbv := hfalse.eq [] rfl
    simp [Term.eval, Term.evalGo, Term.bool] at hbv
    have := congrArg Val.asBool? hbv
    simp at this
  refine ⟨kx, hva, ?_⟩
  rw [hkyEq] at hvb
  exact hvb

/-- Builds the term-quantified step goal `natStepGoal 0 predicate` from a step function
  indexed by literal `Nat`s. All the `isSuccPr`/`hasType`/weaken-instantiate wiring needed to
  go from arbitrary `x y : Term` satisfying `isSuccPr` down to concrete literals `k, k + 1` is
  handled here, once, generically in `predicate` — callers only ever supply:
  - `hcongr`: `instantiateTermAt 0 predicate` is invariant under swapping a well-typed term for
    the literal it evaluates to (this is the one genuinely predicate-specific fact — it can't be
    derived generically because `predicate` may inspect its argument's syntax, not just its
    value; for an `.eq`/`.hasType`-shaped predicate over evaluation-only content it is usually a
    short proof, e.g. `gaussPredicate_provable_of_eval` for `gaussPredicate`).
  - `hstep`: the actual induction step, `P(k) → P(k + 1)`. -/
theorem natStepGoal_of_literal_step {primCtx : PrimitiveCtx} {primFuncCtx : PrimFuncCtx primCtx}
    {ctxTy : List Ty} {predicate : Pr primCtx}
    (hqf : quantifierFree predicate = true)
    (hcongr : ∀ (t : Term primCtx) (k : Nat),
      Term.hasType primCtx primFuncCtx [] t (.prim "Nat") →
      Term.eval primCtx primFuncCtx [] t = some (Val.nat k) →
      (Pr.Provable primCtx primFuncCtx ctxTy [] (instantiateTermAt 0 predicate t) ↔
        Pr.Provable primCtx primFuncCtx ctxTy [] (instantiateTermAt 0 predicate (Term.nat k))))
    (hstep : ∀ k : Nat,
      Pr.Provable primCtx primFuncCtx ctxTy [] (instantiateTermAt 0 predicate (Term.nat k)) →
      Pr.Provable primCtx primFuncCtx ctxTy [] (instantiateTermAt 0 predicate (Term.nat (k + 1)))) :
    Pr.Provable primCtx primFuncCtx ctxTy [] (natStepGoal 0 predicate) := by
  refine Pr.Provable.ofProof ?_
  intro x hxtyRaw y hytyRaw hsuccRaw hbodyRaw
  have hxty : Term.hasType primCtx primFuncCtx [] x (.prim "Nat") := by
    simpa [Pr.interp, Ty.subst] using hxtyRaw
  have hyty : Term.hasType primCtx primFuncCtx [] y (.prim "Nat") := by
    simpa [Pr.interp, Ty.subst] using hytyRaw
  have hsucc : Pr.interp primCtx primFuncCtx ctxTy (([] : List (Term primCtx)) ++ [x, y])
      (isSuccPr 0) := hsuccRaw
  obtain ⟨k, hxe, hye⟩ := isSuccPr_extract hxty hyty hsucc
  have hwkPrev := interp_weaken_concat (primFuncCtx := primFuncCtx) ctxTy [x] y predicate hqf
  have hbodyPrev : Pr.interp primCtx primFuncCtx ctxTy ([x] ++ [y])
      (weaken ([x] : List (Term primCtx)).length predicate) := hbodyRaw
  have hprevInterp : Pr.interp primCtx primFuncCtx ctxTy [x] predicate := hwkPrev.mp hbodyPrev
  have hbridgePrev := interp_instantiateTermAt (primFuncCtx := primFuncCtx) ctxTy
    ([] : List (Term primCtx)) x predicate hqf
  simp only [Term.subst_nil, List.length_nil] at hbridgePrev
  have hprevProvX : Pr.Provable primCtx primFuncCtx ctxTy []
      (instantiateTermAt 0 predicate x) :=
    Pr.Provable.ofProof (hbridgePrev.mpr (by simpa using hprevInterp))
  have hprevProvK : Pr.Provable primCtx primFuncCtx ctxTy []
      (instantiateTermAt 0 predicate (Term.nat k)) :=
    (hcongr x k hxty hxe).mp hprevProvX
  have hnextProvK := hstep k hprevProvK
  have hnextProvY : Pr.Provable primCtx primFuncCtx ctxTy []
      (instantiateTermAt 0 predicate y) :=
    (hcongr y (k + 1) hyty hye).mpr hnextProvK
  cases hnextProvY with
  | ofProof hnextInterp =>
      have hbridgeNext := interp_instantiateTermAt (primFuncCtx := primFuncCtx) ctxTy
        ([] : List (Term primCtx)) y predicate hqf
      simp only [Term.subst_nil, List.length_nil] at hbridgeNext
      have hyInterp : Pr.interp primCtx primFuncCtx ctxTy ([] ++ [y]) predicate :=
        hbridgeNext.mp hnextInterp
      have hwkNext := interp_weaken_middle (primFuncCtx := primFuncCtx) ctxTy
        ([] : List (Term primCtx)) x y predicate hqf
      exact hwkNext.mpr (by simpa using hyInterp)

theorem natInductionChain {primCtx : PrimitiveCtx} {primFuncCtx : PrimFuncCtx primCtx}
    {ctxTy : List Ty} {ctxTerm : List (Term primCtx)} {body : Pr primCtx}
    (hqf : quantifierFree body = true)
    (hbase : Pr.Provable primCtx primFuncCtx ctxTy ctxTerm
      (instantiateTermAt ctxTerm.length body (Term.nat 0)))
    (hstep : Pr.Provable primCtx primFuncCtx ctxTy ctxTerm
      (natStepGoal ctxTerm.length body)) :
    ∀ n, Pr.Provable primCtx primFuncCtx ctxTy ctxTerm
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
              have hguardx : Pr.interp primCtx primFuncCtx ctxTy (ctxTerm ++ [Term.nat k])
                  (.hasType [] (.var ctxTerm.length) (.prim "Nat")) := by
                simpa [Pr.interp, hvarx, Ty.subst] using
                  natLit_hasType (primCtx := primCtx) (primFuncCtx := primFuncCtx) [] k
              have hy := hstepProof (Term.nat k) hguardx
              have hvary : Term.subst (ctxTerm ++ [Term.nat k] ++ [Term.nat (k + 1)])
                  (.var (ctxTerm.length + 1)) = Term.nat (k + 1) := by
                have e : (ctxTerm ++ [Term.nat k] ++
                    [Term.nat (k + 1)])[ctxTerm.length + 1]? = some (Term.nat (k + 1)) := by
                  rw [show ctxTerm.length + 1 = (ctxTerm ++ [Term.nat k]).length by simp]
                  exact List.getElem?_concat_length
                have hc : ctxTerm.length + 1 < ctxTerm.length + 1 + 1 := by omega
                simp [e, hc]
              have hguardy : Pr.interp primCtx primFuncCtx ctxTy
                  (ctxTerm ++ [Term.nat k] ++ [Term.nat (k + 1)])
                  (.hasType [] (.var (ctxTerm.length + 1)) (.prim "Nat")) := by
                simpa [Pr.interp, hvary, Ty.subst] using
                  natLit_hasType (primCtx := primCtx) (primFuncCtx := primFuncCtx) [] (k + 1)
              have h1 := hy (Term.nat (k + 1)) hguardy
              have hvarx2 : Term.subst (ctxTerm ++ [Term.nat k] ++ [Term.nat (k + 1)])
                  (.var ctxTerm.length) = Term.nat k := by
                have e : (ctxTerm ++ [Term.nat k] ++
                    [Term.nat (k + 1)])[ctxTerm.length]? = some (Term.nat k) := by
                  rw [List.getElem?_append_left (by simp)]
                  exact List.getElem?_concat_length
                have hc : ctxTerm.length < ctxTerm.length + 1 + 1 := by omega
                simp [e, hc]
              have hsucc : Pr.interp primCtx primFuncCtx ctxTy
                  (ctxTerm ++ [Term.nat k] ++ [Term.nat (k + 1)])
                  (isSuccPr ctxTerm.length) := by
                refine ⟨?_, ?_, ?_⟩
                · have hdec : decide (k < 0) = false := by simp
                  have hlt := primLt_natLit_eq
                    (primCtx := primCtx) (primFuncCtx := primFuncCtx) k 0
                  rw [hdec] at hlt
                  simpa [primLtIs, Pr.interp, hvarx2, Ty.subst, Term.nat, Term.bool]
                    using hlt
                · have hdec : decide (k < k + 1) = true := by simp
                  have hlt := primLt_natLit_eq
                    (primCtx := primCtx) (primFuncCtx := primFuncCtx) k (k + 1)
                  rw [hdec] at hlt
                  simpa [primLtIs, Pr.interp, hvarx2, hvary, Ty.subst, Term.nat, Term.bool]
                    using hlt
                · intro z hzty hpair
                  obtain ⟨hlt1, hlt2⟩ := hpair
                  have hvz : Term.subst (ctxTerm ++ [Term.nat k] ++ [Term.nat (k + 1)] ++ [z])
                      (.var (ctxTerm.length + 2)) = z := by
                    have e : (ctxTerm ++ [Term.nat k] ++ [Term.nat (k + 1)] ++
                        [z])[ctxTerm.length + 2]? = some z := by
                      rw [show ctxTerm.length + 2 =
                        (ctxTerm ++ [Term.nat k] ++ [Term.nat (k + 1)]).length by simp]
                      exact List.getElem?_concat_length
                    have hc : ctxTerm.length + 2 < ctxTerm.length + 1 + 1 + 1 := by omega
                    simp [e, hc]
                  have hvx3 : Term.subst (ctxTerm ++ [Term.nat k] ++ [Term.nat (k + 1)] ++ [z])
                      (.var ctxTerm.length) = Term.nat k := by
                    have e : (ctxTerm ++ [Term.nat k] ++ [Term.nat (k + 1)] ++
                        [z])[ctxTerm.length]? = some (Term.nat k) := by
                      rw [List.getElem?_append_left (by simp),
                        List.getElem?_append_left (by simp)]
                      exact List.getElem?_concat_length
                    have hc : ctxTerm.length < ctxTerm.length + 1 + 1 + 1 := by omega
                    simp [e, hc]
                  have hvy3 : Term.subst (ctxTerm ++ [Term.nat k] ++ [Term.nat (k + 1)] ++ [z])
                      (.var (ctxTerm.length + 1)) = Term.nat (k + 1) := by
                    have e : (ctxTerm ++ [Term.nat k] ++ [Term.nat (k + 1)] ++
                        [z])[ctxTerm.length + 1]? = some (Term.nat (k + 1)) := by
                      rw [List.getElem?_append_left (by simp),
                        show ctxTerm.length + 1 = (ctxTerm ++ [Term.nat k]).length by simp]
                      exact List.getElem?_concat_length
                    have hc : ctxTerm.length + 1 < ctxTerm.length + 1 + 1 + 1 := by omega
                    simp [e, hc]
                  have hlt1' : Term.eq primCtx primFuncCtx [] (.prim "Bool")
                      (.primLt (Term.nat k) (Term.subst (ctxTerm ++ [Term.nat k] ++
                        [Term.nat (k + 1)] ++ [z]) (.var (ctxTerm.length + 2))))
                      (Term.bool true) := by
                    simpa [primLtIs, Pr.interp, hvx3, Ty.subst, Term.bool] using hlt1
                  have hlt2' : Term.eq primCtx primFuncCtx [] (.prim "Bool")
                      (.primLt (Term.subst (ctxTerm ++ [Term.nat k] ++
                        [Term.nat (k + 1)] ++ [z]) (.var (ctxTerm.length + 2)))
                        (Term.nat (k + 1)))
                      (Term.bool true) := by
                    simpa [primLtIs, Pr.interp, hvy3, Ty.subst, Term.bool] using hlt2
                  obtain ⟨va, vz, hva, hvz1, hplt1⟩ := eval_primLt_bool hlt1'
                  obtain ⟨vz2, vb, hvz2, hvb, hplt2⟩ := eval_primLt_bool hlt2'
                  have hva' : va = Val.nat k := by
                    have := eval_natLit primFuncCtx k
                    simp only [Term.eval] at this
                    rw [this] at hva
                    exact (Option.some.inj hva).symm
                  have hvb' : vb = Val.nat (k + 1) := by
                    have := eval_natLit primFuncCtx (k + 1)
                    simp only [Term.eval] at this
                    rw [this] at hvb
                    exact (Option.some.inj hvb).symm
                  have hvzeq : vz2 = vz := by
                    rw [hvz1] at hvz2
                    exact (Option.some.inj hvz2).symm
                  subst hva' hvb' hvzeq
                  obtain ⟨m, hm, hcm⟩ := primLt?_natLeft hplt1
                  obtain ⟨j, hj, hcj⟩ := primLt?_natRight hplt2
                  have hmj : m = j := by
                    rw [hm] at hj
                    exact Option.some.inj hj
                  subst hmj
                  have hkm : k < m := of_decide_eq_true hcm.symm
                  have hmk : m < k + 1 := of_decide_eq_true hcj.symm
                  exact absurd rfl (by omega : ¬ (0 = 0))
              have h2 := h1 hsucc
              have hlen1 : (ctxTerm ++ [Term.nat k]).length = ctxTerm.length + 1 := by simp
              have hwk1 := interp_weaken_concat (primFuncCtx := primFuncCtx) ctxTy
                (ctxTerm ++ [Term.nat k]) (Term.nat (k + 1)) body hqf
              rw [hlen1] at hwk1
              have hbx := hwk1.mpr (by
                have h' := (interp_instantiateTermAt ctxTy ctxTerm (Term.nat k) body hqf).mp
                  ihProof
                rwa [show Term.subst ctxTerm (Term.nat k) = Term.nat k by simp [Term.nat]] at h')
              have h3 := h2 hbx
              have hwk2 := interp_weaken_middle (primFuncCtx := primFuncCtx) ctxTy ctxTerm
                (Term.nat k) (Term.nat (k + 1)) body hqf
              have hfin := hwk2.mp h3
              refine (interp_instantiateTermAt ctxTy ctxTerm (Term.nat (k + 1)) body hqf).mpr ?_
              rwa [show Term.subst ctxTerm (Term.nat (k + 1)) = Term.nat (k + 1) by
                simp [Term.nat]]

def natInductionWithPredicate {primCtx : PrimitiveCtx} {primFuncCtx : PrimFuncCtx primCtx}
    {ctxTy : List Ty} {ctxTerm : List (Term primCtx)}
    (goal : Pr primCtx) (predicate : Pr primCtx) (target : Nat)
    (hinst : goal = instantiateTermAt ctxTerm.length predicate (Term.nat target))
    (hqf : quantifierFree predicate = true) :
    MetaProgram primCtx primFuncCtx ctxTy ctxTerm goal :=
  { goals := natInductionGoals ctxTerm.length predicate
    prove := by
      intro proveSubgoals
      have hbase := proveSubgoals (instantiateTermAt ctxTerm.length predicate (Term.nat 0))
        (by simp [natInductionGoals])
      have hstep := proveSubgoals (natStepGoal ctxTerm.length predicate)
        (by simp [natInductionGoals])
      rw [hinst]
      exact natInductionChain hqf hbase hstep target }

def simpleInduction {primCtx : PrimitiveCtx} {primFuncCtx : PrimFuncCtx primCtx}
    {ctxTy : List Ty} {ctxTerm : List (Term primCtx)} :
    (goal : Pr primCtx) → MetaProgram primCtx primFuncCtx ctxTy ctxTerm goal
| goal =>
    match findRecurseInPr ctxTerm.length goal with
    | some found =>
        match found.init.natLit? with
        | some target =>
            let abstracted := abstractInitInPr ctxTerm.length found.init goal
            let body := abstracted.predicate
            if hqf : quantifierFree body then
              { goals := natInductionGoals ctxTerm.length body
                prove := by
                  intro proveSubgoals
                  have hbase := proveSubgoals
                    (instantiateTermAt ctxTerm.length body (Term.nat 0))
                    (by simp [natInductionGoals])
                  have hstep := proveSubgoals (natStepGoal ctxTerm.length body)
                    (by simp [natInductionGoals])
                  have htarget := natInductionChain hqf hbase hstep target.val
                  have hgoalEq :
                      instantiateTermAt ctxTerm.length body (Term.nat target.val) = goal := by
                    dsimp [body]
                    calc
                      instantiateTermAt ctxTerm.length abstracted.predicate (Term.nat target.val)
                          = instantiateTermAt ctxTerm.length abstracted.predicate found.init := by
                            rw [← target.property]
                      _ = goal := abstracted.property.symm
                  exact Eq.mp (by rw [hgoalEq]) htarget }
            else
              { goals := [goal]
                prove := by
                  intro proveSubgoals
                  exact proveSubgoals goal (by simp) }
        | none =>
            let abstracted := abstractInitInPr ctxTerm.length found.init goal
            if hqf : quantifierFree abstracted.predicate then
              { goals :=
                  [ .hasType [] found.init (.prim "Nat")
                  , .forallNat ctxTerm.length abstracted.predicate ]
                prove := by
                  intro proveSubgoals
                  have htype : Pr.Provable primCtx primFuncCtx ctxTy ctxTerm
                      (.hasType [] found.init (.prim "Nat")) :=
                    proveSubgoals (.hasType [] found.init (.prim "Nat")) (by simp)
                  have hforall : Pr.Provable primCtx primFuncCtx ctxTy ctxTerm
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
                          have hpremise : Pr.interp primCtx primFuncCtx ctxTy
                              (ctxTerm ++ [Term.subst ctxTerm found.init])
                              (.hasType [] (.var ctxTerm.length) (.prim "Nat")) := by
                            simpa [Pr.interp, hvar, Ty.subst] using htypeProof
                          have hbody := hx hpremise
                          show Pr.interp primCtx primFuncCtx ctxTy ctxTerm goal
                          rw [abstracted.property]
                          exact (interp_instantiateTermAt ctxTy ctxTerm found.init
                            abstracted.predicate hqf).mpr hbody }
            else
              { goals := [goal]
                prove := by
                  intro proveSubgoals
                  exact proveSubgoals goal (by simp) }
    | none =>
        { goals := [goal]
          prove := by
            intro proveSubgoals
            exact proveSubgoals goal (by simp) }

end MetaProgram

end Pr

end Zag
