import Lean.Elab.Tactic.Decide
import Zag.Data

namespace Zag

mutual

def Ty.isAbbrevFree : Ty → Bool
| .var _ | .prim _ => true
| .option ty | .m ty => ty.isAbbrevFree
| .union tys | .struct tys => Ty.isAbbrevFreeList tys
| .func args out => Ty.isAbbrevFreeList args && out.isAbbrevFree
| .«abbrev» _ _ => false

def Ty.isAbbrevFreeList : List Ty → Bool
| [] => true
| ty :: tys => ty.isAbbrevFree && Ty.isAbbrevFreeList tys

end

private theorem TypeAbbrevCtx.Raw.getWithPrefix?_eq_get?
    {ctx prior : TypeAbbrevCtx.Raw} {name : String} {definition : TypeAbbrev}
    (h : ctx.getWithPrefix? name = some (prior, definition)) :
    ctx.get? name = some definition := by
  induction ctx generalizing prior definition with
  | nil => simp [TypeAbbrevCtx.Raw.getWithPrefix?] at h
  | cons entry rest ih =>
      by_cases hname : entry.1 = name
      · simp only [TypeAbbrevCtx.Raw.getWithPrefix?, hname, ↓reduceIte,
          Option.some.injEq] at h
        have hdef : entry.2 = definition := congrArg Prod.snd h
        simp [TypeAbbrevCtx.Raw.get?, List.find?, hname, hdef]
      · simp only [TypeAbbrevCtx.Raw.getWithPrefix?, hname, ↓reduceIte] at h
        split at h
        · next foundPrior foundDefinition hrest =>
            cases h
            simpa [TypeAbbrevCtx.Raw.get?, List.find?, hname] using ih hrest
        · contradiction

private theorem TypeAbbrevCtx.Raw.getWithPrefix?_append_of_some
    {left prior : TypeAbbrevCtx.Raw} {right : TypeAbbrevCtx.Raw}
    {name : String} {definition : TypeAbbrev}
    (h : left.getWithPrefix? name = some (prior, definition)) :
    (left ++ right).getWithPrefix? name = some (prior, definition) := by
  induction left generalizing prior definition with
  | nil => simp [TypeAbbrevCtx.Raw.getWithPrefix?] at h
  | cons entry rest ih =>
      by_cases hname : entry.1 = name
      · simpa [TypeAbbrevCtx.Raw.getWithPrefix?, hname] using h
      · simp only [TypeAbbrevCtx.Raw.getWithPrefix?, hname, ↓reduceIte] at h ⊢
        split at h
        · next foundPrior foundDefinition hrest =>
            cases h
            rw [TypeAbbrevCtx.Raw.getWithPrefix?.eq_def]
            change (if entry.1 = name then some ([], entry.2) else
              match TypeAbbrevCtx.Raw.getWithPrefix? (rest ++ right) name with
              | some (foundPrior, definition) => some (entry :: foundPrior, definition)
              | none => none) = some (entry :: foundPrior, definition)
            rw [if_neg hname]
            rw [ih hrest]
        · contradiction

private theorem TypeAbbrevCtx.Raw.getWithPrefix?_split
    {ctx prior : TypeAbbrevCtx.Raw} {name : String} {definition : TypeAbbrev}
    (h : ctx.getWithPrefix? name = some (prior, definition)) :
    ∃ rest, ctx = prior ++ (name, definition) :: rest := by
  induction ctx generalizing prior definition with
  | nil => simp [TypeAbbrevCtx.Raw.getWithPrefix?] at h
  | cons entry rest ih =>
      simp only [TypeAbbrevCtx.Raw.getWithPrefix?] at h
      split at h
      · next heq =>
        cases h
        have hentry : entry = (name, entry.2) := Prod.ext heq rfl
        rw [hentry]
        exact ⟨rest, rfl⟩
      · split at h
        · next foundPrior foundDefinition hrest =>
            cases h
            obtain ⟨suffix, hsuffix⟩ := ih hrest
            exact ⟨suffix, by simp [hsuffix]⟩
        · contradiction

private theorem TypeAbbrevCtx.Raw.getWithPrefix?_of_get?
    {ctx : TypeAbbrevCtx.Raw} {name : String} {definition : TypeAbbrev}
    (h : ctx.get? name = some definition) :
    ∃ prior, ctx.getWithPrefix? name = some (prior, definition) := by
  induction ctx with
  | nil => simp [TypeAbbrevCtx.Raw.get?] at h
  | cons entry rest ih =>
      by_cases hname : entry.1 = name
      · have hdef : entry.2 = definition := by
          simpa [TypeAbbrevCtx.Raw.get?, List.find?, hname] using h
        exact ⟨[], by simp [TypeAbbrevCtx.Raw.getWithPrefix?, hname, hdef]⟩
      · have hrest : TypeAbbrevCtx.Raw.get? rest name = some definition := by
          simpa [TypeAbbrevCtx.Raw.get?, List.find?, hname] using h
        obtain ⟨prior, hprior⟩ := ih hrest
        exact ⟨entry :: prior, by simp [TypeAbbrevCtx.Raw.getWithPrefix?, hname, hprior]⟩

private theorem TypeAbbrevCtx.validFrom_append
    (previous left right : TypeAbbrevCtx.Raw) :
    TypeAbbrevCtx.validFrom previous (left ++ right) =
      (TypeAbbrevCtx.validFrom previous left &&
        TypeAbbrevCtx.validFrom (previous ++ left) right) := by
  induction left generalizing previous with
  | nil => simp [TypeAbbrevCtx.validFrom]
  | cons entry rest ih =>
      simp only [List.cons_append, TypeAbbrevCtx.validFrom]
      rw [ih]
      simp only [List.singleton_append, List.append_assoc, Bool.and_assoc]

private theorem TypeAbbrevCtx.Valid.snoc
    {ctx : TypeAbbrevCtx.Raw} {entry : String × TypeAbbrev}
    (hctx : TypeAbbrevCtx.Valid ctx)
    (hname : entry.1 ∉ ctx.map Prod.fst)
    (hentry : Ty.validIn ctx entry.2.typeArity entry.2.body = true) :
    TypeAbbrevCtx.Valid (ctx ++ [entry]) := by
  rw [TypeAbbrevCtx.Valid] at hctx ⊢
  constructor
  · rw [List.map_append]
    refine List.nodup_append.mpr ⟨hctx.1, by simp, ?_⟩
    intro name hmem appended happended
    have : appended = entry.1 := by simpa using happended
    subst appended
    exact fun heq => hname (heq ▸ hmem)
  · rw [TypeAbbrevCtx.validFrom_append]
    simp [hctx.2, TypeAbbrevCtx.validFrom, hentry]

theorem TypeAbbrevCtx.Valid.getWithPrefix?
    {ctx prior : TypeAbbrevCtx.Raw} {name : String} {definition : TypeAbbrev}
    (hctx : TypeAbbrevCtx.Valid ctx)
    (hget : ctx.getWithPrefix? name = some (prior, definition)) :
    TypeAbbrevCtx.Valid prior ∧
      Ty.validIn prior definition.typeArity definition.body = true := by
  have go : ∀ previous rest prior definition,
      TypeAbbrevCtx.Valid previous → TypeAbbrevCtx.validFrom previous rest = true →
      ((previous ++ rest).map Prod.fst).Nodup →
      rest.getWithPrefix? name = some (prior, definition) →
      TypeAbbrevCtx.Valid (previous ++ prior) ∧
        Ty.validIn (previous ++ prior) definition.typeArity definition.body = true := by
    intro previous rest
    induction rest generalizing previous with
    | nil => simp [TypeAbbrevCtx.Raw.getWithPrefix?]
    | cons entry rest ih =>
        intro prior definition hprevious hvalid hnames hget
        simp only [TypeAbbrevCtx.validFrom, Bool.and_eq_true] at hvalid
        simp only [TypeAbbrevCtx.Raw.getWithPrefix?] at hget
        split at hget
        · cases hget
          simpa using And.intro hprevious hvalid.1
        · split at hget
          · next foundPrior foundDefinition heq =>
              cases hget
              have hentryName : entry.1 ∉ previous.map Prod.fst := by
                intro hmem
                have hcross := (List.nodup_append.mp (by
                  simpa only [List.map_append] using hnames)).2.2
                exact hcross entry.1 hmem entry.1 (by simp) rfl
              have hnames' :
                  (((previous ++ [entry]) ++ rest).map Prod.fst).Nodup := by
                simpa [List.append_assoc] using hnames
              have result := ih (previous ++ [entry]) foundPrior definition
                (hprevious.snoc hentryName hvalid.1) hvalid.2 hnames' heq
              simpa [List.append_assoc] using result
          · contradiction
  exact go [] ctx prior definition
    (by simp [TypeAbbrevCtx.Valid, TypeAbbrevCtx.validFrom]) hctx.2 hctx.1 hget

mutual

def Ty.AbbrevFree : Ty → Prop
| .var _ | .prim _ => True
| .option ty | .m ty => ty.AbbrevFree
| .union tys | .struct tys => Ty.AbbrevFreeList tys
| .func args out => Ty.AbbrevFreeList args ∧ out.AbbrevFree
| .«abbrev» _ _ => False

def Ty.AbbrevFreeList : List Ty → Prop
| [] => True
| ty :: tys => ty.AbbrevFree ∧ Ty.AbbrevFreeList tys

end

mutual

private theorem Ty.normalizeWith_nil_eq_self_of_abbrevFree (ctx : TypeAbbrevCtx.Raw) :
    ∀ (ty : Ty), ty.isAbbrevFree = true → Ty.normalizeWith ctx [] ty = ty
| .var _, _ => by simp [Ty.normalizeWith]
| .prim _, _ => by simp [Ty.normalizeWith]
| .option ty, h => by
    simp only [Ty.isAbbrevFree] at h
    simp [Ty.normalizeWith, Ty.normalizeWith_nil_eq_self_of_abbrevFree ctx ty h]
| .m ty, h => by
    simp only [Ty.isAbbrevFree] at h
    simp [Ty.normalizeWith, Ty.normalizeWith_nil_eq_self_of_abbrevFree ctx ty h]
| .union tys, h => by
    simp only [Ty.isAbbrevFree] at h
    simp [Ty.normalizeWith, Ty.normalizeWithList_nil_eq_self_of_abbrevFree ctx tys h]
| .struct tys, h => by
    simp only [Ty.isAbbrevFree] at h
    simp [Ty.normalizeWith, Ty.normalizeWithList_nil_eq_self_of_abbrevFree ctx tys h]
| .func args out, h => by
    simp only [Ty.isAbbrevFree, Bool.and_eq_true] at h
    simp [Ty.normalizeWith, Ty.normalizeWithList_nil_eq_self_of_abbrevFree ctx args h.1,
      Ty.normalizeWith_nil_eq_self_of_abbrevFree ctx out h.2]

private theorem Ty.normalizeWithList_nil_eq_self_of_abbrevFree (ctx : TypeAbbrevCtx.Raw) :
    ∀ (tys : List Ty), Ty.isAbbrevFreeList tys = true →
      tys.map (Ty.normalizeWith ctx []) = tys
| [], _ => rfl
| ty :: tys, h => by
    simp only [Ty.isAbbrevFreeList, Bool.and_eq_true] at h
    simp [Ty.normalizeWith_nil_eq_self_of_abbrevFree ctx ty h.1,
      Ty.normalizeWithList_nil_eq_self_of_abbrevFree ctx tys h.2]

end

/-- Delta normalization is the identity on abbreviation-free types. -/
theorem Ty.normalizeAbbrev_eq_self_of_abbrevFree (ctx : TypeAbbrevCtx) (ty : Ty)
    (h : ty.isAbbrevFree = true) : ty.normalizeAbbrev ctx = ty := by
  exact Ty.normalizeWith_nil_eq_self_of_abbrevFree ctx.val ty h

/-- List form of `Ty.normalizeAbbrev_eq_self_of_abbrevFree`. -/
theorem Ty.normalizeAbbrevList_eq_self_of_abbrevFree (ctx : TypeAbbrevCtx)
    (tys : List Ty) (h : Ty.isAbbrevFreeList tys = true) :
    tys.map (Ty.normalizeAbbrev ctx) = tys := by
  exact Ty.normalizeWithList_nil_eq_self_of_abbrevFree ctx.val tys h

@[simp] theorem Ty.normalizeAbbrev_func (ctx : TypeAbbrevCtx) (args : List Ty) (out : Ty) :
    (Ty.func args out).normalizeAbbrev ctx =
      .func (args.map (Ty.normalizeAbbrev ctx)) (out.normalizeAbbrev ctx) := by
  simp [Ty.normalizeAbbrev, Ty.normalizeWith]

private theorem Ty.validListIn_of_mem
    (h : Ty.validListIn ctx typeArity tys = true) (hty : ty ∈ tys) :
    Ty.validIn ctx typeArity ty = true := by
  induction tys with
  | nil => simp at hty
  | cons head tail ih =>
      simp only [Ty.validListIn, Bool.and_eq_true] at h
      simp only [List.mem_cons] at hty
      rcases hty with rfl | hty
      · exact h.1
      · exact ih h.2 hty

private theorem Ty.normalizeWith_subst
    {small big : TypeAbbrevCtx.Raw} {env args : List Ty} {body : Ty}
    (hprefix : ∃ suffix, big = small ++ suffix)
    (hvalid : Ty.validIn small args.length body = true) :
    Ty.normalizeWith big env (Ty.subst args body) =
      Ty.normalizeWith small (args.map (Ty.normalizeWith big env)) body := by
  cases body with
  | var idx =>
      simp only [Ty.validIn, decide_eq_true_eq] at hvalid
      simp [Ty.subst, Ty.normalizeWith, hvalid]
  | prim name => simp [Ty.subst, Ty.normalizeWith]
  | option ty | m ty =>
      simp only [Ty.validIn] at hvalid
      simp [Ty.subst, Ty.normalizeWith, Ty.normalizeWith_subst hprefix hvalid]
  | union tys | struct tys =>
      simp only [Ty.validIn] at hvalid
      have hmap : (tys.map (Ty.subst args)).map (Ty.normalizeWith big env) =
          tys.map (Ty.normalizeWith small (args.map (Ty.normalizeWith big env))) := by
        simp only [List.map_map]
        apply List.map_congr_left
        intro ty hty
        exact Ty.normalizeWith_subst hprefix (Ty.validListIn_of_mem hvalid hty)
      simp [Ty.subst, Ty.normalizeWith, hmap]
  | func inputs output =>
      simp only [Ty.validIn, Bool.and_eq_true] at hvalid
      have hmap : (inputs.map (Ty.subst args)).map (Ty.normalizeWith big env) =
          inputs.map (Ty.normalizeWith small (args.map (Ty.normalizeWith big env))) := by
        simp only [List.map_map]
        apply List.map_congr_left
        intro ty hty
        exact Ty.normalizeWith_subst hprefix (Ty.validListIn_of_mem hvalid.1 hty)
      simp [Ty.subst, Ty.normalizeWith, hmap,
        Ty.normalizeWith_subst hprefix hvalid.2]
  | «abbrev» name typeArgs =>
      simp only [Ty.validIn] at hvalid
      split at hvalid
      next definition hget =>
        simp only [Bool.and_eq_true, decide_eq_true_eq] at hvalid
        obtain ⟨prior, hgetSmall⟩ :=
          TypeAbbrevCtx.Raw.getWithPrefix?_of_get? hget
        obtain ⟨suffix, rfl⟩ := hprefix
        have hgetBig := TypeAbbrevCtx.Raw.getWithPrefix?_append_of_some
          (right := suffix) hgetSmall
        have hargs :
            ((typeArgs.map (Ty.subst args)).map
                (Ty.normalizeWith (small ++ suffix) env)) =
              typeArgs.map (Ty.normalizeWith small
                (args.map (Ty.normalizeWith (small ++ suffix) env))) := by
          simp only [List.map_map]
          apply List.map_congr_left
          intro ty hty
          exact Ty.normalizeWith_subst ⟨suffix, rfl⟩
            (Ty.validListIn_of_mem hvalid.2 hty)
        simp only [Ty.subst, Ty.normalizeWith]
        rw [hgetBig, hgetSmall, hargs]
      next hget => contradiction
termination_by (small.length, sizeOf body)
decreasing_by
  all_goals
    first
    | apply Prod.Lex.left
      exact TypeAbbrevCtx.Raw.getWithPrefix?_prefix_lt (by assumption)
    | apply Prod.Lex.right
      simp_all only [Ty.option.sizeOf_spec, Ty.union.sizeOf_spec, Ty.struct.sizeOf_spec,
        Ty.func.sizeOf_spec, Ty.m.sizeOf_spec, Ty.«abbrev».sizeOf_spec]
      first
      | omega
      | (have := List.sizeOf_lt_of_mem (by assumption); omega)

mutual

private theorem Ty.subst_nil (ty : Ty) : Ty.subst [] ty = ty := by
  cases ty with
  | var idx | prim idx => simp [Ty.subst]
  | option ty | m ty => simp [Ty.subst, Ty.subst_nil ty]
  | union tys | struct tys => simp [Ty.subst, Ty.substNilList tys]
  | func args out => simp [Ty.subst, Ty.substNilList args, Ty.subst_nil out]
  | «abbrev» name args => simp [Ty.subst, Ty.substNilList args]

private theorem Ty.substNilList (tys : List Ty) : tys.map (Ty.subst []) = tys := by
  cases tys with
  | nil => rfl
  | cons ty tys => simp [Ty.subst_nil ty, Ty.substNilList tys]

end

private theorem Ty.AbbrevFreeList.getD_get?
    (h : Ty.AbbrevFreeList tys) (hfallback : fallback.AbbrevFree) (idx : Nat) :
    ((tys[idx]?).getD fallback).AbbrevFree := by
  induction tys generalizing idx with
  | nil => simpa using hfallback
  | cons ty tys ih =>
      cases idx with
      | zero => simpa [Ty.AbbrevFreeList] using h.1
      | succ idx => simpa using ih h.2 idx

mutual

private theorem Ty.normalizeWith_abbrevFree
    {ctx : TypeAbbrevCtx.Raw} {env : List Ty} {body : Ty}
    (hctx : TypeAbbrevCtx.Valid ctx) (henv : Ty.AbbrevFreeList env)
    (hvalid : Ty.validIn ctx env.length body = true) :
    (Ty.normalizeWith ctx env body).AbbrevFree := by
  cases body with
  | var idx =>
      simp only [Ty.normalizeWith]
      split
      · exact henv.getD_get? (by simp [Ty.AbbrevFree]) idx
      · simp [Ty.AbbrevFree]
  | prim name => simp [Ty.normalizeWith, Ty.AbbrevFree]
  | option ty | m ty =>
      simp only [Ty.validIn] at hvalid
      simpa [Ty.normalizeWith, Ty.AbbrevFree] using
        Ty.normalizeWith_abbrevFree hctx henv hvalid
  | union tys | struct tys =>
      simp only [Ty.validIn] at hvalid
      simpa [Ty.normalizeWith, Ty.AbbrevFree] using
        Ty.normalizeWithList_abbrevFree hctx henv hvalid
  | func inputs output =>
      simp only [Ty.validIn, Bool.and_eq_true] at hvalid
      simpa [Ty.normalizeWith, Ty.AbbrevFree] using And.intro
        (Ty.normalizeWithList_abbrevFree hctx henv hvalid.1)
        (Ty.normalizeWith_abbrevFree hctx henv hvalid.2)
  | «abbrev» name args =>
      simp only [Ty.validIn] at hvalid
      split at hvalid
      next definition hget =>
        simp only [Bool.and_eq_true, decide_eq_true_eq] at hvalid
        obtain ⟨prior, hgetPrefix⟩ :=
          TypeAbbrevCtx.Raw.getWithPrefix?_of_get? hget
        have hargs := Ty.normalizeWithList_abbrevFree hctx henv hvalid.2
        have hdefinition := hctx.getWithPrefix? hgetPrefix
        have hbodyValid : Ty.validIn prior
            (args.map (Ty.normalizeWith ctx env)).length definition.body = true := by
          simp [hvalid.1, hdefinition.2]
        simp only [Ty.normalizeWith]
        rw [hgetPrefix]
        simp only [List.length_map, hvalid.1, ↓reduceIte]
        exact Ty.normalizeWith_abbrevFree hdefinition.1 hargs hbodyValid
      next hget => contradiction
termination_by (ctx.length, sizeOf body)
decreasing_by
  all_goals
    first
    | apply Prod.Lex.left
      exact TypeAbbrevCtx.Raw.getWithPrefix?_prefix_lt (by assumption)
    | apply Prod.Lex.right
      simp_all only [Ty.option.sizeOf_spec, Ty.union.sizeOf_spec, Ty.struct.sizeOf_spec,
        Ty.func.sizeOf_spec, Ty.m.sizeOf_spec, Ty.«abbrev».sizeOf_spec]
      first
      | omega
      | (have := List.sizeOf_lt_of_mem (by assumption); omega)

private theorem Ty.normalizeWithList_abbrevFree
    {ctx : TypeAbbrevCtx.Raw} {env : List Ty} {bodies : List Ty}
    (hctx : TypeAbbrevCtx.Valid ctx) (henv : Ty.AbbrevFreeList env)
    (hvalid : Ty.validListIn ctx env.length bodies = true) :
    Ty.AbbrevFreeList (bodies.map (Ty.normalizeWith ctx env)) := by
  cases bodies with
  | nil => trivial
  | cons body bodies =>
      simp only [Ty.validListIn, Bool.and_eq_true] at hvalid
      exact ⟨Ty.normalizeWith_abbrevFree hctx henv hvalid.1,
        Ty.normalizeWithList_abbrevFree hctx henv hvalid.2⟩
termination_by (ctx.length, sizeOf bodies)
decreasing_by
  all_goals
    apply Prod.Lex.right
    simp_all only [List.cons.sizeOf_spec]
    omega

end

/-- Valid closed inputs normalize to types containing no abbreviation applications. -/
theorem Ty.normalizeAbbrev_abbrevFree {ctx : TypeAbbrevCtx} {ty : Ty}
    (hvalid : Ty.validIn ctx.val 0 ty = true) :
    (ty.normalizeAbbrev ctx).AbbrevFree := by
  exact Ty.normalizeWith_abbrevFree ctx.isValid (by trivial) hvalid

mutual

private theorem Ty.AbbrevFree.isAbbrevFree : ∀ (ty : Ty),
    ty.AbbrevFree → ty.isAbbrevFree = true
| .var _, _ | .prim _, _ => rfl
| .option ty, h | .m ty, h => Ty.AbbrevFree.isAbbrevFree ty h
| .union tys, h | .struct tys, h => Ty.AbbrevFreeList.isAbbrevFreeList tys h
| .func args out, h => by
    simp [Ty.isAbbrevFree, Ty.AbbrevFreeList.isAbbrevFreeList args h.1,
      Ty.AbbrevFree.isAbbrevFree out h.2]

private theorem Ty.AbbrevFreeList.isAbbrevFreeList : ∀ (tys : List Ty),
    Ty.AbbrevFreeList tys → Ty.isAbbrevFreeList tys = true
| [], _ => rfl
| ty :: tys, h => by
    simp [Ty.isAbbrevFreeList, Ty.AbbrevFree.isAbbrevFree ty h.1,
      Ty.AbbrevFreeList.isAbbrevFreeList tys h.2]

end


/-- Delta normalization is idempotent on valid closed types. -/
theorem Ty.normalizeAbbrev_idempotent {ctx : TypeAbbrevCtx} {ty : Ty}
    (hvalid : Ty.validIn ctx.val 0 ty = true) :
    (ty.normalizeAbbrev ctx).normalizeAbbrev ctx = ty.normalizeAbbrev ctx := by
  apply Ty.normalizeAbbrev_eq_self_of_abbrevFree
  exact Ty.AbbrevFree.isAbbrevFree _ (Ty.normalizeAbbrev_abbrevFree hvalid)

syntax (name := expandAbbrev) "expand_abbrev" : tactic

elab_rules : tactic
| `(tactic| expand_abbrev) => Lean.Elab.Tactic.withMainContext do
    let target ← Lean.Elab.Tactic.getMainTarget
    match target with
    | .app (.app (.app (.const ``Eq _) _) lhs) _ =>
        unless lhs.isAppOfArity ``Ty.normalizeAbbrev 2 do
          throwError "expand_abbrev requires an equality with Ty.normalizeAbbrev on the left"
        Lean.Elab.Tactic.evalTactic (← `(tactic| native_decide))
    | _ =>
        throwError "expand_abbrev requires an equality with Ty.normalizeAbbrev on the left"

end Zag
