import Lang.Simple.ABI
import Lang.Simple.Defs
import Lang.Simple.Lift

/-!
  # C0 — restricted surface (`BitVec 32` words)

  `Expr` / `Stmt` are the only surface AST. For arity 2, `elab` produces `Com`
  with Basics that are **only** assignments `setᵢ(e)` for word expressions.
-/

namespace Lang.Simple.C0

open Lang.Simple
open Lang.Simple.ABI
open Zag

inductive BinOp where
  | add | sub | lt
  deriving DecidableEq, Repr

inductive Expr (n : Nat) where
  | var : Fin n → Expr n
  | lit : Word → Expr n
  | bin : BinOp → Expr n → Expr n → Expr n
  deriving Repr

inductive Stmt (n : Nat) where
  | skip : Stmt n
  | assign : Fin n → Expr n → Stmt n
  | seq : Stmt n → Stmt n → Stmt n
  | ite : Expr n → Stmt n → Stmt n → Stmt n
  | «while» : Expr n → Stmt n → Stmt n
  | throw : Stmt n
  | catch : Stmt n → Stmt n → Stmt n
  deriving Repr

def localName : Nat → String
  | 0 => "x" | 1 => "y" | 2 => "z" | 3 => "w"
  | k => "v" ++ toString k

def locals (n : Nat) : Lang.Simple.Lift.L2.LocalContext where
  vars := (List.range n).map fun i => { name := localName i, ty := WordTy }

end Lang.Simple.C0

namespace Lang.Simple.C0.W2

open Lang.Simple
open Lang.Simple.ABI
open Lang.Simple.Lift
open Zag
open C0

abbrev ctx : Context := wordStateContext 2
abbrev Proc := Empty
abbrev Fault := Unit
def locals : L2.LocalContext := C0.locals 2

def iGet0 : Fin ctx.zagCtx.primFuncCtx.length := ⟨0, by native_decide⟩
def iGet1 : Fin ctx.zagCtx.primFuncCtx.length := ⟨1, by native_decide⟩
def iSet0 : Fin ctx.zagCtx.primFuncCtx.length := ⟨2, by native_decide⟩
def iSet1 : Fin ctx.zagCtx.primFuncCtx.length := ⟨3, by native_decide⟩
def iLt : Fin ctx.zagCtx.primFuncCtx.length := ⟨5, by native_decide⟩
def iAdd : Fin ctx.zagCtx.primFuncCtx.length := ⟨6, by native_decide⟩
def iSub : Fin ctx.zagCtx.primFuncCtx.length := ⟨7, by native_decide⟩

private theorem nGet0 : ctx.zagCtx.primFuncCtx[iGet0].1 = "state.get.0" := by native_decide
private theorem nGet1 : ctx.zagCtx.primFuncCtx[iGet1].1 = "state.get.1" := by native_decide
private theorem nSet0 : ctx.zagCtx.primFuncCtx[iSet0].1 = "state.set.0" := by native_decide
private theorem nSet1 : ctx.zagCtx.primFuncCtx[iSet1].1 = "state.set.1" := by native_decide
private theorem nLt : ctx.zagCtx.primFuncCtx[iLt].1 = "word.lt" := by native_decide
private theorem nAdd : ctx.zagCtx.primFuncCtx[iAdd].1 = "word.add" := by native_decide
private theorem nSub : ctx.zagCtx.primFuncCtx[iSub].1 = "word.sub" := by native_decide
private theorem tGet0 : ctx.zagCtx.primFuncCtx[iGet0].2.ty = .func [StateTy] WordTy := by native_decide
private theorem tGet1 : ctx.zagCtx.primFuncCtx[iGet1].2.ty = .func [StateTy] WordTy := by native_decide
private theorem tSet0 : ctx.zagCtx.primFuncCtx[iSet0].2.ty = .func [StateTy, WordTy] StateTy := by native_decide
private theorem tSet1 : ctx.zagCtx.primFuncCtx[iSet1].2.ty = .func [StateTy, WordTy] StateTy := by native_decide
private theorem tLt : ctx.zagCtx.primFuncCtx[iLt].2.ty = .func [WordTy, WordTy] (.prim "Bool") := by native_decide
private theorem tAdd : ctx.zagCtx.primFuncCtx[iAdd].2.ty = .func [WordTy, WordTy] WordTy := by native_decide
private theorem tSub : ctx.zagCtx.primFuncCtx[iSub].2.ty = .func [WordTy, WordTy] WordTy := by native_decide

def st : Term ctx.primCtx := .var 0
def x : Term ctx.primCtx := .app (.primFunc "state.get.0") [st]
def y : Term ctx.primCtx := .app (.primFunc "state.get.1") [st]
def setX (v : Term ctx.primCtx) : Term ctx.primCtx :=
  .app (.primFunc "state.set.0") [st, v]
def setY (v : Term ctx.primCtx) : Term ctx.primCtx :=
  .app (.primFunc "state.set.1") [st, v]
def litT (w : Word) : Term ctx.primCtx := .prim WordTy (State.ofWord w)

theorem lit_ty (w : Word) : Term.hasType ctx.zagCtx [StateTy] (litT w) WordTy :=
  Term.hasType.prim _

theorem x_ty : Term.hasType ctx.zagCtx [StateTy] x WordTy := by
  have hf := hasType_primFunc_at (ctx := ctx.zagCtx) (varCtx := [StateTy]) iGet0
  rw [nGet0, tGet0] at hf
  refine Term.hasType.app hf rfl ?_
  intro idx; match idx with | ⟨0, _⟩ => exact Term.hasType.var (idx := ⟨0, by decide⟩) rfl

theorem y_ty : Term.hasType ctx.zagCtx [StateTy] y WordTy := by
  have hf := hasType_primFunc_at (ctx := ctx.zagCtx) (varCtx := [StateTy]) iGet1
  rw [nGet1, tGet1] at hf
  refine Term.hasType.app hf rfl ?_
  intro idx; match idx with | ⟨0, _⟩ => exact Term.hasType.var (idx := ⟨0, by decide⟩) rfl

theorem setX_ty (v : Term ctx.primCtx) (hv : Term.hasType ctx.zagCtx [StateTy] v WordTy) :
    Term.hasType ctx.zagCtx [StateTy] (setX v) StateTy := by
  have hf := hasType_primFunc_at (ctx := ctx.zagCtx) (varCtx := [StateTy]) iSet0
  rw [nSet0, tSet0] at hf
  refine Term.hasType.app hf rfl ?_
  intro idx; match idx with
  | ⟨0, _⟩ => exact Term.hasType.var (idx := ⟨0, by decide⟩) rfl
  | ⟨1, _⟩ => exact hv

theorem setY_ty (v : Term ctx.primCtx) (hv : Term.hasType ctx.zagCtx [StateTy] v WordTy) :
    Term.hasType ctx.zagCtx [StateTy] (setY v) StateTy := by
  have hf := hasType_primFunc_at (ctx := ctx.zagCtx) (varCtx := [StateTy]) iSet1
  rw [nSet1, tSet1] at hf
  refine Term.hasType.app hf rfl ?_
  intro idx; match idx with
  | ⟨0, _⟩ => exact Term.hasType.var (idx := ⟨0, by decide⟩) rfl
  | ⟨1, _⟩ => exact hv

def get (i : Fin 2) : Term ctx.primCtx := match i with | ⟨0, _⟩ => x | ⟨1, _⟩ => y
def setT (i : Fin 2) (v : Term ctx.primCtx) : Term ctx.primCtx :=
  match i with | ⟨0, _⟩ => setX v | ⟨1, _⟩ => setY v

theorem get_ty (i : Fin 2) : Term.hasType ctx.zagCtx [StateTy] (get i) WordTy := by
  match i with | ⟨0, _⟩ => exact x_ty | ⟨1, _⟩ => exact y_ty

theorem set_ty (i : Fin 2) (v : Term ctx.primCtx)
    (hv : Term.hasType ctx.zagCtx [StateTy] v WordTy) :
    Term.hasType ctx.zagCtx [StateTy] (setT i v) StateTy := by
  match i with | ⟨0, _⟩ => exact setX_ty v hv | ⟨1, _⟩ => exact setY_ty v hv

theorem bin_word_ty (name : String) (idx : Fin ctx.zagCtx.primFuncCtx.length)
    (hn : ctx.zagCtx.primFuncCtx[idx].1 = name)
    (ht : ctx.zagCtx.primFuncCtx[idx].2.ty = .func [WordTy, WordTy] WordTy)
    (a b : Term ctx.primCtx)
    (ha : Term.hasType ctx.zagCtx [StateTy] a WordTy)
    (hb : Term.hasType ctx.zagCtx [StateTy] b WordTy) :
    Term.hasType ctx.zagCtx [StateTy] (.app (.primFunc name) [a, b]) WordTy := by
  have hf := hasType_primFunc_at (ctx := ctx.zagCtx) (varCtx := [StateTy]) idx
  rw [hn, ht] at hf
  refine Term.hasType.app hf rfl ?_
  intro i; match i with
  | ⟨0, _⟩ => exact ha
  | ⟨1, _⟩ => exact hb

theorem bin_bool_ty (name : String) (idx : Fin ctx.zagCtx.primFuncCtx.length)
    (hn : ctx.zagCtx.primFuncCtx[idx].1 = name)
    (ht : ctx.zagCtx.primFuncCtx[idx].2.ty = .func [WordTy, WordTy] (.prim "Bool"))
    (a b : Term ctx.primCtx)
    (ha : Term.hasType ctx.zagCtx [StateTy] a WordTy)
    (hb : Term.hasType ctx.zagCtx [StateTy] b WordTy) :
    Term.hasType ctx.zagCtx [StateTy] (.app (.primFunc name) [a, b]) (.prim "Bool") := by
  have hf := hasType_primFunc_at (ctx := ctx.zagCtx) (varCtx := [StateTy]) idx
  rw [hn, ht] at hf
  refine Term.hasType.app hf rfl ?_
  intro i; match i with
  | ⟨0, _⟩ => exact ha
  | ⟨1, _⟩ => exact hb

/-- Elaborate a word-valued expression (not `lt`). -/
def elabWord : Expr 2 → Option (TermOf ctx.zagCtx [StateTy] WordTy)
  | .var i => some ⟨get i, get_ty i⟩
  | .lit w => some ⟨litT w, lit_ty w⟩
  | .bin .add a b => do
      let ⟨ta, ha⟩ ← elabWord a
      let ⟨tb, hb⟩ ← elabWord b
      some ⟨.app (.primFunc "word.add") [ta, tb],
        bin_word_ty "word.add" iAdd nAdd tAdd ta tb ha hb⟩
  | .bin .sub a b => do
      let ⟨ta, ha⟩ ← elabWord a
      let ⟨tb, hb⟩ ← elabWord b
      some ⟨.app (.primFunc "word.sub") [ta, tb],
        bin_word_ty "word.sub" iSub nSub tSub ta tb ha hb⟩
  | .bin .lt _ _ => none

/-- Elaborate a boolean expression (`lt` only). -/
def elabBool : Expr 2 → Option (TermOf ctx.zagCtx [StateTy] (.prim "Bool"))
  | .bin .lt a b => do
      let ⟨ta, ha⟩ ← elabWord a
      let ⟨tb, hb⟩ ← elabWord b
      some ⟨.app (.primFunc "word.lt") [ta, tb],
        bin_bool_ty "word.lt" iLt nLt tLt ta tb ha hb⟩
  | _ => none

/-- Elaborate C0 statement → Simpl `Com` (Basics are only assignments). -/
def toCom : Stmt 2 → Option (Com ctx Proc Fault)
  | .skip => some .Skip
  | .assign i e => do
      let ⟨te, he⟩ ← elabWord e
      some (.Basic ⟨setT i te, set_ty i te he⟩)
  | .seq a b => do
      let ca ← toCom a
      let cb ← toCom b
      some (.Seq ca cb)
  | .ite c t e => do
      let ⟨tc, hc⟩ ← elabBool c
      let ct ← toCom t
      let ce ← toCom e
      some (.Cond ⟨tc, hc⟩ ct ce)
  | .while c b => do
      let ⟨tc, hc⟩ ← elabBool c
      let cb ← toCom b
      some (.While ⟨tc, hc⟩ cb)
  | .throw => some .Throw
  | .catch a b => do
      let ca ← toCom a
      let cb ← toCom b
      some (.Catch ca cb)

/-! ### Surface programs as C0 AST, then `elab` -/

/-- `x = x + y` -/
def addStmt : Stmt 2 :=
  .assign ⟨0, by decide⟩ (.bin .add (.var ⟨0, by decide⟩) (.var ⟨1, by decide⟩))

theorem add_elab : (toCom addStmt).isSome = true := by native_decide
def add : Com ctx Proc Fault := (toCom addStmt).get (by simp [add_elab])

/-- `if (x < y) x = y; else skip` -/
def maxStmt : Stmt 2 :=
  .ite (.bin .lt (.var ⟨0, by decide⟩) (.var ⟨1, by decide⟩))
    (.assign ⟨0, by decide⟩ (.var ⟨1, by decide⟩))
    .skip

theorem max_elab : (toCom maxStmt).isSome = true := by native_decide
def max : Com ctx Proc Fault := (toCom maxStmt).get (by simp [max_elab])

/-- `try { throw } catch { skip }` -/
def throwCatchStmt : Stmt 2 := .catch .throw .skip

theorem throwCatch_elab : (toCom throwCatchStmt).isSome = true := by native_decide
def throwCatch : Com ctx Proc Fault := (toCom throwCatchStmt).get (by simp [throwCatch_elab])

/--
  Gauss body loop (same shape as `Test/Gauss/Simple`):
  `while (0 < i) { acc = acc + i; i = i - 1; }`
  with locals x=i, y=acc.
-/
def gaussStmt : Stmt 2 :=
  .while (.bin .lt (.lit (Word.ofNat 0)) (.var ⟨0, by decide⟩))
    (.seq
      (.assign ⟨1, by decide⟩
        (.bin .add (.var ⟨1, by decide⟩) (.var ⟨0, by decide⟩)))
      (.assign ⟨0, by decide⟩
        (.bin .sub (.var ⟨0, by decide⟩) (.lit (Word.ofNat 1)))))

theorem gauss_elab : (toCom gaussStmt).isSome = true := by native_decide
def gauss : Com ctx Proc Fault := (toCom gaussStmt).get (by simp [gauss_elab])

def add_L2 := pureChain? locals add
def max_L2 := pureChain? locals max
def gauss_L2 := pureChain? locals gauss
def throwCatch_L1 := exnChain? throwCatch

def add_WA := do let s ← add_L2; chainWA? 2 s
def gauss_WA := do let s ← gauss_L2; chainWA? 2 s
def add_full := fullPureChain? 2 locals add

def eval_L2 (ssa : Zag.Lang.SSA.SSAExpr ctx.primCtx) (xv yv : Word) :
    Option (Word × Word) := do
  let v ← L2.evalSSAWithLocals? locals [State.wordVal xv, State.wordVal yv] ssa
  let tys := [WordTy, WordTy]
  let raw ← v.as? (.struct tys)
  let fields := cast (Ty.type.eq_5 ctx.primCtx tys) raw
  some (State.toWord (fields ⟨0, by decide⟩), State.toWord (fields ⟨1, by decide⟩))

def eval_L2_nats (ssa : Zag.Lang.SSA.SSAExpr ctx.primCtx) (x y : Nat) :
    Option (Nat × Nat) := do
  let (a, b) ← eval_L2 ssa (Word.ofNat x) (Word.ofNat y)
  some (Word.toNat a, Word.toNat b)

end Lang.Simple.C0.W2
