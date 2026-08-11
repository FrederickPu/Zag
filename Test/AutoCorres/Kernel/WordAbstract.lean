import Lang.AutoCorres.ML.word_abstract

/-!
# WordAbstract kernel test

This file retains the synthetic unsigned-addition and catch regression; the
signed/unsigned scalar matrix is in `WordAbstractOperations`. It is not coverage
of `Plus.thy`, which does not enable `unsigned_word_abs`. The catch case also pins
the locally supported part of
[`word_abs_exn.c`](https://github.com/seL4/l4v/blob/bc2599a59c43e673dca021b10b9841e9b8da4430/tools/autocorres/tests/parse-tests/word_abs_exn.c),
without claiming its unsupported calls and loops. Rules are linked directly to:

* [`WordAbstract.thy`](https://github.com/seL4/l4v/blob/bc2599a59c43e673dca021b10b9841e9b8da4430/tools/autocorres/WordAbstract.thy)
* [`word_abstract.ML`](https://github.com/seL4/l4v/blob/bc2599a59c43e673dca021b10b9841e9b8da4430/tools/autocorres/word_abstract.ML)
-/

namespace Zag.Test.AutoCorres.Kernel.WordAbstract

open Zag.Lang.AutoCorres

abbrev Word32 := BitVec 32
abbrev Word := Zag.Lang.AutoCorres.WordAbstract.Kernel.ValueType.word 32
private def w32 (value : Nat) : Word32 := BitVec.ofNat 32 value

def expression : ML.WordAbstract.Source.Expr Word Word32 Word :=
  .add .arg (.state Word id)

def source : ML.WordAbstract.Source.Syntax Word Word32 .unit Word :=
  .gets expression ["ret"]

def certificate := ML.WordAbstract.transformSource source

def expressionCertificate :=
  ML.WordAbstract.Expr.transform (ML.WordAbstract.Expr.supported expression)

theorem generates_entry_guard :
    match certificate.target with | .seq (.guard _) _ => True | _ => False := by
  trivial

theorem exact_target :
    certificate.target =
      Zag.Lang.AutoCorres.WordAbstract.Kernel.Target.Syntax.seq
        (.guard expressionCertificate.guard)
        (fun _ => .gets expressionCertificate.target ["ret"]) := by
  rfl

theorem certified (a : Word32) :
    Zag.Lang.AutoCorres.WordAbstract.corresTA (fun _ => True)
      (Zag.Lang.AutoCorres.WordAbstract.Kernel.typeMap Word).abstract
      (Zag.Lang.AutoCorres.WordAbstract.Kernel.typeMap .unit).abstract
      (certificate.target.denote a.toNat) (source.denote a) :=
  certificate.corres a

def generatedGuard (a : Nat) (b : Word32) : Prop :=
  expressionCertificate.guard a b

theorem generated_guard_eq (a : Nat) (b : Word32) :
    generatedGuard a b <-> a + b.toNat <= 4294967295 := by
  simp [generatedGuard, expressionCertificate, expression,
    ML.WordAbstract.Expr.supported, ML.WordAbstract.Expr.transform,
    Zag.Lang.AutoCorres.WordAbstract.Kernel.Target.Expr.eval,
    Zag.Lang.AutoCorres.WordAbstract.Kernel.Target.asNat,
    Zag.Lang.AutoCorres.WordAbstract.Kernel.Target.maxFor,
    Zag.Lang.AutoCorres.WordAbstract.UWORD_MAX]

theorem in_range_guard_holds : generatedGuard 3 (w32 4) := by
  rw [generated_guard_eq]
  native_decide

theorem overflow_guard_rejects : ¬generatedGuard 4294967295 (w32 1) := by
  rw [generated_guard_eq]
  native_decide

theorem target_runs_in_range :
    (Except.ok 7, w32 4) ∈ (certificate.target.denote 3 (w32 4)).results := by
  rw [exact_target]
  simp [Zag.Lang.AutoCorres.WordAbstract.Kernel.Target.Syntax.denote,
    expressionCertificate, expression, ML.WordAbstract.Expr.supported,
    ML.WordAbstract.Expr.transform,
    Zag.Lang.AutoCorres.WordAbstract.Kernel.Target.Expr.eval,
    Zag.Lang.AutoCorres.WordAbstract.Kernel.Target.asNat,
    Zag.Lang.AutoCorres.WordAbstract.Kernel.Target.maxFor,
    Zag.Lang.AutoCorres.WordAbstract.UWORD_MAX, L2.seq, L2.guard, L2.gets]
  constructor <;> native_decide

theorem in_range_target_does_not_fail :
    ¬(certificate.target.denote 3 (w32 4)).failed := by
  rw [exact_target]
  simp [Zag.Lang.AutoCorres.WordAbstract.Kernel.Target.Syntax.denote,
    expressionCertificate, expression, ML.WordAbstract.Expr.supported,
    ML.WordAbstract.Expr.transform,
    Zag.Lang.AutoCorres.WordAbstract.Kernel.Target.Expr.eval,
    Zag.Lang.AutoCorres.WordAbstract.Kernel.Target.asNat,
    Zag.Lang.AutoCorres.WordAbstract.Kernel.Target.maxFor,
    Zag.Lang.AutoCorres.WordAbstract.UWORD_MAX, L2.seq, L2.guard, bindE,
    L2.failed_liftE, Zag.Lang.AutoCorres.guard]
  constructor
  · native_decide
  · intros
    simp_all [L2.gets, Zag.Lang.AutoCorres.gets]

theorem concrete_source_wraps_without_failure :
    (Except.ok (w32 0), w32 1) ∈
        (source.denote (w32 4294967295) (w32 1)).results ∧
      ¬(source.denote (w32 4294967295) (w32 1)).failed := by
  constructor
  · simp [source, expression,
      Zag.Lang.AutoCorres.WordAbstract.Kernel.Source.Syntax.denote,
      Zag.Lang.AutoCorres.WordAbstract.Kernel.Source.Expr.eval,
      Zag.Lang.AutoCorres.WordAbstract.Kernel.Source.asWord, L2.gets, w32]
  · simp [source, expression,
      Zag.Lang.AutoCorres.WordAbstract.Kernel.Source.Syntax.denote,
      Zag.Lang.AutoCorres.WordAbstract.Kernel.Source.Expr.eval,
      Zag.Lang.AutoCorres.WordAbstract.Kernel.Source.asWord, L2.gets,
      Zag.Lang.AutoCorres.gets]

theorem target_fails_on_overflow :
    (certificate.target.denote 4294967295 (w32 1)).failed := by
  rw [exact_target]
  simp [Zag.Lang.AutoCorres.WordAbstract.Kernel.Target.Syntax.denote,
    expressionCertificate, expression, ML.WordAbstract.Expr.supported,
    ML.WordAbstract.Expr.transform,
    Zag.Lang.AutoCorres.WordAbstract.Kernel.Target.Expr.eval,
    Zag.Lang.AutoCorres.WordAbstract.Kernel.Target.asNat,
    Zag.Lang.AutoCorres.WordAbstract.Kernel.Target.maxFor,
    Zag.Lang.AutoCorres.WordAbstract.UWORD_MAX, L2.seq, L2.guard, bindE,
    L2.failed_liftE, Zag.Lang.AutoCorres.guard]
  exact Or.inl (by native_decide)

theorem overflow_target_has_no_results (result : Except Unit Nat × Word32) :
    result ∉ (certificate.target.denote 4294967295 (w32 1)).results := by
  rw [exact_target]
  rcases result with ⟨outcome, post⟩
  simp [Zag.Lang.AutoCorres.WordAbstract.Kernel.Target.Syntax.denote,
    expressionCertificate, expression, ML.WordAbstract.Expr.supported,
    ML.WordAbstract.Expr.transform,
    Zag.Lang.AutoCorres.WordAbstract.Kernel.Target.Expr.eval,
    Zag.Lang.AutoCorres.WordAbstract.Kernel.Target.asNat,
    Zag.Lang.AutoCorres.WordAbstract.Kernel.Target.maxFor,
    Zag.Lang.AutoCorres.WordAbstract.UWORD_MAX, L2.seq, L2.guard, bindE,
    Zag.Lang.AutoCorres.bind, Zag.Lang.AutoCorres.liftE,
    Zag.Lang.AutoCorres.guard]
  rintro ⟨_, _, ⟨_, _, impossible, _⟩, _⟩
  have overflow : ¬(4294967295 + BitVec.toNat (w32 1) ≤ 4294967295) := by
    native_decide
  exact overflow impossible.1

abbrev UnitType := Zag.Lang.AutoCorres.WordAbstract.Kernel.ValueType.unit
abbrev Word8 := Zag.Lang.AutoCorres.WordAbstract.Kernel.ValueType.word 8
private def w8 (value : Nat) : BitVec 8 := BitVec.ofNat 8 value

def throwSource : ML.WordAbstract.Source.Syntax UnitType Unit Word8 Word8 :=
  .throw (w8 7) ["throw"]

def catchSource : ML.WordAbstract.Source.Syntax UnitType Unit UnitType Word8 :=
  .catch throwSource fun caught => .gets (.word 8 caught) ["caught"]

def catchCertificate := ML.WordAbstract.transformSource catchSource

def expectedCatchTarget :
    ML.WordAbstract.Target.Syntax UnitType Unit UnitType Word8 :=
  .seq (.guard fun _ _ => True) fun _ =>
    .catch (show ML.WordAbstract.Target.Syntax UnitType Unit Word8 Word8 from
      .throw 7 ["throw"]) fun caught =>
      .seq (.guard fun _ _ =>
        (Zag.Lang.AutoCorres.WordAbstract.Kernel.typeMap Word8).certificate.concreteGuard
          caught /\ True) fun _ =>
        .gets (.word 8 (BitVec.ofNat 8 caught).toNat) ["caught"]

theorem catch_target_is_wired : catchCertificate.target = expectedCatchTarget := by
  rfl

theorem catch_is_certified :
    Zag.Lang.AutoCorres.WordAbstract.corresTA (fun _ => True)
      (Zag.Lang.AutoCorres.WordAbstract.Kernel.typeMap Word8).abstract
      (Zag.Lang.AutoCorres.WordAbstract.Kernel.typeMap UnitType).abstract
      (catchCertificate.target.denote ()) (catchSource.denote ()) :=
  catchCertificate.corres ()

theorem catch_target_runs_handler :
    (Except.ok 7, ()) ∈ (catchCertificate.target.denote () ()).results := by
  rw [catch_target_is_wired]
  simp [expectedCatchTarget,
    Zag.Lang.AutoCorres.WordAbstract.Kernel.Target.Syntax.denote,
    L2.seq, L2.guard, L2.catch, L2.throw, L2.gets]
  refine ⟨(), ?_⟩
  unfold handle
  rw [mem_bind]
  refine ⟨Except.error 7, (), ?_, ?_⟩
  · rfl
  · change (Except.ok 7, ()) ∈
      (L2.seq (L2.guard (Exception := Unit) fun _ : Unit => True)
        (fun _ => L2.gets (Exception := Unit)
          (fun _ : Unit => (BitVec.ofNat 8 7).toNat) ["caught"]) ()).results
    rw [L2.seq, mem_bindE_ok]
    exact ⟨(), (), by simp [L2.guard], by simp [L2.gets]⟩

private theorem expected_handler_does_not_fail (caught : Nat) :
    ¬(L2.seq (L2.guard (Exception := Unit) fun _ : Unit => True)
      (fun _ => L2.gets (Exception := Unit)
        (fun _ : Unit => (BitVec.ofNat 8 caught).toNat) ["caught"]) ()).failed := by
  simp [L2.seq, L2.guard, L2.gets, bindE, L2.failed_liftE,
    Zag.Lang.AutoCorres.guard]
  intro x x1 x2 hx _
  cases hx
  cases x1
  cases x2
  simp [L2.failed_liftE, Zag.Lang.AutoCorres.gets]

theorem catch_target_does_not_fail :
    ¬(catchCertificate.target.denote () ()).failed := by
  rw [catch_target_is_wired]
  simp [expectedCatchTarget,
    Zag.Lang.AutoCorres.WordAbstract.Kernel.Target.Syntax.denote,
    L2.seq, L2.guard, L2.catch, L2.throw, L2.gets, bindE,
    L2.failed_liftE, Zag.Lang.AutoCorres.guard]
  intro x x1 x2 hx _
  cases hx
  cases x1
  cases x2
  intro _
  rename_i _ continuationFailed
  exact continuationFailed.elim
    (fun bodyFailed => by
      simp [Zag.Lang.AutoCorres.throw, Zag.Lang.AutoCorres.pure] at bodyFailed)
    (fun rest => rest.elim fun value tail => tail.elim fun middle data =>
      match value with
      | .error exception => expected_handler_does_not_fail exception data.2
      | .ok value => by
          simpa [returnOk, Zag.Lang.AutoCorres.pure] using data.2)

private theorem expected_handler_has_no_error (caught : Nat) :
    (Except.error (), ()) ∉
      (L2.seq (L2.guard (Exception := Unit) fun _ : Unit => True)
        (fun _ => L2.gets (Exception := Unit)
          (fun _ : Unit => (BitVec.ofNat 8 caught).toNat) ["caught"]) ()).results := by
  intro member
  unfold L2.seq bindE at member
  rcases member with ⟨first, middle, firstMember, nextMember⟩
  cases first with
  | error exception =>
      simp [L2.guard] at firstMember
  | ok value =>
      change (Except.error (), ()) ∈
        (L2.gets (Exception := Unit)
          (fun _ : Unit => (BitVec.ofNat 8 caught).toNat) ["caught"] middle).results
        at nextMember
      simp [L2.gets] at nextMember

theorem catch_consumes_exception :
    (Except.error (), ()) ∉ (catchCertificate.target.denote () ()).results := by
  rw [catch_target_is_wired]
  simp [expectedCatchTarget,
    Zag.Lang.AutoCorres.WordAbstract.Kernel.Target.Syntax.denote,
    L2.seq, L2.guard, L2.catch, L2.throw, L2.gets]
  rintro ⟨value, middle, outer, continuation⟩
  rcases outer with ⟨outerValue, outerState, _, returned⟩
  change (value, middle) = (Except.ok outerValue, outerState) at returned
  cases returned
  rcases continuation with ⟨caught, caughtState, bodyMember, handlerMember⟩
  change (caught, caughtState) = (Except.error 7, middle) at bodyMember
  cases bodyMember
  exact expected_handler_has_no_error 7 handlerMember

end Zag.Test.AutoCorres.Kernel.WordAbstract
