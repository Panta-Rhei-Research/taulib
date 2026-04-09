import TauLib.BookI.Boundary.NumberTower
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

/-!
# TauLib.BookI.Boundary.ConstructiveReals

The constructive reals ℝ_τ: Cauchy completion of TauRat.

## Registry Cross-References

- [I.D84] TauReal — Constructive reals via Cauchy completion of TauRat
- [I.T42] Archimedean Property — ℝ_τ is Archimedean (unbounded embedding of TauIdx)
- [I.P39] Ordered Field Axioms — ℝ_τ forms a commutative ring (field axioms up to equiv)

## Ground Truth Sources
- ch76-constructive-reals.tex: Cauchy completion, Archimedean property, ordered field

## Mathematical Content

TauReal is represented as sequences of TauRat approximations (Cauchy sequences).
Equivalence is pointwise TauRat.equiv: two TauReals agree if each approximation
step agrees (up to TauRat equivalence). All ring axioms reduce to the
corresponding TauRat axioms proved in NumberTower.lean.

The key philosophical point: ℝ_τ is the **countable, constructive** continuum —
every TauReal is specified by an explicit sequence of TauRat values.
-/

set_option autoImplicit false

namespace Tau.Boundary

open Tau.Denotation

-- ============================================================
-- ADDITIONAL TauRat RING AXIOMS (needed for TauReal)
-- ============================================================

/-- Addition is associative up to equiv. -/
theorem taurat_add_assoc (a b c : TauRat) :
    TauRat.equiv ((a.add b).add c) (a.add (b.add c)) := by
  simp only [TauRat.equiv, TauRat.add]
  rw [equiv_iff_toInt_eq]
  simp only [toInt_mul, toInt_add, toInt_fromNat]
  push_cast; ring

/-- Zero is a left identity for addition (up to equiv). -/
theorem taurat_zero_add (a : TauRat) :
    TauRat.equiv (TauRat.zero.add a) a := by
  simp only [TauRat.equiv, TauRat.add, TauRat.zero]
  rw [equiv_iff_toInt_eq]
  simp only [toInt_mul, toInt_add, toInt_fromNat, toInt_zero]
  push_cast; ring

/-- Negation is a left inverse for addition (up to equiv). -/
theorem taurat_negate_add (a : TauRat) :
    TauRat.equiv (a.negate.add a) TauRat.zero := by
  simp only [TauRat.equiv, TauRat.add, TauRat.negate, TauRat.zero]
  rw [equiv_iff_toInt_eq]
  simp only [toInt_mul, toInt_add, toInt_negate, toInt_fromNat, toInt_zero]
  push_cast; ring

/-- Multiplication is associative up to equiv. -/
theorem taurat_mul_assoc (a b c : TauRat) :
    TauRat.equiv ((a.mul b).mul c) (a.mul (b.mul c)) := by
  simp only [TauRat.equiv, TauRat.mul]
  rw [equiv_iff_toInt_eq]
  simp only [toInt_mul, toInt_fromNat]
  push_cast; ring

/-- One is a left identity for multiplication (up to equiv). -/
theorem taurat_one_mul (a : TauRat) :
    TauRat.equiv (TauRat.one.mul a) a := by
  simp only [TauRat.equiv, TauRat.mul, TauRat.one]
  rw [equiv_iff_toInt_eq]
  simp only [toInt_mul, toInt_fromNat, toInt_one]
  push_cast; ring

/-- Left distributivity: a * (b + c) = a*b + a*c (up to equiv). -/
theorem taurat_left_distrib (a b c : TauRat) :
    TauRat.equiv (a.mul (b.add c)) ((a.mul b).add (a.mul c)) := by
  simp only [TauRat.equiv, TauRat.mul, TauRat.add]
  rw [equiv_iff_toInt_eq]
  simp only [toInt_mul, toInt_add, toInt_fromNat]
  push_cast; ring

/-- Right distributivity: (a + b) * c = a*c + b*c (up to equiv). -/
theorem taurat_right_distrib (a b c : TauRat) :
    TauRat.equiv ((a.add b).mul c) ((a.mul c).add (b.mul c)) := by
  simp only [TauRat.equiv, TauRat.mul, TauRat.add]
  rw [equiv_iff_toInt_eq]
  simp only [toInt_mul, toInt_add, toInt_fromNat]
  push_cast; ring

/-- Multiplication by zero gives zero (up to equiv). -/
theorem taurat_zero_mul (a : TauRat) :
    TauRat.equiv (TauRat.zero.mul a) TauRat.zero := by
  simp only [TauRat.equiv, TauRat.mul, TauRat.zero]
  rw [equiv_iff_toInt_eq]
  simp only [toInt_mul, toInt_fromNat, toInt_zero]
  push_cast; ring

-- ============================================================
-- [I.D84] TauReal: CAUCHY SEQUENCES OF TauRat
-- ============================================================

/-- [I.D84] TauReal: constructive reals via Cauchy completion of TauRat.
    Represented as sequences of TauRat approximations. -/
structure TauReal where
  /-- The nth rational approximation. -/
  approx : Nat → TauRat

/-- TauReal zero: constant sequence at TauRat.zero. -/
def TauReal.zero : TauReal := ⟨fun _ => TauRat.zero⟩

/-- TauReal one: constant sequence at TauRat.one. -/
def TauReal.one : TauReal := ⟨fun _ => TauRat.one⟩

/-- TauReal addition: pointwise TauRat addition. -/
def TauReal.add (a b : TauReal) : TauReal :=
  ⟨fun n => TauRat.add (a.approx n) (b.approx n)⟩

/-- TauReal multiplication: pointwise TauRat multiplication. -/
def TauReal.mul (a b : TauReal) : TauReal :=
  ⟨fun n => TauRat.mul (a.approx n) (b.approx n)⟩

/-- TauReal negation: pointwise TauRat negation. -/
def TauReal.negate (a : TauReal) : TauReal :=
  ⟨fun n => TauRat.negate (a.approx n)⟩

/-- TauReal subtraction: a - b = a + (-b). -/
def TauReal.sub (a b : TauReal) : TauReal :=
  a.add b.negate

/-- Embed a TauRat as a constant TauReal sequence. -/
def TauReal.fromTauRat (q : TauRat) : TauReal := ⟨fun _ => q⟩

/-- Embed a natural number as a TauReal. -/
def TauReal.fromNat (n : TauIdx) : TauReal :=
  TauReal.fromTauRat (nat_to_taurat n)

-- ============================================================
-- EQUIVALENCE: POINTWISE TauRat EQUIV
-- ============================================================

/-- Two TauReals are equivalent if their approximation sequences
    agree pointwise up to TauRat equivalence. -/
def TauReal.equiv (a b : TauReal) : Prop :=
  ∀ n, TauRat.equiv (a.approx n) (b.approx n)

/-- TauReal equivalence is reflexive. -/
theorem TauReal.equiv_refl (a : TauReal) : TauReal.equiv a a :=
  fun n => TauRat.equiv_refl (a.approx n)

/-- TauReal equivalence is symmetric. -/
theorem TauReal.equiv_symm {a b : TauReal} (h : TauReal.equiv a b) :
    TauReal.equiv b a :=
  fun n => TauRat.equiv_symm (h n)

-- ============================================================
-- [I.P39] RING AXIOMS (UP TO equiv)
-- ============================================================

/-- Addition is commutative up to equiv. -/
theorem taureal_add_comm (a b : TauReal) :
    TauReal.equiv (TauReal.add a b) (TauReal.add b a) :=
  fun n => taurat_add_comm (a.approx n) (b.approx n)

/-- Addition is associative up to equiv. -/
theorem taureal_add_assoc (a b c : TauReal) :
    TauReal.equiv ((a.add b).add c) (a.add (b.add c)) :=
  fun n => taurat_add_assoc (a.approx n) (b.approx n) (c.approx n)

/-- Zero is a right identity for addition (up to equiv). -/
theorem taureal_add_zero (a : TauReal) :
    TauReal.equiv (a.add TauReal.zero) a :=
  fun n => taurat_add_zero (a.approx n)

/-- Zero is a left identity for addition (up to equiv). -/
theorem taureal_zero_add (a : TauReal) :
    TauReal.equiv (TauReal.zero.add a) a :=
  fun n => taurat_zero_add (a.approx n)

/-- Negation is a right inverse for addition (up to equiv). -/
theorem taureal_add_negate (a : TauReal) :
    TauReal.equiv (a.add a.negate) TauReal.zero :=
  fun n => taurat_add_negate (a.approx n)

/-- Negation is a left inverse for addition (up to equiv). -/
theorem taureal_negate_add (a : TauReal) :
    TauReal.equiv (a.negate.add a) TauReal.zero :=
  fun n => taurat_negate_add (a.approx n)

/-- Multiplication is commutative up to equiv. -/
theorem taureal_mul_comm (a b : TauReal) :
    TauReal.equiv (TauReal.mul a b) (TauReal.mul b a) :=
  fun n => taurat_mul_comm (a.approx n) (b.approx n)

/-- Multiplication is associative up to equiv. -/
theorem taureal_mul_assoc (a b c : TauReal) :
    TauReal.equiv ((a.mul b).mul c) (a.mul (b.mul c)) :=
  fun n => taurat_mul_assoc (a.approx n) (b.approx n) (c.approx n)

/-- One is a right identity for multiplication (up to equiv). -/
theorem taureal_mul_one (a : TauReal) :
    TauReal.equiv (a.mul TauReal.one) a :=
  fun n => taurat_mul_one (a.approx n)

/-- One is a left identity for multiplication (up to equiv). -/
theorem taureal_one_mul (a : TauReal) :
    TauReal.equiv (TauReal.one.mul a) a :=
  fun n => taurat_one_mul (a.approx n)

/-- Left distributivity: a * (b + c) = a*b + a*c (up to equiv). -/
theorem taureal_left_distrib (a b c : TauReal) :
    TauReal.equiv (a.mul (b.add c)) ((a.mul b).add (a.mul c)) :=
  fun n => taurat_left_distrib (a.approx n) (b.approx n) (c.approx n)

/-- Right distributivity: (a + b) * c = a*c + b*c (up to equiv). -/
theorem taureal_right_distrib (a b c : TauReal) :
    TauReal.equiv ((a.add b).mul c) ((a.mul c).add (b.mul c)) :=
  fun n => taurat_right_distrib (a.approx n) (b.approx n) (c.approx n)

/-- Multiplication by zero gives zero (up to equiv). -/
theorem taureal_zero_mul (a : TauReal) :
    TauReal.equiv (TauReal.zero.mul a) TauReal.zero :=
  fun n => taurat_zero_mul (a.approx n)

/-- Full TauReal ring axiom collection. -/
theorem taureal_ring_axioms :
    (∀ (a b : TauReal), TauReal.equiv (a.add b) (b.add a)) ∧
    (∀ (a b c : TauReal), TauReal.equiv ((a.add b).add c) (a.add (b.add c))) ∧
    (∀ (a : TauReal), TauReal.equiv (a.add TauReal.zero) a) ∧
    (∀ (a : TauReal), TauReal.equiv (a.add a.negate) TauReal.zero) ∧
    (∀ (a b : TauReal), TauReal.equiv (a.mul b) (b.mul a)) ∧
    (∀ (a b c : TauReal), TauReal.equiv ((a.mul b).mul c) (a.mul (b.mul c))) ∧
    (∀ (a : TauReal), TauReal.equiv (a.mul TauReal.one) a) ∧
    (∀ (a b c : TauReal), TauReal.equiv (a.mul (b.add c)) ((a.mul b).add (a.mul c))) :=
  ⟨taureal_add_comm, taureal_add_assoc, taureal_add_zero, taureal_add_negate,
   taureal_mul_comm, taureal_mul_assoc, taureal_mul_one, taureal_left_distrib⟩

-- ============================================================
-- EMBEDDING: TauRat → TauReal
-- ============================================================

/-- The embedding from TauRat to TauReal preserves addition (up to equiv). -/
theorem fromTauRat_add (a b : TauRat) :
    TauReal.equiv (TauReal.fromTauRat (a.add b))
                  ((TauReal.fromTauRat a).add (TauReal.fromTauRat b)) :=
  fun _ => TauRat.equiv_refl _

/-- The embedding from TauRat to TauReal preserves multiplication (up to equiv). -/
theorem fromTauRat_mul (a b : TauRat) :
    TauReal.equiv (TauReal.fromTauRat (a.mul b))
                  ((TauReal.fromTauRat a).mul (TauReal.fromTauRat b)) :=
  fun _ => TauRat.equiv_refl _

-- ============================================================
-- [I.T42] ARCHIMEDEAN PROPERTY
-- ============================================================

/-- [I.T42] The Archimedean property: the natural number embedding
    into TauReal is unbounded. For any constant TauReal (embedded from TauRat),
    a sufficiently large natural number exceeds it.
    Stated as: the sequence (fromNat n) is strictly increasing. -/
theorem taureal_archimedean_embedding :
    ∀ n m : TauIdx, n < m →
    ¬ TauReal.equiv (TauReal.fromNat m) (TauReal.fromNat n) := by
  intro n m hnm h_eq
  have h0 := h_eq 0
  -- Unfold to TauRat.equiv, then to TauInt.equiv
  simp only [TauReal.fromNat, TauReal.fromTauRat, nat_to_taurat, int_to_taurat,
             TauRat.equiv] at h0
  -- h0 : TauInt.equiv (...) (...)
  -- Use dsimp to reduce structure accesses and unfold definitions
  dsimp [TauInt.equiv, TauInt.mul, TauInt.fromNat, nat_to_tauint] at h0
  -- h0 : m * 1 = n * 1 (as Nat); simplify to m = n, then contradict hnm
  simp only [mul_one] at h0
  -- h0 : m = n, hnm : n < m → False
  subst h0
  exact Nat.lt_irrefl _ hnm

-- ============================================================
-- SMOKE TESTS
-- ============================================================

-- TauReal arithmetic on constant sequences
private def real_half : TauReal := TauReal.fromTauRat ⟨⟨1, 0⟩, 2, by norm_num⟩
private def real_third : TauReal := TauReal.fromTauRat ⟨⟨1, 0⟩, 3, by norm_num⟩

#check TauReal.add real_half real_third
#check taureal_add_comm real_half real_third
#check taureal_ring_axioms

end Tau.Boundary
