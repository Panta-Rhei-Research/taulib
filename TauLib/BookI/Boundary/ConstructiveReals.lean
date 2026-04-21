import TauLib.BookI.Boundary.TauRatAbs
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push
import Mathlib.Tactic.FieldSimp

/-!
# TauLib.BookI.Boundary.ConstructiveReals

The constructive reals ℝ_τ: Cauchy completion of TauRat.

## Registry Cross-References

- [I.D84] TauReal — Constructive reals via Cauchy completion of TauRat
- [I.T42] Archimedean Property — ℝ_τ is Archimedean (unbounded embedding of TauIdx)
- [I.P39] Ordered Field Axioms — ℝ_τ forms a commutative ring (field axioms up to equiv)
- [I.D111] TauReal.IsCauchy — Wave 2 Cauchy predicate with explicit modulus
- [I.D112] TauReal.equiv — Wave 2 Cauchy equivalence

## Ground Truth Sources
- ch76-constructive-reals.tex: Cauchy completion, Archimedean property, ordered field

## Mathematical Content

**Wave 2a refactor** (see `ROADMAP-3-HINGES.md`): `TauReal.equiv` is now
**Cauchy equivalence** — two TauReals are equivalent when the pointwise
difference sequence converges to zero at some explicit rate
(modulus of convergence).  This is the correct notion of equality in
the Cauchy completion of TauRat and is strictly weaker than pointwise
`TauRat.equiv` at every index.

Design principle (per discussion #5): strict single-relation purity at
the τ-kernel level.  The former pointwise version is preserved as the
`TauReal.equiv_of_pointwise` bridge lemma — any proof that previously
supplied a pointwise witness now routes through that helper.

Core new API:

- `TauReal.IsCauchy x` : `∃ modulus, ∀ k m n, m, n ≥ modulus k →
  |x.approx m - x.approx n| < 1/(k+1)`.
- `TauReal.equiv a b` : analogous, on the difference sequence
  `a.approx n - b.approx n`.  This **replaces** the pointwise version.
- `TauReal.equiv_of_pointwise` : pointwise `TauRat.equiv` at every index
  implies Cauchy equivalence (the modulus is `λ _ => 0`).

All existing ring-axiom proofs are rewritten to apply
`equiv_of_pointwise` to the pre-existing pointwise witnesses — the
underlying pointwise reasoning is unchanged, only the final wrapping.
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
-- [I.D84] TauReal: SEQUENCES OF TauRat APPROXIMATIONS
-- ============================================================

/-- [I.D84] TauReal: constructive reals, represented as sequences of
    TauRat approximations.  The sequence need not be Cauchy in the
    definition of the type — the Cauchy condition is carried by the
    separate `TauReal.IsCauchy` predicate, and equivalence is defined
    as Cauchy equivalence regardless of whether the underlying
    sequences themselves are Cauchy. -/
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
-- [I.D111] IsCauchy PREDICATE (explicit modulus)
-- ============================================================

/-- [I.D111] `TauReal.IsCauchy x`: the approximation sequence of `x`
    is Cauchy with an explicit (constructive) modulus of convergence.

    For every `k`, there is an index `modulus k` after which the
    pairwise distance of approximations stays below `1/(k+1)`. -/
def TauReal.IsCauchy (x : TauReal) : Prop :=
  ∃ modulus : Nat → Nat, ∀ k m n : Nat,
    modulus k ≤ m → modulus k ≤ n →
    TauRat.lt ((x.approx m).sub (x.approx n)).abs (TauRat.ofNatRecip k)

-- ============================================================
-- [I.D112] EQUIVALENCE: CAUCHY COMPLETION
-- ============================================================

/-- [I.D112] Two TauReals are **Cauchy-equivalent** if the pointwise
    difference sequence converges to zero at some explicit rate.

    Formally: there is a modulus `μ : Nat → Nat` such that for every
    tolerance level `k`, past index `μ k` the pointwise difference
    `|a.approx n - b.approx n|` is below `1 / (k + 1)`.

    This is the correct notion of equality in the Cauchy completion of
    TauRat and is strictly weaker than pointwise `TauRat.equiv` at every
    index (captured by `TauReal.equiv_of_pointwise` below).  Downstream
    callers that previously supplied a pointwise witness now route
    through that bridge. -/
def TauReal.equiv (a b : TauReal) : Prop :=
  ∃ modulus : Nat → Nat, ∀ k n : Nat,
    modulus k ≤ n →
    TauRat.lt ((a.approx n).sub (b.approx n)).abs (TauRat.ofNatRecip k)

-- ============================================================
-- POINTWISE → CAUCHY BRIDGE
-- ============================================================

/-- Pointwise equivalence is strictly stronger than Cauchy equivalence.

    The modulus is the constant zero — at every index the pointwise
    difference is already equiv to zero, hence strictly below any
    positive `1/(k+1)`.  This bridge wraps every existing pointwise
    witness (ring axioms, fromTauRat embedding, downstream callers)
    into a Cauchy-equiv proof. -/
theorem TauReal.equiv_of_pointwise {a b : TauReal}
    (h : ∀ n, TauRat.equiv (a.approx n) (b.approx n)) :
    TauReal.equiv a b := by
  refine ⟨fun _ => 0, fun k n _ => ?_⟩
  unfold TauRat.lt
  rw [TauRat.toRat_abs, toRat_sub]
  have h_eq : (a.approx n).toRat = (b.approx n).toRat :=
    (equiv_iff_toRat_eq _ _).mp (h n)
  rw [h_eq]
  simp
  exact TauRat.ofNatRecip_pos k

-- ============================================================
-- equiv IS AN EQUIVALENCE RELATION
-- ============================================================

/-- TauReal equivalence is reflexive (via the pointwise bridge). -/
theorem TauReal.equiv_refl (a : TauReal) : TauReal.equiv a a :=
  TauReal.equiv_of_pointwise (fun n => TauRat.equiv_refl _)

/-- TauReal equivalence is symmetric. -/
theorem TauReal.equiv_symm {a b : TauReal} (h : TauReal.equiv a b) :
    TauReal.equiv b a := by
  obtain ⟨modulus, hmod⟩ := h
  refine ⟨modulus, fun k n hn => ?_⟩
  have h_orig := hmod k n hn
  unfold TauRat.lt at h_orig ⊢
  rw [TauRat.toRat_abs, toRat_sub] at h_orig
  rw [TauRat.toRat_abs, toRat_sub]
  rw [show (b.approx n).toRat - (a.approx n).toRat =
         -((a.approx n).toRat - (b.approx n).toRat) from by ring, abs_neg]
  exact h_orig

/-- TauReal equivalence is transitive (triangle inequality on the modulus). -/
theorem TauReal.equiv_trans {a b c : TauReal}
    (hab : TauReal.equiv a b) (hbc : TauReal.equiv b c) :
    TauReal.equiv a c := by
  obtain ⟨μ₁, h₁⟩ := hab
  obtain ⟨μ₂, h₂⟩ := hbc
  -- Target tolerance `1/(k+1)` via halved tolerance at level `2k+1`.
  refine ⟨fun k => max (μ₁ (2 * k + 1)) (μ₂ (2 * k + 1)), fun k n hn => ?_⟩
  have hn₁ : μ₁ (2 * k + 1) ≤ n := le_of_max_le_left hn
  have hn₂ : μ₂ (2 * k + 1) ≤ n := le_of_max_le_right hn
  have h_ab := h₁ (2 * k + 1) n hn₁
  have h_bc := h₂ (2 * k + 1) n hn₂
  unfold TauRat.lt at h_ab h_bc ⊢
  rw [TauRat.toRat_abs, toRat_sub] at h_ab h_bc
  rw [TauRat.toRat_abs, toRat_sub]
  rw [TauRat.ofNatRecip_toRat] at h_ab h_bc ⊢
  have h_triangle :
      |(a.approx n).toRat - (c.approx n).toRat|
        ≤ |(a.approx n).toRat - (b.approx n).toRat|
        + |(b.approx n).toRat - (c.approx n).toRat| := by
    rw [show (a.approx n).toRat - (c.approx n).toRat =
           ((a.approx n).toRat - (b.approx n).toRat)
           + ((b.approx n).toRat - (c.approx n).toRat) from by ring]
    exact abs_add_le _ _
  have h_eq : (1 : Rat) / ((2 * k + 1 : Nat) + 1) + 1 / ((2 * k + 1 : Nat) + 1)
              = 1 / ((k : Rat) + 1) := by
    push_cast; field_simp; ring
  linarith [h_triangle, h_ab, h_bc, h_eq]

-- ============================================================
-- [I.P39] RING AXIOMS (UP TO equiv)
-- ============================================================

/-- Addition is commutative up to equiv. -/
theorem taureal_add_comm (a b : TauReal) :
    TauReal.equiv (TauReal.add a b) (TauReal.add b a) :=
  TauReal.equiv_of_pointwise (fun n => taurat_add_comm (a.approx n) (b.approx n))

/-- Addition is associative up to equiv. -/
theorem taureal_add_assoc (a b c : TauReal) :
    TauReal.equiv ((a.add b).add c) (a.add (b.add c)) :=
  TauReal.equiv_of_pointwise (fun n => taurat_add_assoc (a.approx n) (b.approx n) (c.approx n))

/-- Zero is a right identity for addition (up to equiv). -/
theorem taureal_add_zero (a : TauReal) :
    TauReal.equiv (a.add TauReal.zero) a :=
  TauReal.equiv_of_pointwise (fun n => taurat_add_zero (a.approx n))

/-- Zero is a left identity for addition (up to equiv). -/
theorem taureal_zero_add (a : TauReal) :
    TauReal.equiv (TauReal.zero.add a) a :=
  TauReal.equiv_of_pointwise (fun n => taurat_zero_add (a.approx n))

/-- Negation is a right inverse for addition (up to equiv). -/
theorem taureal_add_negate (a : TauReal) :
    TauReal.equiv (a.add a.negate) TauReal.zero :=
  TauReal.equiv_of_pointwise (fun n => taurat_add_negate (a.approx n))

/-- Negation is a left inverse for addition (up to equiv). -/
theorem taureal_negate_add (a : TauReal) :
    TauReal.equiv (a.negate.add a) TauReal.zero :=
  TauReal.equiv_of_pointwise (fun n => taurat_negate_add (a.approx n))

/-- Multiplication is commutative up to equiv. -/
theorem taureal_mul_comm (a b : TauReal) :
    TauReal.equiv (TauReal.mul a b) (TauReal.mul b a) :=
  TauReal.equiv_of_pointwise (fun n => taurat_mul_comm (a.approx n) (b.approx n))

/-- Multiplication is associative up to equiv. -/
theorem taureal_mul_assoc (a b c : TauReal) :
    TauReal.equiv ((a.mul b).mul c) (a.mul (b.mul c)) :=
  TauReal.equiv_of_pointwise (fun n => taurat_mul_assoc (a.approx n) (b.approx n) (c.approx n))

/-- One is a right identity for multiplication (up to equiv). -/
theorem taureal_mul_one (a : TauReal) :
    TauReal.equiv (a.mul TauReal.one) a :=
  TauReal.equiv_of_pointwise (fun n => taurat_mul_one (a.approx n))

/-- One is a left identity for multiplication (up to equiv). -/
theorem taureal_one_mul (a : TauReal) :
    TauReal.equiv (TauReal.one.mul a) a :=
  TauReal.equiv_of_pointwise (fun n => taurat_one_mul (a.approx n))

/-- Left distributivity: a * (b + c) = a*b + a*c (up to equiv). -/
theorem taureal_left_distrib (a b c : TauReal) :
    TauReal.equiv (a.mul (b.add c)) ((a.mul b).add (a.mul c)) :=
  TauReal.equiv_of_pointwise (fun n => taurat_left_distrib (a.approx n) (b.approx n) (c.approx n))

/-- Right distributivity: (a + b) * c = a*c + b*c (up to equiv). -/
theorem taureal_right_distrib (a b c : TauReal) :
    TauReal.equiv ((a.add b).mul c) ((a.mul c).add (b.mul c)) :=
  TauReal.equiv_of_pointwise (fun n => taurat_right_distrib (a.approx n) (b.approx n) (c.approx n))

/-- Multiplication by zero gives zero (up to equiv). -/
theorem taureal_zero_mul (a : TauReal) :
    TauReal.equiv (TauReal.zero.mul a) TauReal.zero :=
  TauReal.equiv_of_pointwise (fun n => taurat_zero_mul (a.approx n))

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
  TauReal.equiv_of_pointwise (fun _ => TauRat.equiv_refl _)

/-- The embedding from TauRat to TauReal preserves multiplication (up to equiv). -/
theorem fromTauRat_mul (a b : TauRat) :
    TauReal.equiv (TauReal.fromTauRat (a.mul b))
                  ((TauReal.fromTauRat a).mul (TauReal.fromTauRat b)) :=
  TauReal.equiv_of_pointwise (fun _ => TauRat.equiv_refl _)

-- ============================================================
-- [I.T42] ARCHIMEDEAN PROPERTY
-- ============================================================

/-- [I.T42] The Archimedean property: the natural number embedding
    into TauReal is unbounded.  The sequence `fromNat n` is strictly
    increasing (distinct naturals give non-equivalent TauReals).

    Under the Cauchy `equiv`, distinctness means the difference
    sequence does NOT converge to zero.  Since `fromNat n` is constant
    at `n`, the difference `|m - n|` is a fixed nonzero constant, and
    any small enough `1/(k+1)` tolerance witnesses non-convergence. -/
theorem taureal_archimedean_embedding :
    ∀ n m : TauIdx, n < m →
    ¬ TauReal.equiv (TauReal.fromNat m) (TauReal.fromNat n) := by
  intro n m hnm h_eq
  obtain ⟨μ, h⟩ := h_eq
  -- Pick tolerance level `k = 1` (tolerance `1/2`).  The difference
  -- `|m - n|` is a constant integer ≥ 1, so it never dips below `1/2`.
  have h1 := h 1 (μ 1) (_root_.le_refl _)
  have h_toRat_nat : ∀ k : TauIdx, (nat_to_taurat k).toRat = (k : Rat) := by
    intro k
    simp only [nat_to_taurat, int_to_taurat, nat_to_tauint, TauRat.toRat,
               TauInt.toInt, TauInt.fromNat]
    push_cast; ring
  unfold TauRat.lt at h1
  rw [TauRat.toRat_abs, toRat_sub, TauRat.ofNatRecip_toRat] at h1
  -- Constant-sequence `.approx (μ 1)` reduces definitionally to `nat_to_taurat _`.
  have h_approx_m : (TauReal.fromNat m).approx (μ 1) = nat_to_taurat m := rfl
  have h_approx_n : (TauReal.fromNat n).approx (μ 1) = nat_to_taurat n := rfl
  rw [h_approx_m, h_approx_n, h_toRat_nat, h_toRat_nat] at h1
  have hmn_rat : ((m : Rat) - n) ≥ 1 := by
    have : (n : Rat) + 1 ≤ m := by exact_mod_cast hnm
    linarith
  rw [abs_of_nonneg (by linarith : (0 : Rat) ≤ (m : Rat) - n)] at h1
  push_cast at h1
  linarith

-- ============================================================
-- SMOKE TESTS
-- ============================================================

private def real_half : TauReal := TauReal.fromTauRat ⟨⟨1, 0⟩, 2, by norm_num⟩
private def real_third : TauReal := TauReal.fromTauRat ⟨⟨1, 0⟩, 3, by norm_num⟩

#check TauReal.add real_half real_third
#check taureal_add_comm real_half real_third
#check taureal_ring_axioms
#check @TauReal.IsCauchy
#check @TauReal.equiv
#check @TauReal.equiv_of_pointwise
#check @TauReal.equiv_trans

end Tau.Boundary
