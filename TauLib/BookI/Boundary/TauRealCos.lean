import TauLib.BookI.Boundary.TauRealIotaTau
import TauLib.BookI.Boundary.TauRealAnalyticalHelpers
import TauLib.BookI.Boundary.TauRealSum
import TauLib.BookI.Boundary.TauRealExp
import TauLib.BookI.Boundary.TauRealSin
import Mathlib.Tactic.Ring
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity

/-!
# TauLib.BookI.Boundary.TauRealCos

**Wave Γ₇ Phase 3B — τ-native cos(x) at TauRat arguments.**

The cos Taylor series

$$ \cos(x) \;=\; \sum_{n=0}^\infty \frac{(-1)^n \, x^{2n}}{(2n)!}
   \;=\; 1 - \frac{x^2}{2!} + \frac{x^4}{4!} - \frac{x^6}{6!} + \cdots $$

paired into the all-positive form:

$$ \mathrm{cos\_pair}_k(x) \;=\; \frac{x^{4k}}{(4k)!} - \frac{x^{4k+2}}{(4k+2)!} $$

Same Cauchy-bound template instantiation as `TauRealSin`, with the
factorial growth bound `2^k ≤ (4k)!` (slightly tighter than the sin
case `2^k ≤ (4k+1)!`).

## Structural parallel to sin

The construction mirrors `TauRealSin.lean` verbatim:
- Paired-term via `.sub` of two factorial-divided pow terms.
- toRat bridge via field_simp + push_cast.
- Partial sum via TauRat.sum.
- Per-term magnitude bound via triangle inequality on the difference.
- Cauchy tail bound via factorial growth → geometric tail.
- TauReal.cos_of_rat with IsCauchy at modulus `λ k => k + 3`.

## Wave Γ₇ Phase plan

* **Phase 3A** ✓ — sin foundations + Cauchy + IsCauchy.
* **Phase 3B** (this commit) — cos foundations + Cauchy + IsCauchy.
* **Phase 3C (M3 breakthrough)** — sin/cos addition formula via
  exp-addition + i-structure decomposition.
* **Phase 3D-3F** — arctan inverse + addition formula + Machin equiv.

## Build state

* `sorry` count: 0
* `axiom` count: 0
* Imports: TauLib (TauRealIotaTau, TauRealAnalyticalHelpers,
  TauRealSum, TauRealExp for TauRat.pow, TauRealSin for the
  factorial-growth template) + Mathlib tactics-only.

## Phase 3B deliverables (this commit)

* `TauRat.cos_pair_term_first/second` + `cos_pair_term` —
  paired cos term construction.
* `cos_pair_term_rat` + `TauRat.cos_pair_term_toRat` — bridges.
* `TauRat.cos_partial` + `cos_partial_rat` + bridge.
* `cos_pair_term_rat_abs_bound` — per-term `≤ 2/(4k)!`.
* `Nat.factorial_4k_ge_two_pow_k` — factorial growth bound.
* `cos_pair_term_rat_abs_bound_geom` — geometric form `≤ 2/2^k`.
* `cos_partial_rat_cauchy_bound_exact/cauchy_bound` — exact + loose.
* `TauReal.cos_of_rat` + `TauReal.cos_of_rat_isCauchy` (modulus `k+3`).
-/

set_option autoImplicit false

namespace Tau.Boundary

open Tau.Denotation

-- ============================================================
-- PART 1: COS PAIRED TERM CONSTRUCTION (TauRat level)
-- ============================================================

/-- The first sub-fraction of the k-th cos paired term:
    `x^(4k) / (4k)!`. -/
def TauRat.cos_pair_term_first (x : TauRat) (k : Nat) : TauRat :=
  { num    := (TauRat.pow x (4*k)).num
    den    := (TauRat.pow x (4*k)).den * Nat.factorial (4*k)
    den_pos := Nat.mul_pos (TauRat.pow x (4*k)).den_pos
                            (Nat.factorial_pos (4*k)) }

/-- The second sub-fraction of the k-th cos paired term:
    `x^(4k+2) / (4k+2)!`. -/
def TauRat.cos_pair_term_second (x : TauRat) (k : Nat) : TauRat :=
  { num    := (TauRat.pow x (4*k+2)).num
    den    := (TauRat.pow x (4*k+2)).den * Nat.factorial (4*k+2)
    den_pos := Nat.mul_pos (TauRat.pow x (4*k+2)).den_pos
                            (Nat.factorial_pos (4*k+2)) }

/-- The k-th cos paired term as a TauRat:
    `pair_k(x) = x^(4k)/(4k)! − x^(4k+2)/(4k+2)!`. -/
def TauRat.cos_pair_term (x : TauRat) (k : Nat) : TauRat :=
  (TauRat.cos_pair_term_first x k).sub (TauRat.cos_pair_term_second x k)

-- ============================================================
-- PART 2: TOR-LEVEL BRIDGE
-- ============================================================

/-- The k-th cos paired term at the Rat level. -/
def cos_pair_term_rat (x : Rat) (k : Nat) : Rat :=
  x^(4*k) / (Nat.factorial (4*k) : Rat) -
  x^(4*k+2) / (Nat.factorial (4*k+2) : Rat)

private theorem cos_pair_term_first_toRat (x : TauRat) (k : Nat) :
    (TauRat.cos_pair_term_first x k).toRat
      = (TauRat.pow x (4*k)).toRat / (Nat.factorial (4*k) : Rat) := by
  unfold TauRat.cos_pair_term_first TauRat.toRat TauInt.toInt
  have h_fac : (0 : Rat) < (Nat.factorial (4*k) : Rat) := by
    have := Nat.factorial_pos (4*k); exact_mod_cast this
  push_cast
  field_simp

private theorem cos_pair_term_second_toRat (x : TauRat) (k : Nat) :
    (TauRat.cos_pair_term_second x k).toRat
      = (TauRat.pow x (4*k+2)).toRat / (Nat.factorial (4*k+2) : Rat) := by
  unfold TauRat.cos_pair_term_second TauRat.toRat TauInt.toInt
  have h_fac : (0 : Rat) < (Nat.factorial (4*k+2) : Rat) := by
    have := Nat.factorial_pos (4*k+2); exact_mod_cast this
  push_cast
  field_simp

theorem TauRat.cos_pair_term_toRat (x : TauRat) (k : Nat) :
    (TauRat.cos_pair_term x k).toRat = cos_pair_term_rat x.toRat k := by
  unfold TauRat.cos_pair_term cos_pair_term_rat
  rw [toRat_sub, cos_pair_term_first_toRat, cos_pair_term_second_toRat,
      TauRat.pow_toRat, TauRat.pow_toRat]

-- ============================================================
-- PART 3: COS PARTIAL SUM
-- ============================================================

def TauRat.cos_partial (x : TauRat) (n : Nat) : TauRat :=
  TauRat.sum (TauRat.cos_pair_term x) n

@[simp] theorem TauRat.cos_partial_zero (x : TauRat) :
    TauRat.cos_partial x 0 = TauRat.zero := rfl

@[simp] theorem TauRat.cos_partial_succ (x : TauRat) (n : Nat) :
    TauRat.cos_partial x (n + 1) =
      (TauRat.cos_partial x n).add (TauRat.cos_pair_term x n) := rfl

def cos_partial_rat (x : Rat) : Nat → Rat
  | 0 => 0
  | n + 1 => cos_partial_rat x n + cos_pair_term_rat x n

@[simp] theorem cos_partial_rat_zero (x : Rat) : cos_partial_rat x 0 = 0 := rfl

@[simp] theorem cos_partial_rat_succ (x : Rat) (n : Nat) :
    cos_partial_rat x (n + 1) = cos_partial_rat x n + cos_pair_term_rat x n := rfl

theorem TauRat.cos_partial_toRat (x : TauRat) (n : Nat) :
    (TauRat.cos_partial x n).toRat = cos_partial_rat x.toRat n := by
  induction n with
  | zero => simp [TauRat.cos_partial_zero, cos_partial_rat_zero, toRat_zero]
  | succ n ih =>
    rw [TauRat.cos_partial_succ, toRat_add, ih, TauRat.cos_pair_term_toRat,
        cos_partial_rat_succ]

-- ============================================================
-- PART 4: PER-TERM MAGNITUDE BOUND
-- ============================================================

private theorem factorial_4k_le_4k2 (k : Nat) :
    Nat.factorial (4*k) ≤ Nat.factorial (4*k+2) := by
  apply Nat.factorial_le; omega

/-- **Per-term magnitude bound**: `|cos_pair_term_rat x k| ≤ 2/(4k)!`
    for `|x| ≤ 1`. -/
theorem cos_pair_term_rat_abs_bound (x : Rat) (hx : |x| ≤ 1) (k : Nat) :
    |cos_pair_term_rat x k| ≤ 2 / (Nat.factorial (4*k) : Rat) := by
  unfold cos_pair_term_rat
  have h_fac_4k_pos : (0 : Rat) < (Nat.factorial (4*k) : Rat) := by
    have := Nat.factorial_pos (4*k); exact_mod_cast this
  have h_fac_4k2_pos : (0 : Rat) < (Nat.factorial (4*k+2) : Rat) := by
    have := Nat.factorial_pos (4*k+2); exact_mod_cast this
  have h_fac_le : (Nat.factorial (4*k) : Rat) ≤ (Nat.factorial (4*k+2) : Rat) := by
    have := factorial_4k_le_4k2 k; exact_mod_cast this
  have h_x_pow_4k : |x^(4*k)| ≤ 1 := by
    rw [abs_pow]; exact pow_le_one₀ (abs_nonneg _) hx
  have h_x_pow_4k2 : |x^(4*k+2)| ≤ 1 := by
    rw [abs_pow]; exact pow_le_one₀ (abs_nonneg _) hx
  have h_first_abs : |x^(4*k) / (Nat.factorial (4*k) : Rat)|
                      ≤ 1 / (Nat.factorial (4*k) : Rat) := by
    rw [abs_div, abs_of_pos h_fac_4k_pos]
    rw [div_le_div_iff₀ h_fac_4k_pos h_fac_4k_pos]
    nlinarith
  have h_second_abs : |x^(4*k+2) / (Nat.factorial (4*k+2) : Rat)|
                      ≤ 1 / (Nat.factorial (4*k) : Rat) := by
    rw [abs_div, abs_of_pos h_fac_4k2_pos]
    rw [div_le_div_iff₀ h_fac_4k2_pos h_fac_4k_pos]
    nlinarith
  have h_tri : |x^(4*k) / (Nat.factorial (4*k) : Rat) -
                x^(4*k+2) / (Nat.factorial (4*k+2) : Rat)|
                ≤ |x^(4*k) / (Nat.factorial (4*k) : Rat)| +
                  |x^(4*k+2) / (Nat.factorial (4*k+2) : Rat)| := by
    have := abs_sub (x^(4*k) / (Nat.factorial (4*k) : Rat))
                    (x^(4*k+2) / (Nat.factorial (4*k+2) : Rat))
    linarith
  have h_sum : 1 / (Nat.factorial (4*k) : Rat) +
               1 / (Nat.factorial (4*k) : Rat)
               = 2 / (Nat.factorial (4*k) : Rat) := by ring
  linarith

-- ============================================================
-- PART 5: FACTORIAL GROWTH + GEOMETRIC PER-TERM BOUND
-- ============================================================

/-- **Factorial growth bound**: `2^k ≤ (4k)!` for all `k ≥ 0`.

    Proof by induction (parallel to `Nat.factorial_4k1_ge_two_pow_k`):
    * `k = 0`: `2^0 = 1 = 0!` ✓.
    * `k → k+1`: `(4(k+1))! = (4k+4)·(4k+3)·(4k+2)·(4k+1)·(4k)!`.
      By IH `(4k)! ≥ 2^k`, and the four-factor product
      is `≥ 4·3·2·1 = 24 ≥ 2`. So `(4(k+1))! ≥ 2·2^k = 2^(k+1)`. ✓ -/
theorem Nat.factorial_4k_ge_two_pow_k (k : Nat) :
    2^k ≤ (4*k).factorial := by
  induction k with
  | zero => simp [Nat.factorial]
  | succ k ih =>
    have h_index : 4*(k+1) = 4*k+4 := by ring
    rw [h_index]
    -- (4k+4)! = (4k+4) * (4k+3) * (4k+2) * (4k+1) * (4k)!
    have e0 : (4*k+4).factorial = (4*k+4) * (4*k+3).factorial := by
      rw [show (4*k+4 : Nat) = (4*k+3) + 1 from by omega]
      exact Nat.factorial_succ _
    have e1 : (4*k+3).factorial = (4*k+3) * (4*k+2).factorial := by
      rw [show (4*k+3 : Nat) = (4*k+2) + 1 from by omega]
      exact Nat.factorial_succ _
    have e2 : (4*k+2).factorial = (4*k+2) * (4*k+1).factorial := by
      rw [show (4*k+2 : Nat) = (4*k+1) + 1 from by omega]
      exact Nat.factorial_succ _
    have e3 : (4*k+1).factorial = (4*k+1) * (4*k).factorial := by
      rw [show (4*k+1 : Nat) = (4*k) + 1 from by omega]
      exact Nat.factorial_succ _
    have h_unfold : (4*k+4).factorial =
        ((4*k+4) * (4*k+3) * (4*k+2) * (4*k+1)) * (4*k).factorial := by
      rw [e0, e1, e2, e3]; ring
    rw [h_unfold]
    -- Four-factor product is ≥ 2 (in fact ≥ 4·3·2·1 = 24).
    have h_factor_ge_two : 2 ≤ (4*k+4) * (4*k+3) * (4*k+2) * (4*k+1) := by
      have h_1 : 2 ≤ 4*k+2 := by omega
      have h_pos : 1 ≤ (4*k+4) * (4*k+3) := by
        have : 0 < (4*k+4) * (4*k+3) := by positivity
        omega
      have h_pos2 : 1 ≤ 4*k+1 := by omega
      calc 2 = 1 * 2 * 1 := by ring
        _ ≤ (4*k+4) * (4*k+3) * (4*k+2) * (4*k+1) := by
            apply Nat.mul_le_mul (Nat.mul_le_mul h_pos h_1) h_pos2
    have h_pow_succ : 2^(k+1) = 2 * 2^k := by ring
    calc 2^(k+1)
        = 2 * 2^k := h_pow_succ
      _ ≤ 2 * (4*k).factorial := Nat.mul_le_mul_left 2 ih
      _ ≤ ((4*k+4) * (4*k+3) * (4*k+2) * (4*k+1)) * (4*k).factorial :=
          Nat.mul_le_mul_right _ h_factor_ge_two

/-- **Geometric per-term bound**: `|cos_pair_term_rat x k| ≤ 2/2^k` for `|x| ≤ 1`. -/
theorem cos_pair_term_rat_abs_bound_geom (x : Rat) (hx : |x| ≤ 1) (k : Nat) :
    |cos_pair_term_rat x k| ≤ 2 / (2 : Rat)^k := by
  have h_factorial := cos_pair_term_rat_abs_bound x hx k
  have h_fac_ge : (2 : Rat)^k ≤ (Nat.factorial (4*k) : Rat) := by
    have := Nat.factorial_4k_ge_two_pow_k k
    have h_cast : ((2^k : Nat) : Rat) = (2 : Rat)^k := by push_cast; ring
    have h_cast_le : ((2^k : Nat) : Rat) ≤ ((Nat.factorial (4*k) : Nat) : Rat) :=
      by exact_mod_cast this
    rw [h_cast] at h_cast_le
    exact h_cast_le
  have h_2k_pos : (0 : Rat) < (2 : Rat)^k := by positivity
  have h_fac_pos : (0 : Rat) < (Nat.factorial (4*k) : Rat) := by
    have := Nat.factorial_pos (4*k); exact_mod_cast this
  have h_bound : (2 : Rat) / (Nat.factorial (4*k) : Rat) ≤ 2 / (2 : Rat)^k := by
    rw [div_le_div_iff₀ h_fac_pos h_2k_pos]
    nlinarith
  linarith

-- ============================================================
-- PART 6: CAUCHY TAIL BOUND
-- ============================================================

theorem cos_partial_rat_cauchy_bound_exact (x : Rat) (hx : |x| ≤ 1)
    (m n : Nat) (hnm : n ≤ m) :
    |cos_partial_rat x m - cos_partial_rat x n|
      ≤ 4 / (2 : Rat)^n - 4 / (2 : Rat)^m := by
  induction m, hnm using Nat.le_induction with
  | base => simp
  | succ m hnm ih =>
    rw [cos_partial_rat_succ]
    have h_diff : cos_partial_rat x m + cos_pair_term_rat x m - cos_partial_rat x n
                    = (cos_partial_rat x m - cos_partial_rat x n) + cos_pair_term_rat x m := by ring
    rw [h_diff]
    have h_tri : |(cos_partial_rat x m - cos_partial_rat x n) + cos_pair_term_rat x m|
                  ≤ |cos_partial_rat x m - cos_partial_rat x n|
                    + |cos_pair_term_rat x m| := abs_add_le _ _
    have h_term := cos_pair_term_rat_abs_bound_geom x hx m
    have h_2_m_pos : (0 : Rat) < (2 : Rat)^m := by positivity
    have h_pow_succ : (2 : Rat)^(m+1) = 2 * (2 : Rat)^m := by rw [pow_succ]; ring
    have h_algebra :
        4 / (2 : Rat)^n - 4 / (2 : Rat)^m + 2 / (2 : Rat)^m
          = 4 / (2 : Rat)^n - 4 / (2 : Rat)^(m+1) := by
      rw [h_pow_succ]
      have h_2_n_pos : (0 : Rat) < (2 : Rat)^n := by positivity
      field_simp; ring
    linarith

theorem cos_partial_rat_cauchy_bound (x : Rat) (hx : |x| ≤ 1)
    (m n : Nat) (hnm : n ≤ m) :
    |cos_partial_rat x m - cos_partial_rat x n| ≤ 4 / (2 : Rat)^n := by
  have h_exact := cos_partial_rat_cauchy_bound_exact x hx m n hnm
  have h_subtract_nn : (0 : Rat) ≤ 4 / (2 : Rat)^m := by
    apply div_nonneg (by norm_num : (0 : Rat) ≤ 4)
    positivity
  linarith

-- ============================================================
-- PART 7: TauReal.cos_of_rat + IsCauchy
-- ============================================================

/-- **[I.D-Cos-of-Rat]** The τ-native cos at a fixed TauRat argument. -/
def TauReal.cos_of_rat (x : TauRat) : TauReal :=
  ⟨TauRat.cos_partial x⟩

@[simp] theorem TauReal.cos_of_rat_approx (x : TauRat) (n : Nat) :
    (TauReal.cos_of_rat x).approx n = TauRat.cos_partial x n := rfl

/-- **[I.T-Cos-of-Rat-IsCauchy]** `TauReal.cos_of_rat x` is Cauchy
    under `|x.toRat| ≤ 1` with explicit modulus `λ k => k + 3`. -/
theorem TauReal.cos_of_rat_isCauchy (x : TauRat) (hx : |x.toRat| ≤ 1) :
    (TauReal.cos_of_rat x).IsCauchy := by
  refine ⟨fun k => k + 3, ?_⟩
  intro k m n hm hn
  change k + 3 ≤ m at hm
  change k + 3 ≤ n at hn
  unfold TauRat.lt
  rw [TauRat.toRat_abs, toRat_sub, TauRat.ofNatRecip_toRat]
  show |(TauRat.cos_partial x m).toRat - (TauRat.cos_partial x n).toRat|
         < 1 / ((k : Rat) + 1)
  rw [TauRat.cos_partial_toRat, TauRat.cos_partial_toRat]
  by_cases h_le : n ≤ m
  · have h_bound := cos_partial_rat_cauchy_bound x.toRat hx m n h_le
    have h_four_lt := Rat.four_div_two_pow_lt_recip k n hn
    linarith
  · push_neg at h_le
    have h_m_le_n : m ≤ n := Nat.le_of_lt h_le
    have h_swap_abs :
        |cos_partial_rat x.toRat m - cos_partial_rat x.toRat n|
          = |cos_partial_rat x.toRat n - cos_partial_rat x.toRat m| := by
      rw [show cos_partial_rat x.toRat m - cos_partial_rat x.toRat n
            = -(cos_partial_rat x.toRat n - cos_partial_rat x.toRat m) from by ring, abs_neg]
    rw [h_swap_abs]
    have h_bound := cos_partial_rat_cauchy_bound x.toRat hx n m h_m_le_n
    have h_four_lt := Rat.four_div_two_pow_lt_recip k m hm
    linarith

end Tau.Boundary
