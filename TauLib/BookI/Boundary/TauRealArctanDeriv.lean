import TauLib.BookI.Boundary.TauRealArctan
import TauLib.BookI.Boundary.TauRealPowerSeriesDiff
import TauLib.BookI.Boundary.TauRealInv
import TauLib.BookI.Boundary.TauRealSum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity

/-!
# TauLib.BookI.Boundary.TauRealArctanDeriv

**Wave Γ₈ Phase 2.6.B.2.β.4.9 — Module 3**: the arctan derivative for
the τ-canon programme.

## Goal

Prove:

    IsDerivAt arctan_of_rat a (TauReal.inv (1 + a²))

for `2 · |a.toRat| ≤ 1`, where the right-hand side is the TauReal
representation of `1/(1+a²)`.

## Wave 1 — formal derivative series

This wave ships the **formal-derivative series** structure: the pair
terms `x^(4k) − x^(4k+2)` of the term-by-term differentiated arctan
series, their partial sums, the closed-form geometric identity, and
Cauchy bounds.

The series partial sum has the **telescoping geometric identity**

    P'_N(x) · (1 + x²) = 1 − x^(4N)

(true at Rat level for any x, any N). Combined with `|x|^(4N) → 0`
for `|x| < 1`, this gives the limit `P'_∞(x) = 1/(1+x²)` algebraically.

This identity is the **load-bearing tool** that lets Module 3 close
the IsDerivAt theorem without infinite-series Taylor-remainder arguments
— the formal derivative has a CLOSED form, making the convergence
geometric rather than analytic.

## Architectural context

Module 2's `IsDerivAt_pow_nat` (Wave 4) provides the differentiation
machinery for each polynomial term. Combined with Module 1's linearity
rules (sum, const_mul, sub), the arctan partial sum's derivative is
computable term-by-term.

The entire construction stays within the τ-canon-native
stabilization-at-depth paradigm — the closed-form geometric identity
is a finite Rat-level computation, not an infinite-series limit.
-/

set_option autoImplicit false

namespace Tau.Boundary

open Tau.Denotation

-- ============================================================
-- PART 1: FORMAL DERIVATIVE PAIR TERM
-- ============================================================

/-- **Formal derivative pair term** at TauRat level:

    `arctan_deriv_pair_term x k = x^(4k) − x^(4k+2)`.

    This is the term-by-term derivative of `arctan_pair_term`:

      arctan_pair_term x k     = x^(4k+1)/(4k+1) − x^(4k+3)/(4k+3)
      arctan_deriv_pair_term x k = x^(4k)         − x^(4k+2). -/
def TauRat.arctan_deriv_pair_term (x : TauRat) (k : Nat) : TauRat :=
  (x.pow_nat (4*k)).sub (x.pow_nat (4*k+2))

/-- Rat-level companion. -/
def arctan_deriv_pair_term_rat (x : Rat) (k : Nat) : Rat :=
  x^(4*k) - x^(4*k+2)

/-- Bridge: TauRat construction = Rat companion under `.toRat`. -/
theorem TauRat.arctan_deriv_pair_term_toRat (x : TauRat) (k : Nat) :
    (TauRat.arctan_deriv_pair_term x k).toRat = arctan_deriv_pair_term_rat x.toRat k := by
  unfold TauRat.arctan_deriv_pair_term arctan_deriv_pair_term_rat
  rw [toRat_sub, TauRat.pow_nat_toRat, TauRat.pow_nat_toRat]

-- ============================================================
-- PART 2: FORMAL DERIVATIVE PARTIAL SUM
-- ============================================================

/-- **Formal derivative partial sum** at TauRat level:

    `arctan_deriv_partial x n = Σ_{k=0}^{n-1} (x^(4k) − x^(4k+2))`. -/
def TauRat.arctan_deriv_partial (x : TauRat) (n : Nat) : TauRat :=
  TauRat.sum (fun k => TauRat.arctan_deriv_pair_term x k) n

/-- Rat-level companion partial sum. -/
def arctan_deriv_partial_rat (x : Rat) : Nat → Rat
  | 0     => 0
  | n + 1 => arctan_deriv_partial_rat x n + arctan_deriv_pair_term_rat x n

@[simp] theorem TauRat.arctan_deriv_partial_zero (x : TauRat) :
    TauRat.arctan_deriv_partial x 0 = TauRat.zero := rfl

@[simp] theorem TauRat.arctan_deriv_partial_succ (x : TauRat) (n : Nat) :
    TauRat.arctan_deriv_partial x (n + 1) =
      (TauRat.arctan_deriv_partial x n).add (TauRat.arctan_deriv_pair_term x n) := rfl

@[simp] theorem arctan_deriv_partial_rat_zero (x : Rat) :
    arctan_deriv_partial_rat x 0 = 0 := rfl

@[simp] theorem arctan_deriv_partial_rat_succ (x : Rat) (n : Nat) :
    arctan_deriv_partial_rat x (n+1) =
      arctan_deriv_partial_rat x n + arctan_deriv_pair_term_rat x n := rfl

/-- Bridge for partial sums. -/
theorem TauRat.arctan_deriv_partial_toRat (x : TauRat) (n : Nat) :
    (TauRat.arctan_deriv_partial x n).toRat = arctan_deriv_partial_rat x.toRat n := by
  induction n with
  | zero =>
    simp [TauRat.arctan_deriv_partial_zero, arctan_deriv_partial_rat_zero, toRat_zero]
  | succ n ih =>
    rw [TauRat.arctan_deriv_partial_succ, toRat_add, ih,
        TauRat.arctan_deriv_pair_term_toRat, arctan_deriv_partial_rat_succ]

-- ============================================================
-- PART 3: GEOMETRIC IDENTITY (LOAD-BEARING)
-- ============================================================

/-- **The closed-form geometric identity** at Rat level:

      arctan_deriv_partial_rat x n · (1 + x²) = 1 − x^(4n)

    Proof by induction on `n`, using the telescoping structure:

      (x^(4k) − x^(4k+2)) · (1 + x²) = x^(4k) − x^(4k+4)

    so the sum telescopes to `1 − x^(4n)`.

    This identity is the **load-bearing tool** for Module 3: it converts
    the infinite-series limit `lim arctan_deriv_partial_rat x n = 1/(1+x²)`
    into a finite Rat-level algebraic computation, since the partial sum
    has a closed form. -/
theorem arctan_deriv_partial_rat_geometric_identity (x : Rat) (n : Nat) :
    arctan_deriv_partial_rat x n * (1 + x^2) = 1 - x^(4*n) := by
  induction n with
  | zero =>
    simp [arctan_deriv_partial_rat_zero]
  | succ n ih =>
    rw [arctan_deriv_partial_rat_succ]
    rw [add_mul, ih]
    unfold arctan_deriv_pair_term_rat
    -- Goal: 1 - x^(4n) + (x^(4n) - x^(4n+2)) * (1 + x^2) = 1 - x^(4(n+1))
    have h_step : (x^(4*n) - x^(4*n+2)) * (1 + x^2)
                  = x^(4*n) - x^(4*n+4) := by
      have h1 : x^(4*n+2) = x^(4*n) * x^2 := by
        rw [show 4*n+2 = 4*n + 2 from rfl, pow_add]
      have h2 : x^(4*n+4) = x^(4*n) * x^4 := by
        rw [show 4*n+4 = 4*n + 4 from rfl, pow_add]
      rw [h1, h2]
      ring
    rw [h_step]
    have h_4_succ : 4 * (n + 1) = 4 * n + 4 := by ring
    rw [h_4_succ]
    ring

-- ============================================================
-- PART 4: PER-TERM BOUND
-- ============================================================

/-- **Per-term bound** for the formal derivative series:

    For `|x| ≤ 1/2`, `|arctan_deriv_pair_term_rat x k| ≤ 2/2^(4k)`.

    Proof: triangle inequality on `|x^(4k)| + |x^(4k+2)|`, each
    bounded by `|x|^(4k) ≤ (1/2)^(4k) = 1/2^(4k)`. -/
theorem arctan_deriv_pair_term_rat_abs_bound_geom
    (x : Rat) (hx : 2 * |x| ≤ 1) (k : Nat) :
    |arctan_deriv_pair_term_rat x k| ≤ 2 / (2 : Rat)^(4*k) := by
  unfold arctan_deriv_pair_term_rat
  have h_abs_x_le_half : |x| ≤ 1/2 := by linarith
  have h_abs_x_nn : (0 : Rat) ≤ |x| := abs_nonneg _
  -- Key bounds: |x|^(4k) ≤ (1/2)^(4k) = 1/2^(4k), |x|^(4k+2) ≤ 1/2^(4k+2) ≤ 1/2^(4k)
  have h_pow_4k : |x|^(4*k) ≤ (1/2 : Rat)^(4*k) := by
    apply pow_le_pow_left₀ h_abs_x_nn h_abs_x_le_half
  have h_pow_4k_eq : (1/2 : Rat)^(4*k) = 1 / (2 : Rat)^(4*k) := by
    rw [div_pow, one_pow]
  have h_pow_4k2 : |x|^(4*k+2) ≤ (1/2 : Rat)^(4*k+2) := by
    apply pow_le_pow_left₀ h_abs_x_nn h_abs_x_le_half
  have h_pow_4k2_le_4k : (1/2 : Rat)^(4*k+2) ≤ (1/2 : Rat)^(4*k) :=
    pow_le_pow_of_le_one (by norm_num : (0 : Rat) ≤ 1/2)
                         (by norm_num : (1/2 : Rat) ≤ 1)
                         (by omega : 4*k ≤ 4*k+2)
  -- Triangle: |x^(4k) - x^(4k+2)| ≤ |x^(4k)| + |x^(4k+2)| ≤ 2 · (1/2)^(4k) = 2/2^(4k)
  calc |x^(4*k) - x^(4*k+2)|
      ≤ |x^(4*k)| + |x^(4*k+2)| := abs_sub _ _
    _ = |x|^(4*k) + |x|^(4*k+2) := by rw [abs_pow, abs_pow]
    _ ≤ (1/2 : Rat)^(4*k) + (1/2 : Rat)^(4*k) := by
        linarith [h_pow_4k, h_pow_4k2, h_pow_4k2_le_4k]
    _ = 2 * (1/2 : Rat)^(4*k) := by ring
    _ = 2 / (2 : Rat)^(4*k) := by rw [h_pow_4k_eq]; ring

-- ============================================================
-- PART 5: CAUCHY BOUND (via closed-form geometric identity)
-- ============================================================

/-- **Cauchy bound** for the formal derivative partial sum, via the
    closed-form geometric identity.

    For `|x| ≤ 1/2` and `n ≤ m`,

      |arctan_deriv_partial_rat x m − arctan_deriv_partial_rat x n|
        ≤ 4 / 2^n   (loose bound; tight bound would be 2 · |x|^(4n)/(1+x²))

    Proof strategy: use the geometric identity to express each partial
    sum as `(1 − x^(4n))/(1+x²)`, then the difference is
    `(x^(4n) − x^(4m))/(1+x²)`, bounded by `|x|^(4n) + |x|^(4m)` divided
    by `(1+x²)` ≥ 1 for any x, giving ≤ 2·|x|^(4n) ≤ 2/2^(4n) ≤ 4/2^n. -/
theorem arctan_deriv_partial_rat_cauchy_bound
    (x : Rat) (hx : 2 * |x| ≤ 1) (m n : Nat) (hmn : n ≤ m) :
    |arctan_deriv_partial_rat x m - arctan_deriv_partial_rat x n|
      ≤ 4 / (2 : Rat)^n := by
  -- Use geometric identity: P_m · (1+x²) = 1 - x^(4m), P_n · (1+x²) = 1 - x^(4n)
  -- So (P_m - P_n) · (1+x²) = (1 - x^(4m)) - (1 - x^(4n)) = x^(4n) - x^(4m)
  -- Hence P_m - P_n = (x^(4n) - x^(4m)) / (1 + x²)
  have h_pos_1px2 : (0 : Rat) < 1 + x^2 := by positivity
  have h_id_m := arctan_deriv_partial_rat_geometric_identity x m
  have h_id_n := arctan_deriv_partial_rat_geometric_identity x n
  -- Compute difference: P_m - P_n
  have h_diff_id :
      (arctan_deriv_partial_rat x m - arctan_deriv_partial_rat x n) * (1 + x^2)
        = x^(4*n) - x^(4*m) := by
    have : arctan_deriv_partial_rat x m * (1 + x^2) -
           arctan_deriv_partial_rat x n * (1 + x^2)
         = (1 - x^(4*m)) - (1 - x^(4*n)) := by
      rw [h_id_m, h_id_n]
    linarith [this]
  -- |P_m - P_n| = |x^(4n) - x^(4m)| / (1 + x²)
  have h_div_eq :
      arctan_deriv_partial_rat x m - arctan_deriv_partial_rat x n
        = (x^(4*n) - x^(4*m)) / (1 + x^2) := by
    have h_ne : (1 + x^2) ≠ 0 := ne_of_gt h_pos_1px2
    field_simp
    linarith [h_diff_id]
  rw [h_div_eq]
  rw [abs_div]
  -- |x^(4n) - x^(4m)| ≤ |x|^(4n) + |x|^(4m) ≤ 2 · (1/2)^(4n)
  have h_abs_x_le_half : |x| ≤ 1/2 := by linarith
  have h_abs_x_nn : (0 : Rat) ≤ |x| := abs_nonneg _
  have h_x4n : |x|^(4*n) ≤ (1/2 : Rat)^(4*n) :=
    pow_le_pow_left₀ h_abs_x_nn h_abs_x_le_half _
  have h_x4m : |x|^(4*m) ≤ (1/2 : Rat)^(4*m) :=
    pow_le_pow_left₀ h_abs_x_nn h_abs_x_le_half _
  have h_4m_4n : (1/2 : Rat)^(4*m) ≤ (1/2 : Rat)^(4*n) :=
    pow_le_pow_of_le_one (by norm_num : (0 : Rat) ≤ 1/2)
                         (by norm_num : (1/2 : Rat) ≤ 1)
                         (by omega : 4*n ≤ 4*m)
  have h_num :
      |x^(4*n) - x^(4*m)| ≤ 2 * (1/2 : Rat)^(4*n) := by
    calc |x^(4*n) - x^(4*m)|
        ≤ |x^(4*n)| + |x^(4*m)| := abs_sub _ _
      _ = |x|^(4*n) + |x|^(4*m) := by rw [abs_pow, abs_pow]
      _ ≤ (1/2 : Rat)^(4*n) + (1/2 : Rat)^(4*n) := by linarith
      _ = 2 * (1/2 : Rat)^(4*n) := by ring
  -- |1 + x²| = 1 + x² ≥ 1 ≥ (something positive)
  have h_abs_denom : |1 + x^2| = 1 + x^2 := abs_of_pos h_pos_1px2
  have h_denom_ge_one : (1 : Rat) ≤ 1 + x^2 := by
    have h_sq_nn : (0 : Rat) ≤ x^2 := sq_nonneg _
    linarith
  rw [h_abs_denom]
  -- |x^(4n) - x^(4m)| / (1+x²) ≤ 2·(1/2)^(4n) / 1 = 2·(1/2)^(4n)
  have h_div_le : |x^(4*n) - x^(4*m)| / (1 + x^2) ≤ 2 * (1/2 : Rat)^(4*n) := by
    have h_div_step : |x^(4*n) - x^(4*m)| / (1 + x^2) ≤ |x^(4*n) - x^(4*m)| / 1 := by
      apply div_le_div_of_nonneg_left
        (_root_.abs_nonneg _) (by norm_num : (0 : Rat) < 1) h_denom_ge_one
    rw [div_one] at h_div_step
    linarith
  -- 2·(1/2)^(4n) = 2/2^(4n) ≤ 4/2^n (since 2^(4n) ≥ 2^n for n ≥ 0... wait, 4/2^n vs 2/2^(4n))
  -- 2/2^(4n) ≤ 4/2^n iff 2 · 2^n ≤ 4 · 2^(4n) iff 2^(n+1) ≤ 2^(4n+2)
  -- For n ≥ 0: n + 1 ≤ 4n + 2 iff 0 ≤ 3n + 1, true. So 2^(n+1) ≤ 2^(4n+2). ✓
  have h_final : 2 * (1/2 : Rat)^(4*n) ≤ 4 / (2 : Rat)^n := by
    rw [div_pow, one_pow]
    -- 2 / 2^(4n) ≤ 4 / 2^n
    have h_pow_n_pos : (0 : Rat) < (2 : Rat)^n := by positivity
    have h_pow_4n_pos : (0 : Rat) < (2 : Rat)^(4*n) := by positivity
    rw [show (2 : Rat) * (1 / 2^(4*n)) = 2 / 2^(4*n) from by field_simp]
    rw [div_le_div_iff₀ h_pow_4n_pos h_pow_n_pos]
    -- 2 · 2^n ≤ 4 · 2^(4n)
    have h_pow_le : (2 : Rat)^n ≤ (2 : Rat)^(4*n) := by
      apply pow_le_pow_right₀ (by norm_num : (1 : Rat) ≤ 2)
      omega
    linarith
  linarith

-- ============================================================
-- PART 6: TauReal-LEVEL FORMAL DERIVATIVE SEQUENCE
-- ============================================================

/-- **TauReal-level formal derivative partial-sum sequence**:
    `⟨n ↦ arctan_deriv_partial x n⟩`.

    For `|x| ≤ 1/2`, this is Cauchy with modulus `λ k => k + 3`. -/
def TauReal.arctan_deriv_partial_seq (x : TauRat) : TauReal :=
  ⟨TauRat.arctan_deriv_partial x⟩

@[simp] theorem TauReal.arctan_deriv_partial_seq_approx (x : TauRat) (n : Nat) :
    (TauReal.arctan_deriv_partial_seq x).approx n = TauRat.arctan_deriv_partial x n := rfl

/-- **Cauchy property** for `arctan_deriv_partial_seq` when `|x| ≤ 1/2`:
    modulus `λ k => k + 3`. -/
theorem TauReal.arctan_deriv_partial_seq_isCauchy
    (x : TauRat) (hx : 2 * |x.toRat| ≤ 1) :
    (TauReal.arctan_deriv_partial_seq x).IsCauchy := by
  refine ⟨fun k => k + 3, ?_⟩
  intro k m n hm hn
  change k + 3 ≤ m at hm
  change k + 3 ≤ n at hn
  unfold TauRat.lt
  rw [TauRat.toRat_abs, toRat_sub, TauRat.ofNatRecip_toRat]
  show |((TauRat.arctan_deriv_partial x m).toRat -
         (TauRat.arctan_deriv_partial x n).toRat)| < 1 / ((k : Rat) + 1)
  rw [TauRat.arctan_deriv_partial_toRat, TauRat.arctan_deriv_partial_toRat]
  by_cases h_le : n ≤ m
  · have h_bound := arctan_deriv_partial_rat_cauchy_bound x.toRat hx m n h_le
    have h_four_lt := Rat.four_div_two_pow_lt_recip k n hn
    linarith
  · push_neg at h_le
    have h_m_le_n : m ≤ n := Nat.le_of_lt h_le
    have h_swap_abs :
        |arctan_deriv_partial_rat x.toRat m - arctan_deriv_partial_rat x.toRat n|
          = |arctan_deriv_partial_rat x.toRat n - arctan_deriv_partial_rat x.toRat m| := by
      rw [show arctan_deriv_partial_rat x.toRat m - arctan_deriv_partial_rat x.toRat n
            = -(arctan_deriv_partial_rat x.toRat n - arctan_deriv_partial_rat x.toRat m)
            from by ring, abs_neg]
    rw [h_swap_abs]
    have h_bound := arctan_deriv_partial_rat_cauchy_bound x.toRat hx n m h_m_le_n
    have h_four_lt := Rat.four_div_two_pow_lt_recip k m hm
    linarith

-- ============================================================
-- PART 7: TauReal arctan_deriv_of_rat (Wave 2 user-facing)
-- ============================================================

/-! ## Wave 2 — user-facing TauReal `arctan_deriv_of_rat`

  Packages `arctan_deriv_partial_seq` with the convergence-domain
  hypothesis `2·|a.toRat| ≤ 1`, giving the formal derivative of
  `arctan_of_rat` as a Cauchy TauReal.

  By the geometric identity (Wave 1),

      (arctan_deriv_of_rat a hx).approx N .toRat
        = (1 − a.toRat^(4N)) / (1 + a.toRat²)

  which converges geometrically to `1/(1+a.toRat²)` as `N → ∞`.

  This is the candidate derivative TauReal for the IsDerivAt theorem
  in Wave 3. The connection to `TauReal.inv (1 + a²)` (the "cleanest"
  representation) is a downstream equivalence we'll establish if Module
  6 needs it — but for the IsDerivAt theorem itself, the partial-sum
  form is strictly more useful because `.approx N` directly equals the
  N-th partial sum.
-/

/-- **[I.D-Arctan-Deriv-General]** τ-native formal derivative
    `arctan_deriv_of_rat(x)` as a TauReal, for any `x : TauRat` with
    `|x.toRat| ≤ 1/2`. -/
def TauReal.arctan_deriv_of_rat (x : TauRat) (_ : 2 * |x.toRat| ≤ 1) : TauReal :=
  TauReal.arctan_deriv_partial_seq x

@[simp] theorem TauReal.arctan_deriv_of_rat_approx
    (x : TauRat) (hx : 2 * |x.toRat| ≤ 1) (n : Nat) :
    (TauReal.arctan_deriv_of_rat x hx).approx n = TauRat.arctan_deriv_partial x n := rfl

/-- **Cauchy property** for `arctan_deriv_of_rat`: inherited from
    `arctan_deriv_partial_seq_isCauchy`. -/
theorem TauReal.arctan_deriv_of_rat_isCauchy
    (x : TauRat) (hx : 2 * |x.toRat| ≤ 1) :
    (TauReal.arctan_deriv_of_rat x hx).IsCauchy :=
  TauReal.arctan_deriv_partial_seq_isCauchy x hx

/-- **Closed-form approximation** for `arctan_deriv_of_rat`: at every
    depth `N`, the approximation evaluates to `(1 − x^(4N))/(1 + x²)`
    at Rat level. -/
theorem TauReal.arctan_deriv_of_rat_approx_toRat_closed_form
    (x : TauRat) (hx : 2 * |x.toRat| ≤ 1) (N : Nat) :
    ((TauReal.arctan_deriv_of_rat x hx).approx N).toRat
      = (1 - x.toRat^(4*N)) / (1 + x.toRat^2) := by
  rw [TauReal.arctan_deriv_of_rat_approx]
  rw [TauRat.arctan_deriv_partial_toRat]
  have h_pos : (0 : Rat) < 1 + x.toRat^2 := by positivity
  have h_ne : (1 + x.toRat^2) ≠ 0 := ne_of_gt h_pos
  have h_id := arctan_deriv_partial_rat_geometric_identity x.toRat N
  field_simp
  linarith [h_id]

-- ============================================================
-- PART 8: Wave 3.A — MONOMIAL SECANT TAYLOR REMAINDER BOUND
-- ============================================================

/-! ## Wave 3.A — monomial secant Taylor remainder bound

  For `|a| ≤ 1/2` and `0 ≤ h ≤ 1/2`, the secant numerator
  `(a+h)^(n+1) − a^(n+1)` differs from the tangent-line approximation
  `h · (n+1) · a^n` by at most `h² · (n+1)² / 2`.

  Proof by induction on `n`, using the recursive identity

      (a+h)^(n+2) − a^(n+2) = h · (a+h)^(n+1) + a · ((a+h)^(n+1) − a^(n+1))

  which gives `E_{n+1} = h² · (n+1) · a^n + (h+a) · E_n` for the error
  `E_n := ((a+h)^(n+1) − a^(n+1)) − h · (n+1) · a^n`.

  Triangle inequality + `|a|, |h| ≤ 1/2` + induction hypothesis closes:
  `|E_{n+1}| ≤ h²·(n+1) + |E_n| ≤ h²·(n+1) + h²·(n+1)²/2 ≤ h²·(n+2)²/2`.

  This bound is the load-bearing tool for Wave 3.B (arctan partial-sum
  secant bound) and Wave 3.C (the main IsDerivAt theorem). -/
theorem monomial_secant_taylor_bound (a h : Rat) (n : Nat)
    (ha : |a| ≤ 1/2) (hh_nn : 0 ≤ h) (hh : h ≤ 1/2) :
    |((a+h)^(n+1) - a^(n+1)) - h * ((n+1 : Nat) : Rat) * a^n|
      ≤ h^2 * ((n+1 : Nat) : Rat)^2 / 2 := by
  induction n with
  | zero =>
    -- (a+h)^1 - a^1 - h * 1 * a^0 = 0
    have h_eq : (a+h)^(0+1) - a^(0+1) - h * ((0+1 : Nat) : Rat) * a^0 = 0 := by
      push_cast; ring
    rw [h_eq, abs_zero]
    positivity
  | succ n ih =>
    -- E_{n+1} = h² · (n+1) · a^n + (h + a) · E_n  (algebraic identity)
    have h_eq :
        (a+h)^((n+1)+1) - a^((n+1)+1) - h * (((n+1)+1 : Nat) : Rat) * a^(n+1)
        = h^2 * (((n+1 : Nat)) : Rat) * a^n
        + (h + a) * ((a+h)^(n+1) - a^(n+1) - h * ((n+1 : Nat) : Rat) * a^n) := by
      push_cast; ring
    rw [h_eq]
    -- Triangle inequality on the two pieces
    have h_abs_a_le_one : |a|^n ≤ 1 := by
      have h_a_nn : (0 : Rat) ≤ |a| := _root_.abs_nonneg _
      have h_a_le_one : |a| ≤ 1 := by linarith
      calc |a|^n ≤ (1 : Rat)^n := pow_le_pow_left₀ h_a_nn h_a_le_one n
        _ = 1 := one_pow _
    have h_n1_nn : (0 : Rat) ≤ ((n+1 : Nat) : Rat) := by exact_mod_cast Nat.zero_le _
    have h_h_sq_nn : (0 : Rat) ≤ h^2 := sq_nonneg _
    -- Bound on first piece: |h² · (n+1) · a^n| ≤ h² · (n+1)
    have h_prod_nn : (0 : Rat) ≤ h^2 * ((n+1 : Nat) : Rat) := mul_nonneg h_h_sq_nn h_n1_nn
    have h_bound_1 : |h^2 * ((n+1 : Nat) : Rat) * a^n| ≤ h^2 * ((n+1 : Nat) : Rat) := by
      have h_factor : h^2 * ((n+1 : Nat) : Rat) * a^n
                    = (h^2 * ((n+1 : Nat) : Rat)) * a^n := by ring
      rw [h_factor, abs_mul, abs_of_nonneg h_prod_nn, abs_pow]
      calc (h^2 * ((n+1 : Nat) : Rat)) * |a|^n
          ≤ (h^2 * ((n+1 : Nat) : Rat)) * 1 :=
            mul_le_mul_of_nonneg_left h_abs_a_le_one h_prod_nn
        _ = h^2 * ((n+1 : Nat) : Rat) := by ring
    -- Bound on second piece: |(h+a) · E_n| ≤ (|h|+|a|) · |E_n| ≤ 1 · h^2·(n+1)^2/2
    have h_sum_le_one : |h + a| ≤ 1 := by
      have h_h_abs : |h| = h := abs_of_nonneg hh_nn
      calc |h + a| ≤ |h| + |a| := abs_add_le _ _
        _ = h + |a| := by rw [h_h_abs]
        _ ≤ 1/2 + 1/2 := by linarith
        _ = 1 := by norm_num
    have h_En_nn : (0 : Rat) ≤
        |(a+h)^(n+1) - a^(n+1) - h * ((n+1 : Nat) : Rat) * a^n| := _root_.abs_nonneg _
    have h_bound_2 :
        |(h + a) * ((a+h)^(n+1) - a^(n+1) - h * ((n+1 : Nat) : Rat) * a^n)|
        ≤ h^2 * ((n+1 : Nat) : Rat)^2 / 2 := by
      rw [abs_mul]
      calc |h + a| * |(a+h)^(n+1) - a^(n+1) - h * ((n+1 : Nat) : Rat) * a^n|
          ≤ 1 * |(a+h)^(n+1) - a^(n+1) - h * ((n+1 : Nat) : Rat) * a^n| :=
            mul_le_mul_of_nonneg_right h_sum_le_one h_En_nn
        _ = |(a+h)^(n+1) - a^(n+1) - h * ((n+1 : Nat) : Rat) * a^n| := by ring
        _ ≤ h^2 * ((n+1 : Nat) : Rat)^2 / 2 := ih
    -- Combine: |A + B| ≤ |A| + |B|
    have h_tri :
        |h^2 * (((n+1 : Nat)) : Rat) * a^n
          + (h + a) * ((a+h)^(n+1) - a^(n+1) - h * ((n+1 : Nat) : Rat) * a^n)|
        ≤ h^2 * ((n+1 : Nat) : Rat) + h^2 * ((n+1 : Nat) : Rat)^2 / 2 := by
      calc |h^2 * (((n+1 : Nat)) : Rat) * a^n
              + (h + a) * ((a+h)^(n+1) - a^(n+1) - h * ((n+1 : Nat) : Rat) * a^n)|
          ≤ |h^2 * (((n+1 : Nat)) : Rat) * a^n|
            + |(h + a) * ((a+h)^(n+1) - a^(n+1) - h * ((n+1 : Nat) : Rat) * a^n)| :=
            abs_add_le _ _
        _ ≤ h^2 * ((n+1 : Nat) : Rat)
            + h^2 * ((n+1 : Nat) : Rat)^2 / 2 := by linarith
    -- Show h²·(n+1) + h²·(n+1)²/2 ≤ h²·(n+2)²/2
    -- Equivalent to: 2(n+1) + (n+1)² ≤ (n+2)², i.e., (n+1)(n+3) ≤ (n+2)²
    -- (n+1)(n+3) = n²+4n+3, (n+2)² = n²+4n+4, so (n+1)(n+3) = (n+2)² - 1 ≤ (n+2)². ✓
    have h_final :
        h^2 * ((n+1 : Nat) : Rat) + h^2 * ((n+1 : Nat) : Rat)^2 / 2
        ≤ h^2 * (((n+1)+1 : Nat) : Rat)^2 / 2 := by
      have h_nat_eq : (((n+1)+1 : Nat) : Rat) = ((n+1 : Nat) : Rat) + 1 := by push_cast; ring
      rw [h_nat_eq]
      -- Goal: h²(n+1) + h²(n+1)²/2 ≤ h²((n+1)+1)²/2
      -- Multiply through: 2(n+1) + (n+1)² ≤ (n+2)²
      -- (n+1)² + 2(n+1) + 1 = (n+2)², so (n+1)² + 2(n+1) = (n+2)² - 1 ≤ (n+2)²
      nlinarith [h_h_sq_nn, h_n1_nn,
                 sq_nonneg (((n+1 : Nat) : Rat) + 1),
                 sq_nonneg (((n+1 : Nat) : Rat))]
    linarith

-- ============================================================
-- PART 9: Wave 3.B — ARCTAN PAIR-TERM SECANT BOUND
-- ============================================================

/-! ## Wave 3.B — arctan pair-term secant Taylor remainder bound

  Lifts the Wave 3.A monomial bound to the arctan pair-term level:

      |(pair_term(a+h, k) − pair_term(a, k)) − h · deriv_pair_term(a, k)|
        ≤ h² · (4k+2)

  Proof: decompose pair_term into its two monomial subtractions
  `x^(4k+1)/(4k+1) − x^(4k+3)/(4k+3)`. The numerator difference matches
  the monomial bound at `n = 4k` and `n = 4k+2`. After dividing by
  `(4k+1)` and `(4k+3)` respectively and triangle-inequalitying:

      |error| ≤ h²·(4k+1)/2 + h²·(4k+3)/2 = h²·(4k+2)
-/

theorem arctan_pair_term_secant_taylor_bound (a h : Rat)
    (ha : |a| ≤ 1/2) (hh_nn : 0 ≤ h) (hh : h ≤ 1/2) (k : Nat) :
    |(arctan_pair_term_rat (a+h) k - arctan_pair_term_rat a k)
      - h * (arctan_deriv_pair_term_rat a k)|
      ≤ h^2 * (4 * (k : Rat) + 2) := by
  -- Apply Wave 3.A at n=4k and n=4k+2
  have h_mono_4k1 := monomial_secant_taylor_bound a h (4*k) ha hh_nn hh
  have h_mono_4k3 := monomial_secant_taylor_bound a h (4*k+2) ha hh_nn hh
  -- Normalize casts to canonical Rat-arithmetic form
  push_cast at h_mono_4k1 h_mono_4k3
  -- Normalize (4k+2)+1 ↦ 4k+3 at both Nat and Rat levels
  rw [show (4 * k + 2 + 1 : Nat) = 4 * k + 3 from by omega] at h_mono_4k3
  rw [show (4 * (k : Rat) + 2 + 1) = 4 * (k : Rat) + 3 from by ring] at h_mono_4k3
  -- Normalize (4k+0)+1 ↦ 4k+1 at both Nat and Rat levels (Wave 3.A's n=4k gives n+1=4k+1)
  rw [show (4 * k + 1 : Nat) = 4 * k + 1 from rfl] at h_mono_4k1
  -- Denominators positive (Rat-arithmetic form)
  have h_4k1_pos : (0 : Rat) < 4 * (k : Rat) + 1 := by
    have h_k_nn : (0 : Rat) ≤ (k : Rat) := by exact_mod_cast Nat.zero_le _
    linarith
  have h_4k3_pos : (0 : Rat) < 4 * (k : Rat) + 3 := by
    have h_k_nn : (0 : Rat) ≤ (k : Rat) := by exact_mod_cast Nat.zero_le _
    linarith
  -- Unfold definitions
  unfold arctan_pair_term_rat arctan_deriv_pair_term_rat
  -- Normalize the unfolded goal
  push_cast
  -- The goal now uses canonical Rat-form denominators (4*↑k+1, 4*↑k+3)
  -- Algebraic identity:
  have h_4k1_ne : 4 * (k : Rat) + 1 ≠ 0 := ne_of_gt h_4k1_pos
  have h_4k3_ne : 4 * (k : Rat) + 3 ≠ 0 := ne_of_gt h_4k3_pos
  have h_split :
      (a+h)^(4*k+1)/(4 * (k : Rat) + 1) - (a+h)^(4*k+3)/(4 * (k : Rat) + 3)
      - (a^(4*k+1)/(4 * (k : Rat) + 1) - a^(4*k+3)/(4 * (k : Rat) + 3))
      - h * (a^(4*k) - a^(4*k+2))
      = ((a+h)^(4*k+1) - a^(4*k+1) - h * (4 * (k : Rat) + 1) * a^(4*k))
          / (4 * (k : Rat) + 1)
        - ((a+h)^(4*k+3) - a^(4*k+3) - h * (4 * (k : Rat) + 3) * a^(4*k+2))
          / (4 * (k : Rat) + 3) := by
    field_simp
    ring
  rw [h_split]
  -- Set the bounded pieces
  set X := (a+h)^(4*k+1) - a^(4*k+1) - h * (4 * (k : Rat) + 1) * a^(4*k) with hX_def
  set Y := (a+h)^(4*k+3) - a^(4*k+3) - h * (4 * (k : Rat) + 3) * a^(4*k+2) with hY_def
  have h_X_bound : |X| ≤ h^2 * (4 * (k : Rat) + 1)^2 / 2 := h_mono_4k1
  have h_Y_bound : |Y| ≤ h^2 * (4 * (k : Rat) + 3)^2 / 2 := h_mono_4k3
  -- Triangle inequality
  have h_tri : |X / (4 * (k : Rat) + 1) - Y / (4 * (k : Rat) + 3)|
              ≤ |X| / (4 * (k : Rat) + 1) + |Y| / (4 * (k : Rat) + 3) := by
    calc |X / (4 * (k : Rat) + 1) - Y / (4 * (k : Rat) + 3)|
        ≤ |X / (4 * (k : Rat) + 1)| + |Y / (4 * (k : Rat) + 3)| := abs_sub _ _
      _ = |X| / (4 * (k : Rat) + 1) + |Y| / (4 * (k : Rat) + 3) := by
          rw [abs_div, abs_div]
          rw [abs_of_pos h_4k1_pos, abs_of_pos h_4k3_pos]
  -- Bound each piece: |X|/(4k+1) ≤ h²·(4k+1)/2 and similarly for Y
  have h_X_div : |X| / (4 * (k : Rat) + 1) ≤ h^2 * (4 * (k : Rat) + 1) / 2 := by
    rw [div_le_div_iff₀ h_4k1_pos (by norm_num : (0 : Rat) < 2)]
    have h_X_bound_x2 : |X| ≤ h^2 * (4 * (k : Rat) + 1)^2 / 2 := h_X_bound
    have h_pow_2 : (h^2 * (4 * (k : Rat) + 1)^2 / 2) * 2 = h^2 * (4 * (k : Rat) + 1)^2 := by
      field_simp
    have h_X_bound' : |X| * 2 ≤ h^2 * (4 * (k : Rat) + 1)^2 := by
      linarith [mul_le_mul_of_nonneg_right h_X_bound_x2 (by norm_num : (0 : Rat) ≤ 2)]
    have h_sq : (4 * (k : Rat) + 1)^2 = (4 * (k : Rat) + 1) * (4 * (k : Rat) + 1) := sq _
    nlinarith [h_X_bound', h_sq]
  have h_Y_div : |Y| / (4 * (k : Rat) + 3) ≤ h^2 * (4 * (k : Rat) + 3) / 2 := by
    rw [div_le_div_iff₀ h_4k3_pos (by norm_num : (0 : Rat) < 2)]
    have h_Y_bound_x2 : |Y| ≤ h^2 * (4 * (k : Rat) + 3)^2 / 2 := h_Y_bound
    have h_pow_2 : (h^2 * (4 * (k : Rat) + 3)^2 / 2) * 2 = h^2 * (4 * (k : Rat) + 3)^2 := by
      field_simp
    have h_Y_bound' : |Y| * 2 ≤ h^2 * (4 * (k : Rat) + 3)^2 := by
      linarith [mul_le_mul_of_nonneg_right h_Y_bound_x2 (by norm_num : (0 : Rat) ≤ 2)]
    have h_sq : (4 * (k : Rat) + 3)^2 = (4 * (k : Rat) + 3) * (4 * (k : Rat) + 3) := sq _
    nlinarith [h_Y_bound', h_sq]
  -- Final assembly
  have h_sum_eq : h^2 * (4 * (k : Rat) + 1) / 2 + h^2 * (4 * (k : Rat) + 3) / 2
                  = h^2 * (4 * (k : Rat) + 2) := by ring
  calc |X / (4 * (k : Rat) + 1) - Y / (4 * (k : Rat) + 3)|
      ≤ |X| / (4 * (k : Rat) + 1) + |Y| / (4 * (k : Rat) + 3) := h_tri
    _ ≤ h^2 * (4 * (k : Rat) + 1) / 2 + h^2 * (4 * (k : Rat) + 3) / 2 := by
        linarith [h_X_div, h_Y_div]
    _ = h^2 * (4 * (k : Rat) + 2) := h_sum_eq

end Tau.Boundary
