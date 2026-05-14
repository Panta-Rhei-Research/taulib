import TauLib.BookI.Boundary.TauRealIotaTau
import TauLib.BookI.Boundary.TauRealAnalyticalHelpers
import TauLib.BookI.Boundary.TauRealExp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity

/-!
# TauLib.BookI.Boundary.TauRealGeometric

The geometric series `Σ_{k=0}^{n-1} x^(2k)` and the closed-form
identity `Σ x^(2k) = 1 / (1 - x²)` realised at the TauReal level —
the τ-native replacement for `Mathlib.Analysis.SpecificLimits.Normed`'s
`tsum_geometric_of_lt_one` in the T₁ wedge-loop trace identity proof
(`TauLib/BookIV/Particles/OmegaCycle.lean`).

## Registry Cross-References

- [I.D115] TauRat partial-sum helpers (Wave 3a, `TauRealSum`)
- [I.D116] TauRealAnalyticalHelpers (Wave 3 helpers)
- [I.D-IotaTau-Structural] `TauReal.iota_tau` (Wave 4)
- [I.T-Geom-FinitePartial]  `TauRat.geom_partial_closed_form` (this module)
- [I.T-Geom-Tail-Bound]     `TauRat.geom_partial_cauchy_bound` (this module)
- [I.T-Geom-Limit-Equiv]    `TauReal.geom_limit_equiv_inv_one_sub_sq` (this module)

Migration target:
- `BookIV/Particles/OmegaCycle.lean::geometric_resummation`
  (line 274 — uses `tsum_geometric_of_lt_one`).
  Replaced by the τ-native finite + tail decomposition supplied here:
  `TauRat.geom_partial_closed_form` (finite-N identity) +
  `TauRat.geom_partial_cauchy_bound` (Cauchy tail) — together giving
  an explicit Cauchy-bound surrogate for the infinite tsum, with the
  bridge through `TauReal.geom_limit_equiv_inv_one_sub_sq`.

## Mathematical Content

**Wave M1** of the mathlib-free migration. Two complementary
formulations:

### (A) Finite-partial-sum identity, at the Rat level (via TauRat.toRat)

For `q : TauRat` with `q.toRat^2 ≠ 1` (in particular for `0 ≤ q.toRat < 1`):

$$ \sum_{k=0}^{N-1} q^{2k} \;=\; \frac{1 - q^{2N}}{1 - q^2} . $$

Proved by induction on `N`. This is the load-bearing closed form;
the infinite-sum claim is its limit as `N → ∞`, controlled by:

### (B) Tail bound, at the Rat level

For `0 ≤ q.toRat < 1` and any `n ≤ m`:

$$ \left| \frac{1 - q^{2m}}{1 - q^2} - \frac{1 - q^{2n}}{1 - q^2} \right|
   \;=\; \frac{q^{2n} - q^{2m}}{1 - q^2}
   \;\leq\; \frac{q^{2n}}{1 - q^2} . $$

The right-hand side tends to zero as `n → ∞` because `q² < 1`. This
gives an explicit Cauchy modulus on the partial-sum sequence.

### (C) Structural TauReal equivalence

The pointwise equivalence between

- `⟨n ↦ Σ_{k=0}^{n-1} q^(2k)⟩`  — `TauReal.geom_of_rat q`
- `TauReal.div TauReal.one (TauReal.sub TauReal.one (q · q))` — closed form

is captured by `TauReal.geom_limit_equiv_inv_one_sub_sq`, which states
that the two TauReals are equiv past an explicit modulus governed by
the tail bound.

## Strategic balance

The recommendation enacted here is **Option (C) hybrid**:

1. The finite-N closed form (Option A core) is proved as a sorry-free
   TauRat-level identity — this is the load-bearing arithmetic content of T₁.
2. The Cauchy tail bound is sorry-free (`TauRat.geom_partial_cauchy_bound`).
3. The TauReal Cauchy property is sorry-free
   (`TauReal.geom_of_rat_isCauchy`, modulus `λ k => k + 3`).
4. The structural TauReal equivalence to the closed form `1/(1 - q²)`
   (Option C — full limit identity) is queued as Part 5 of this module
   and the τ-native T₁ variant in `OmegaCycle.lean` is queued
   correspondingly.

This separates the **arithmetic identity** (sorry-free) from the
**convergence calibration** (sorry-free at the Cauchy bound layer)
from the **closed-form bridge** (Part 5, queued). The T₁ proof at
`OmegaCycle.lean` can be replaced by the finite-N identity at fixed
N matching its truncation depth, with the limit identity invoked only
at the level of the τ-canon-specific corollary
`wedge_loop_trace_identity_iota_tau`.

## Wave Γ₃ status

* **Part 1 (`geom_term`, `geom_partial`)**: sorry-free.
* **Part 2 (`geom_partial_closed_form`)**: sorry-free.
* **Part 3 (`geom_partial_cauchy_bound`)**: sorry-free, the Rat-level
  Cauchy tail bound for `0 ≤ q ≤ 1/2`.
* **Part 4 (`geom_of_rat`, `geom_of_rat_isCauchy`)**: sorry-free, the
  TauReal-level infinite geometric series with explicit Cauchy modulus.
* **Part 5 (closed-form equivalence)**: queued as a follow-on.

## Mathlib tactic-only discipline

This module imports `TauRealIotaTau`, `TauRealAnalyticalHelpers`,
`TauRealExp` (for `TauRat.pow`) — strictly TauLib content modules.
The only Mathlib imports are tactic-bearing (`Ring`, `Linarith`, etc.)
per the lakefile policy "Mathlib for TACTICS ONLY".
-/

set_option autoImplicit false

namespace Tau.Boundary

open Tau.Denotation

-- ============================================================
-- PART 1: GEOMETRIC TERM AND PARTIAL SUM (TauRat level)
-- ============================================================

/-- The k-th term of the geometric series with base `q²`:
    `geom_term q k = q^(2k)`. Uses `TauRat.pow` from `TauRealExp`. -/
def TauRat.geom_term (q : TauRat) (k : Nat) : TauRat :=
  TauRat.pow q (2 * k)

@[simp] theorem TauRat.geom_term_zero (q : TauRat) :
    TauRat.geom_term q 0 = TauRat.one := by
  unfold TauRat.geom_term
  simp [TauRat.pow_zero]

theorem TauRat.geom_term_toRat (q : TauRat) (k : Nat) :
    (TauRat.geom_term q k).toRat = q.toRat ^ (2 * k) := by
  unfold TauRat.geom_term
  exact TauRat.pow_toRat q (2 * k)

/-- Partial sum of the geometric-of-q² series:
    `geom_partial q n = Σ_{k=0}^{n-1} q^(2k)`. -/
def TauRat.geom_partial (q : TauRat) (n : Nat) : TauRat :=
  TauRat.sum (TauRat.geom_term q) n

@[simp] theorem TauRat.geom_partial_zero (q : TauRat) :
    TauRat.geom_partial q 0 = TauRat.zero := rfl

@[simp] theorem TauRat.geom_partial_succ (q : TauRat) (n : Nat) :
    TauRat.geom_partial q (n + 1) =
      (TauRat.geom_partial q n).add (TauRat.geom_term q n) := rfl

-- ============================================================
-- PART 2: FINITE-N CLOSED FORM AT THE Rat LEVEL
-- ============================================================

/-- **Algebraic identity (Rat level).**
    The partial geometric sum has the standard closed form

    $$ \sum_{k=0}^{N-1} q^{2k} \;=\; \frac{1 - q^{2N}}{1 - q^2}, $$

    valid for any `q : TauRat` with `q.toRat^2 ≠ 1`. Proved by
    induction on `N`. This is the load-bearing arithmetic identity. -/
theorem TauRat.geom_partial_closed_form (q : TauRat) (hq_sq_ne : q.toRat ^ 2 ≠ 1)
    (N : Nat) :
    (TauRat.geom_partial q N).toRat
      = (1 - q.toRat ^ (2 * N)) / (1 - q.toRat ^ 2) := by
  have h_one_sub_sq_ne : (1 : Rat) - q.toRat ^ 2 ≠ 0 := by
    intro h
    apply hq_sq_ne
    linarith
  induction N with
  | zero =>
    simp [TauRat.geom_partial_zero, toRat_zero]
  | succ N ih =>
    rw [TauRat.geom_partial_succ, toRat_add, ih, TauRat.geom_term_toRat]
    -- Goal: (1 - q^(2N))/(1 - q²) + q^(2N) = (1 - q^(2(N+1)))/(1 - q²)
    have h_pow_succ : q.toRat ^ (2 * (N + 1)) = q.toRat ^ (2 * N) * q.toRat ^ 2 := by
      rw [show 2 * (N + 1) = 2 * N + 2 from by ring, pow_add]
    rw [h_pow_succ]
    field_simp
    ring

-- ============================================================
-- PART 3: CAUCHY TAIL BOUND AT THE Rat LEVEL  (Wave Γ₃)
-- ============================================================

/-- **Monotone decrease of powers (Rat helper)**: for `0 ≤ q ≤ 1` and
    `n ≤ m`, `q^(2m) ≤ q^(2n) ≤ 1`. The geometric-series tail bound
    relies on this in the form `q^(2n) - q^(2m) ≥ 0`. -/
private theorem rat_pow_two_mul_antitone (q : Rat) (hq_pos : 0 ≤ q) (hq_le : q ≤ 1)
    (n m : Nat) (hnm : n ≤ m) :
    q ^ (2 * m) ≤ q ^ (2 * n) := by
  -- Use `pow_le_pow_of_le_one` (Mathlib) which gives `q^a ≤ q^b` for `a ≥ b`.
  exact pow_le_pow_of_le_one hq_pos hq_le (by omega : 2 * n ≤ 2 * m)

/-- **Upper bound on the squared-power (Rat helper)**: for `0 ≤ q ≤ 1/2`,
    `q^(2n) ≤ 1/2^n`. Proof: `q^2 ≤ 1/4 ≤ 1/2`, so `q^(2n) = (q²)^n ≤
    (1/2)^n = 1/2^n`. -/
private theorem rat_pow_two_mul_le_two_pow_neg (q : Rat) (hq_pos : 0 ≤ q)
    (hq_half : q ≤ 1/2) (n : Nat) :
    q ^ (2 * n) ≤ 1 / (2 : Rat) ^ n := by
  -- Step 1: q² ≤ 1/4 (from q ≤ 1/2, 0 ≤ q).
  have h_sq : q ^ 2 ≤ (1 / 2 : Rat) ^ 2 := by
    have h_pos_q : 0 ≤ q := hq_pos
    have h_le : q ≤ 1/2 := hq_half
    nlinarith
  have h_sq_quarter : q ^ 2 ≤ 1 / 4 := by
    have : ((1 : Rat) / 2) ^ 2 = 1 / 4 := by norm_num
    linarith
  -- Step 2: rewrite q^(2n) = (q²)^n.
  have h_pow_eq : q ^ (2 * n) = (q ^ 2) ^ n := by rw [pow_mul]
  rw [h_pow_eq]
  -- Step 3: (q²)^n ≤ (1/4)^n.
  have h_sq_nn : 0 ≤ q ^ 2 := sq_nonneg q
  have h_pow_le_quarter : (q ^ 2) ^ n ≤ ((1 : Rat) / 4) ^ n :=
    pow_le_pow_left₀ h_sq_nn h_sq_quarter n
  -- Step 4: (1/4)^n ≤ (1/2)^n.
  have h_quarter_le_half : ((1 : Rat) / 4) ^ n ≤ ((1 : Rat) / 2) ^ n := by
    apply pow_le_pow_left₀ (by norm_num : (0 : Rat) ≤ 1/4) (by norm_num : (1 : Rat)/4 ≤ 1/2)
  -- Step 5: (1/2)^n = 1/2^n.
  have h_half_pow : ((1 : Rat) / 2) ^ n = 1 / (2 : Rat) ^ n := by
    rw [div_pow, one_pow]
  linarith

/-- **The Cauchy tail bound (Rat level).**
    For `q : TauRat` with `0 ≤ q.toRat ≤ 1/2` and `n ≤ m`,

    $$ \left| \mathrm{geom\_partial}\,q\,m - \mathrm{geom\_partial}\,q\,n \right|
       \;\leq\; \frac{2}{2^n} . $$

    This is the explicit Cauchy modulus that replaces the
    `tsum_geometric_of_lt_one` use in T₁'s wedge-loop trace identity:
    the partial-sum sequence `n ↦ geom_partial q n` is Cauchy with
    modulus `n ↦ n + 3` (using `Rat.four_div_two_pow_lt_recip`).

    The proof uses the finite-N closed form
    (`TauRat.geom_partial_closed_form`) and the bound
    `q^(2n) ≤ 1/2^n` (from `q ≤ 1/2`) combined with
    `1/(1 - q²) ≤ 4/3 ≤ 2` (from `q² ≤ 1/4`).

    The hypothesis `q.toRat ≤ 1/2` is comfortable for the τ-canon
    application: `ι_τ ≈ 0.341 < 1/2`. -/
theorem TauRat.geom_partial_cauchy_bound (q : TauRat)
    (hq_pos : 0 ≤ q.toRat) (hq_half : q.toRat ≤ 1/2)
    (m n : Nat) (hnm : n ≤ m) :
    |(TauRat.geom_partial q m).toRat - (TauRat.geom_partial q n).toRat|
      ≤ 2 / (2 : Rat) ^ n := by
  -- Prerequisite: q² ≠ 1 (from q ≤ 1/2, 0 ≤ q).
  have h_q_le_one : q.toRat ≤ 1 := by linarith
  have h_q_sq_lt : q.toRat ^ 2 < 1 := by nlinarith
  have h_q_sq_ne : q.toRat ^ 2 ≠ 1 := ne_of_lt h_q_sq_lt
  -- Denominator positivity: 1 - q² ≥ 3/4 > 0.
  have h_q_sq_le_quarter : q.toRat ^ 2 ≤ 1/4 := by nlinarith
  have h_denom : (1 : Rat) - q.toRat ^ 2 ≥ 3/4 := by linarith
  have h_denom_pos : (0 : Rat) < 1 - q.toRat ^ 2 := by linarith
  -- Apply closed form to both partial sums.
  rw [TauRat.geom_partial_closed_form q h_q_sq_ne m,
      TauRat.geom_partial_closed_form q h_q_sq_ne n]
  -- Simplify: (1 - q^(2m))/D - (1 - q^(2n))/D = (q^(2n) - q^(2m))/D.
  have h_diff_eq :
      (1 - q.toRat ^ (2 * m)) / (1 - q.toRat ^ 2)
        - (1 - q.toRat ^ (2 * n)) / (1 - q.toRat ^ 2)
        = (q.toRat ^ (2 * n) - q.toRat ^ (2 * m)) / (1 - q.toRat ^ 2) := by
    field_simp
    ring
  rw [h_diff_eq]
  -- Power monotonicity: q^(2m) ≤ q^(2n) ≤ 1.
  have h_pow_anti := rat_pow_two_mul_antitone q.toRat hq_pos h_q_le_one n m hnm
  have h_pow_n_nn : 0 ≤ q.toRat ^ (2 * n) := by positivity
  -- The numerator is non-negative; remove the abs.
  have h_num_nn : 0 ≤ q.toRat ^ (2 * n) - q.toRat ^ (2 * m) := by linarith
  have h_denom_pos_le : 0 ≤ 1 - q.toRat ^ 2 := h_denom_pos.le
  have h_ratio_nn : 0 ≤ (q.toRat ^ (2 * n) - q.toRat ^ (2 * m))
                          / (1 - q.toRat ^ 2) :=
    div_nonneg h_num_nn h_denom_pos_le
  rw [abs_of_nonneg h_ratio_nn]
  -- Bound numerator: q^(2n) - q^(2m) ≤ q^(2n) ≤ 1/2^n.
  have h_num_le : q.toRat ^ (2 * n) - q.toRat ^ (2 * m) ≤ q.toRat ^ (2 * n) := by
    have h_pow_m_nn : 0 ≤ q.toRat ^ (2 * m) := by positivity
    linarith
  have h_pow_le := rat_pow_two_mul_le_two_pow_neg q.toRat hq_pos hq_half n
  have h_num_le_half_pow :
      q.toRat ^ (2 * n) - q.toRat ^ (2 * m) ≤ 1 / (2 : Rat) ^ n := by linarith
  -- Bound the ratio: (q^(2n) - q^(2m)) / (1-q²) ≤ 2/2^n via cross-multiplication.
  -- Equivalent: (q^(2n) - q^(2m)) · 2^n ≤ 2 · (1 - q²).
  have h_two_pow_pos : (0 : Rat) < (2 : Rat) ^ n := by positivity
  -- Rewrite the goal as a cross-multiplied inequality, then close with linarith.
  rw [div_le_div_iff₀ h_denom_pos h_two_pow_pos]
  -- Goal: (q^(2n) - q^(2m)) * 2^n ≤ 2 * (1 - q²).
  -- From h_num_le_half_pow: q^(2n) - q^(2m) ≤ 1/2^n, i.e. (q^(2n) - q^(2m)) · 2^n ≤ 1.
  -- From h_denom ≥ 3/4: 2(1-q²) ≥ 3/2 > 1.
  have h_two_pow_pos_le : (0 : Rat) ≤ (2 : Rat) ^ n := h_two_pow_pos.le
  have h_lhs_le_one : (q.toRat ^ (2 * n) - q.toRat ^ (2 * m)) * (2 : Rat) ^ n ≤ 1 := by
    have h := mul_le_mul_of_nonneg_right h_num_le_half_pow h_two_pow_pos_le
    have h_rewrite : (1 / (2 : Rat) ^ n) * (2 : Rat) ^ n = 1 := by
      field_simp
    linarith
  have h_rhs_ge : (2 : Rat) * (1 - q.toRat ^ 2) ≥ 3/2 := by linarith
  linarith

-- ============================================================
-- PART 4: TauReal.geom_of_rat + IsCauchy  (Wave Γ₃)
-- ============================================================

/-- **[I.D-Geom-of-Rat]**  The τ-native infinite geometric series of
    `q²`, realised as a `TauReal` whose `n`-th approximation is the
    partial sum `Σ_{k=0}^{n-1} q^(2k)`.

    Mirrors `TauReal.exp_of_rat` (the exp series) at the architectural
    level: a sequence of TauRat partial sums, Cauchy by the explicit
    tail bound of `TauRat.geom_partial_cauchy_bound`.

    The τ-native replacement for Mathlib's `tsum_geometric_of_lt_one`:
    rather than asserting `∑' k, x^k = 1/(1-x)` in an analytic-topology
    setting, we provide an explicit Cauchy sequence whose limit is
    structurally identified with `1/(1-q²)` via
    `TauReal.geom_limit_equiv_inv_one_sub_sq` (Part 5, queued). -/
def TauReal.geom_of_rat (q : TauRat) : TauReal :=
  ⟨TauRat.geom_partial q⟩

@[simp] theorem TauReal.geom_of_rat_approx (q : TauRat) (n : Nat) :
    (TauReal.geom_of_rat q).approx n = TauRat.geom_partial q n := rfl

/-- **[I.T-Geom-IsCauchy]**  `TauReal.geom_of_rat q` is a well-defined
    constructive real (Cauchy) under the standing hypothesis
    `0 ≤ q.toRat ≤ 1/2`. Modulus: `λ k => k + 3`.

    The proof mirrors `TauReal.exp_of_rat_isCauchy`:
    1. Unfold the IsCauchy / TauRat.lt / abs / ofNatRecip layers.
    2. Apply `TauRat.geom_partial_cauchy_bound` to bound
       `|geom_partial m - geom_partial n| ≤ 2/2^n` (for `n ≤ m`).
    3. Chain through `2/2^n ≤ 4/2^n < 1/(k+1)`
       (using `Rat.four_div_two_pow_lt_recip` at modulus `k + 3`).
    4. Symmetric case `m ≤ n` by abs-symmetry.

    The hypothesis `q.toRat ≤ 1/2` is comfortably satisfied for the
    τ-canon application `q = ι_τ ≈ 0.341 < 1/2`. -/
theorem TauReal.geom_of_rat_isCauchy (q : TauRat)
    (hq_pos : 0 ≤ q.toRat) (hq_half : q.toRat ≤ 1/2) :
    (TauReal.geom_of_rat q).IsCauchy := by
  refine ⟨fun k => k + 3, ?_⟩
  intro k m n hm hn
  change k + 3 ≤ m at hm
  change k + 3 ≤ n at hn
  unfold TauRat.lt
  rw [TauRat.toRat_abs, toRat_sub, TauRat.ofNatRecip_toRat]
  show |(TauRat.geom_partial q m).toRat - (TauRat.geom_partial q n).toRat|
         < 1 / ((k : Rat) + 1)
  by_cases h_le : n ≤ m
  · -- n ≤ m: direct application of cauchy bound.
    have h_bound := TauRat.geom_partial_cauchy_bound q hq_pos hq_half m n h_le
    have h_two_pow_pos : (0 : Rat) < (2 : Rat) ^ n := by positivity
    have h_two_le_four : (2 : Rat) / (2 : Rat) ^ n ≤ 4 / (2 : Rat) ^ n := by
      rw [div_le_div_iff₀ h_two_pow_pos h_two_pow_pos]; nlinarith
    have h_four_lt := Rat.four_div_two_pow_lt_recip k n hn
    linarith
  · -- m < n: swap with abs symmetry.
    push_neg at h_le
    have h_m_le_n : m ≤ n := Nat.le_of_lt h_le
    have h_swap_abs :
        |(TauRat.geom_partial q m).toRat - (TauRat.geom_partial q n).toRat|
          = |(TauRat.geom_partial q n).toRat - (TauRat.geom_partial q m).toRat| := by
      rw [show (TauRat.geom_partial q m).toRat - (TauRat.geom_partial q n).toRat
            = -((TauRat.geom_partial q n).toRat - (TauRat.geom_partial q m).toRat)
              from by ring, abs_neg]
    rw [h_swap_abs]
    have h_bound := TauRat.geom_partial_cauchy_bound q hq_pos hq_half n m h_m_le_n
    have h_two_pow_pos : (0 : Rat) < (2 : Rat) ^ m := by positivity
    have h_two_le_four : (2 : Rat) / (2 : Rat) ^ m ≤ 4 / (2 : Rat) ^ m := by
      rw [div_le_div_iff₀ h_two_pow_pos h_two_pow_pos]; nlinarith
    have h_four_lt := Rat.four_div_two_pow_lt_recip k m hm
    linarith

-- ============================================================
-- PART 5: CLOSED-FORM CONVERGENCE  (Wave Γ₃)
-- ============================================================

/-- **[I.T-Geom-Limit-Pointwise]**  The `n`-th approximation of
    `TauReal.geom_of_rat q` is exactly the finite-N closed form
    `(1 - q^(2n)) / (1 - q²)`. Trivial rewrap of
    `geom_partial_closed_form` at the TauReal-approximation interface. -/
theorem TauReal.geom_of_rat_approx_toRat
    (q : TauRat) (hq_sq_ne : q.toRat ^ 2 ≠ 1) (n : Nat) :
    ((TauReal.geom_of_rat q).approx n).toRat
      = (1 - q.toRat ^ (2 * n)) / (1 - q.toRat ^ 2) := by
  show (TauRat.geom_partial q n).toRat
        = (1 - q.toRat ^ (2 * n)) / (1 - q.toRat ^ 2)
  exact TauRat.geom_partial_closed_form q hq_sq_ne n

/-- **The closed-form tail bound at the Rat level (Wave Γ₃).**
    For `q : TauRat` with `0 ≤ q.toRat ≤ 1/2` and any `n : Nat`,

    $$ \left| \mathrm{geom\_partial}\,q\,n - \frac{1}{1 - q^2} \right|
       \;\leq\; \frac{2}{2^n} . $$

    This is the Rat-level convergence statement that pairs the
    Cauchy property (Part 4) with the **closed-form limit**
    `1/(1 - q²)`: the partial sums approach the closed form at
    a geometric rate.

    Proof: `geom_partial q n - 1/(1-q²) = -q^(2n)/(1-q²)` (from the
    finite-N closed form); then bound `q^(2n)/(1-q²) ≤ 2/2^n` by the
    same chain as in `geom_partial_cauchy_bound`. -/
theorem TauRat.geom_partial_to_closed_form_bound
    (q : TauRat) (hq_pos : 0 ≤ q.toRat) (hq_half : q.toRat ≤ 1/2)
    (n : Nat) :
    |(TauRat.geom_partial q n).toRat - 1 / (1 - q.toRat ^ 2)|
      ≤ 2 / (2 : Rat) ^ n := by
  have h_q_le_one : q.toRat ≤ 1 := by linarith
  have h_q_sq_lt : q.toRat ^ 2 < 1 := by nlinarith
  have h_q_sq_ne : q.toRat ^ 2 ≠ 1 := ne_of_lt h_q_sq_lt
  have h_q_sq_le_quarter : q.toRat ^ 2 ≤ 1/4 := by nlinarith
  have h_denom : (1 : Rat) - q.toRat ^ 2 ≥ 3/4 := by linarith
  have h_denom_pos : (0 : Rat) < 1 - q.toRat ^ 2 := by linarith
  -- Apply closed form: geom_partial q n = (1 - q^(2n))/(1-q²).
  rw [TauRat.geom_partial_closed_form q h_q_sq_ne n]
  -- Difference: (1 - q^(2n))/(1-q²) - 1/(1-q²) = -q^(2n)/(1-q²).
  have h_diff_eq :
      (1 - q.toRat ^ (2 * n)) / (1 - q.toRat ^ 2)
        - 1 / (1 - q.toRat ^ 2)
        = -(q.toRat ^ (2 * n) / (1 - q.toRat ^ 2)) := by
    field_simp
    ring
  rw [h_diff_eq]
  -- |-q^(2n)/(1-q²)| = q^(2n)/(1-q²).
  have h_pow_nn : 0 ≤ q.toRat ^ (2 * n) := by positivity
  have h_ratio_nn : 0 ≤ q.toRat ^ (2 * n) / (1 - q.toRat ^ 2) :=
    div_nonneg h_pow_nn h_denom_pos.le
  rw [abs_neg, abs_of_nonneg h_ratio_nn]
  -- Same bound chain as in geom_partial_cauchy_bound.
  have h_pow_le := rat_pow_two_mul_le_two_pow_neg q.toRat hq_pos hq_half n
  have h_two_pow_pos : (0 : Rat) < (2 : Rat) ^ n := by positivity
  rw [div_le_div_iff₀ h_denom_pos h_two_pow_pos]
  -- Goal: q^(2n) * 2^n ≤ 2 * (1 - q²).
  -- LHS ≤ 1 (from q^(2n) ≤ 1/2^n).
  have h_lhs_le_one : q.toRat ^ (2 * n) * (2 : Rat) ^ n ≤ 1 := by
    have h := mul_le_mul_of_nonneg_right h_pow_le h_two_pow_pos.le
    have h_rewrite : (1 / (2 : Rat) ^ n) * (2 : Rat) ^ n = 1 := by
      field_simp
    linarith
  -- RHS ≥ 3/2.
  have h_rhs_ge : (2 : Rat) * (1 - q.toRat ^ 2) ≥ 3/2 := by linarith
  linarith

/-- **[I.T-Geom-Closed-Form-Modulus]**  Past modulus `k + 3`,
    the partial sums of `TauReal.geom_of_rat q` lie within
    `1/(k+1)` of the closed form `1/(1 - q²)`, in the Rat metric.

    This is the load-bearing convergence theorem: the τ-native
    replacement for `tsum_geometric_of_lt_one`'s statement
    `∑ x^k = 1/(1-x)`. The closed-form limit is captured at the
    Rat level (not a separate TauReal), making this statement
    self-contained and directly usable in downstream contexts
    that need to know the partial-sum sequence has a specific
    Rat limit. -/
theorem TauReal.geom_of_rat_to_closed_form
    (q : TauRat) (hq_pos : 0 ≤ q.toRat) (hq_half : q.toRat ≤ 1/2)
    (k n : Nat) (hn : k + 3 ≤ n) :
    |((TauReal.geom_of_rat q).approx n).toRat - 1 / (1 - q.toRat ^ 2)|
      < 1 / ((k : Rat) + 1) := by
  show |(TauRat.geom_partial q n).toRat - 1 / (1 - q.toRat ^ 2)|
         < 1 / ((k : Rat) + 1)
  have h_bound := TauRat.geom_partial_to_closed_form_bound q hq_pos hq_half n
  have h_two_pow_pos : (0 : Rat) < (2 : Rat) ^ n := by positivity
  have h_two_le_four : (2 : Rat) / (2 : Rat) ^ n ≤ 4 / (2 : Rat) ^ n := by
    rw [div_le_div_iff₀ h_two_pow_pos h_two_pow_pos]; nlinarith
  have h_four_lt := Rat.four_div_two_pow_lt_recip k n hn
  linarith

end Tau.Boundary
