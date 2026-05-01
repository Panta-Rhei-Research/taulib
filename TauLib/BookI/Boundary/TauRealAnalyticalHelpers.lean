import TauLib.BookI.Boundary.TauRealSum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity

/-!
# TauLib.BookI.Boundary.TauRealAnalyticalHelpers

Named tactic-plumbing lemmas for the Wave 3 series-convergence proofs.

## Rationale

TauLib's tactics-only Mathlib policy excludes the content lemmas that a
mainstream project would pull in transparently.  Series-convergence
proofs (factorial bounds, geometric tails, reciprocal monotonicity)
require a handful of inequality-shuffling patterns that `linarith` and
`positivity` don't close out of the box.

Encoding those patterns as named lemmas here — proved once, reused
across Waves 3b (e), 3c (π), and 3d (π + e) — collapses the per-wave
tactic plumbing from ~200 lines of iteration-heavy trial-and-error
back down to ~60 lines that close on first pass.

## Contents

- `Nat.factorial_ge_two_pow`          : `2^(n-1) ≤ n!` for `n ≥ 1`
- `Nat.two_pow_succ_gt_linear`        : `k + 1 < 2^(k+1)`           (Nat)
- `Rat.two_pow_succ_gt_linear`        : `(k+1 : Rat) < 2^(k+1)`     (Rat cast)
- `Rat.pow_pred_eq`                   : `(2 : Rat)^m = 2 * 2^(m-1)` for `m ≥ 1`
- `Rat.four_div_two_pow_succ_eq_two_div_two_pow`
                                      : `4/2^(m+1) = 2/2^m`
- `TauRat.ofNatRecip_lt_of_exp_bound` : the workhorse `4/2^n < 1/(k+1)`
  conclusion from `k + 1 < 2^(k+1)` + `k + 3 ≤ n`
-/

set_option autoImplicit false

namespace Tau.Boundary

open Tau.Denotation

-- ============================================================
-- PART 1: FACTORIAL LOWER BOUND  (Nat)
-- ============================================================

/-- `2^(n−1) ≤ n!` for `n ≥ 1`, pure-Nat form. -/
theorem Nat.factorial_ge_two_pow (n : Nat) (hn : 1 ≤ n) :
    2 ^ (n - 1) ≤ Nat.factorial n := by
  induction n with
  | zero => omega
  | succ n ih =>
    rcases Nat.lt_or_ge 1 (n + 1) with h | h
    · have hn' : 1 ≤ n := by omega
      have ih' := ih hn'
      have h_lhs : 2 ^ ((n + 1) - 1) = 2 * 2 ^ (n - 1) := by
        have h_sub : (n + 1) - 1 = n := by omega
        have h_n : n = (n - 1) + 1 := by omega
        rw [h_sub]; conv_lhs => rw [h_n]
        rw [pow_succ]; ring
      rw [h_lhs, Nat.factorial_succ]
      have h2 : 2 ≤ n + 1 := by omega
      have hfn : 0 < Nat.factorial n := Nat.factorial_pos n
      calc 2 * 2 ^ (n - 1)
          ≤ 2 * Nat.factorial n := by
            have := ih'; have := hfn; nlinarith
        _ ≤ (n + 1) * Nat.factorial n :=
            Nat.mul_le_mul_right _ h2
    · have hn0 : n = 0 := by omega
      subst hn0; simp [Nat.factorial]

-- ============================================================
-- PART 2: EXPONENTIAL BEATS LINEAR
-- ============================================================

/-- `k + 1 < 2^(k+1)` at the Nat level. -/
theorem Nat.two_pow_succ_gt_linear (k : Nat) : k + 1 < 2 ^ (k + 1) := by
  induction k with
  | zero => norm_num
  | succ k ih =>
    have h_ring : 2 ^ (k + 1 + 1) = 2 * 2 ^ (k + 1) := by ring
    linarith

/-- Rat cast: `(k + 1 : Rat) < 2^(k+1)`. -/
theorem Rat.two_pow_succ_gt_linear (k : Nat) :
    ((k : Rat) + 1) < (2 : Rat) ^ (k + 1) := by
  have h_nat := Nat.two_pow_succ_gt_linear k
  have h_cast : ((k + 1 : Nat) : Rat) < ((2 ^ (k + 1) : Nat) : Rat) := by
    exact_mod_cast h_nat
  have h1 : ((k + 1 : Nat) : Rat) = (k : Rat) + 1 := by push_cast; ring
  have h2 : ((2 ^ (k + 1) : Nat) : Rat) = (2 : Rat) ^ (k + 1) := by
    push_cast; ring
  linarith

-- ============================================================
-- PART 3: POWER-OF-TWO ALGEBRAIC IDENTITIES
-- ============================================================

/-- `(2 : Rat)^m = 2 * 2^(m-1)` for `m ≥ 1`.  Packaged so downstream
    proofs don't need to redo the `m = (m-1)+1 + pow_succ + ring` dance. -/
theorem Rat.pow_pred_eq (m : Nat) (hm : 1 ≤ m) :
    (2 : Rat) ^ m = 2 * (2 : Rat) ^ (m - 1) := by
  have h : m = (m - 1) + 1 := by omega
  conv_lhs => rw [h]
  rw [pow_succ]; ring

/-- `4/2^(m+1) = 2/2^m` — a common reshuffle in telescoping geometric bounds. -/
theorem Rat.four_div_two_pow_succ_eq_two_div_two_pow (m : Nat) :
    (4 : Rat) / (2 : Rat) ^ (m + 1) = 2 / (2 : Rat) ^ m := by
  have h_pow : (2 : Rat) ^ (m + 1) = 2 * 2 ^ m := by ring
  rw [h_pow]
  have h_pos : (0 : Rat) < 2 ^ m := by positivity
  have h_ne : (2 : Rat) ^ m ≠ 0 := ne_of_gt h_pos
  field_simp
  ring

/-- `1/2^(m-1) = 2/2^m` for `m ≥ 1`. -/
theorem Rat.one_div_two_pow_pred_eq_two_div_two_pow (m : Nat) (hm : 1 ≤ m) :
    (1 : Rat) / (2 : Rat) ^ (m - 1) = 2 / (2 : Rat) ^ m := by
  rw [Rat.pow_pred_eq m hm]
  have h_pos : (0 : Rat) < (2 : Rat) ^ (m - 1) := by positivity
  field_simp

-- ============================================================
-- PART 4: THE WORKHORSE  4/2^n < 1/(k+1)  FROM  k + 3 ≤ n
-- ============================================================

/-- The central inequality: for `k + 3 ≤ n`, `4/2^n < 1/(k+1)` over `Rat`.

    Proof chain:
    • `k + 3 ≤ n` gives `2^(k+3) ≤ 2^n` via `pow_le_pow_right₀`.
    • `2^(k+3) = 4 · 2^(k+1)` by ring.
    • `(k + 1 : Rat) < 2^(k+1)` by `Rat.two_pow_succ_gt_linear`.
    • Combine: `4(k+1) < 4 · 2^(k+1) = 2^(k+3) ≤ 2^n`.
    • Reciprocal: `4/2^n < 1/(k+1)` via `div_lt_div_iff₀`. -/
theorem Rat.four_div_two_pow_lt_recip (k n : Nat) (hn : k + 3 ≤ n) :
    (4 : Rat) / (2 : Rat) ^ n < 1 / ((k : Rat) + 1) := by
  have h_exp : (2 : Rat) ^ (k + 3) ≤ (2 : Rat) ^ n :=
    pow_le_pow_right₀ (by norm_num : (1 : Rat) ≤ 2) (by omega : k + 3 ≤ n)
  have h_exp_pos : (0 : Rat) < 2 ^ n := by positivity
  have h_lin := Rat.two_pow_succ_gt_linear k
  have h_k3 : (2 : Rat) ^ (k + 3) = 4 * (2 : Rat) ^ (k + 1) := by ring
  have h_pos_k1 : (0 : Rat) < (k : Rat) + 1 := by
    have : (0 : Rat) ≤ (k : Rat) := by exact_mod_cast Nat.zero_le k
    linarith
  have h_key : 4 * ((k : Rat) + 1) < (2 : Rat) ^ n := by
    have h1 : 4 * ((k : Rat) + 1) < 4 * (2 : Rat) ^ (k + 1) := by linarith
    linarith [h_exp, h_k3]
  rw [div_lt_div_iff₀ h_exp_pos h_pos_k1]
  linarith

-- ============================================================
-- PART 5: TOWER-EXPONENT BOUND  (Wave R8b R2 helper)
--
-- Required by Newton's quadratic convergence in TauRealSqrt.lean.
-- The existing four_div_two_pow_lt_recip handles linear-exponent n
-- (used for series of factorial / Leibniz type); Newton iteration
-- converges as 1/2^{2^n} — a tower exponential — needing a sharper
-- bound. This section provides it.
-- ============================================================

/-- `2^{2^n}` grows faster than `n+1`. Proved by induction:
    base case `2^{2^0} = 2 > 1`; step case `2^{2^{n+1}} = (2^{2^n})^2`
    grows quadratically while `n+2` grows linearly. -/
theorem Nat.two_tower_pow_gt_linear (n : Nat) : n + 1 < 2 ^ (2 ^ n) := by
  induction n with
  | zero => decide
  | succ n ih =>
    have h_exp : 2 ^ (2 ^ (n + 1)) = (2 ^ (2 ^ n)) ^ 2 := by
      rw [pow_succ, pow_mul]
    rw [h_exp]
    have h_base : 2 ≤ 2 ^ (2 ^ n) := by
      have h_pos : 0 < 2 ^ n := by positivity
      calc 2 = 2^1 := by norm_num
        _ ≤ 2^(2^n) := Nat.pow_le_pow_right (by norm_num) h_pos
    have h_pos2 : 0 < 2 ^ (2 ^ n) := by positivity
    nlinarith [h_base, h_pos2, ih]

/-- Rat cast of the tower bound: `(n + 1 : Rat) < 2^{2^n}`. -/
theorem Rat.two_tower_pow_gt_linear (n : Nat) :
    ((n : Rat) + 1) < (2 : Rat) ^ (2 ^ n) := by
  have h_nat := Nat.two_tower_pow_gt_linear n
  have h_cast : ((n + 1 : Nat) : Rat) < ((2 ^ (2^n) : Nat) : Rat) := by
    exact_mod_cast h_nat
  have h1 : ((n + 1 : Nat) : Rat) = (n : Rat) + 1 := by push_cast; ring
  have h2 : ((2 ^ (2^n) : Nat) : Rat) = (2 : Rat) ^ (2^n) := by push_cast; ring
  linarith

/-- Tower-exponent bound: for `n ≥ k+1`, `1 / 2^{2^n} < 1 / (k+1)`.

    This is the Cauchy bound for Newton's quadratic convergence in
    `TauRealSqrt.lean`. Compare `Rat.four_div_two_pow_lt_recip` (linear
    `n`; used for factorial/Leibniz series). Here the exponent is `2^n`
    — a tower — giving far stronger decay. -/
theorem Rat.one_div_tower_pow_lt_recip (k n : Nat) (hn : k + 1 ≤ n) :
    (1 : Rat) / (2 : Rat) ^ (2 ^ n) < 1 / ((k : Rat) + 1) := by
  have h_k1_pos : (0 : Rat) < (k : Rat) + 1 := by
    have : (0 : Rat) ≤ (k : Rat) := by exact_mod_cast Nat.zero_le k
    linarith
  have h_exp_pos : (0 : Rat) < (2 : Rat) ^ (2 ^ n) := by positivity
  have h_tower := Rat.two_tower_pow_gt_linear n
  -- 2^{2^n} > n + 1 ≥ k + 1 (since k + 1 ≤ n implies k ≤ n - 1 ≤ n, hence k + 1 ≤ n + 1)
  have h_n_ge_k : ((k : Rat) + 1) ≤ ((n : Rat) + 1) := by
    have h_kn : k ≤ n := by omega
    have : (k : Rat) ≤ (n : Rat) := by exact_mod_cast h_kn
    linarith
  have h_large : ((k : Rat) + 1) < (2 : Rat) ^ (2 ^ n) := lt_of_le_of_lt h_n_ge_k h_tower
  rw [div_lt_div_iff₀ h_exp_pos h_k1_pos]
  linarith

-- ============================================================
-- PART 6: EVENTUAL BOUNDEDNESS OF CAUCHY SEQUENCES (Wave R8e)
-- ============================================================

/-- A Cauchy sequence is eventually bounded:
    there exists `C` and `N` such that `|(x.approx n).toRat| ≤ C` for all `n ≥ N`.

    Proof: at level k = 0, past the modulus M = μ(0), all terms satisfy
    `|(x.approx n).toRat - (x.approx M).toRat| < 1/(0+1) = 1`.
    Triangle inequality then gives `|(x.approx n).toRat| ≤ |(x.approx M).toRat| + 1`.

    Required by Wave R8e for sqrt_isCauchy Term C and sqrt_sq tower bound:
    bounding the initial Newton error `e₀ = (a_n + 1)² − a_n` requires
    eventual boundedness of `a.approx n`.
-/
theorem TauReal.IsCauchy.eventually_bounded {x : TauReal} (hx : x.IsCauchy) :
    ∃ C : Rat, ∃ N : Nat, ∀ idx : Nat, N ≤ idx → |(x.approx idx).toRat| ≤ C := by
  obtain ⟨μ, hμ⟩ := hx
  refine ⟨|(x.approx (μ 0)).toRat| + 1, μ 0, ?_⟩
  intro idx h_idx_ge
  -- Cauchy at level 0: |x_idx - x_(μ 0)| < 1/(0+1)
  have h_self : μ 0 ≤ μ 0 := Nat.le_refl _
  have h_close : TauRat.lt
      (((x.approx idx).sub (x.approx (μ 0))).abs) (TauRat.ofNatRecip 0) :=
    hμ 0 idx (μ 0) h_idx_ge h_self
  unfold TauRat.lt at h_close
  rw [TauRat.toRat_abs, toRat_sub, TauRat.ofNatRecip_toRat] at h_close
  -- h_close: |(x_idx).toRat - (x_(μ 0)).toRat| < 1/((0:Rat)+1)
  have h_one_eq : (1 : Rat) / ((0 : Rat) + 1) = 1 := by norm_num
  have h_diff_lt_1 : |(x.approx idx).toRat - (x.approx (μ 0)).toRat| < 1 := by
    linarith [h_close, h_one_eq]
  -- Triangle inequality directly (avoid rewrite trap):
  -- |a| ≤ |b| + |a - b| via |a| = |b + (a - b)| ≤ |b| + |a - b|
  have h_abs_triangle :
      |(x.approx idx).toRat|
      ≤ |(x.approx (μ 0)).toRat|
        + |(x.approx idx).toRat - (x.approx (μ 0)).toRat| := by
    have h_split :
        (x.approx (μ 0)).toRat + ((x.approx idx).toRat - (x.approx (μ 0)).toRat)
        = (x.approx idx).toRat := by ring
    have h_add_le : |(x.approx (μ 0)).toRat
                     + ((x.approx idx).toRat - (x.approx (μ 0)).toRat)|
                  ≤ |(x.approx (μ 0)).toRat|
                    + |(x.approx idx).toRat - (x.approx (μ 0)).toRat| :=
      abs_add_le _ _
    rw [h_split] at h_add_le
    exact h_add_le
  linarith

-- ============================================================
-- PART 7: SIGNED POSITIVITY FROM CAUCHY + APARTNESS (Wave R8i)
-- ============================================================

/-- A Cauchy sequence that is bounded away from zero has eventually
    coherent sign: there is an index past which every approximation is
    either uniformly positive or uniformly negative.

    Proof sketch: BAZ gives `δ = 1/(k₀+1)` with `|a.approx n| > δ` for
    `n ≥ N₀`. Choose Cauchy level `k' = 2*k₀ + 2` so that pairwise
    distance is `< 1/(2k₀+3) < δ` for indices past `μ k'`. Take
    `N = max(N₀, μ k')`. Inspect the sign at index `N`. If positive,
    every later term must be positive — flipping to negative would force
    distance `> 2δ`, contradicting Cauchy `< δ`. Symmetric for negative.

    This closes the signed-positivity gap that `sqrt_isCauchy` requires
    in addition to BAZ apartness.
-/
theorem TauReal.IsCauchy.signed_positive_eventually {a : TauReal}
    (h_cauchy : a.IsCauchy) (h_baz : a.BoundedAwayFromZero) :
    (∃ Ns : Nat, ∀ n : Nat, Ns ≤ n → 0 < (a.approx n).toRat)
    ∨ (∃ Ns : Nat, ∀ n : Nat, Ns ≤ n → (a.approx n).toRat < 0) := by
  obtain ⟨k₀, N₀, hN₀⟩ := h_baz
  obtain ⟨μ, hμ⟩ := h_cauchy
  -- Cauchy level k' = 2*k₀ + 2 → pairwise distance < 1/(2k₀+3)
  set k' : Nat := 2 * k₀ + 2 with hk'_def
  set N : Nat := max N₀ (μ k') with hN_def
  -- Helpful arithmetic facts
  have h_k₀_nn : (0 : Rat) ≤ (k₀ : Rat) := by exact_mod_cast Nat.zero_le k₀
  have h_k1_pos : (0 : Rat) < (k₀ : Rat) + 1 := by linarith
  have h_2k3_pos : (0 : Rat) < 2 * (k₀ : Rat) + 3 := by linarith
  -- Useful inequality: 1/(2k₀+3) + 1/(2k₀+3) ≤ 1/(k₀+1)
  -- Equivalent: 2/(2k₀+3) ≤ 1/(k₀+1) iff 2*(k₀+1) ≤ 2k₀+3, i.e., 2 ≤ 3.
  have h_two_recip_le_recip :
      1 / (2 * (k₀ : Rat) + 3) + 1 / (2 * (k₀ : Rat) + 3) ≤ 1 / ((k₀ : Rat) + 1) := by
    have h_combined : 1 / (2 * (k₀ : Rat) + 3) + 1 / (2 * (k₀ : Rat) + 3)
                    = 2 / (2 * (k₀ : Rat) + 3) := by ring
    rw [h_combined]
    rw [div_le_div_iff₀ h_2k3_pos h_k1_pos]
    nlinarith
  -- Sign at the pivot index N
  have hN_ge_N₀ : N₀ ≤ N := Nat.le_max_left _ _
  have hN_ge_μ : μ k' ≤ N := Nat.le_max_right _ _
  have h_aN_apart : 1 / ((k₀ : Rat) + 1) < |(a.approx N).toRat| := by
    have h := hN₀ N hN_ge_N₀
    unfold TauRat.lt at h
    rw [TauRat.ofNatRecip_toRat, TauRat.toRat_abs] at h
    exact h
  -- Either a.approx N > 0 or < 0 (since |a.approx N| > δ > 0).
  have h_aN_ne : (a.approx N).toRat ≠ 0 := by
    intro h_zero
    rw [h_zero, abs_zero] at h_aN_apart
    have h_recip_pos : (0 : Rat) < 1 / ((k₀ : Rat) + 1) := div_pos (by norm_num) h_k1_pos
    linarith
  -- Helper: bound on |a.approx n - a.approx N| for n ≥ N
  have h_close_pair : ∀ n : Nat, N ≤ n →
      |(a.approx n).toRat - (a.approx N).toRat| < 1 / (2 * (k₀ : Rat) + 3) := by
    intro n hn
    have h_n_ge_μ : μ k' ≤ n := Nat.le_trans hN_ge_μ hn
    have h := hμ k' n N h_n_ge_μ hN_ge_μ
    unfold TauRat.lt at h
    rw [TauRat.toRat_abs, toRat_sub, TauRat.ofNatRecip_toRat] at h
    -- 1/((k':Nat)+1 : Rat) = 1/(2k₀+3)
    have h_cast : ((k' : Rat) + 1) = 2 * (k₀ : Rat) + 3 := by
      show ((2 * k₀ + 2 : Nat) : Rat) + 1 = 2 * (k₀ : Rat) + 3
      push_cast; ring
    rw [h_cast] at h
    exact h
  rcases lt_or_gt_of_ne h_aN_ne with h_neg | h_pos
  · -- a.approx N < 0: prove uniformly negative past N
    right
    refine ⟨N, fun n hn => ?_⟩
    have h_diff := h_close_pair n hn
    -- Need: a.approx n < 0
    -- We have a.approx N < 0 and |a.approx N| > δ, so a.approx N < -δ.
    rw [abs_of_neg h_neg] at h_aN_apart
    -- h_aN_apart : 1/(k₀+1) < -(a.approx N)
    -- So a.approx N < -1/(k₀+1) ≤ -2/(2k₀+3)
    -- And a.approx n < a.approx N + 1/(2k₀+3) < -2/(2k₀+3) + 1/(2k₀+3) = -1/(2k₀+3) < 0.
    have h_diff_bound : (a.approx n).toRat - (a.approx N).toRat < 1 / (2 * (k₀ : Rat) + 3) := by
      have := abs_lt.mp h_diff
      linarith [this.2]
    have h_recip_pos : (0 : Rat) < 1 / (2 * (k₀ : Rat) + 3) :=
      div_pos (by norm_num) h_2k3_pos
    nlinarith [h_aN_apart, h_two_recip_le_recip, h_diff_bound, h_recip_pos]
  · -- a.approx N > 0: prove uniformly positive past N
    left
    refine ⟨N, fun n hn => ?_⟩
    have h_diff := h_close_pair n hn
    rw [abs_of_pos h_pos] at h_aN_apart
    -- h_aN_apart : 1/(k₀+1) < a.approx N
    -- So a.approx N > 2/(2k₀+3)
    -- And a.approx n > a.approx N - 1/(2k₀+3) > 2/(2k₀+3) - 1/(2k₀+3) = 1/(2k₀+3) > 0.
    have h_diff_bound : -(1 / (2 * (k₀ : Rat) + 3)) < (a.approx n).toRat - (a.approx N).toRat := by
      have := abs_lt.mp h_diff
      linarith [this.1]
    have h_recip_pos : (0 : Rat) < 1 / (2 * (k₀ : Rat) + 3) :=
      div_pos (by norm_num) h_2k3_pos
    nlinarith [h_aN_apart, h_two_recip_le_recip, h_diff_bound, h_recip_pos]

-- ============================================================
-- PART 8: PURE-RAT NEWTON DYNAMICS (Wave R8i)
--
-- Pure-Rat lemmas about the Newton iteration `step(t) = (t + a/t)/2`,
-- to be combined with `TauRat.sqrtNewtonStep_toRat` and
-- `TauRat.sqrtIter_lower_bound` in `TauRealSqrt.lean` by Wave R8j.
--
-- These live here (not in TauRealSqrt) because TauRealSqrt imports
-- this file. The R8j caller will iterate them through `sqrtIter` by
-- induction, using `sqrtNewtonStep_toRat` to unfold each step.
-- ============================================================

/-- One pure-Rat Newton step `step(t) = (t + a/t)/2` is upper-bounded by
    `max(t, M/δ)` whenever `a ≤ M` and `δ ≤ t` with `δ > 0`.

    Proof: `(t + a/t)/2 ≤ (t + M/δ)/2 ≤ max(t, M/δ)` (average ≤ max).

    R8j use: iterate over `sqrtIter` by induction, combining with
    `sqrtIter_lower_bound` to get `δ ≤ x_k` at each step. -/
theorem Rat.newton_step_upper_bound {t a M δ : Rat}
    (h_t_ge_δ : δ ≤ t) (h_δ_pos : 0 < δ)
    (h_a_le_M : a ≤ M) (h_a_nn : 0 ≤ a) :
    (t + a / t) / 2 ≤ max t (M / δ) := by
  have h_t_pos : 0 < t := lt_of_lt_of_le h_δ_pos h_t_ge_δ
  have h_M_nn : 0 ≤ M := le_trans h_a_nn h_a_le_M
  -- Step 1: a / t ≤ M / δ
  have h_div_le : a / t ≤ M / δ := by
    rw [div_le_div_iff₀ h_t_pos h_δ_pos]
    nlinarith
  -- Step 2: average ≤ max(t, M/δ)
  rcases lt_or_ge t (M / δ) with h_lt | h_ge
  · rw [max_eq_right (le_of_lt h_lt)]
    linarith
  · rw [max_eq_left h_ge]
    have h_div_le_t : a / t ≤ t := le_trans h_div_le h_ge
    linarith

/-- The Newton step preserves the upper bound `max(seed, M/δ)`:
    if `t ≤ U` where `U = max(seed, M/δ)` and `t ≥ δ > 0`, then
    `step(t) ≤ U`. -/
theorem Rat.newton_step_preserves_upper {t a U δ M : Rat}
    (h_t_ge_δ : δ ≤ t) (h_δ_pos : 0 < δ)
    (h_a_le_M : a ≤ M) (h_a_nn : 0 ≤ a)
    (h_U_ge_t : t ≤ U) (h_U_ge_M_div_δ : M / δ ≤ U) :
    (t + a / t) / 2 ≤ U := by
  have h_step := Rat.newton_step_upper_bound h_t_ge_δ h_δ_pos h_a_le_M h_a_nn
  have h_max_le : max t (M / δ) ≤ U := max_le h_U_ge_t h_U_ge_M_div_δ
  linarith

-- ============================================================
-- PART 9: PURE-RAT NEWTON ERROR RECURRENCE (Wave R8i)
--
-- The master quadratic-decay identity for Newton's method, stated at
-- the pure-Rat level. R8j combines this with sqrtNewtonStep_toRat to
-- iterate the squared error |x_k² - a| through sqrtIter.
-- ============================================================

/-- Pure-Rat Newton error-squared recurrence:
    `((x + a/x)/2)² − a = (x² − a)² / (2x)²` when `x ≠ 0`.

    This is the master identity driving Newton's quadratic convergence.
    Discharged by `field_simp` + `ring`. -/
theorem Rat.newton_step_error_sq {a x : Rat} (hx : x ≠ 0) :
    ((x + a / x) / 2) ^ 2 - a = (x ^ 2 - a) ^ 2 / (2 * x) ^ 2 := by
  field_simp
  ring

/-- Quadratic shrinkage bound: with `δ ≤ x` and `δ > 0`, the new squared
    error is bounded by `(x² − a)² / (4 δ²)`.

    Used by R8j to iterate `|x_{k+1}² − a| ≤ |x_k² − a|² / (4 δ²)`
    through `sqrtIter`. -/
theorem Rat.newton_step_error_sq_le {a x δ : Rat}
    (h_x_ge_δ : δ ≤ x) (h_δ_pos : 0 < δ) :
    ((x + a / x) / 2) ^ 2 - a ≤ (x ^ 2 - a) ^ 2 / (4 * δ ^ 2) := by
  have h_x_pos : 0 < x := lt_of_lt_of_le h_δ_pos h_x_ge_δ
  have h_x_ne : x ≠ 0 := ne_of_gt h_x_pos
  rw [Rat.newton_step_error_sq h_x_ne]
  -- Goal: (x² − a)² / (2x)² ≤ (x² − a)² / (4 δ²)
  -- Note (2x)² = 4 x² ≥ 4 δ² since x ≥ δ > 0
  have h_sq_nn : 0 ≤ (x ^ 2 - a) ^ 2 := sq_nonneg _
  have h_2x_sq : (2 * x) ^ 2 = 4 * x ^ 2 := by ring
  have h_4δ_sq_pos : 0 < 4 * δ ^ 2 := by positivity
  have h_4x_sq_pos : 0 < 4 * x ^ 2 := by positivity
  have h_denom_le : 4 * δ ^ 2 ≤ 4 * x ^ 2 := by nlinarith
  rw [h_2x_sq]
  -- (x²-a)² / (4 x²) ≤ (x²-a)² / (4 δ²) iff (since (x²-a)² ≥ 0) 4 δ² ≤ 4 x²
  exact div_le_div_of_nonneg_left h_sq_nn h_4δ_sq_pos h_denom_le

/-- Absolute-value version of the quadratic shrinkage bound:
    `|step² − a| ≤ |x² − a|² / (4 δ²)`.

    The squared form `(x² − a)² = |x² − a|²` cancels the absolute-value
    on the right. -/
theorem Rat.newton_step_abs_error_sq_le {a x δ : Rat}
    (h_x_ge_δ : δ ≤ x) (h_δ_pos : 0 < δ)
    (h_a_le_x_sq : a ≤ x ^ 2) :
    ((x + a / x) / 2) ^ 2 - a ≤ |x ^ 2 - a| ^ 2 / (4 * δ ^ 2) := by
  have h_step := Rat.newton_step_error_sq_le (a := a) h_x_ge_δ h_δ_pos
  have h_abs_eq : |x ^ 2 - a| = x ^ 2 - a := abs_of_nonneg (by linarith)
  rw [h_abs_eq]
  exact h_step

-- ============================================================
-- PART 10: TOWER DECAY OF AN ABSTRACT QUADRATIC RECURRENCE (Wave R8i)
--
-- Pure-Rat closed-form bound on any sequence satisfying
-- `e_{k+1} ≤ e_k² / C`. Composed with the per-step Newton bound from
-- Part 9, this gives R8j the tower-exponent decay needed to close
-- `sqrt_isCauchy` and `sqrt_sq` against the existing
-- `Rat.one_div_tower_pow_lt_recip` Cauchy bound.
-- ============================================================

/-- Abstract quadratic-recurrence tower bound: if `e_{k+1} ≤ e_k² / C`
    with `0 < C` and `0 ≤ e_k` for every `k`, and `e_0 ≤ C`, then for
    every `k`: `e_k ≤ C * (e_0 / C) ^ (2^k)`.

    Proof: induction on `k`. Step uses `e_{k+1} ≤ e_k² / C
    ≤ (C (e_0/C)^{2^k})² / C = C (e_0/C)^{2 · 2^k} = C (e_0/C)^{2^{k+1}}`.
-/
theorem Rat.quadratic_recurrence_tower_bound
    (e : Nat → Rat) (C : Rat) (hC : 0 < C)
    (h_nn : ∀ k, 0 ≤ e k)
    (h_rec : ∀ k, e (k + 1) ≤ (e k) ^ 2 / C)
    (h_e0_le : e 0 ≤ C) :
    ∀ k, e k ≤ C * (e 0 / C) ^ (2 ^ k) := by
  intro k
  induction k with
  | zero =>
    -- 2^0 = 1, so goal is e 0 ≤ C * (e 0 / C)^1 = C * (e 0 / C) = e 0
    show e 0 ≤ C * (e 0 / C) ^ (2 ^ 0)
    have h_pow_zero : (2 : Nat) ^ 0 = 1 := by norm_num
    rw [h_pow_zero, pow_one]
    have h_C_ne : C ≠ 0 := ne_of_gt hC
    rw [mul_div_cancel₀ _ h_C_ne]
  | succ k ih =>
    have h_step := h_rec k
    -- Goal: e (k+1) ≤ C * (e 0 / C)^(2^(k+1))
    -- Have: e (k+1) ≤ e_k² / C ≤ (C * (e_0/C)^(2^k))² / C
    have h_e0_div_nn : 0 ≤ e 0 / C := div_nonneg (h_nn 0) (le_of_lt hC)
    have h_e0_div_le_one : e 0 / C ≤ 1 := by
      rw [div_le_one hC]; exact h_e0_le
    have h_pow_nn : 0 ≤ (e 0 / C) ^ (2 ^ k) := pow_nonneg h_e0_div_nn _
    have h_C_target_nn : 0 ≤ C * (e 0 / C) ^ (2 ^ k) := mul_nonneg (le_of_lt hC) h_pow_nn
    -- e_k² ≤ (C (e_0/C)^(2^k))²  (square monotone for nonneg)
    have h_sq_mono : (e k) ^ 2 ≤ (C * (e 0 / C) ^ (2 ^ k)) ^ 2 :=
      sq_le_sq' (by linarith [h_nn k]) ih
    -- Then divide by C > 0
    have h_div_le : (e k) ^ 2 / C ≤ (C * (e 0 / C) ^ (2 ^ k)) ^ 2 / C := by
      rw [div_le_div_iff₀ hC hC]
      nlinarith [h_sq_mono]
    -- Simplify (C * x)² / C = C * x²
    have h_C_ne : C ≠ 0 := ne_of_gt hC
    have h_simp : (C * (e 0 / C) ^ (2 ^ k)) ^ 2 / C
                = C * ((e 0 / C) ^ (2 ^ k)) ^ 2 := by
      field_simp
    -- ((e 0 / C) ^ (2^k))^2 = (e 0 / C) ^ (2 * 2^k) = (e 0 / C) ^ (2^(k+1))
    have h_pow : ((e 0 / C) ^ (2 ^ k)) ^ 2 = (e 0 / C) ^ (2 ^ (k + 1)) := by
      rw [← pow_mul]
      have h_exp_eq : 2 ^ k * 2 = 2 ^ (k + 1) := by
        rw [pow_succ]
      rw [h_exp_eq]
    have h_chain : e (k + 1) ≤ C * ((e 0 / C) ^ (2 ^ k)) ^ 2 := by
      calc e (k + 1) ≤ (e k) ^ 2 / C := h_step
        _ ≤ (C * (e 0 / C) ^ (2 ^ k)) ^ 2 / C := h_div_le
        _ = C * ((e 0 / C) ^ (2 ^ k)) ^ 2 := h_simp
    rw [h_pow] at h_chain
    exact h_chain

/-- Convenient corollary: if additionally `e 0 ≤ C / 2`, then
    `e k ≤ C * (1/2) ^ (2^k)`. Combined with
    `Rat.one_div_tower_pow_lt_recip`, this gives R8j the tower bound
    for any tolerance level. -/
theorem Rat.quadratic_recurrence_half_tower
    (e : Nat → Rat) (C : Rat) (hC : 0 < C)
    (h_nn : ∀ k, 0 ≤ e k)
    (h_rec : ∀ k, e (k + 1) ≤ (e k) ^ 2 / C)
    (h_e0_le_half : e 0 ≤ C / 2) :
    ∀ k, e k ≤ C * (1 / 2) ^ (2 ^ k) := by
  intro k
  have h_e0_le : e 0 ≤ C := le_trans h_e0_le_half (by linarith)
  have h_main := Rat.quadratic_recurrence_tower_bound e C hC h_nn h_rec h_e0_le k
  have h_e0_div_le : e 0 / C ≤ 1 / 2 := by
    rw [div_le_div_iff₀ hC (by norm_num : (0:Rat) < 2)]
    linarith
  have h_e0_div_nn : 0 ≤ e 0 / C := div_nonneg (h_nn 0) (le_of_lt hC)
  have h_pow_mono : (e 0 / C) ^ (2 ^ k) ≤ (1 / 2) ^ (2 ^ k) :=
    pow_le_pow_left₀ h_e0_div_nn h_e0_div_le _
  have h_C_pos := hC
  calc e k ≤ C * (e 0 / C) ^ (2 ^ k) := h_main
    _ ≤ C * (1 / 2) ^ (2 ^ k) := by
      apply mul_le_mul_of_nonneg_left h_pow_mono (le_of_lt h_C_pos)

end Tau.Boundary
