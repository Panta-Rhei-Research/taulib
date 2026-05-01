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

end Tau.Boundary
