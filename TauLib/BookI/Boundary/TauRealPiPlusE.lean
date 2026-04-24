import TauLib.BookI.Boundary.TauRealPi
import TauLib.BookI.Boundary.TauRealE
import Mathlib.Tactic.Ring
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity

/-!
# TauLib.BookI.Boundary.TauRealPiPlusE

`(TauReal.pi + TauReal.e)` is bounded away from zero — the
constructive apartness witness needed by Wave 4 to define
`2 / (π + e)` as a well-behaved TauReal.

## Registry Cross-References

- [I.D84] TauReal, [I.D111] TauReal.IsCauchy, [I.D114] inv / div layer
- [I.D117] TauReal.e (Wave 3b)
- [I.D118] TauReal.pi (Wave 3c)

## Mathematical Content

**Wave 3d** of the TauReal infrastructure (see `ROADMAP-3-HINGES.md`).

Both `pi_partial` and `e_partial` are monotone-increasing sums of
all-positive TauRat terms (Wave 3b: `e_term k = 1/k! > 0`;
Wave 3c: `pi_pair_term k = 8/((4k+1)(4k+3)) > 0`).  At every index
`n ≥ 1`:

- `e_partial n ≥ e_partial 1 = 1`
- `pi_partial n ≥ pi_partial 1 = 8/3`
- Sum  ≥ 11/3  >  1  >  1/(0+1)

This gives `BoundedAwayFromZero` with the simplest possible witness:
`k = 0` (tolerance `1/(0+1) = 1`), `N = 1` (starting index).

Wave 4 can then invoke `TauReal.inv (TauReal.pi.add TauReal.e)` safely
(via `TauReal.mul_inv_cancel`) to construct `2 / (π + e)` and state
the `iota_tau = 2 / (π + e)` identity as a well-formed theorem.
-/

set_option autoImplicit false

namespace Tau.Boundary

open Tau.Denotation

-- ============================================================
-- PART 1: MONOTONICITY OF pi_partial AND e_partial
-- ============================================================

/-- `pi_partial` is monotone increasing at the `toRat` level. -/
theorem TauRat.pi_partial_monotone {m n : Nat} (hmn : m ≤ n) :
    (TauRat.pi_partial m).toRat ≤ (TauRat.pi_partial n).toRat := by
  induction n with
  | zero =>
    have : m = 0 := by omega
    subst this
    exact _root_.le_refl _
  | succ n ih =>
    by_cases h : m = n + 1
    · subst h; exact _root_.le_refl _
    · have hmn' : m ≤ n := by omega
      have ih' := ih hmn'
      have h_succ : TauRat.pi_partial (n + 1) =
                    (TauRat.pi_partial n).add (TauRat.pi_pair_term n) := by
        show TauRat.sum TauRat.pi_pair_term (n + 1) = _
        rfl
      rw [h_succ, toRat_add]
      have h_pos := _root_.le_of_lt (TauRat.pi_pair_term_pos n)
      linarith

/-- `e_partial` is monotone increasing at the `toRat` level. -/
theorem TauRat.e_partial_monotone {m n : Nat} (hmn : m ≤ n) :
    (TauRat.e_partial m).toRat ≤ (TauRat.e_partial n).toRat := by
  induction n with
  | zero =>
    have : m = 0 := by omega
    subst this
    exact _root_.le_refl _
  | succ n ih =>
    by_cases h : m = n + 1
    · subst h; exact _root_.le_refl _
    · have hmn' : m ≤ n := by omega
      have ih' := ih hmn'
      have h_succ : TauRat.e_partial (n + 1) =
                    (TauRat.e_partial n).add (TauRat.e_term n) := by
        show TauRat.sum TauRat.e_term (n + 1) = _
        rfl
      rw [h_succ, toRat_add]
      have h_pos := _root_.le_of_lt (TauRat.e_term_pos n)
      linarith

-- ============================================================
-- PART 2: VALUES AT INDEX 1
-- ============================================================

/-- `pi_partial 1 = 8/3` at the `toRat` level. -/
theorem TauRat.pi_partial_one_toRat :
    (TauRat.pi_partial 1).toRat = 8 / 3 := by
  show (TauRat.sum TauRat.pi_pair_term 1).toRat = 8 / 3
  -- sum f 1 = sum f 0 + f 0 = 0 + f 0
  rw [TauRat.sum_succ, toRat_add, TauRat.sum_zero, toRat_zero]
  -- goal: 0 + (pi_pair_term 0).toRat = 8/3
  rw [TauRat.pi_pair_term_toRat]
  -- 0 + 8 / (((4*0+1)*(4*0+3) : Nat) : Rat) = 8/3
  push_cast
  norm_num

/-- `e_partial 1 = 1` at the `toRat` level. -/
theorem TauRat.e_partial_one_toRat :
    (TauRat.e_partial 1).toRat = 1 := by
  show (TauRat.sum TauRat.e_term 1).toRat = 1
  rw [TauRat.sum_succ, toRat_add, TauRat.sum_zero, toRat_zero]
  rw [TauRat.e_term_toRat]
  -- goal: 0 + 1 / (Nat.factorial 0 : Rat) = 1
  simp [Nat.factorial]

-- ============================================================
-- PART 3: LOWER BOUND  pi_partial n + e_partial n ≥ 11/3  for n ≥ 1
-- ============================================================

theorem TauReal.pi_plus_e_partial_lower_bound (n : Nat) (hn : 1 ≤ n) :
    (TauRat.pi_partial n).toRat + (TauRat.e_partial n).toRat ≥ 11 / 3 := by
  have h_pi_mono : (TauRat.pi_partial 1).toRat ≤ (TauRat.pi_partial n).toRat :=
    TauRat.pi_partial_monotone hn
  have h_e_mono : (TauRat.e_partial 1).toRat ≤ (TauRat.e_partial n).toRat :=
    TauRat.e_partial_monotone hn
  have h_pi_1 := TauRat.pi_partial_one_toRat
  have h_e_1 := TauRat.e_partial_one_toRat
  linarith

-- ============================================================
-- PART 4: BoundedAwayFromZero FOR π + e
-- ============================================================

/-- `TauReal.pi + TauReal.e` is bounded away from zero — the sum
    exceeds `1/(0+1) = 1` at every index `n ≥ 1`, and with room to
    spare (we could use any tolerance `1/(k+1)` for small `k` by
    taking `N = 1`).  We pick the minimal witness:
    `modulus = 0`, `N = 1`. -/
theorem TauReal.pi_plus_e_boundedAwayFromZero :
    (TauReal.pi.add TauReal.e).BoundedAwayFromZero := by
  refine ⟨0, 1, fun n hn => ?_⟩
  -- Goal: TauRat.lt (ofNatRecip 0) ((pi.add e).approx n).abs
  unfold TauRat.lt
  rw [TauRat.ofNatRecip_toRat]
  -- ofNatRecip 0 .toRat = 1 / (0 + 1) = 1
  show (1 : Rat) / ((0 : Nat) + 1) < ((TauReal.pi.add TauReal.e).approx n).abs.toRat
  -- (pi.add e).approx n = (pi.approx n).add (e.approx n) = pi_partial n + e_partial n  (as TauRat)
  have h_add_approx :
      ((TauReal.pi.add TauReal.e).approx n).toRat
        = (TauRat.pi_partial n).toRat + (TauRat.e_partial n).toRat := by
    show ((TauReal.pi.approx n).add (TauReal.e.approx n)).toRat = _
    rw [toRat_add]
    rfl
  -- The value is positive; abs = value at toRat level.
  have h_pos : 0 < ((TauReal.pi.add TauReal.e).approx n).toRat := by
    rw [h_add_approx]
    have h_bound := TauReal.pi_plus_e_partial_lower_bound n hn
    linarith
  rw [TauRat.toRat_abs, abs_of_pos h_pos, h_add_approx]
  -- Goal: 1 / (0 + 1) < pi_partial n .toRat + e_partial n .toRat
  have h_bound := TauReal.pi_plus_e_partial_lower_bound n hn
  push_cast
  linarith

-- ============================================================
-- PART 5: NON-NEGATIVITY OF pi_partial AND e_partial
-- ============================================================

/-- `pi_partial n ≥ 0` at the `toRat` level, from monotonicity and
    `pi_partial 0 = 0`.  All terms `pi_pair_term k` are positive, so
    their prefix sum is non-negative. -/
theorem TauRat.pi_partial_nonneg (n : Nat) :
    0 ≤ (TauRat.pi_partial n).toRat := by
  have h_zero : (TauRat.pi_partial 0).toRat = 0 := by
    show (TauRat.sum _ 0).toRat = 0
    rw [TauRat.sum_zero, toRat_zero]
  have h_mono := TauRat.pi_partial_monotone (Nat.zero_le n)
  linarith

/-- `e_partial n ≥ 0` at the `toRat` level, from monotonicity and
    `e_partial 0 = 0`.  All terms `e_term k` are positive, so their
    prefix sum is non-negative. -/
theorem TauRat.e_partial_nonneg (n : Nat) :
    0 ≤ (TauRat.e_partial n).toRat := by
  have h_zero : (TauRat.e_partial 0).toRat = 0 := by
    show (TauRat.sum _ 0).toRat = 0
    rw [TauRat.sum_zero, toRat_zero]
  have h_mono := TauRat.e_partial_monotone (Nat.zero_le n)
  linarith

-- ============================================================
-- PART 6: UPPER BOUNDS VIA TELESCOPING
-- ============================================================

/-- **Upper bound on `pi_partial`**: for every `n`,
    `pi_partial n .toRat ≤ 19/6`.  Proof: for `n = 0`, value is 0;
    for `n ≥ 1`, telescope via `sum_sub_toRat_eq_sumFromTo` and apply
    `sumFromTo_pi_pair_term_bound` with starting index `1`:

      `pi_partial n .toRat = pi_partial 1 .toRat + sumFromTo pi_pair_term 1 n .toRat`
                          `≤ 8/3 + (1/2 - 1/(2n)) ≤ 8/3 + 1/2 = 19/6 < 4`.

    The bound `19/6 ≈ 3.17 < π ≈ 3.14159...` is loose by design; we just
    need *some* integer bound below 7 for the `(π + e)` combination. -/
theorem TauRat.pi_partial_le_19_div_6 (n : Nat) :
    (TauRat.pi_partial n).toRat ≤ 19 / 6 := by
  by_cases hn : 1 ≤ n
  · -- Case n ≥ 1: telescope via sum_sub_toRat_eq_sumFromTo
    have h_tele := TauRat.sum_sub_toRat_eq_sumFromTo TauRat.pi_pair_term 1 n hn
    have h_sum_bound :
        (TauRat.sumFromTo TauRat.pi_pair_term 1 n).toRat
          ≤ 1 / (2 * (1 : Rat)) - 1 / (2 * (n : Rat)) :=
      TauReal.sumFromTo_pi_pair_term_bound 1 (by norm_num) n hn
    have h_pi1 : (TauRat.pi_partial 1).toRat = 8 / 3 :=
      TauRat.pi_partial_one_toRat
    have h_n_pos : (0 : Rat) < (n : Rat) := by exact_mod_cast hn
    have h_2n_pos : (0 : Rat) < 2 * (n : Rat) := by linarith
    have h_recip_nonneg : (0 : Rat) ≤ 1 / (2 * (n : Rat)) := by
      have h_one_nn : (0 : Rat) ≤ 1 := by norm_num
      exact div_nonneg h_one_nn h_2n_pos.le
    -- Bound the ranged sum by `1/2` directly via calc, avoiding
    -- reliance on linarith's ability to normalise `1 / (2 * 1) = 1/2`.
    have h_sum_le_half :
        (TauRat.sumFromTo TauRat.pi_pair_term 1 n).toRat ≤ 1 / 2 := by
      have h_21 : (1 : Rat) / (2 * (1 : Rat)) = 1 / 2 := by norm_num
      have h_step :
          (1 : Rat) / (2 * (1 : Rat)) - 1 / (2 * (n : Rat)) ≤ 1 / 2 := by
        rw [h_21]; linarith
      linarith [h_sum_bound]
    have h_pi_eq :
        (TauRat.pi_partial n).toRat =
          (TauRat.pi_partial 1).toRat + (TauRat.sumFromTo TauRat.pi_pair_term 1 n).toRat := by
      show (TauRat.sum TauRat.pi_pair_term n).toRat =
           (TauRat.sum TauRat.pi_pair_term 1).toRat + _
      linarith [h_tele]
    rw [h_pi_eq, h_pi1]
    linarith
  · -- Case n = 0: value is 0 ≤ 19/6 trivially
    push_neg at hn
    have hn0 : n = 0 := by omega
    subst hn0
    show (TauRat.sum TauRat.pi_pair_term 0).toRat ≤ 19 / 6
    rw [TauRat.sum_zero, toRat_zero]
    norm_num

/-- **Upper bound on `e_partial`**: for every `n`,
    `e_partial n .toRat ≤ 3`.  Proof: for `n = 0`, value is 0; for
    `n ≥ 1`, telescope via `sum_sub_toRat_eq_sumFromTo` and apply
    `sumFromTo_e_term_bound` with starting index `1`:

      `e_partial n .toRat = e_partial 1 .toRat + sumFromTo e_term 1 n .toRat`
                         `≤ 1 + (2 - 4/2^n) ≤ 3`.

    The bound `3 > e ≈ 2.718` is loose; tight enough for the
    `(π + e) ≤ 7` combination. -/
theorem TauRat.e_partial_le_three (n : Nat) :
    (TauRat.e_partial n).toRat ≤ 3 := by
  by_cases hn : 1 ≤ n
  · -- Case n ≥ 1
    have h_tele := TauRat.sum_sub_toRat_eq_sumFromTo TauRat.e_term 1 n hn
    have h_sum_bound :
        (TauRat.sumFromTo TauRat.e_term 1 n).toRat
          ≤ 4 / (2 ^ (1 : Nat) : Rat) - 4 / (2 ^ n : Rat) :=
      TauReal.sumFromTo_e_term_bound 1 (by norm_num) n hn
    have h_e1 : (TauRat.e_partial 1).toRat = 1 :=
      TauRat.e_partial_one_toRat
    have h_pow_pos : (0 : Rat) < 2 ^ n := by positivity
    have h_recip_nonneg : (0 : Rat) ≤ 4 / (2 ^ n : Rat) := by
      have h_4_nn : (0 : Rat) ≤ 4 := by norm_num
      exact div_nonneg h_4_nn h_pow_pos.le
    -- Bound the ranged sum by 2 directly via calc, avoiding reliance
    -- on linarith's ability to normalise `4 / 2^1 = 2`.
    have h_sum_le_2 : (TauRat.sumFromTo TauRat.e_term 1 n).toRat ≤ 2 := by
      have h_base : (4 : Rat) / (2 ^ (1 : Nat) : Rat) = 2 := by norm_num
      have h_step :
          (4 : Rat) / (2 ^ (1 : Nat) : Rat) - 4 / (2 ^ n : Rat) ≤ 2 := by
        rw [h_base]; linarith
      linarith [h_sum_bound]
    have h_e_eq :
        (TauRat.e_partial n).toRat =
          (TauRat.e_partial 1).toRat + (TauRat.sumFromTo TauRat.e_term 1 n).toRat := by
      show (TauRat.sum TauRat.e_term n).toRat =
           (TauRat.sum TauRat.e_term 1).toRat + _
      linarith [h_tele]
    rw [h_e_eq, h_e1]
    linarith
  · -- Case n = 0: value is 0 ≤ 3 trivially
    push_neg at hn
    have hn0 : n = 0 := by omega
    subst hn0
    show (TauRat.sum TauRat.e_term 0).toRat ≤ 3
    rw [TauRat.sum_zero, toRat_zero]
    norm_num

-- ============================================================
-- PART 7: UPPER BOUND ON (π + e).approx n
-- ============================================================

/-- `(π + e).approx n .toRat ≥ 0`: the partial sum is non-negative. -/
theorem TauReal.pi_plus_e_approx_nonneg (n : Nat) :
    0 ≤ ((TauReal.pi.add TauReal.e).approx n).toRat := by
  show 0 ≤ ((TauReal.pi.approx n).add (TauReal.e.approx n)).toRat
  rw [toRat_add]
  have h_pi_nonneg : 0 ≤ (TauReal.pi.approx n).toRat :=
    TauRat.pi_partial_nonneg n
  have h_e_nonneg : 0 ≤ (TauReal.e.approx n).toRat :=
    TauRat.e_partial_nonneg n
  linarith

/-- **Master upper bound**: `(π + e).approx n .toRat ≤ 7` for every
    `n`.  Combines `pi_partial_le_19_div_6` and `e_partial_le_three`:
    `19/6 + 3 = 19/6 + 18/6 = 37/6 ≈ 6.17 ≤ 7`. -/
theorem TauReal.pi_plus_e_approx_le_seven (n : Nat) :
    ((TauReal.pi.add TauReal.e).approx n).toRat ≤ 7 := by
  show ((TauReal.pi.approx n).add (TauReal.e.approx n)).toRat ≤ 7
  rw [toRat_add]
  have h_pi := TauRat.pi_partial_le_19_div_6 n
  have h_e := TauRat.e_partial_le_three n
  -- pi.approx n = pi_partial n, e.approx n = e_partial n (definitional)
  show (TauReal.pi.approx n).toRat + (TauReal.e.approx n).toRat ≤ 7
  have h_pi_unfold : (TauReal.pi.approx n).toRat = (TauRat.pi_partial n).toRat := rfl
  have h_e_unfold : (TauReal.e.approx n).toRat = (TauRat.e_partial n).toRat := rfl
  rw [h_pi_unfold, h_e_unfold]
  linarith

/-- **The bound theorem consumed by `coupling_identity`**: for every
    `n`, the absolute value of `(π + e).approx n` is bounded above
    by `7`.  Since the approximation is non-negative
    (`pi_plus_e_approx_nonneg`), `abs = value`, and the bound is the
    pointwise `≤ 7` established above. -/
theorem TauReal.pi_plus_e_abs_le_seven (n : Nat) :
    ((TauReal.pi.add TauReal.e).approx n).abs.toRat ≤ 7 := by
  rw [TauRat.toRat_abs]
  have h_nonneg := TauReal.pi_plus_e_approx_nonneg n
  rw [abs_of_nonneg h_nonneg]
  exact TauReal.pi_plus_e_approx_le_seven n

end Tau.Boundary
