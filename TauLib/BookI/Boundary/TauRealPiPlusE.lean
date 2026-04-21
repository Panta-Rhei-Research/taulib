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

end Tau.Boundary
