import TauLib.BookI.Boundary.TauRealDerivative
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity

/-!
# TauLib.BookI.Boundary.TauRealPowerSeriesDiff

**Wave Γ₈ Phase 2.6.B.2.β.4.9 — Module 2**: term-by-term differentiation
for the τ-canon power-series machinery.

This module ships, in successive waves, derivative rules for natural-number
powers `x^k` and (in later waves) the arctan-shape pair-term differentiation
needed for Module 3.

## Architectural context

Per `atlas/insights/2026-05-17-tau-canon-derivative-deep-forensic.md`,
the dyadic `TauReal.IsDerivAt` from Module 1 is the τ-canon-native
realization of I.D42 D-Differentiability (eventual constancy at finite
primorial stages). Module 2's power rule and term-by-term differentiation
operate entirely within this stabilization-at-depth paradigm — no ε-δ
machinery is introduced, and none is needed.

## Wave 1 — the square rule

Concrete proof of `IsDerivAt (fun x => fromTauRat (x · x)) a (2a)` on the
disk `2·|a.toRat| ≤ 1`. Uses `IsDerivAt_mul` (Module 1's Leibniz) with
both factors equal to `fun x => fromTauRat x` (the identity-style function
from `IsDerivAt_id`). The bound parameter `M = 2` accommodates the worst-case
dyadic step `dyadicStep 0 = 1`, which can shift the input by `+1`.

This wave establishes the **Leibniz-induction pattern** that subsequent waves
extend to cubic, fourth, and general k-th-power rules.
-/

set_option autoImplicit false

namespace Tau.Boundary

open Tau.Denotation

-- ============================================================
-- PART 1: HELPERS — Bound lemmas for the square rule
-- ============================================================

/-- `|fromTauRat q . approx N|.toRat ≤ |q.toRat|`: the `.approx N` of a
    constant-sequence TauReal is just `q`. -/
private theorem fromTauRat_approx_abs_toRat (q : TauRat) (N : Nat) :
    ((TauReal.fromTauRat q).approx N).abs.toRat = |q.toRat| := by
  show (q.abs).toRat = |q.toRat|
  rw [TauRat.toRat_abs]

/-- `|a + dyadicStep N| ≤ |a| + 1`: the worst-case dyadic step shift
    bound. `dyadicStep N = 1/2^N ≤ 1` for all `N ≥ 0`. -/
private theorem dyadicStep_shift_abs_le (a : TauRat) (N : Nat) :
    |((a.add (TauRat.dyadicStep N))).toRat| ≤ |a.toRat| + 1 := by
  rw [toRat_add, TauRat.dyadicStep_toRat]
  have h_pow_pos : (0 : Rat) < (2 : Rat)^N := by positivity
  have h_pow_ge_one : (1 : Rat) ≤ (2 : Rat)^N := by
    have h_nat : 1 ≤ 2^N := Nat.one_le_pow N 2 (by norm_num)
    have h_cast : ((1 : Nat) : Rat) ≤ ((2^N : Nat) : Rat) := by exact_mod_cast h_nat
    have h_left : ((1 : Nat) : Rat) = 1 := by norm_num
    have h_right : ((2^N : Nat) : Rat) = (2 : Rat)^N := by push_cast; ring
    linarith
  have h_step_le_one : (1 : Rat) / (2 : Rat)^N ≤ 1 := by
    rw [div_le_one h_pow_pos]; exact h_pow_ge_one
  have h_step_nn : (0 : Rat) ≤ 1 / (2 : Rat)^N := by positivity
  have h_abs_step : |(1 : Rat) / (2 : Rat)^N| = 1 / (2 : Rat)^N := abs_of_nonneg h_step_nn
  calc |a.toRat + 1 / (2 : Rat)^N|
      ≤ |a.toRat| + |1 / (2 : Rat)^N| := abs_add_le _ _
    _ = |a.toRat| + 1 / (2 : Rat)^N := by rw [h_abs_step]
    _ ≤ |a.toRat| + 1 := by linarith

-- ============================================================
-- PART 2: THE SQUARE RULE
-- ============================================================

/-- **[I.T-IsDerivAt-Sq]** Square rule for the TauReal derivative:

    `IsDerivAt (fun x => fromTauRat (x · x)) a ((1·a) + (a·1))`

    on the disk `2·|a.toRat| ≤ 1` (i.e., `|a.toRat| ≤ 1/2`).

    Proof strategy: apply `IsDerivAt_mul` (Module 1's Leibniz) with
    `f = g = fun x => fromTauRat x`, both having derivative `TauReal.one`
    by `IsDerivAt_id`. The bound parameter `M = 2` is chosen to cover
    the worst-case dyadic shift at depth `N = 0` (where `dyadicStep 0 = 1`,
    giving `|a + 1| ≤ 3/2 ≤ 2`).

    The resulting derivative `((TauReal.one.mul (fromTauRat a)).add
    ((fromTauRat a).mul TauReal.one))` is the unsimplified Leibniz form;
    consumers who need the cleaner `fromTauRat (a.add a)` form can apply
    a simplification congruence (deferred to a later wave). -/
theorem TauReal.IsDerivAt_sq (a : TauRat) (ha : 2 * |a.toRat| ≤ 1) :
    TauReal.IsDerivAt
      (fun x : TauRat => TauReal.fromTauRat (TauRat.mul x x))
      a
      ((TauReal.one.mul (TauReal.fromTauRat a)).add
        ((TauReal.fromTauRat a).mul TauReal.one)) := by
  -- The function `fun x => fromTauRat (x · x)` equals
  -- `fun x => (fromTauRat x).mul (fromTauRat x)` definitionally, so we
  -- can directly apply Leibniz to f = g = fromTauRat.
  have h_id : TauReal.IsDerivAt (fun x => TauReal.fromTauRat x) a TauReal.one :=
    TauReal.IsDerivAt_id a
  -- Bounds with M = 2:
  --   |a.toRat| ≤ 1/2 ≤ 2.
  --   |(a + dyadicStep N).toRat| ≤ |a.toRat| + 1 ≤ 3/2 ≤ 2.
  --   |TauReal.one.approx n .toRat| = 1 ≤ 2.
  have h_a_abs : |a.toRat| ≤ (1 : Rat)/2 := by linarith
  have h_a_le_M : |a.toRat| ≤ (2 : Rat) := by linarith
  -- Bound: |(fromTauRat a).approx n|.abs.toRat ≤ 2
  have h_bound_fa : ∀ n, ((TauReal.fromTauRat a).approx n).abs.toRat ≤ (2 : Nat) := by
    intro n
    rw [fromTauRat_approx_abs_toRat]
    have : (((2 : Nat) : Rat) : Rat) = 2 := by norm_num
    show |a.toRat| ≤ ((2 : Nat) : Rat)
    have : ((2 : Nat) : Rat) = 2 := by norm_num
    linarith
  -- Bound: |TauReal.one.approx n|.abs.toRat ≤ 2
  have h_bound_one : ∀ n, (TauReal.one.approx n).abs.toRat ≤ (2 : Nat) := by
    intro n
    show (TauRat.one.abs).toRat ≤ ((2 : Nat) : Rat)
    rw [TauRat.toRat_abs, toRat_one]
    have : ((2 : Nat) : Rat) = 2 := by norm_num
    rw [this]; norm_num
  -- Bound: |(fun x => fromTauRat x) (a + dyad).approx n|.abs.toRat ≤ 2
  have h_bound_g_at_steps :
      ∀ N n, (((fun x : TauRat => TauReal.fromTauRat x)
                (a.add (TauRat.dyadicStep N))).approx n).abs.toRat ≤ (2 : Nat) := by
    intro N n
    show ((TauReal.fromTauRat (a.add (TauRat.dyadicStep N))).approx n).abs.toRat
        ≤ ((2 : Nat) : Rat)
    rw [fromTauRat_approx_abs_toRat]
    have h_shift := dyadicStep_shift_abs_le a N
    have : ((2 : Nat) : Rat) = 2 := by norm_num
    rw [this]
    linarith
  -- Apply Leibniz with M = 2 and the bounds above.
  exact TauReal.IsDerivAt_mul (f := fun x => TauReal.fromTauRat x)
                              (g := fun x => TauReal.fromTauRat x)
                              (a := a) (L_f := TauReal.one) (L_g := TauReal.one)
    2 (by norm_num : 1 ≤ 2)
    h_bound_fa h_bound_fa h_bound_g_at_steps
    h_bound_one h_bound_one
    h_id h_id

end Tau.Boundary
