import TauLib.BookI.Boundary.TauRealInv
import TauLib.BookI.Boundary.TauRealAnalyticalHelpers
import Mathlib.Tactic.Ring
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity

/-!
# TauLib.BookI.Boundary.TauRealDerivative

The **TauReal derivative** predicate `IsDerivAt`, defined via the
dyadic-step difference quotient.

## Wave Γ₈ Phase 2.6.B.2.β.4.9 — Module 1

For a function `f : TauRat → TauReal`, the derivative at point `a : TauRat`
is the limit (as the step `h_N = 1/2^N` tends to zero) of the **scaled
difference quotient**

    (f(a + h_N) − f(a)) · 2^N

at TauReal-equivalence level. The "limit" is encoded constructively via
an explicit modulus `μ : Nat → Nat` such that for every tolerance `k`
and every step exponent `N ≥ μ k`, the difference quotient is within
`1/(k+1)` of the claimed derivative `L : TauReal` at depth `N`.

### Why dyadic steps `h_N = 1/2^N`?

* Matches the existing Cauchy infrastructure (`Rat.four_div_two_pow_lt_recip`
  workhorse from TauRealAnalyticalHelpers.lean).
* Provides natural sub-division for the discrete Gronwall lemma's dyadic
  grid argument (TauRealGronwall.lean).
* Native to `TauRat.ofNatRecip`: `ofNatRecip (2^N - 1) = 1/2^N` for `N ≥ 0`.

This module ships the **core definitions** (IsDerivAt, dyadic step
helpers). Linearity (sum/scalar), product (Leibniz), chain rules, and
the constant rule are queued for follow-up after the basic definition
infrastructure stabilises in downstream usage.
-/

set_option autoImplicit false

namespace Tau.Boundary

open Tau.Denotation

-- ============================================================
-- PART 1: HELPERS — TauRat constructions for dyadic steps
-- ============================================================

/-- The dyadic step `h_N = 1/2^N` as a TauRat.

    Using `TauRat.ofNatRecip (2^N - 1)`: since `ofNatRecip k = 1/(k+1)`,
    we get `1/(2^N - 1 + 1) = 1/2^N`. For `N = 0` this gives `1`, for
    `N ≥ 1` it gives the standard dyadic step. -/
def TauRat.dyadicStep (N : Nat) : TauRat :=
  TauRat.ofNatRecip (2^N - 1)

/-- `2^N` embedded as a TauRat with denominator 1. -/
def TauRat.twoPowN (N : Nat) : TauRat :=
  ⟨TauInt.fromNat (2^N), 1, Nat.one_pos⟩

/-- `dyadicStep N .toRat = 1 / 2^N`. -/
theorem TauRat.dyadicStep_toRat (N : Nat) :
    (TauRat.dyadicStep N).toRat = 1 / (2 : Rat)^N := by
  unfold TauRat.dyadicStep
  rw [TauRat.ofNatRecip_toRat]
  have h_pos : 1 ≤ 2^N := Nat.one_le_pow N 2 (by norm_num)
  have h_nat : (2^N - 1 + 1 : Nat) = 2^N := by omega
  have h_cast : (((2^N - 1 : Nat) : Rat) + 1) = (2 : Rat)^N := by
    have h_left : ((2^N - 1 + 1 : Nat) : Rat) = ((2^N : Nat) : Rat) := by
      exact_mod_cast h_nat
    have h_split : ((2^N - 1 + 1 : Nat) : Rat) = ((2^N - 1 : Nat) : Rat) + 1 := by
      push_cast; ring
    have h_pow : ((2^N : Nat) : Rat) = (2 : Rat)^N := by push_cast; ring
    linarith
  rw [h_cast]

/-- `twoPowN N .toRat = 2^N`. -/
theorem TauRat.twoPowN_toRat (N : Nat) :
    (TauRat.twoPowN N).toRat = (2 : Rat)^N := by
  unfold TauRat.twoPowN TauRat.toRat TauInt.toInt TauInt.fromNat
  push_cast
  ring

/-- `dyadicStep N · twoPowN N = 1` at Rat level (multiplicative inverses). -/
theorem TauRat.dyadicStep_mul_twoPowN_toRat (N : Nat) :
    (TauRat.dyadicStep N).toRat * (TauRat.twoPowN N).toRat = 1 := by
  rw [TauRat.dyadicStep_toRat, TauRat.twoPowN_toRat]
  have h_pos : (0 : Rat) < (2 : Rat)^N := by positivity
  field_simp

-- ============================================================
-- PART 2: IsDerivAt DEFINITION
-- ============================================================

/-- **[I.D-IsDerivAt]** `IsDerivAt f a L`: f has derivative L at TauRat point a.

    Constructively: there exists `μ : Nat → Nat` such that for every
    tolerance level `k` and step exponent `N ≥ μ k`, the scaled difference
    quotient

        (f(a + 1/2^N) − f(a)) · 2^N

    is within `1/(k+1)` of `L` at depth-N TauRat approximation level.

    The scaled-difference form (multiplying by `2^N` rather than dividing
    by `h_N`) avoids the need to invoke `TauReal.inv` and matches the
    discrete Gronwall lemma's natural step structure. -/
def TauReal.IsDerivAt (f : TauRat → TauReal) (a : TauRat) (L : TauReal) : Prop :=
  ∃ μ : Nat → Nat, ∀ k N : Nat, μ k ≤ N →
    TauRat.lt
      (((((f (a.add (TauRat.dyadicStep N))).sub (f a)).mul
            (TauReal.fromTauRat (TauRat.twoPowN N))).sub L).approx N).abs
      (TauRat.ofNatRecip k)

-- ============================================================
-- PART 3: CONSTANT RULE
-- ============================================================

/-- **[I.T-IsDerivAt-Const]** The constant function `fun _ => c` has
    derivative `TauReal.zero` at every point.

    Proof: `(c - c) · 2^N = 0` at TauReal level, so the scaled
    difference is zero in every approximation. Modulus is `fun _ => 0`. -/
theorem TauReal.IsDerivAt_const (c : TauReal) (a : TauRat) :
    TauReal.IsDerivAt (fun _ => c) a TauReal.zero := by
  refine ⟨fun _ => 0, fun k N _ => ?_⟩
  unfold TauRat.lt
  rw [TauRat.toRat_abs, TauRat.ofNatRecip_toRat]
  -- Compute the inner .toRat = 0 via step-by-step unfolding
  -- The expression at depth N: ((c - c) · 2^N - 0).approx N
  -- = TauRat.add ((c-c).mul ...).approx N (TauRat.negate TauRat.zero)
  -- = TauRat.add (TauRat.mul ((c-c).approx N) (...)) (...)
  -- = TauRat.mul (TauRat.add (c.approx N) (TauRat.negate (c.approx N))) ... etc.
  -- All toRat values cancel to 0.
  have h_zero : ((((((fun _ : TauRat => c) (a.add (TauRat.dyadicStep N))).sub
                  ((fun _ : TauRat => c) a)).mul
                (TauReal.fromTauRat (TauRat.twoPowN N))).sub
                TauReal.zero).approx N).toRat = 0 := by
    -- Beta-reduces (fun _ => c) applications
    show (((((c).sub c).mul
              (TauReal.fromTauRat (TauRat.twoPowN N))).sub
            TauReal.zero).approx N).toRat = 0
    -- Expand (.sub TauReal.zero).approx N
    show (TauRat.add
            (((c.sub c).mul (TauReal.fromTauRat (TauRat.twoPowN N))).approx N)
            ((TauReal.zero.negate).approx N)).toRat = 0
    rw [toRat_add]
    -- (TauReal.zero.negate).approx N .toRat = 0
    have h_neg_zero : ((TauReal.zero.negate).approx N).toRat = 0 := by
      show (TauRat.negate (TauReal.zero.approx N)).toRat = 0
      show (TauRat.negate TauRat.zero).toRat = 0
      rw [toRat_negate, toRat_zero]
      ring
    rw [h_neg_zero]
    -- ((c.sub c).mul ...).approx N .toRat = 0 · ... = 0
    have h_mul_zero :
        (((c.sub c).mul (TauReal.fromTauRat (TauRat.twoPowN N))).approx N).toRat = 0 := by
      show (TauRat.mul ((c.sub c).approx N)
              ((TauReal.fromTauRat (TauRat.twoPowN N)).approx N)).toRat = 0
      rw [toRat_mul]
      -- (c.sub c).approx N .toRat = 0 via add+negate cancellation
      have h_diff : ((c.sub c).approx N).toRat = 0 := by
        show ((c.add c.negate).approx N).toRat = 0
        show (TauRat.add (c.approx N) ((c.negate).approx N)).toRat = 0
        show (TauRat.add (c.approx N) (TauRat.negate (c.approx N))).toRat = 0
        rw [toRat_add, toRat_negate]
        ring
      rw [h_diff]
      ring
    rw [h_mul_zero]
    ring
  rw [h_zero, abs_zero]
  -- Goal: 0 < 1/((k:Rat)+1)
  have h_k : (0 : Rat) ≤ (k : Rat) := by exact_mod_cast Nat.zero_le k
  have h_pos : (0 : Rat) < (k : Rat) + 1 := by linarith
  exact div_pos (by norm_num : (0 : Rat) < 1) h_pos

-- ============================================================
-- PART 4: IDENTITY RULE
-- ============================================================

/-- **[I.T-IsDerivAt-Id]** The identity function `fromTauRat` has derivative
    `TauReal.one` at every point.

    The scaled difference quotient is exactly
        ((a₀ + 1/2^N) - a₀) · 2^N = (1/2^N) · 2^N = 1
    at every depth (Rat-exact), so it equals `TauReal.one` exactly up to
    equivalence. Modulus is `fun _ => 0`. -/
theorem TauReal.IsDerivAt_id (a₀ : TauRat) :
    TauReal.IsDerivAt (fun a => TauReal.fromTauRat a) a₀ TauReal.one := by
  refine ⟨fun _ => 0, fun k N _ => ?_⟩
  unfold TauRat.lt
  rw [TauRat.toRat_abs, TauRat.ofNatRecip_toRat]
  -- Compute the inner toRat = 0:
  -- scaledDiff = (fromTauRat (a₀ + h_N) - fromTauRat a₀) · fromTauRat (2^N)
  -- At depth N, .toRat = ((a₀.toRat + h_N.toRat) - a₀.toRat) · 2^N.toRat = h_N.toRat · 2^N.toRat = 1
  -- (scaledDiff.sub TauReal.one).approx N .toRat = 1 - 1 = 0
  have h_inner :
      ((((((fun a => TauReal.fromTauRat a) (a₀.add (TauRat.dyadicStep N))).sub
            ((fun a => TauReal.fromTauRat a) a₀)).mul
          (TauReal.fromTauRat (TauRat.twoPowN N))).sub
          TauReal.one).approx N).toRat = 0 := by
    -- Beta-reduce: (fun a => fromTauRat a) x = fromTauRat x
    show ((((((TauReal.fromTauRat (a₀.add (TauRat.dyadicStep N))).sub
              (TauReal.fromTauRat a₀)).mul
            (TauReal.fromTauRat (TauRat.twoPowN N))).sub
            TauReal.one).approx N).toRat = 0)
    -- Outer .sub structure: ((X.sub Y).approx N).toRat
    show (TauRat.add
            ((((TauReal.fromTauRat (a₀.add (TauRat.dyadicStep N))).sub
                (TauReal.fromTauRat a₀)).mul
              (TauReal.fromTauRat (TauRat.twoPowN N))).approx N)
            (TauReal.one.negate.approx N)).toRat = 0
    rw [toRat_add]
    -- TauReal.one.negate.approx N .toRat = -1
    have h_neg_one : (TauReal.one.negate.approx N).toRat = -1 := by
      show (TauRat.negate TauRat.one).toRat = -1
      rw [toRat_negate, toRat_one]
    rw [h_neg_one]
    -- The scaledDiff at depth N .toRat = 1
    have h_scaled :
        (((((TauReal.fromTauRat (a₀.add (TauRat.dyadicStep N))).sub
              (TauReal.fromTauRat a₀)).mul
            (TauReal.fromTauRat (TauRat.twoPowN N))).approx N)).toRat = 1 := by
      show (TauRat.mul
              ((((TauReal.fromTauRat (a₀.add (TauRat.dyadicStep N))).sub
                  (TauReal.fromTauRat a₀)).approx N))
              ((TauReal.fromTauRat (TauRat.twoPowN N)).approx N)).toRat = 1
      rw [toRat_mul]
      -- (fromTauRat x).approx N = x (constant sequence)
      -- so ((fromTauRat A).sub (fromTauRat B)).approx N = TauRat.add A (negate B)
      have h_diff :
          (((TauReal.fromTauRat (a₀.add (TauRat.dyadicStep N))).sub
              (TauReal.fromTauRat a₀)).approx N).toRat = (TauRat.dyadicStep N).toRat := by
        show (TauRat.add (a₀.add (TauRat.dyadicStep N)) (TauRat.negate a₀)).toRat
            = (TauRat.dyadicStep N).toRat
        rw [toRat_add, toRat_add, toRat_negate]
        ring
      have h_two :
          ((TauReal.fromTauRat (TauRat.twoPowN N)).approx N).toRat
            = (TauRat.twoPowN N).toRat := rfl
      rw [h_diff, h_two]
      exact TauRat.dyadicStep_mul_twoPowN_toRat N
    rw [h_scaled]
    ring
  rw [h_inner, abs_zero]
  have h_k : (0 : Rat) ≤ (k : Rat) := by exact_mod_cast Nat.zero_le k
  have h_pos : (0 : Rat) < (k : Rat) + 1 := by linarith
  exact div_pos (by norm_num : (0 : Rat) < 1) h_pos

end Tau.Boundary
