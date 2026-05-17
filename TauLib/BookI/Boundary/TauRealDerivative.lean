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

end Tau.Boundary
