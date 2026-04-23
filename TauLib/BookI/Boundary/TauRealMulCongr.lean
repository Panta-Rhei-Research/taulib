import TauLib.BookI.Boundary.TauRealInv
import Mathlib.Tactic.Ring
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity

/-!
# TauLib.BookI.Boundary.TauRealMulCongr

**Multiplication respects Cauchy equivalence (with an explicit bound)**.

The Wave 2.5 infrastructure piece ledger-booked by Wave 7's
`coupling_identity_reduces_to_wave4` (see
`Boundary/IotaTauStructural.lean`).

## Registry Cross-References

- [I.D84] TauReal, [I.D112] TauReal.equiv (Cauchy)
- [I.T-W2.5] TauReal.mul_respects_equiv_right_of_bound (this module)

## Mathematical Content

**The core claim**: if `a ≡ b` at the Cauchy level and `c` is bounded
above by some natural number `M ≥ 1`, then `a · c ≡ b · c`.

The need for the bound is structural: at each index `n`,

  `|(a · c)(n) − (b · c)(n)|.toRat = |c(n)| · |a(n) − b(n)|.toRat`

so to bound the LHS by `1/(k+1)` we need to bound `|c(n)|` uniformly.
For genuinely unbounded c (e.g. c.approx n = 2^n), the conclusion
is FALSE — multiplication does not respect Cauchy equivalence
without boundedness.  The bounded form is the cleanest provable
statement.

Concrete consumers (e.g. `(π + e)` in Wave 7) supply the bound
explicitly.  For `(π + e)` we know `M = 6` works (since `π < 4` and
`e < 3`), and the bound is checkable from the partial sum at any
specific index plus monotonicity (Wave 3).

## What this delivers

- `TauReal.mul_respects_equiv_right_of_bound`: the bounded
  congruence theorem.
- Used downstream to **eliminate the explicit hypothesis parameter**
  on Wave 7's `coupling_identity_reduces_to_wave4` — the structural
  coupling identity becomes a zero-arg theorem (`coupling_identity`).
-/

set_option autoImplicit false

namespace Tau.Boundary

open Tau.Denotation

-- ============================================================
-- PART 1: The bounded mul-congruence theorem
-- ============================================================

/-- **Multiplication respects Cauchy equivalence (with explicit bound).**

    If `a ≡ b` at the Cauchy level (`TauReal.equiv`) and the
    `toRat`-absolute-value of every approximation of `c` is bounded
    above by a positive natural number `M`, then `a · c ≡ b · c`.

    Strategy: for target tolerance `1/(k+1)` on the conclusion, pull
    the equivalence at the finer tolerance level `M·(k+1) − 1` (so
    `|a − b| < 1 / (M·(k+1))` past that modulus).  Then
    `|c| · |a − b| ≤ M · 1/(M·(k+1)) = 1/(k+1)`, as required. -/
theorem TauReal.mul_respects_equiv_right_of_bound
    (a b c : TauReal) (M : Nat) (hM : 1 ≤ M)
    (h_bound : ∀ n, (c.approx n).abs.toRat ≤ M)
    (h_equiv : TauReal.equiv a b) :
    TauReal.equiv (a.mul c) (b.mul c) := by
  obtain ⟨μ, h_mod⟩ := h_equiv
  -- The refined modulus uses level `M · (k + 1) - 1` on h_mod:
  -- at that level, |a - b| < 1 / (M·(k+1)), and `M · |a − b| < 1/(k+1)`.
  refine ⟨fun k => μ (M * (k + 1) - 1), fun k n hn => ?_⟩
  have h_base := h_mod (M * (k + 1) - 1) n hn
  unfold TauRat.lt at h_base ⊢
  rw [TauRat.toRat_abs, toRat_sub] at h_base
  rw [TauRat.toRat_abs, toRat_sub]
  rw [TauRat.ofNatRecip_toRat] at h_base ⊢
  -- h_base: |a.approx n .toRat - b.approx n .toRat|
  --           < 1 / ((M * (k + 1) - 1 : Nat) + 1)
  -- Goal:  |(a.mul c).approx n .toRat - (b.mul c).approx n .toRat|
  --           < 1 / ((k : Rat) + 1)
  -- Step 1: rewrite (a.mul c).approx n  as  a.approx n  *  c.approx n
  --         (and same for b), reducing the difference to
  --         (a - b)(n) · c(n) and applying abs_mul.
  have h_lhs_eq :
      ((a.mul c).approx n).toRat
        = (a.approx n).toRat * (c.approx n).toRat := by
    show ((a.approx n).mul (c.approx n)).toRat = _
    rw [toRat_mul]
  have h_rhs_eq :
      ((b.mul c).approx n).toRat
        = (b.approx n).toRat * (c.approx n).toRat := by
    show ((b.approx n).mul (c.approx n)).toRat = _
    rw [toRat_mul]
  rw [h_lhs_eq, h_rhs_eq]
  -- Goal: |a(n)·c(n) − b(n)·c(n)| < 1/(k+1)
  -- Factor:  = |c(n)| · |a(n) − b(n)|
  have h_factor :
      (a.approx n).toRat * (c.approx n).toRat
        - (b.approx n).toRat * (c.approx n).toRat
        = ((a.approx n).toRat - (b.approx n).toRat) * (c.approx n).toRat := by ring
  rw [h_factor]
  -- Goal: |(a(n) - b(n)) · c(n)| < 1/(k+1)
  -- Hand-rolled abs_mul (the mathlib lemma exists but isn't reachable
  -- via the tactics-only imports we have).  Case-analysis on signs.
  have h_abs_mul_local : |((a.approx n).toRat - (b.approx n).toRat) * (c.approx n).toRat|
                          = |(a.approx n).toRat - (b.approx n).toRat| * |(c.approx n).toRat| := by
    set x := (a.approx n).toRat - (b.approx n).toRat
    set y := (c.approx n).toRat
    by_cases hx : 0 ≤ x
    · by_cases hy : 0 ≤ y
      · have hxy : 0 ≤ x * y := mul_nonneg hx hy
        rw [abs_of_nonneg hxy, abs_of_nonneg hx, abs_of_nonneg hy]
      · push_neg at hy
        have hxy : x * y ≤ 0 := by nlinarith
        rw [abs_of_nonpos hxy, abs_of_nonneg hx, abs_of_neg hy]; ring
    · push_neg at hx
      by_cases hy : 0 ≤ y
      · have hxy : x * y ≤ 0 := by nlinarith
        rw [abs_of_nonpos hxy, abs_of_neg hx, abs_of_nonneg hy]; ring
      · push_neg at hy
        have hxy : 0 ≤ x * y := by nlinarith
        rw [abs_of_nonneg hxy, abs_of_neg hx, abs_of_neg hy]; ring
  rw [h_abs_mul_local]
  -- Goal: |a(n) - b(n)| · |c(n)| < 1/(k+1)
  have h_c_bound : |(c.approx n).toRat| ≤ (M : Rat) := by
    have h_abs_form : (c.approx n).abs.toRat = |(c.approx n).toRat| :=
      TauRat.toRat_abs _
    have := h_bound n
    rw [h_abs_form] at this
    exact this
  have h_diff_pos :
      0 ≤ |(a.approx n).toRat - (b.approx n).toRat| := _root_.abs_nonneg _
  -- Numeric setup
  have h_M_pos : (0 : Rat) < M := by exact_mod_cast hM
  have h_k1_pos : (0 : Rat) < (k : Rat) + 1 := by
    have : (0 : Rat) ≤ (k : Rat) := by exact_mod_cast Nat.zero_le k
    linarith
  have h_Mk1_pos : (0 : Rat) < (M : Rat) * ((k : Rat) + 1) := by positivity
  -- The refined-tolerance Rat conversion
  have h_refined_eq :
      (1 : Rat) / ((M * (k + 1) - 1 : Nat) + 1) = 1 / ((M : Rat) * ((k : Rat) + 1)) := by
    have h_Mk1_nat_pos : 1 ≤ M * (k + 1) := by
      have : 1 ≤ k + 1 := by omega
      have := Nat.mul_le_mul hM this
      omega
    have h_cast : ((M * (k + 1) - 1 : Nat) + 1 : Rat) = (M : Rat) * ((k : Rat) + 1) := by
      have h_nat_eq : (M * (k + 1) - 1) + 1 = M * (k + 1) := by omega
      rw [show ((M * (k + 1) - 1 : Nat) + 1 : Rat) = ((M * (k + 1) - 1 + 1 : Nat) : Rat) by push_cast; ring]
      rw [h_nat_eq]
      push_cast; ring
    rw [h_cast]
  rw [h_refined_eq] at h_base
  -- Now: |a - b| < 1 / (M · (k+1))  and  |c| ≤ M
  -- Combine: |a - b| · |c| ≤ |a - b| · M < (1 / (M·(k+1))) · M = 1/(k+1)
  have h_step1 :
      |(a.approx n).toRat - (b.approx n).toRat| * |(c.approx n).toRat|
        ≤ |(a.approx n).toRat - (b.approx n).toRat| * M := by
    apply mul_le_mul_of_nonneg_left h_c_bound h_diff_pos
  have h_step2 :
      |(a.approx n).toRat - (b.approx n).toRat| * (M : Rat)
        < (1 / ((M : Rat) * ((k : Rat) + 1))) * (M : Rat) :=
    mul_lt_mul_of_pos_right h_base h_M_pos
  have h_step3 :
      (1 / ((M : Rat) * ((k : Rat) + 1))) * (M : Rat)
        = 1 / ((k : Rat) + 1) := by
    field_simp
  linarith

end Tau.Boundary
