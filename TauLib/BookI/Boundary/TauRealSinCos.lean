import TauLib.BookI.Boundary.TauComplexExp
import TauLib.BookI.Boundary.TauRealSin
import TauLib.BookI.Boundary.TauRealCos
import Mathlib.Tactic.Ring
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity

/-!
# TauLib.BookI.Boundary.TauRealSinCos

The Euler bridge `exp(i·x).re ≈ cos_of_rat x, .im ≈ sin_of_rat x` and the
sin/cos addition formulae derived from `TauComplex.exp_add` (the M3
endpoint shipped 2026-05-15).

## Wave Γ₈ Path B Phase 1

This module ships the structural connection between TauComplex's exp
diagonal and TauReal's sin/cos series. It validates the M3 endpoint by
deriving the classical sin/cos addition formulae from the cyclotomic-4
specialization `exp(i·(x₁+x₂)) ≈ exp(i·x₁) · exp(i·x₂)`.

## Cross-references

* [I.D-PureIm]   `TauComplex.pureIm` — the `i·x` construction.
* [I.T-PureIm-BoundedBy-1] `BoundedBy (pureIm x) 1` for `|x.toRat| ≤ 1`.
* [I.T-Euler-Re] `exp(i·x).re ≈ cos_of_rat x` (Phase 1C, queued).
* [I.T-Euler-Im] `exp(i·x).im ≈ sin_of_rat x` (Phase 1C, queued).
* [I.T-CosAdd]   `cos(α+β) ≈ cos α · cos β − sin α · sin β` (Phase 1D, queued).
* [I.T-SinAdd]   `sin(α+β) ≈ sin α · cos β + cos α · sin β` (Phase 1D, queued).
-/

namespace Tau.Boundary

open Tau.Denotation

-- ============================================================
-- PART 1: THE pureIm CONSTRUCTION  (i·x as a TauComplex)
-- ============================================================

/-- **[I.D-PureIm]** The `i·x` value as a TauComplex.

    Direct definition: real part is `TauReal.zero`, imaginary part is the
    constant TauReal sequence at `x`.

    Equivalent (at toRat level) to `TauComplex.i_unit.mul
    (TauComplex.fromTauReal (TauReal.fromTauRat x))` — but the direct
    struct constructor avoids the `taucomplex_mul` unfolding overhead. -/
def TauComplex.pureIm (x : TauRat) : TauComplex :=
  ⟨TauReal.zero, TauReal.fromTauRat x⟩

/-- **[I.T-PureIm-Re]** `(pureIm x).re.approx n = TauRat.zero` (rfl). -/
@[simp] theorem TauComplex.pureIm_re_approx (x : TauRat) (n : Nat) :
    (TauComplex.pureIm x).re.approx n = TauRat.zero := rfl

/-- **[I.T-PureIm-Im]** `(pureIm x).im.approx n = x` (rfl, constant sequence). -/
@[simp] theorem TauComplex.pureIm_im_approx (x : TauRat) (n : Nat) :
    (TauComplex.pureIm x).im.approx n = x := rfl

-- ============================================================
-- PART 2: BOUNDED BY 1 — the hypothesis bridge for M3 endpoint
-- ============================================================

/-- **[I.T-PureIm-BoundedBy-1]** Given `|x.toRat| ≤ 1`, the value `pureIm x`
    satisfies `TauComplex.BoundedBy 1`.

    The re-component is `TauReal.zero` whose approximations are all
    `TauRat.zero` with abs-toRat `= 0 ≤ 1`. The im-component is the
    constant sequence at `x` whose approximations all have abs-toRat
    `= |x.toRat| ≤ 1`. -/
theorem TauComplex.pureIm_BoundedBy_1 (x : TauRat) (hx : |x.toRat| ≤ 1) :
    TauComplex.BoundedBy (TauComplex.pureIm x) 1 := by
  refine ⟨?_, ?_⟩
  · -- Real part: all approximations are TauRat.zero, abs.toRat = 0 ≤ 1.
    intro n
    show (TauRat.zero.abs.toRat) ≤ ((1 : Nat) : Rat)
    rw [TauRat.toRat_abs]
    rw [toRat_zero]
    simp
  · -- Imaginary part: all approximations are x, abs.toRat = |x.toRat| ≤ 1.
    intro n
    show (x.abs.toRat) ≤ ((1 : Nat) : Rat)
    rw [TauRat.toRat_abs]
    have : ((1 : Nat) : Rat) = 1 := by norm_num
    rw [this]
    exact hx

-- ============================================================
-- PART 3: pureIm RESPECTS TauRat ADDITION
-- ============================================================

/-- **[I.T-PureIm-Add]** `pureIm (x₁ + x₂) ≈ pureIm x₁ + pureIm x₂` —
    pure-imaginaries add componentwise. -/
theorem TauComplex.pureIm_add (x₁ x₂ : TauRat) :
    TauComplex.equiv (TauComplex.pureIm (x₁.add x₂))
                     ((TauComplex.pureIm x₁).add (TauComplex.pureIm x₂)) := by
  refine ⟨?_, ?_⟩
  · -- Real parts: LHS = TauReal.zero, RHS = TauReal.add zero zero (both toRat = 0)
    apply TauReal.equiv_of_pointwise
    intro n
    rw [equiv_iff_toRat_eq]
    -- Unfold (TauComplex.pureIm _).re.approx n via simp lemmas + TauReal.add structure
    show ((TauComplex.pureIm (x₁.add x₂)).re.approx n).toRat
        = (((TauComplex.pureIm x₁).add (TauComplex.pureIm x₂)).re.approx n).toRat
    show (TauRat.zero).toRat
        = (TauRat.add ((TauComplex.pureIm x₁).re.approx n)
                      ((TauComplex.pureIm x₂).re.approx n)).toRat
    show (TauRat.zero).toRat = (TauRat.add TauRat.zero TauRat.zero).toRat
    rw [toRat_add, toRat_zero]
    ring
  · -- Imaginary parts: LHS = fromTauRat (x₁+x₂), RHS = (fromTauRat x₁).add (fromTauRat x₂)
    --   At .approx n: LHS = x₁+x₂, RHS = TauRat.add x₁ x₂ — same TauRat.
    apply TauReal.equiv_of_pointwise
    intro n
    exact TauRat.equiv_refl _

end Tau.Boundary
