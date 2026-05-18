import TauLib.BookI.Boundary.TauRealCisDeriv
import TauLib.BookI.Boundary.TauRealGronwall
import Mathlib.Tactic.Ring
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity

/-!
# TauLib.BookI.Boundary.TauRealTangentIdentity

**Module 6** of the τ-canon arctan/tangent program — the **tangent
identity discharge**:

  `tan(arctan(a)) ≈ a`  for TauRat `a` with `4·|a.toRat| ≤ 1`,

formulated τ-natively as

  `cis_arctan_im(a) ≈ a · cis_arctan_re(a)`

(i.e., `sin(arctan(a)) = a · cos(arctan(a))`, the Target A form from
`TauRealSinCos.lean`).

## Discharge strategy (Path ii via Gronwall — Wave 6c shortcut)

After the 2026-05-18 investigation (see `atlas/insights/2026-05-18-module-6-discharge-paths-investigation.md`),
Module 6 is discharged WITHOUT requiring Wave 6c.10c's full IsDerivAt
at general `a`. Instead:

1. Define `tangent_defect a := cis_arctan_im a − a · cis_arctan_re a`.
2. Show `tangent_defect 0 ≈ 0` (base case via Wave 2).
3. Bound the increment `tangent_defect(a+h) − tangent_defect(a)` via
   Wave 6c.10b's difference formulas — yielding the discrete-Gronwall
   recurrence `|h(a+δ)| ≤ (1+M)·|h(a)| + δ²·C`.
4. Apply β.4.9 discrete Gronwall at Rat level (at fixed `.approx K`).
5. Conclude `tangent_defect a ≈ 0` at TauReal-equiv level.

**All five load-bearing dependencies are SHIPPED** (Waves 2, 4, 5,
Module 3, 6c.10b, β.4.9).

## Today's foundation (2026-05-18 morning)

This file ships the FOUNDATION of Module 6:

- The `tangent_defect` definition.
- The base case `tangent_defect 0 ≈ 0`.

The Gronwall application (steps 3-5 above) is the next sub-Wave.
-/

set_option autoImplicit false

namespace Tau.Boundary

open Tau.Denotation

-- ============================================================
-- PART 1: THE TANGENT DEFECT
-- ============================================================

/-! ## The tangent defect

  `tangent_defect a := cis_arctan_im(a) − a · cis_arctan_re(a)`

  is the τ-native version of `sin(arctan(a)) − a·cos(arctan(a))`.
  The tangent identity says this is `≈ 0`.

  We embed `a : TauRat` into TauReal via `TauReal.fromTauRat` for the
  product term. -/

/-- The tangent-identity defect at TauRat `a`. -/
def TauReal.tangent_defect (a : TauRat) : TauReal :=
  (TauReal.cis_arctan_im a).sub
    ((TauReal.fromTauRat a).mul (TauReal.cis_arctan_re a))

/-- `.approx` of `tangent_defect`: structural unfolding. -/
@[simp] theorem TauReal.tangent_defect_approx (a : TauRat) (n : Nat) :
    (TauReal.tangent_defect a).approx n
      = ((TauReal.cis_arctan_im a).approx n).sub
          ((TauReal.fromTauRat a).approx n |>.mul ((TauReal.cis_arctan_re a).approx n)) :=
  rfl

/-- At depth `n`, the `.toRat` of `tangent_defect` is the algebraic difference
    `cis_arctan_im(a).approx n .toRat − a.toRat · cis_arctan_re(a).approx n .toRat`. -/
theorem TauReal.tangent_defect_approx_toRat (a : TauRat) (n : Nat) :
    ((TauReal.tangent_defect a).approx n).toRat
      = ((TauReal.cis_arctan_im a).approx n).toRat
        - a.toRat * ((TauReal.cis_arctan_re a).approx n).toRat := by
  show ((TauRat.add ((TauReal.cis_arctan_im a).approx n)
          (((TauReal.fromTauRat a).approx n).mul
            ((TauReal.cis_arctan_re a).approx n)).negate)).toRat = _
  rw [toRat_add, toRat_negate, toRat_mul]
  -- (fromTauRat a).approx n = a (constant sequence)
  show ((TauReal.cis_arctan_im a).approx n).toRat
        + -(a.toRat * ((TauReal.cis_arctan_re a).approx n).toRat)
      = _
  ring

-- ============================================================
-- PART 2: BASE CASE — tangent_defect 0 ≈ 0
-- ============================================================

/-! ## Base case: `tangent_defect 0 ≈ 0`

  At `a = 0`:
  - `cis_arctan_im(0) ≈ 0` (Wave 2: `cis_arctan_im_zero_equiv_zero`)
  - `0 · cis_arctan_re(0) ≈ 0` trivially (any product with `0` is `0`)
  - So `tangent_defect(0) = 0 − 0 = 0`.

  At `.approx n .toRat`, the closed forms from Wave 6c.7 give us
  pointwise zero for all `n ≥ 1` (and trivially for `n = 0` too).
-/

/-- **Module 6 base case** — `tangent_defect 0 ≈ 0` as TauReal equiv.

    Proof via pointwise toRat-zero at every depth, using:
    - `cis_arctan_im_at_zero_approx_zero` (Wave 6c.7): im part is 0 at all depths
    - The literal `0 · x = 0` at TauRat level. -/
theorem TauReal.tangent_defect_at_zero_equiv :
    TauReal.equiv (TauReal.tangent_defect TauRat.zero) TauReal.zero := by
  apply TauReal.equiv_of_pointwise
  intro n
  rw [equiv_iff_toRat_eq]
  rw [tangent_defect_approx_toRat]
  -- Goal: cis_arctan_im(0).approx n .toRat − 0.toRat · cis_arctan_re(0).approx n .toRat
  --     = TauReal.zero.approx n .toRat
  rw [toRat_zero]
  -- Goal: cis_arctan_im(0).approx n .toRat − 0 · ... = 0
  show ((TauReal.cis_arctan_im TauRat.zero).approx n).toRat - 0 * _ = _
  -- Use the pointwise closed form from Wave 6c.7
  rw [TauReal.cis_arctan_im_at_zero_approx_zero n]
  -- Goal: 0 − 0 · _ = TauReal.zero.approx n .toRat
  show 0 - 0 * _ = (TauReal.zero.approx n).toRat
  show 0 - 0 * _ = (TauRat.zero).toRat
  rw [toRat_zero]
  ring

-- ============================================================
-- PART 3: SUB-WAVE 6.M1 — INCREMENT REARRANGEMENT (PURE ALGEBRA)
-- ============================================================

/-! ## Sub-Wave 6.M1 — algebraic rearrangement of the increment

  The tangent_defect increment decomposes algebraically as:

      tangent_defect(a+dh) − tangent_defect(a)
        = [im(a+dh) − im(a)] − dh·re(a+dh) − a·[re(a+dh) − re(a)]

  where `im = cis_arctan_im`, `re = cis_arctan_re`. The proof is pure
  algebra: `(a+dh) · re(a+dh) = a · re(a+dh) + dh · re(a+dh)`, then
  collect terms.

  This rearrangement isolates the THREE pieces that the Gronwall bound
  will treat separately:
  - `[im(a+dh) − im(a)]`: handled by Wave 6c.10b (im diff formula)
  - `dh·re(a+dh)`: scaled by step size, multiplied by `cis_arctan_re(a+dh)`
  - `a·[re(a+dh) − re(a)]`: linear coefficient times re diff (Wave 6c.10b re)

  The proof: at each .approx n .toRat, expand both sides via
  `tangent_defect_approx_toRat` + toRat algebra, then ring.
-/

/-- **Sub-Wave 6.M1** — Pure algebraic rearrangement of the tangent-defect
    increment at TauReal-equiv level. No hypotheses needed (pure ring). -/
theorem TauReal.tangent_defect_increment_rearranged (a dh : TauRat) :
    TauReal.equiv
      ((TauReal.tangent_defect (a.add dh)).sub (TauReal.tangent_defect a))
      ((((TauReal.cis_arctan_im (a.add dh)).sub (TauReal.cis_arctan_im a)).sub
          ((TauReal.fromTauRat dh).mul (TauReal.cis_arctan_re (a.add dh)))).sub
        ((TauReal.fromTauRat a).mul
          ((TauReal.cis_arctan_re (a.add dh)).sub (TauReal.cis_arctan_re a)))) := by
  apply TauReal.equiv_of_pointwise
  intro n
  rw [equiv_iff_toRat_eq]
  -- Establish LHS and RHS as concrete Rat expressions in 4 opaque variables.
  have h_LHS :
      ((((TauReal.tangent_defect (a.add dh)).sub (TauReal.tangent_defect a)).approx n)).toRat
        = ((TauReal.cis_arctan_im (a.add dh)).approx n).toRat
          - (a.toRat + dh.toRat) * ((TauReal.cis_arctan_re (a.add dh)).approx n).toRat
          - (((TauReal.cis_arctan_im a).approx n).toRat
              - a.toRat * ((TauReal.cis_arctan_re a).approx n).toRat) := by
    show (TauRat.add ((TauReal.tangent_defect (a.add dh)).approx n)
            ((TauReal.tangent_defect a).approx n).negate).toRat = _
    rw [toRat_add, toRat_negate,
        TauReal.tangent_defect_approx_toRat, TauReal.tangent_defect_approx_toRat,
        toRat_add]
    ring
  have h_RHS :
      (((((TauReal.cis_arctan_im (a.add dh)).sub (TauReal.cis_arctan_im a)).sub
            ((TauReal.fromTauRat dh).mul (TauReal.cis_arctan_re (a.add dh)))).sub
          ((TauReal.fromTauRat a).mul
            ((TauReal.cis_arctan_re (a.add dh)).sub
              (TauReal.cis_arctan_re a)))).approx n).toRat
        = ((TauReal.cis_arctan_im (a.add dh)).approx n).toRat
          - ((TauReal.cis_arctan_im a).approx n).toRat
          - dh.toRat * ((TauReal.cis_arctan_re (a.add dh)).approx n).toRat
          - a.toRat * (((TauReal.cis_arctan_re (a.add dh)).approx n).toRat
              - ((TauReal.cis_arctan_re a).approx n).toRat) := by
    show (TauRat.add
            (TauRat.add
              (TauRat.add ((TauReal.cis_arctan_im (a.add dh)).approx n)
                ((TauReal.cis_arctan_im a).approx n).negate)
              (((TauReal.fromTauRat dh).approx n).mul
                ((TauReal.cis_arctan_re (a.add dh)).approx n)).negate)
            (((TauReal.fromTauRat a).approx n).mul
              (TauRat.add ((TauReal.cis_arctan_re (a.add dh)).approx n)
                ((TauReal.cis_arctan_re a).approx n).negate)).negate).toRat = _
    simp only [toRat_add, toRat_negate, toRat_mul,
               show ((TauReal.fromTauRat dh).approx n).toRat = dh.toRat from rfl,
               show ((TauReal.fromTauRat a).approx n).toRat = a.toRat from rfl]
    ring
  rw [h_LHS, h_RHS]
  ring

-- ============================================================
-- PART 4: SUB-WAVE 6.M2 — SMALL-ANGLE BOUNDS ON cisTauReal(δ_arctan)
-- ============================================================

/-! ## Sub-Wave 6.M2 — bounds on (R−1) and (I − δ_arctan) at .approx K

  Specializes Wave 6a's small-angle bounds to the arctan-increment input
  `δ_arctan := arctan_of_rat_seq(a+dh) − arctan_of_rat_seq(a)`:

      |R.approx K .toRat − 1|             ≤ K · (δ_arctan.approx K .toRat)²
      |I.approx K .toRat − δ_arctan.approx K .toRat|  ≤ K · |δ_arctan.approx K .toRat|³

  where `R := cisTauReal(δ_arctan).re`, `I := cisTauReal(δ_arctan).im`.

  These are POINTWISE bounds at fixed `.approx K`, suitable for the
  Gronwall recurrence in 6.M4.

  PROOF: direct application of `cisTauReal_re_approx_small_angle_bound`
  (Wave 6a re) / `cisTauReal_im_approx_small_angle_bound` (Wave 6a im),
  with the boundedness hypothesis discharged via Wave 6c.3
  (`arctan_increment_bounded`).
-/

/-- **Sub-Wave 6.M2 (re)** — small-angle bound for `cisTauReal(δ_arctan).re`. -/
theorem TauReal.cisTauReal_arctan_increment_re_small_angle
    (a dh : TauRat) (ha : 4 * |a.toRat| ≤ 1) (hah : 4 * |(a.add dh).toRat| ≤ 1)
    (K : Nat) (hK : 1 ≤ K) :
    |((TauComplex.cisTauReal
        ((TauReal.arctan_of_rat_seq (a.add dh)).sub
          (TauReal.arctan_of_rat_seq a))).re.approx K).toRat - 1|
      ≤ (K : Rat) * (((((TauReal.arctan_of_rat_seq (a.add dh)).sub
                          (TauReal.arctan_of_rat_seq a)).approx K)).toRat)^2 := by
  apply TauReal.cisTauReal_re_approx_small_angle_bound _ K hK
  have h_bound := TauReal.arctan_increment_bounded a dh ha hah K
  rw [TauRat.toRat_abs] at h_bound
  exact h_bound

/-- **Sub-Wave 6.M2 (im)** — small-angle bound for `cisTauReal(δ_arctan).im`. -/
theorem TauReal.cisTauReal_arctan_increment_im_small_angle
    (a dh : TauRat) (ha : 4 * |a.toRat| ≤ 1) (hah : 4 * |(a.add dh).toRat| ≤ 1)
    (K : Nat) (hK : 2 ≤ K) :
    |((TauComplex.cisTauReal
        ((TauReal.arctan_of_rat_seq (a.add dh)).sub
          (TauReal.arctan_of_rat_seq a))).im.approx K).toRat
       - ((((TauReal.arctan_of_rat_seq (a.add dh)).sub
            (TauReal.arctan_of_rat_seq a)).approx K)).toRat|
      ≤ (K : Rat) * |(((TauReal.arctan_of_rat_seq (a.add dh)).sub
                       (TauReal.arctan_of_rat_seq a)).approx K).toRat|^3 := by
  apply TauReal.cisTauReal_im_approx_small_angle_bound _ K hK
  have h_bound := TauReal.arctan_increment_bounded a dh ha hah K
  rw [TauRat.toRat_abs] at h_bound
  exact h_bound

-- ============================================================
-- PART 5: STRUCTURAL HOOKS — INCREMENT BOUND (FUTURE WAVE)
-- ============================================================

/-! ## Structural hooks for future Gronwall application

  The next sub-Wave will:
  1. Bound `tangent_defect(a+h) − tangent_defect(a)` via Wave 6c.10b's
     difference formulas + Wave 4/5 small-angle bounds + Module 3's arctan derivative.
  2. Apply `Rat.discrete_gronwall_zero_init` (β.4.9) at fixed `.approx K`.
  3. Lift to TauReal-equiv via Cauchy-modulus arithmetic.

  All five load-bearing dependencies are SHIPPED:
  - Wave 2 / 6c.7 (base case at 0)  ✅
  - Waves 4, 5 (small-angle bounds for cisTauReal partial sums)  ✅
  - Module 3 (arctan derivative + arctan_modulus_bound)  ✅
  - Wave 6c.10b (difference formulas)  ✅
  - β.4.9 (discrete Gronwall at Rat-sequence level)  ✅

  Today's deliverable (this file): the FOUNDATION (definition + base case).
  Subsequent sub-Waves: the increment bound + Gronwall application.
-/

end Tau.Boundary
