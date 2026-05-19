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

/-- **B.1 aux** — `tangent_defect`'s `.approx K .toRat` depends only on `a.toRat`.

    If two TauRats `a` and `b` have the same `.toRat`, then their `tangent_defect`
    values agree at every depth `K` in `.toRat`. Used by F.2 to bridge the
    Gronwall walk endpoint `a_seq N` (which has `.toRat = a.toRat` via
    `gronwallWalkStep_full_toRat`) to the actual TauRat `a`.

    Proof: `tangent_defect_approx_toRat` shows that the `.toRat` depends on
    `a.toRat` and on `(cis_arctan_re/im a).approx K .toRat`. The latter
    reduce to `expPartial_pureIm_*_rat (arctan_partial_rat a.toRat K) K`
    via the depth-locality bridge — all functions of `a.toRat`. -/
theorem TauReal.tangent_defect_toRat_congr (a b : TauRat) (K : Nat)
    (h_eq : a.toRat = b.toRat) :
    ((TauReal.tangent_defect a).approx K).toRat
      = ((TauReal.tangent_defect b).approx K).toRat := by
  rw [TauReal.tangent_defect_approx_toRat, TauReal.tangent_defect_approx_toRat]
  -- (cis_arctan_re/im a).approx K .toRat = expPartial_pureIm_*_rat (arctan_partial_rat a.toRat K) K
  show ((TauComplex.cisTauReal (TauReal.arctan_of_rat_seq a)).im.approx K).toRat
        - a.toRat * ((TauComplex.cisTauReal (TauReal.arctan_of_rat_seq a)).re.approx K).toRat
      = ((TauComplex.cisTauReal (TauReal.arctan_of_rat_seq b)).im.approx K).toRat
        - b.toRat * ((TauComplex.cisTauReal (TauReal.arctan_of_rat_seq b)).re.approx K).toRat
  rw [cisTauReal_re_approx_toRat, cisTauReal_re_approx_toRat,
      cisTauReal_im_approx_toRat, cisTauReal_im_approx_toRat,
      TauReal.arctan_of_rat_seq_approx, TauReal.arctan_of_rat_seq_approx,
      TauRat.arctan_partial_toRat, TauRat.arctan_partial_toRat, h_eq]

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
-- PART 5: SUB-WAVE 6.M3 — δ_arctan SECANT TAYLOR BOUND
-- ============================================================

/-! ## Sub-Wave 6.M3 — δ_arctan ≈ dh · arctan_deriv(a) at .approx K

  Specializes Module 3's `arctan_partial_rat_secant_taylor_bound` to
  the arctan-increment at `.approx K .toRat`:

      |δ_arctan.approx K .toRat − dh.toRat · arctan_deriv_partial(a, K).toRat|
        ≤ dh.toRat² · 2K²

  where δ_arctan := arctan_of_rat_seq(a+dh) − arctan_of_rat_seq(a).

  This is the LINEAR APPROXIMATION of the arctan-increment, with explicit
  quadratic error bound. The Gronwall recurrence's linear coefficient
  `dh · a/(1+a²)` emerges from this when chained with 6.M2's bounds.

  HYPOTHESES:
  - `4|a| ≤ 1` (Path β, implies `|a| ≤ 1/2`)
  - `0 ≤ dh.toRat` (positive step; we walk from 0 toward positive a)
  - `dh.toRat ≤ 1/2` (step bounded by 1/2; required by Module 3's secant Taylor)

  The case `a < 0` or `dh < 0` is handled separately by symmetry (tangent_defect
  is ODD in `a`, so the proof transfers via negation).
-/

/-- **Sub-Wave 6.M3** — secant Taylor bound for δ_arctan at .approx K. -/
theorem TauReal.arctan_increment_secant_taylor_bound
    (a dh : TauRat) (ha : 4 * |a.toRat| ≤ 1) (hdh_nn : 0 ≤ dh.toRat)
    (hdh_le_half : dh.toRat ≤ 1/2) (K : Nat) :
    |(((TauReal.arctan_of_rat_seq (a.add dh)).sub
        (TauReal.arctan_of_rat_seq a)).approx K).toRat
       - dh.toRat * arctan_deriv_partial_rat a.toRat K|
      ≤ dh.toRat^2 * 2 * (K : Rat)^2 := by
  -- δ_arctan.approx K .toRat = arctan_partial(a+dh, K).toRat − arctan_partial(a, K).toRat
  have h_a_abs_le : |a.toRat| ≤ 1/2 := by linarith
  -- Compute δ.approx K .toRat
  have h_delta_toRat :
      (((TauReal.arctan_of_rat_seq (a.add dh)).sub
          (TauReal.arctan_of_rat_seq a)).approx K).toRat
        = arctan_partial_rat (a.toRat + dh.toRat) K - arctan_partial_rat a.toRat K := by
    show (TauRat.add ((TauReal.arctan_of_rat_seq (a.add dh)).approx K)
            ((TauReal.arctan_of_rat_seq a).approx K).negate).toRat = _
    rw [toRat_add, toRat_negate, TauReal.arctan_of_rat_seq_approx,
        TauReal.arctan_of_rat_seq_approx, TauRat.arctan_partial_toRat,
        TauRat.arctan_partial_toRat, toRat_add]
    ring
  rw [h_delta_toRat]
  -- Apply Module 3's secant Taylor bound at a.toRat, dh.toRat
  have h_taylor :=
    arctan_partial_rat_secant_taylor_bound a.toRat dh.toRat h_a_abs_le hdh_nn hdh_le_half K
  -- h_taylor: |arctan_partial(a+dh, K) - arctan_partial(a, K) - dh · arctan_deriv_partial(a, K)|
  --           ≤ dh² · 2K²
  exact h_taylor

-- ============================================================
-- PART 6: SUB-WAVE 6.M4 — CYCLOTOMIC-4 PARITY ZERO FACTS
-- ============================================================

/-! ## Sub-Wave 6.M4 — pureIm_pow parity zero facts

  The iℂ-cyclotomic-4 structure of `pureIm_pow α k` makes specific
  components vanish at specific parities. We need these zero facts as
  the foundation for the secant Taylor argument in 6.M4.B.

  Specifically:
  - At EVEN k: (pureIm_pow α k).2 = 0
  - At ODD k:  (pureIm_pow α k).1 = 0

  These vanishings are what makes the alternating-power structure of
  expPartial_re (only even powers of α) and expPartial_im (only odd
  powers of α) emerge.

  We already have the related lemma `pureIm_pow_re_im_rat_zero_succ`
  (at α = 0) shipped earlier. This sub-Wave's parity facts are the
  generalization to arbitrary α.

  PROOF: induction on k via the recursive structure. Each step uses the
  alternating .1 ↔ .2 swap of `pureIm_pow_re_im_rat_succ`.

  Note: the full secant Taylor proof (6.M4.B) is deferred — it requires
  substantial binomial-expansion machinery (~200+ LOC) and is the next
  analytical wave.
-/

/-- **6.M4.A.1**: at EVEN k, `(pureIm_pow α k).2 = 0`. -/
theorem pureIm_pow_im_rat_even_zero (α : Rat) (j : Nat) :
    (pureIm_pow_re_im_rat α (2*j)).2 = 0 := by
  induction j with
  | zero =>
    show (pureIm_pow_re_im_rat α 0).2 = 0
    rw [pureIm_pow_re_im_rat_zero]
  | succ j ih =>
    have h_eq : 2 * (j + 1) = (2 * j + 1) + 1 := by ring
    rw [h_eq, pureIm_pow_re_im_rat_succ]
    have h_2j_succ : 2 * j + 1 = (2 * j) + 1 := by ring
    rw [h_2j_succ, pureIm_pow_re_im_rat_succ]
    rw [ih]
    show ((-((-0 : Rat) * α, (pureIm_pow_re_im_rat α (2*j)).1 * α).2 * α,
           ((-0 : Rat) * α, (pureIm_pow_re_im_rat α (2*j)).1 * α).1 * α)).2 = 0
    show ((-0 : Rat) * α) * α = 0
    ring

/-- **6.M4.A.2**: at ODD k, `(pureIm_pow α k).1 = 0`.
    Follows from the .2-even-zero fact via one step of `pureIm_pow_re_im_rat_succ`. -/
theorem pureIm_pow_re_rat_odd_zero (α : Rat) (j : Nat) :
    (pureIm_pow_re_im_rat α (2*j+1)).1 = 0 := by
  -- pureIm_pow α (2j+1) = pureIm_pow α ((2j)+1) = (-(pureIm_pow α (2j)).2·α, (pureIm_pow α (2j)).1·α)
  -- So .1 = -(pureIm_pow α (2j)).2 · α
  -- By 6.M4.A.1: (pureIm_pow α (2j)).2 = 0, so .1 = -0·α = 0.
  have h_eq : 2*j+1 = (2*j)+1 := by ring
  rw [h_eq, pureIm_pow_re_im_rat_succ]
  rw [pureIm_pow_im_rat_even_zero]
  show (-(0 : Rat) * α) = 0
  ring

/-- **6.M4.A.3 (re-even closed form)**: at EVEN k = 2j,
    `(pureIm_pow α (2j)).1 = (-1)^j · α^(2j)`. -/
theorem pureIm_pow_re_rat_even_closed (α : Rat) (j : Nat) :
    (pureIm_pow_re_im_rat α (2*j)).1 = (-1)^j * α^(2*j) := by
  induction j with
  | zero =>
    show (pureIm_pow_re_im_rat α 0).1 = (-1)^0 * α^0
    rw [pureIm_pow_re_im_rat_zero]; simp
  | succ j ih =>
    have h_eq : 2 * (j + 1) = (2 * j + 1) + 1 := by ring
    rw [h_eq, pureIm_pow_re_im_rat_succ]
    have h_2j_succ : 2 * j + 1 = (2 * j) + 1 := by ring
    rw [h_2j_succ, pureIm_pow_re_im_rat_succ]
    rw [ih]
    -- After unfolding, goal projects to .1 of outer pair, which equals
    -- -((pureIm_pow_re_im_rat α (2j+1)).2 · α)
    -- And (pureIm_pow_re_im_rat α (2j+1)).2 = (-1)^j · α^(2j) · α
    show (-(((-1)^j * α^(2*j)) * α) * α) = (-1)^(j+1) * α^(2*(j+1))
    -- Pure Rat ring identity: -(x · α^(2j) · α) · α = -x · α^(2j+2) = (-x) · α^(2j+2)
    -- (-1)^(j+1) = -(-1)^j
    have h_pow_succ : (-1 : Rat)^(j+1) = -((-1 : Rat)^j) := by
      rw [pow_succ]; ring
    rw [h_pow_succ]
    have h_2jp2 : 2*(j+1) = 2*j+2 := by ring
    rw [h_2jp2]
    ring

/-- **6.M4.A.4 (im-odd closed form)**: at ODD k = 2j+1,
    `(pureIm_pow α (2j+1)).2 = (-1)^j · α^(2j+1)`. -/
theorem pureIm_pow_im_rat_odd_closed (α : Rat) (j : Nat) :
    (pureIm_pow_re_im_rat α (2*j+1)).2 = (-1)^j * α^(2*j+1) := by
  -- pureIm_pow α (2j+1) = ((-(pureIm_pow α 2j).2 · α, (pureIm_pow α 2j).1 · α))
  -- .2 = (pureIm_pow α 2j).1 · α = (-1)^j · α^(2j) · α = (-1)^j · α^(2j+1)
  have h_eq : 2*j+1 = (2*j)+1 := by ring
  rw [h_eq, pureIm_pow_re_im_rat_succ]
  rw [pureIm_pow_re_rat_even_closed]
  show ((-(pureIm_pow_re_im_rat α (2*j)).2 * α, (-1)^j * α^(2*j) * α).2) = (-1)^j * α^(2*j+1)
  show ((-1)^j * α^(2*j) * α) = (-1)^j * α^(2*j+1)
  rw [show 2*j + 1 = (2*j) + 1 from rfl, pow_succ]
  ring

-- ============================================================
-- PART 7: SUB-WAVE 6.M4.B HELPER — pow_sub_pow SECANT TAYLOR
-- ============================================================

/-! ## Helper: secant Taylor for `α^n`

  For |α|, |β| ≤ 1 and n : Nat:
    |α^n − β^n − n · β^(n-1) · (α − β)| ≤ n² · (α − β)² / 2

  Proof: induction on n using the recursion
    R(n+1) = α · R(n) + n · β^(n-1) · (α − β)²
  where R(n) := α^n − β^n − n · β^(n-1) · (α − β).
-/

/-- **6.M4.B helper** — secant Taylor for `α^n`. -/
theorem pow_sub_pow_secant_taylor (α β : Rat) (h_α : |α| ≤ 1) (h_β : |β| ≤ 1) (n : Nat) :
    |α^n - β^n - (n : Rat) * β^(n-1) * (α - β)| ≤ (n : Rat)^2 * (α - β)^2 / 2 := by
  induction n with
  | zero =>
    show |α^0 - β^0 - (0 : Rat) * β^(0-1) * (α - β)| ≤ (0 : Rat)^2 * (α - β)^2 / 2
    simp
  | succ n ih =>
    -- Case split: n = 0 (so we're proving for n+1 = 1) vs n ≥ 1 (recursion works)
    rcases n with _ | m
    · -- n = 0, so we're proving for n+1 = 1.
      -- R(1) = α^1 - β^1 - 1·β^0·(α-β) = α - β - (α - β) = 0
      show |α^1 - β^1 - ((0+1 : Nat) : Rat) * β^((0+1)-1) * (α - β)|
              ≤ ((0+1 : Nat) : Rat)^2 * (α - β)^2 / 2
      have h_zero : α^1 - β^1 - ((0+1 : Nat) : Rat) * β^((0+1)-1) * (α - β) = 0 := by
        push_cast; ring
      rw [h_zero, abs_zero]
      have h_sq_nn : (0 : Rat) ≤ ((0+1 : Nat) : Rat)^2 * (α - β)^2 / 2 := by positivity
      exact h_sq_nn
    · -- n = m+1 ≥ 1. Now β^n = β · β^(n-1) holds cleanly.
      -- We're proving R(m+2) using IH for R(m+1).
      set n := m + 1
      have h_n_pos : 1 ≤ n := by omega
      have h_recursion :
          α^(n+1) - β^(n+1) - ((n+1 : Nat) : Rat) * β^((n+1)-1) * (α - β)
            = α * (α^n - β^n - (n : Rat) * β^(n-1) * (α - β))
              + (n : Rat) * β^(n-1) * (α - β)^2 := by
        have h_n_succ_sub : (n + 1 : Nat) - 1 = n := by omega
        rw [h_n_succ_sub]
        have h_β_pow_succ : β^(n+1) = β * β^n := by rw [pow_succ]; ring
        have h_α_pow_succ : α^(n+1) = α * α^n := by rw [pow_succ]; ring
        rw [h_β_pow_succ, h_α_pow_succ]
        have h_β_pow_n : β^n = β * β^(n-1) := by
          show β^(m+1) = β * β^((m+1)-1)
          have h_m1_sub : (m+1) - 1 = m := by omega
          rw [h_m1_sub, pow_succ]; ring
        push_cast
        rw [h_β_pow_n]
        ring
      rw [h_recursion]
      have h_α_R_bound : |α * (α^n - β^n - (n : Rat) * β^(n-1) * (α - β))| ≤
          (n : Rat)^2 * (α - β)^2 / 2 := by
        rw [abs_mul]
        calc |α| * |α^n - β^n - (n : Rat) * β^(n-1) * (α - β)|
            ≤ 1 * |α^n - β^n - (n : Rat) * β^(n-1) * (α - β)| :=
                mul_le_mul_of_nonneg_right h_α (_root_.abs_nonneg _)
          _ = |α^n - β^n - (n : Rat) * β^(n-1) * (α - β)| := one_mul _
          _ ≤ (n : Rat)^2 * (α - β)^2 / 2 := ih
      have h_β_pow_n_minus_1_bound : |β^(n-1)| ≤ 1 := by
        rw [abs_pow]; exact pow_le_one₀ (_root_.abs_nonneg _) h_β
      have h_n_term_bound : |(n : Rat) * β^(n-1) * (α - β)^2| ≤ (n : Rat) * (α - β)^2 := by
        have h_n_nn : (0 : Rat) ≤ (n : Rat) := Nat.cast_nonneg _
        have h_sq_nn : (0 : Rat) ≤ (α - β)^2 := sq_nonneg _
        rw [abs_mul, abs_mul]
        have h_n_abs : |(n : Rat)| = (n : Rat) := abs_of_nonneg h_n_nn
        have h_sq_abs : |(α - β)^2| = (α - β)^2 := abs_of_nonneg h_sq_nn
        rw [h_n_abs, h_sq_abs]
        calc (n : Rat) * |β^(n-1)| * (α - β)^2
            ≤ (n : Rat) * 1 * (α - β)^2 :=
                mul_le_mul_of_nonneg_right
                  (mul_le_mul_of_nonneg_left h_β_pow_n_minus_1_bound h_n_nn) h_sq_nn
          _ = (n : Rat) * (α - β)^2 := by ring
      have h_sum_bound :
          |α * (α^n - β^n - (n : Rat) * β^(n-1) * (α - β))
            + (n : Rat) * β^(n-1) * (α - β)^2|
            ≤ (n : Rat)^2 * (α - β)^2 / 2 + (n : Rat) * (α - β)^2 := by
        calc |α * (α^n - β^n - (n : Rat) * β^(n-1) * (α - β))
              + (n : Rat) * β^(n-1) * (α - β)^2|
            ≤ |α * (α^n - β^n - (n : Rat) * β^(n-1) * (α - β))|
              + |(n : Rat) * β^(n-1) * (α - β)^2| := abs_add_le _ _
          _ ≤ (n : Rat)^2 * (α - β)^2 / 2 + (n : Rat) * (α - β)^2 := by linarith
      have h_final :
          (n : Rat)^2 * (α - β)^2 / 2 + (n : Rat) * (α - β)^2
            ≤ ((n+1 : Nat) : Rat)^2 * (α - β)^2 / 2 := by
        have h_sq_nn : (0 : Rat) ≤ (α - β)^2 := sq_nonneg _
        have h_n_cast : ((n+1 : Nat) : Rat) = (n : Rat) + 1 := by push_cast; ring
        rw [h_n_cast]
        nlinarith [h_sq_nn]
      linarith

/-! ## Sub-Wave F.0 — Lipschitz bound for `α^n` (helper)

  Standard fact: for `|α|, |β| ≤ 1`, `|α^n − β^n| ≤ n · |α − β|`. Proven by
  induction on `n` via the recurrence `α^(n+1) − β^(n+1) = α·(α^n − β^n)
  + (α − β)·β^n` plus `|α|, |β^n| ≤ 1`.

  Used in F.0's `expPartial_pureIm_re_rat_lipschitz_bound`.
-/

/-- **Lipschitz bound** for `α^n` at bounded inputs. -/
theorem pow_sub_pow_lipschitz (α β : Rat) (h_α : |α| ≤ 1) (h_β : |β| ≤ 1) (n : Nat) :
    |α^n - β^n| ≤ (n : Rat) * |α - β| := by
  induction n with
  | zero => simp
  | succ n ih =>
    have h_recurrence : α^(n+1) - β^(n+1) = α * (α^n - β^n) + (α - β) * β^n := by
      rw [pow_succ, pow_succ]; ring
    rw [h_recurrence]
    have h_β_n_abs : |β^n| ≤ 1 := by
      rw [abs_pow]; exact pow_le_one₀ (_root_.abs_nonneg _) h_β
    calc |α * (α^n - β^n) + (α - β) * β^n|
        ≤ |α * (α^n - β^n)| + |(α - β) * β^n| := abs_add_le _ _
      _ = |α| * |α^n - β^n| + |α - β| * |β^n| := by rw [abs_mul, abs_mul]
      _ ≤ 1 * |α^n - β^n| + |α - β| * 1 := by
          have h_diff_nn : (0 : Rat) ≤ |α^n - β^n| := _root_.abs_nonneg _
          have h_αβ_nn : (0 : Rat) ≤ |α - β| := _root_.abs_nonneg _
          nlinarith [h_α, h_β_n_abs, h_diff_nn, h_αβ_nn]
      _ = |α^n - β^n| + |α - β| := by ring
      _ ≤ (n : Rat) * |α - β| + |α - β| := by linarith [ih]
      _ = ((n + 1 : Nat) : Rat) * |α - β| := by push_cast; ring

/-! ## Sub-Wave F.0 — Lipschitz bound for `expPartial_pureIm_re_rat`

  For `|α|, |β| ≤ 1` and `K : Nat`:

      |expPartial_pureIm_re_rat α K − expPartial_pureIm_re_rat β K| ≤ K · |α − β|

  Bounds `|A_K − A_h.K|` in the increment analysis, ensuring that the
  `re_h` residual contributes only to the quadratic error term `δ_K`,
  not to a linear `M · |T|` term.
-/

/-- **F.0** — Lipschitz bound for `expPartial_pureIm_re_rat`. -/
theorem expPartial_pureIm_re_rat_lipschitz_bound
    (α β : Rat) (h_α : |α| ≤ 1) (h_β : |β| ≤ 1) (K : Nat) :
    |expPartial_pureIm_re_rat α K - expPartial_pureIm_re_rat β K|
      ≤ (K : Rat) * |α - β| := by
  induction K with
  | zero =>
    show |expPartial_pureIm_re_rat α 0 - expPartial_pureIm_re_rat β 0|
          ≤ (0 : Rat) * |α - β|
    rw [expPartial_pureIm_re_rat_zero, expPartial_pureIm_re_rat_zero]
    simp
  | succ K ih =>
    -- expPartial α (K+1) - expPartial β (K+1)
    --   = (expPartial α K - expPartial β K) + new_term_diff
    -- where new_term_diff := ((pureIm_pow α K).1 - (pureIm_pow β K).1) / K!
    rw [expPartial_pureIm_re_rat_succ, expPartial_pureIm_re_rat_succ]
    have h_rearr :
        (expPartial_pureIm_re_rat α K
          + (pureIm_pow_re_im_rat α K).1 / (K.factorial : Rat))
          - (expPartial_pureIm_re_rat β K
              + (pureIm_pow_re_im_rat β K).1 / (K.factorial : Rat))
        = (expPartial_pureIm_re_rat α K - expPartial_pureIm_re_rat β K)
          + ((pureIm_pow_re_im_rat α K).1 - (pureIm_pow_re_im_rat β K).1)
              / (K.factorial : Rat) := by ring
    rw [h_rearr]
    have h_tri : |(expPartial_pureIm_re_rat α K - expPartial_pureIm_re_rat β K)
                 + ((pureIm_pow_re_im_rat α K).1
                    - (pureIm_pow_re_im_rat β K).1) / (K.factorial : Rat)|
        ≤ |expPartial_pureIm_re_rat α K - expPartial_pureIm_re_rat β K|
          + |((pureIm_pow_re_im_rat α K).1
              - (pureIm_pow_re_im_rat β K).1) / (K.factorial : Rat)| :=
      abs_add_le _ _
    -- Bound the new term ≤ |α - β| via parity case-split.
    have h_new :
        |((pureIm_pow_re_im_rat α K).1
          - (pureIm_pow_re_im_rat β K).1) / (K.factorial : Rat)|
          ≤ |α - β| := by
      rcases Nat.even_or_odd K with hEven | hOdd
      · -- K even: K = 2j, closed form (-1)^j · X^(2j)
        obtain ⟨j, hj⟩ := hEven
        have hK_eq : K = 2 * j := by omega
        rw [hK_eq, pureIm_pow_re_rat_even_closed, pureIm_pow_re_rat_even_closed]
        rw [show (-1 : Rat)^j * α^(2*j) - (-1 : Rat)^j * β^(2*j)
              = (-1 : Rat)^j * (α^(2*j) - β^(2*j)) from by ring]
        rw [abs_div, abs_mul]
        have h_neg_one_pow_abs : |((-1 : Rat))^j| = 1 := by
          rw [abs_pow]; simp
        rw [h_neg_one_pow_abs, one_mul]
        have h_pow_diff := pow_sub_pow_lipschitz α β h_α h_β (2*j)
        -- h_pow_diff : |α^(2j) - β^(2j)| ≤ 2j · |α-β|
        -- Goal: |α^(2j) - β^(2j)| / |(2j)!| ≤ |α-β|
        have h_fac_pos : (0 : Rat) < ((2*j).factorial : Rat) := by
          have := Nat.factorial_pos (2*j); exact_mod_cast this
        have h_abs_fac : |((2*j).factorial : Rat)| = ((2*j).factorial : Rat) :=
          abs_of_pos h_fac_pos
        rw [h_abs_fac]
        -- Need: |α^(2j) - β^(2j)| / (2j)! ≤ |α - β|
        -- Equivalent: |α^(2j) - β^(2j)| ≤ (2j)! · |α - β|
        -- Have: |α^(2j) - β^(2j)| ≤ 2j · |α - β|, and 2j ≤ (2j)! for j ≥ 1.
        -- For j = 0: 2j = 0, so |...| ≤ 0, and (2j)! = 1 so RHS = |α-β| ≥ 0. ✓
        have h_factorial_ge : (2 * j : Rat) ≤ ((2*j).factorial : Rat) := by
          rcases Nat.eq_zero_or_pos j with hj0 | hj_pos
          · -- j = 0: 0 ≤ 0! = 1
            rw [hj0]; simp
          · -- j ≥ 1: 2j ≤ (2j)!
            -- (2j)! = (2j) · (2j-1)! ≥ (2j) since (2j-1)! ≥ 1
            have h_2j_pos : 1 ≤ 2 * j := by omega
            have h_fac_ge_2j : 2 * j ≤ (2*j).factorial := by
              have := Nat.self_le_factorial (2*j)
              exact this
            exact_mod_cast h_fac_ge_2j
        rw [div_le_iff₀ h_fac_pos]
        have h_αβ_nn : (0 : Rat) ≤ |α - β| := _root_.abs_nonneg _
        calc |α^(2*j) - β^(2*j)|
            ≤ ((2 * j : Nat) : Rat) * |α - β| := h_pow_diff
          _ = (2 * (j : Rat)) * |α - β| := by push_cast; ring
          _ ≤ ((2*j).factorial : Rat) * |α - β| :=
              mul_le_mul_of_nonneg_right h_factorial_ge h_αβ_nn
          _ = |α - β| * ((2*j).factorial : Rat) := by ring
      · -- K odd: K = 2j+1, both diff components are 0
        obtain ⟨j, hj⟩ := hOdd
        rw [hj, pureIm_pow_re_rat_odd_zero, pureIm_pow_re_rat_odd_zero]
        simp
    -- Combine: |old_diff| ≤ K · |α-β|, |new_term| ≤ |α-β|, sum ≤ (K+1) · |α-β|
    have h_cast : ((K + 1 : Nat) : Rat) = (K : Rat) + 1 := by push_cast; ring
    rw [h_cast]
    have h_αβ_nn : (0 : Rat) ≤ |α - β| := _root_.abs_nonneg _
    linarith [ih, h_tri, h_new]

/-! ## Sub-Wave 6.M4.D.1 — Magnitude bounds for cis_arctan_re / cis_arctan_im

  Triangle-inequality lifts of Wave 6b's small-angle bounds. Used downstream
  in 6.M4.D.3 (linear-term extraction) to control products `|A_K · X|`,
  `|B_K · Y|`.

  - `|A_K| := |((cis_arctan_re a).approx K).toRat| ≤ 1 + K · α²`
  - `|B_K| := |((cis_arctan_im a).approx K).toRat| ≤ |α| + K · |α|³`

  where `α := ((arctan_of_rat_seq a).approx K).toRat`.

  Under Path β (`4·|a.toRat| ≤ 1`), we have `|α| ≤ (4/3)·|a.toRat| ≤ 1/3`,
  so `α² ≤ 1/9` and `|α|³ ≤ 1/27`.
-/

/-- **6.M4.D.1 (re)** — magnitude bound for `cis_arctan_re a` at `.approx K`. -/
theorem TauReal.cis_arctan_re_approx_abs_bound
    (a : TauRat) (ha : 2 * |a.toRat| ≤ 1) (K : Nat) (hK : 1 ≤ K) :
    |((TauReal.cis_arctan_re a).approx K).toRat|
      ≤ 1 + (K : Rat) * (((TauReal.arctan_of_rat_seq a).approx K).toRat)^2 := by
  have h_small := TauReal.cis_arctan_re_approx_small_angle_bound a ha K hK
  -- |A_K - 1| ≤ K · α²
  -- Triangle: |A_K| ≤ |A_K - 1| + 1 ≤ K · α² + 1
  have h_tri : |((TauReal.cis_arctan_re a).approx K).toRat|
      ≤ |((TauReal.cis_arctan_re a).approx K).toRat - 1| + |(1 : Rat)| := by
    have := abs_add_le (((TauReal.cis_arctan_re a).approx K).toRat - 1) (1 : Rat)
    have h_eq : ((TauReal.cis_arctan_re a).approx K).toRat - 1 + 1
              = ((TauReal.cis_arctan_re a).approx K).toRat := by ring
    rw [h_eq] at this
    exact this
  rw [abs_one] at h_tri
  linarith

/-- **6.M4.D.1 (im)** — magnitude bound for `cis_arctan_im a` at `.approx K`. -/
theorem TauReal.cis_arctan_im_approx_abs_bound
    (a : TauRat) (ha : 2 * |a.toRat| ≤ 1) (K : Nat) (hK : 2 ≤ K) :
    |((TauReal.cis_arctan_im a).approx K).toRat|
      ≤ |((TauReal.arctan_of_rat_seq a).approx K).toRat|
        + (K : Rat) * |((TauReal.arctan_of_rat_seq a).approx K).toRat|^3 := by
  have h_small := TauReal.cis_arctan_im_approx_small_angle_bound a ha K hK
  -- |B_K - α| ≤ K · |α|³
  -- Triangle: |B_K| ≤ |B_K - α| + |α|
  set B_K := ((TauReal.cis_arctan_im a).approx K).toRat
  set α := ((TauReal.arctan_of_rat_seq a).approx K).toRat
  have h_tri : |B_K| ≤ |B_K - α| + |α| := by
    have := abs_add_le (B_K - α) α
    have h_eq : B_K - α + α = B_K := by ring
    rw [h_eq] at this
    exact this
  linarith

/-- **6.M4.D.1 (re, Path β)** — under Path β, the magnitude bound becomes
    `|A_K| ≤ 1 + K/9`. -/
theorem TauReal.cis_arctan_re_approx_abs_bound_path_beta
    (a : TauRat) (ha : 4 * |a.toRat| ≤ 1) (K : Nat) (hK : 1 ≤ K) :
    |((TauReal.cis_arctan_re a).approx K).toRat| ≤ 1 + (K : Rat) / 9 := by
  have ha2 : 2 * |a.toRat| ≤ 1 := by linarith [_root_.abs_nonneg a.toRat]
  have h_gen := TauReal.cis_arctan_re_approx_abs_bound a ha2 K hK
  -- Need: K · α² ≤ K/9, i.e., α² ≤ 1/9
  set α := ((TauReal.arctan_of_rat_seq a).approx K).toRat
  have h_α_bound : |α| ≤ (4/3) * |a.toRat| := by
    have h := TauReal.arctan_of_rat_seq_abs_le_four_thirds a ha2 K
    rwa [TauRat.toRat_abs] at h
  have h_α_le_third : |α| ≤ 1/3 := by linarith
  have h_α_nn : (0 : Rat) ≤ |α| := _root_.abs_nonneg _
  have h_α_sq_bound : α^2 ≤ 1/9 := by
    have h_α_abs_sq : α^2 = |α|^2 := by rw [sq_abs]
    rw [h_α_abs_sq]
    have : |α|^2 ≤ (1/3 : Rat)^2 := pow_le_pow_left₀ h_α_nn h_α_le_third 2
    have h_third_sq : (1/3 : Rat)^2 = 1/9 := by norm_num
    linarith
  have h_K_nn : (0 : Rat) ≤ (K : Rat) := Nat.cast_nonneg _
  have : (K : Rat) * α^2 ≤ (K : Rat) * (1/9) :=
    mul_le_mul_of_nonneg_left h_α_sq_bound h_K_nn
  linarith

/-- **6.M4.D.1 (im, Path β)** — under Path β, the magnitude bound becomes
    `|B_K| ≤ 1/3 + K/27`. -/
theorem TauReal.cis_arctan_im_approx_abs_bound_path_beta
    (a : TauRat) (ha : 4 * |a.toRat| ≤ 1) (K : Nat) (hK : 2 ≤ K) :
    |((TauReal.cis_arctan_im a).approx K).toRat| ≤ 1/3 + (K : Rat) / 27 := by
  have ha2 : 2 * |a.toRat| ≤ 1 := by linarith [_root_.abs_nonneg a.toRat]
  have h_gen := TauReal.cis_arctan_im_approx_abs_bound a ha2 K hK
  -- Need: |α| + K · |α|³ ≤ 1/3 + K/27
  set α := ((TauReal.arctan_of_rat_seq a).approx K).toRat
  have h_α_bound : |α| ≤ (4/3) * |a.toRat| := by
    have h := TauReal.arctan_of_rat_seq_abs_le_four_thirds a ha2 K
    rwa [TauRat.toRat_abs] at h
  have h_α_le_third : |α| ≤ 1/3 := by linarith
  have h_α_nn : (0 : Rat) ≤ |α| := _root_.abs_nonneg _
  have h_α_cube_bound : |α|^3 ≤ 1/27 := by
    have : |α|^3 ≤ (1/3 : Rat)^3 := pow_le_pow_left₀ h_α_nn h_α_le_third 3
    have h_third_cube : (1/3 : Rat)^3 = 1/27 := by norm_num
    linarith
  have h_K_nn : (0 : Rat) ≤ (K : Rat) := Nat.cast_nonneg _
  have h_K_times : (K : Rat) * |α|^3 ≤ (K : Rat) * (1/27) :=
    mul_le_mul_of_nonneg_left h_α_cube_bound h_K_nn
  linarith

/-! ## Sub-Wave 6.M4.D.2 — `d_K` geometric identity at TauRat level

  Module 3's `arctan_deriv_partial_rat_geometric_identity` says:

      `arctan_deriv_partial_rat x n · (1 + x²) = 1 − x^(4n)`

  This is the KEY algebraic tool for 6.M4.D.3 (linear-term extraction):
  the coefficient `a/(1+a²)` emerges from this MULTIPLICATIVE form —
  no inductive factorial arithmetic needed.

  Here we:
  1. Lift the identity to TauRat level via `arctan_deriv_partial_toRat`.
  2. Bound the residual `|d_K · (1+a²) − 1| ≤ (1/4)^(4K)` under Path β.
-/

/-- **6.M4.D.2 (identity at TauRat)** — Geometric identity for
    `TauRat.arctan_deriv_partial`. -/
theorem TauRat.arctan_deriv_partial_geometric_identity_toRat
    (a : TauRat) (K : Nat) :
    (TauRat.arctan_deriv_partial a K).toRat * (1 + a.toRat^2)
      = 1 - a.toRat^(4*K) := by
  rw [TauRat.arctan_deriv_partial_toRat]
  exact arctan_deriv_partial_rat_geometric_identity a.toRat K

/-- **6.M4.D.2 (error bound)** — Under Path β (`4·|a.toRat| ≤ 1`),
    `|d_K · (1+a²) − 1| ≤ (1/4)^(4K)`. -/
theorem TauRat.arctan_deriv_partial_geometric_error_bound
    (a : TauRat) (ha : 4 * |a.toRat| ≤ 1) (K : Nat) :
    |(TauRat.arctan_deriv_partial a K).toRat * (1 + a.toRat^2) - 1|
      ≤ (1/4 : Rat)^(4*K) := by
  rw [TauRat.arctan_deriv_partial_geometric_identity_toRat]
  have h_eq : (1 : Rat) - a.toRat^(4*K) - 1 = -(a.toRat^(4*K)) := by ring
  rw [h_eq, abs_neg, abs_pow]
  have h_abs_a : |a.toRat| ≤ 1/4 := by linarith [_root_.abs_nonneg a.toRat]
  have h_abs_a_nn : (0 : Rat) ≤ |a.toRat| := _root_.abs_nonneg _
  exact pow_le_pow_left₀ h_abs_a_nn h_abs_a (4*K)

/-- **6.M4.D.2 (positivity)** — Under Path β, `d_K · (1+a²) ≥ 1 − (1/4)^(4K) > 0`,
    so `d_K > 0` (the partial sum is positive). -/
theorem TauRat.arctan_deriv_partial_geometric_positive
    (a : TauRat) (ha : 4 * |a.toRat| ≤ 1) (K : Nat) :
    1 - (1/4 : Rat)^(4*K)
      ≤ (TauRat.arctan_deriv_partial a K).toRat * (1 + a.toRat^2) := by
  have h_id := TauRat.arctan_deriv_partial_geometric_identity_toRat a K
  rw [h_id]
  -- Need: 1 - (1/4)^(4K) ≤ 1 - a.toRat^(4K)
  -- i.e., a.toRat^(4K) ≤ (1/4)^(4K)
  have h_abs_a : |a.toRat| ≤ 1/4 := by linarith [_root_.abs_nonneg a.toRat]
  have h_abs_a_nn : (0 : Rat) ≤ |a.toRat| := _root_.abs_nonneg _
  have h_a_pow_le : a.toRat^(4*K) ≤ (1/4 : Rat)^(4*K) := by
    -- a.toRat^(4K) ≤ |a.toRat|^(4K) ≤ (1/4)^(4K)
    have h_le_abs : a.toRat^(4*K) ≤ |a.toRat^(4*K)| := le_abs_self _
    rw [abs_pow] at h_le_abs
    have h_abs_pow_le : |a.toRat|^(4*K) ≤ (1/4 : Rat)^(4*K) :=
      pow_le_pow_left₀ h_abs_a_nn h_abs_a (4*K)
    linarith
  linarith

/-! ## Sub-Wave 6.M4.D.3 — Linear-term extraction (analytical heart)

  The key algebraic identity at Rat level:

      (α_h − α_a) · (A_K + a·B_K)
        − dh · a · d_K · T_K
        − dh · A_K · (1 − a^(4K))
      = (A_K + a·B_K) · (α_h − α_a − dh·d_K)

  where:
  - α_a := `((arctan_of_rat_seq a).approx K).toRat`
  - α_h := `((arctan_of_rat_seq (a+dh)).approx K).toRat`
  - d_K := `arctan_deriv_partial_rat a.toRat K`
  - A_K := `((cis_arctan_re a).approx K).toRat`
  - B_K := `((cis_arctan_im a).approx K).toRat`
  - T_K := `((tangent_defect a).approx K).toRat` = B_K − a·A_K

  **The identity REQUIRES** `d_K · (1+a²) = 1 − a^(4K)` (the geometric identity,
  6.M4.D.2) AND `T_K = B_K − a·A_K` (definition).

  **The bound** follows by combining with 6.M3:
  `|α_h − α_a − dh·d_K| ≤ dh²·2K²` ⟹

      | LHS | ≤ |A_K + a·B_K| · dh² · 2K²

  This is the analytical foundation: the linear coefficient `dh·a·d_K` (which
  approximates `dh·a/(1+a²)`) emerges ALGEBRAICALLY from the geometric identity.
-/

/-- **6.M4.D.3 (linear-term extraction bound)** —
    The KEY analytical lemma. Combines:
    - the algebraic identity (from `d_K·(1+a²) = 1 − a^(4K)` and `T_K = B_K − a·A_K`)
    - the secant Taylor bound (6.M3) on `|δ_K − dh·d_K|`. -/
theorem TauReal.M4_D3_linear_extraction_bound
    (a dh : TauRat) (ha : 4 * |a.toRat| ≤ 1)
    (hdh_nn : 0 ≤ dh.toRat) (hdh_le_half : dh.toRat ≤ 1/2)
    (K : Nat) :
    |(((TauReal.arctan_of_rat_seq (a.add dh)).sub
         (TauReal.arctan_of_rat_seq a)).approx K).toRat
       * (((TauReal.cis_arctan_re a).approx K).toRat
            + a.toRat * ((TauReal.cis_arctan_im a).approx K).toRat)
       - dh.toRat * a.toRat * arctan_deriv_partial_rat a.toRat K
           * ((TauReal.tangent_defect a).approx K).toRat
       - dh.toRat * ((TauReal.cis_arctan_re a).approx K).toRat
           * (1 - a.toRat^(4*K))|
      ≤ |((TauReal.cis_arctan_re a).approx K).toRat
          + a.toRat * ((TauReal.cis_arctan_im a).approx K).toRat|
        * (dh.toRat^2 * 2 * (K : Rat)^2) := by
  -- Step 1: δ_K.toRat = α_h - α_a, where α_h := arctan_partial_rat(a+dh, K), α_a := ...
  have h_delta_eq :
      (((TauReal.arctan_of_rat_seq (a.add dh)).sub
          (TauReal.arctan_of_rat_seq a)).approx K).toRat
        = ((TauReal.arctan_of_rat_seq (a.add dh)).approx K).toRat
          - ((TauReal.arctan_of_rat_seq a).approx K).toRat := by
    show (TauRat.add ((TauReal.arctan_of_rat_seq (a.add dh)).approx K)
            ((TauReal.arctan_of_rat_seq a).approx K).negate).toRat = _
    rw [toRat_add, toRat_negate]; ring
  -- Step 2: T_K.toRat = B_K - a·A_K (def of tangent_defect)
  have h_T_eq :
      ((TauReal.tangent_defect a).approx K).toRat
        = ((TauReal.cis_arctan_im a).approx K).toRat
          - a.toRat * ((TauReal.cis_arctan_re a).approx K).toRat := by
    rw [TauReal.tangent_defect_approx_toRat]
  -- Step 3: Apply 6.M3 — |δ_K - dh·d_K| ≤ dh²·2K²
  have h_M3 := TauReal.arctan_increment_secant_taylor_bound a dh ha hdh_nn hdh_le_half K
  rw [h_delta_eq] at h_M3
  -- Step 4: Geometric identity at Rat level — d_K · (1+a²) = 1 - a^(4K)
  have h_geom :
      arctan_deriv_partial_rat a.toRat K * (1 + a.toRat^2) = 1 - a.toRat^(4*K) :=
    arctan_deriv_partial_rat_geometric_identity a.toRat K
  -- Step 5: Algebraic identity (using h_geom and h_T_eq):
  --   (α_h - α_a)·(A_K + a·B_K) − dh·a·d_K·T_K − dh·A_K·(1 - a^(4K))
  --     = (A_K + a·B_K)·(α_h - α_a - dh·d_K)
  -- Then bound: |RHS| = |A_K + a·B_K|·|α_h - α_a - dh·d_K| ≤ |A_K + a·B_K| · dh²·2K²
  rw [h_delta_eq, h_T_eq]
  set α_a : Rat := ((TauReal.arctan_of_rat_seq a).approx K).toRat
  set α_h : Rat := ((TauReal.arctan_of_rat_seq (a.add dh)).approx K).toRat
  set d_K : Rat := arctan_deriv_partial_rat a.toRat K
  set A_K : Rat := ((TauReal.cis_arctan_re a).approx K).toRat
  set B_K : Rat := ((TauReal.cis_arctan_im a).approx K).toRat
  -- h_M3 in terms of named abbreviations
  change |α_h - α_a - dh.toRat * d_K| ≤ dh.toRat^2 * 2 * (K : Rat)^2 at h_M3
  -- Goal in terms of named abbreviations
  change
      |(α_h - α_a) * (A_K + a.toRat * B_K)
       - dh.toRat * a.toRat * d_K * (B_K - a.toRat * A_K)
       - dh.toRat * A_K * (1 - a.toRat^(4*K))|
      ≤ |A_K + a.toRat * B_K| * (dh.toRat^2 * 2 * (K : Rat)^2)
  -- Algebraic identity (closed by h_geom via linear_combination)
  have h_identity :
      (α_h - α_a) * (A_K + a.toRat * B_K)
        - dh.toRat * a.toRat * d_K * (B_K - a.toRat * A_K)
        - dh.toRat * A_K * (1 - a.toRat^(4*K))
      = (A_K + a.toRat * B_K) * (α_h - α_a - dh.toRat * d_K) := by
    have h_step : d_K * (1 + a.toRat^2) - 1 + a.toRat^(4*K) = 0 := by linarith [h_geom]
    linear_combination dh.toRat * A_K * h_step
  rw [h_identity, abs_mul]
  -- |A_K + a·B_K| · |α_h - α_a - dh·d_K| ≤ |A_K + a·B_K| · (dh²·2K²)
  have h_nn : (0 : Rat) ≤ |A_K + a.toRat * B_K| := _root_.abs_nonneg _
  exact mul_le_mul_of_nonneg_left h_M3 h_nn

/-! ## Sub-Wave 6.M4.D.4 — Pointwise algebraic restatement of 6.M1 at .approx K

  6.M1 is a TauReal-equiv obtained from `equiv_of_pointwise`, so at every
  `.approx n .toRat` we have an EXACT Rat-level identity (no Cauchy modulus).
  Here we extract that pointwise identity for direct use in 6.M5.

  This is the cleanest pointwise foundation: it converts the
  tangent_defect increment into three concrete Rat-level pieces that we
  bound separately via Wave 6c.10b (at TauReal-equiv level, lifted) and
  6.M3/6.M2/6.M4.D.1.
-/

/-- **6.M4.D.4 (pointwise increment identity)** — Pure Rat-level restatement
    of 6.M1 at fixed `.approx K`. -/
theorem TauReal.tangent_defect_increment_pointwise (a dh : TauRat) (K : Nat) :
    ((TauReal.tangent_defect (a.add dh)).approx K).toRat
        - ((TauReal.tangent_defect a).approx K).toRat
      = (((TauReal.cis_arctan_im (a.add dh)).approx K).toRat
            - ((TauReal.cis_arctan_im a).approx K).toRat)
        - dh.toRat * ((TauReal.cis_arctan_re (a.add dh)).approx K).toRat
        - a.toRat * (((TauReal.cis_arctan_re (a.add dh)).approx K).toRat
            - ((TauReal.cis_arctan_re a).approx K).toRat) := by
  rw [TauReal.tangent_defect_approx_toRat, TauReal.tangent_defect_approx_toRat,
      toRat_add]
  ring

/-! ## Uniform pointwise bound for cisTauReal_re/im (Path-β-conditional)

  The 6.M4.D.1 magnitude bound `|cis_arctan_re.approx n .toRat| ≤ 1 + n·α²`
  is K-DEPENDENT, which blocks `equiv_mul_congr` (requires Nat bound
  uniformly in n).

  Here we provide a UNIFORM bound (≤ 8 for any n) by replaying the
  residual+cos_partial bound from `exp_pureIm_re_approx_abs_toRat_le_8`
  (TauRealSinCos.lean), bridged via `cisTauReal_re_approx_toRat`.
-/

/-- **Uniform .approx bound (re)** — For any TauReal `x` with `|x.approx n .toRat| ≤ 1`:
    `((cisTauReal x).re.approx n).abs.toRat ≤ 8`. -/
theorem TauComplex.cisTauReal_re_approx_abs_le_8
    (x : TauReal) (n : Nat) (hx : |(x.approx n).toRat| ≤ 1) :
    ((TauComplex.cisTauReal x).re.approx n).abs.toRat ≤ 8 := by
  rw [TauRat.toRat_abs, cisTauReal_re_approx_toRat]
  -- Goal: |expPartial_pureIm_re_rat (x.approx n).toRat n| ≤ 8
  have h := exp_pureIm_re_approx_abs_toRat_le_8 (x.approx n) hx n
  rw [TauRat.toRat_abs, TauComplex.exp_re_approx,
      expPartial_pureIm_re_approx_toRat_eq_rat] at h
  exact h

/-- **Uniform .approx bound (im)** — For any TauReal `x` with `|x.approx n .toRat| ≤ 1`:
    `((cisTauReal x).im.approx n).abs.toRat ≤ 8`. -/
theorem TauComplex.cisTauReal_im_approx_abs_le_8
    (x : TauReal) (n : Nat) (hx : |(x.approx n).toRat| ≤ 1) :
    ((TauComplex.cisTauReal x).im.approx n).abs.toRat ≤ 8 := by
  rw [TauRat.toRat_abs, cisTauReal_im_approx_toRat]
  have h := exp_pureIm_im_approx_abs_toRat_le_8 (x.approx n) hx n
  rw [TauRat.toRat_abs, TauComplex.exp_im_approx,
      expPartial_pureIm_im_approx_toRat_eq_rat] at h
  exact h

/-- **Uniform bound for cis_arctan_re** under Path β. -/
theorem TauReal.cis_arctan_re_approx_abs_le_8
    (a : TauRat) (ha : 2 * |a.toRat| ≤ 1) (n : Nat) :
    ((TauReal.cis_arctan_re a).approx n).abs.toRat ≤ 8 := by
  show ((TauComplex.cisTauReal (TauReal.arctan_of_rat_seq a)).re.approx n).abs.toRat ≤ 8
  apply TauComplex.cisTauReal_re_approx_abs_le_8
  have h_bound := TauReal.arctan_of_rat_seq_bounded a ha n
  rw [TauRat.toRat_abs] at h_bound
  exact h_bound

/-- **Uniform bound for cis_arctan_im** under Path β. -/
theorem TauReal.cis_arctan_im_approx_abs_le_8
    (a : TauRat) (ha : 2 * |a.toRat| ≤ 1) (n : Nat) :
    ((TauReal.cis_arctan_im a).approx n).abs.toRat ≤ 8 := by
  show ((TauComplex.cisTauReal (TauReal.arctan_of_rat_seq a)).im.approx n).abs.toRat ≤ 8
  apply TauComplex.cisTauReal_im_approx_abs_le_8
  have h_bound := TauReal.arctan_of_rat_seq_bounded a ha n
  rw [TauRat.toRat_abs] at h_bound
  exact h_bound

/-! ## Sub-Wave F.1a — Residual bound for `dh · re(a+dh)` vs. `dh · A_K · (1−a^(4K))`

  Combines F.0 (Lipschitz for expPartial_re) with the geometric tail
  `a^(4K)` and the uniform bound `|A_K| ≤ 8`:

      |dh · A_h.K − dh · A_K · (1 − a^(4K))|
        ≤ |dh| · K · |δ_arctan.K| + 8·|dh| · |a|^(4K)

  Downstream (F.1b), the `|δ_arctan.K|` factor is bounded via 6.M3
  (`δ_arctan.K = dh · d_K + O(dh² · K²)`), and `|a|^(4K)` is bounded by
  `(1/4)^(4K)` under Path β — exponentially small in K.
-/

/-- **F.1a** — Residual bound for `dh · re(a+dh) − dh · A_K · (1 − a^(4K))`. -/
theorem TauReal.tangent_defect_re_residual_bound
    (a dh : TauRat) (ha : 4 * |a.toRat| ≤ 1) (hah : 4 * |(a.add dh).toRat| ≤ 1)
    (K : Nat) :
    |dh.toRat * (((TauReal.cis_arctan_re (a.add dh)).approx K).toRat)
       - dh.toRat * (((TauReal.cis_arctan_re a).approx K).toRat)
          * (1 - a.toRat^(4*K))|
      ≤ |dh.toRat| * (K : Rat) *
          |(((TauReal.arctan_of_rat_seq (a.add dh)).sub
              (TauReal.arctan_of_rat_seq a)).approx K).toRat|
        + |dh.toRat| * 8 * |a.toRat|^(4*K) := by
  -- Decompose: A_h.K - A_K · (1 - a^(4K)) = (A_h.K - A_K) + A_K · a^(4K)
  set A_K : Rat := ((TauReal.cis_arctan_re a).approx K).toRat
  set A_h_K : Rat := ((TauReal.cis_arctan_re (a.add dh)).approx K).toRat
  set δ_arctan : Rat := (((TauReal.arctan_of_rat_seq (a.add dh)).sub
      (TauReal.arctan_of_rat_seq a)).approx K).toRat
  have h_decomp :
      dh.toRat * A_h_K - dh.toRat * A_K * (1 - a.toRat^(4*K))
        = dh.toRat * (A_h_K - A_K) + dh.toRat * A_K * a.toRat^(4*K) := by ring
  rw [h_decomp]
  have h_tri :
      |dh.toRat * (A_h_K - A_K) + dh.toRat * A_K * a.toRat^(4*K)|
      ≤ |dh.toRat * (A_h_K - A_K)| + |dh.toRat * A_K * a.toRat^(4*K)| :=
    abs_add_le _ _
  -- Part 1: |dh · (A_h_K - A_K)| ≤ |dh| · K · |δ_arctan|
  have h_part1 : |dh.toRat * (A_h_K - A_K)| ≤ |dh.toRat| * (K : Rat) * |δ_arctan| := by
    rw [abs_mul]
    have h_α_h_bound : |((TauReal.arctan_of_rat_seq (a.add dh)).approx K).toRat| ≤ 1 := by
      have := TauReal.arctan_of_rat_seq_bounded (a.add dh)
        (by linarith [_root_.abs_nonneg (a.add dh).toRat]) K
      rwa [TauRat.toRat_abs] at this
    have h_α_a_bound : |((TauReal.arctan_of_rat_seq a).approx K).toRat| ≤ 1 := by
      have := TauReal.arctan_of_rat_seq_bounded a
        (by linarith [_root_.abs_nonneg a.toRat]) K
      rwa [TauRat.toRat_abs] at this
    have h_F0 : |A_h_K - A_K| ≤ (K : Rat) *
        |((TauReal.arctan_of_rat_seq (a.add dh)).approx K).toRat
          - ((TauReal.arctan_of_rat_seq a).approx K).toRat| := by
      show |((TauComplex.cisTauReal (TauReal.arctan_of_rat_seq (a.add dh))).re.approx K).toRat
            - ((TauComplex.cisTauReal (TauReal.arctan_of_rat_seq a)).re.approx K).toRat|
            ≤ _
      rw [cisTauReal_re_approx_toRat, cisTauReal_re_approx_toRat]
      exact expPartial_pureIm_re_rat_lipschitz_bound _ _ h_α_h_bound h_α_a_bound K
    have h_δ_eq :
        |((TauReal.arctan_of_rat_seq (a.add dh)).approx K).toRat
          - ((TauReal.arctan_of_rat_seq a).approx K).toRat|
        = |δ_arctan| := by
      show _ = |(TauRat.add ((TauReal.arctan_of_rat_seq (a.add dh)).approx K)
                   ((TauReal.arctan_of_rat_seq a).approx K).negate).toRat|
      rw [toRat_add, toRat_negate]
      congr 1; ring
    rw [h_δ_eq] at h_F0
    have h_dh_abs_nn : (0 : Rat) ≤ |dh.toRat| := _root_.abs_nonneg _
    calc |dh.toRat| * |A_h_K - A_K|
        ≤ |dh.toRat| * ((K : Rat) * |δ_arctan|) :=
            mul_le_mul_of_nonneg_left h_F0 h_dh_abs_nn
      _ = |dh.toRat| * (K : Rat) * |δ_arctan| := by ring
  -- Part 2: |dh · A_K · a^(4K)| ≤ |dh| · 8 · |a|^(4K)
  have h_part2 : |dh.toRat * A_K * a.toRat^(4*K)|
      ≤ |dh.toRat| * 8 * |a.toRat|^(4*K) := by
    rw [abs_mul, abs_mul]
    have h_A_K_bound : |A_K| ≤ 8 := by
      have := TauReal.cis_arctan_re_approx_abs_le_8 a
        (by linarith [_root_.abs_nonneg a.toRat]) K
      rwa [TauRat.toRat_abs] at this
    have h_a_pow_abs : |a.toRat^(4*K)| = |a.toRat|^(4*K) := abs_pow _ _
    rw [h_a_pow_abs]
    have h_dh_abs_nn : (0 : Rat) ≤ |dh.toRat| := _root_.abs_nonneg _
    have h_a_pow_nn : (0 : Rat) ≤ |a.toRat|^(4*K) := by positivity
    have h_dh_AK : |dh.toRat| * |A_K| ≤ |dh.toRat| * 8 :=
      mul_le_mul_of_nonneg_left h_A_K_bound h_dh_abs_nn
    exact mul_le_mul_of_nonneg_right h_dh_AK h_a_pow_nn
  linarith [h_tri, h_part1, h_part2]

/-! ## Sub-Wave 6.M5.A — TauReal-equiv increment with Wave 6c.10b (im) substituted

  Chains 6.M1 (algebraic rearrangement) with Wave 6c.10b (im, difference
  formula) to express the tangent_defect increment as:

      T(a+dh) − T(a)
        ≈_TR  [A·I + B·(R−1)] − dh·re(a+dh) − a·(re(a+dh) − re(a))

  where A := cis_arctan_re(a), B := cis_arctan_im(a),
  R := cisTauReal(δ_arctan).re, I := cisTauReal(δ_arctan).im,
  δ_arctan := arctan_of_rat_seq(a+dh) − arctan_of_rat_seq(a).

  The Wave 6c.10b (re) substitution into `a·(re(a+dh) − re(a))` requires
  `equiv_mul_congr` with uniform bounds on re_diff — which we don't have
  pointwise (since |cis_arctan_re.approx n| ≤ 1 + n·α² is K-dependent).
  Substituting Wave 6c.10b (re) is therefore handled at .approx K
  via pointwise toRat algebra in 6.M5.B (next sub-Wave).
-/

/-- **6.M5.A** — Increment via 6.M1 + Wave 6c.10b (im). -/
theorem TauReal.tangent_defect_increment_via_6c10b_im
    (a dh : TauRat) (ha : 4 * |a.toRat| ≤ 1) (hah : 4 * |(a.add dh).toRat| ≤ 1) :
    TauReal.equiv
      ((TauReal.tangent_defect (a.add dh)).sub (TauReal.tangent_defect a))
      (((((TauReal.cis_arctan_re a).mul
              (TauComplex.cisTauReal
                ((TauReal.arctan_of_rat_seq (a.add dh)).sub
                  (TauReal.arctan_of_rat_seq a))).im).add
            ((TauReal.cis_arctan_im a).mul
              (((TauComplex.cisTauReal
                  ((TauReal.arctan_of_rat_seq (a.add dh)).sub
                    (TauReal.arctan_of_rat_seq a))).re).sub TauReal.one))).sub
          ((TauReal.fromTauRat dh).mul (TauReal.cis_arctan_re (a.add dh)))).sub
        ((TauReal.fromTauRat a).mul
          ((TauReal.cis_arctan_re (a.add dh)).sub (TauReal.cis_arctan_re a)))) := by
  -- Chain: 6.M1 → substitute Wave 6c.10b (im) inside via equiv_sub_congr
  apply TauReal.equiv_trans (TauReal.tangent_defect_increment_rearranged a dh)
  -- Goal: 6.M1 RHS ≈_TR target
  -- Structure: 6.M1 RHS = ((im_diff - dh·re_h) - a·re_diff)
  --            target   = ((6c.10b_im_RHS - dh·re_h) - a·re_diff)
  -- So substitute im_diff ≈ 6c.10b_im_RHS via equiv_sub_congr (twice nested).
  apply TauReal.equiv_sub_congr
  · -- Inner: (im_diff - dh·re_h) ≈_TR (6c.10b_im_RHS - dh·re_h)
    apply TauReal.equiv_sub_congr
    · -- im_diff ≈_TR 6c.10b_im_RHS (= Wave 6c.10b im)
      exact TauReal.cis_arctan_im_diff_factored a dh ha hah
    · -- dh·re_h ≈_TR dh·re_h (refl)
      exact TauReal.equiv_refl _
  · -- a·re_diff ≈_TR a·re_diff (refl — no substitution here)
    exact TauReal.equiv_refl _

/-! ## Sub-Wave 6.M5.B — Full TauReal-equiv decomposition

  Chains 6.M5.A with `equiv_mul_congr` to substitute Wave 6c.10b (re) into
  the `a · (re(a+dh) − re(a))` term. The substitution requires the uniform
  bound `|cis_arctan_re.approx n| ≤ 8` (now shipped above), enabling
  `equiv_mul_congr` with Ma = 1, Mb = 16.

  Final form:
      T(a+dh) − T(a) ≈_TR  [A·I + B·(R−1)] − dh·re(a+dh) − a·[A·(R−1) − B·I]
-/

/-- **6.M5.B** — Full TauReal-equiv decomposition of the increment with
    both Wave 6c.10b diffs substituted. -/
theorem TauReal.tangent_defect_increment_via_6c10b_full
    (a dh : TauRat) (ha : 4 * |a.toRat| ≤ 1) (hah : 4 * |(a.add dh).toRat| ≤ 1) :
    TauReal.equiv
      ((TauReal.tangent_defect (a.add dh)).sub (TauReal.tangent_defect a))
      (((((TauReal.cis_arctan_re a).mul
              (TauComplex.cisTauReal
                ((TauReal.arctan_of_rat_seq (a.add dh)).sub
                  (TauReal.arctan_of_rat_seq a))).im).add
            ((TauReal.cis_arctan_im a).mul
              (((TauComplex.cisTauReal
                  ((TauReal.arctan_of_rat_seq (a.add dh)).sub
                    (TauReal.arctan_of_rat_seq a))).re).sub TauReal.one))).sub
          ((TauReal.fromTauRat dh).mul (TauReal.cis_arctan_re (a.add dh)))).sub
        ((TauReal.fromTauRat a).mul
          (((TauReal.cis_arctan_re a).mul
              (((TauComplex.cisTauReal
                  ((TauReal.arctan_of_rat_seq (a.add dh)).sub
                    (TauReal.arctan_of_rat_seq a))).re).sub TauReal.one)).sub
            ((TauReal.cis_arctan_im a).mul
              (TauComplex.cisTauReal
                ((TauReal.arctan_of_rat_seq (a.add dh)).sub
                  (TauReal.arctan_of_rat_seq a))).im)))) := by
  -- Start from 6.M5.A: (im_diff substituted, re_diff untouched)
  apply TauReal.equiv_trans (TauReal.tangent_defect_increment_via_6c10b_im a dh ha hah)
  -- Goal: substitute re_diff inside `a · re_diff` via equiv_mul_congr
  apply TauReal.equiv_sub_congr
  · -- Inner part unchanged
    exact TauReal.equiv_refl _
  · -- `a · re_diff ≈_TR a · re_diff_factored` via equiv_mul_congr
    apply TauReal.equiv_mul_congr (Ma := 1) (Mb := 16) (by omega : (1:Nat) ≤ 1) (by omega : (1:Nat) ≤ 16)
    · -- Bound on `fromTauRat a`: |a.toRat| ≤ 1
      intro n
      show ((TauReal.fromTauRat a).approx n).abs.toRat ≤ (1 : Nat)
      show (a.abs).toRat ≤ (1 : Rat)
      rw [TauRat.toRat_abs]
      have h_abs : |a.toRat| ≤ 1/4 := by linarith [_root_.abs_nonneg a.toRat]
      linarith
    · -- Bound on `re_diff = cis_arctan_re(a+dh) - cis_arctan_re(a)`: |.approx n| ≤ 16
      intro n
      show (((TauReal.cis_arctan_re (a.add dh)).sub (TauReal.cis_arctan_re a)).approx n).abs.toRat
            ≤ (16 : Nat)
      show (TauRat.add ((TauReal.cis_arctan_re (a.add dh)).approx n)
              ((TauReal.cis_arctan_re a).approx n).negate).abs.toRat ≤ (16 : Rat)
      rw [TauRat.toRat_abs, toRat_add, toRat_negate]
      -- |x + (-y)| ≤ |x| + |y|, each ≤ 8
      have h_h : ((TauReal.cis_arctan_re (a.add dh)).approx n).abs.toRat ≤ 8 := by
        apply TauReal.cis_arctan_re_approx_abs_le_8
        linarith [_root_.abs_nonneg (a.add dh).toRat]
      have h_a : ((TauReal.cis_arctan_re a).approx n).abs.toRat ≤ 8 := by
        apply TauReal.cis_arctan_re_approx_abs_le_8
        linarith [_root_.abs_nonneg a.toRat]
      rw [TauRat.toRat_abs] at h_h h_a
      have h_tri :
          |((TauReal.cis_arctan_re (a.add dh)).approx n).toRat
            + -((TauReal.cis_arctan_re a).approx n).toRat|
            ≤ |((TauReal.cis_arctan_re (a.add dh)).approx n).toRat|
              + |-((TauReal.cis_arctan_re a).approx n).toRat| := abs_add_le _ _
      rw [abs_neg] at h_tri
      linarith
    · -- a = a (refl)
      exact TauReal.equiv_refl _
    · -- Wave 6c.10b (re): re_diff ≈_TR (A·(R-1) - B·I)
      exact TauReal.cis_arctan_re_diff_factored a dh ha hah

/-! ## Sub-Wave 6.M5.C — Algebraic simplification: extract `T(a)·(R−1)`

  Simplifies 6.M5.B's RHS by recognizing `B − a·A = T(a)`:

      [A·I + B·(R−1)] − dh·re(a+dh) − a·[A·(R−1) − B·I]
        = (A + a·B)·I + (B − a·A)·(R−1) − dh·re(a+dh)
        = (A + a·B)·I + T(a)·(R−1) − dh·re(a+dh)

  Pure algebra at TauReal-equiv level. Proven via direct pointwise toRat
  comparison: both sides expand to the same Rat-level polynomial.
-/

/-- **6.M5.C** — Full TauReal-equiv decomposition with `T(a)·(R−1)` exposed.

    Proof: chain 6.M5.B's TauReal-equiv with the algebraic identity
    proved pointwise at every `.approx n .toRat`. -/
theorem TauReal.tangent_defect_increment_simplified
    (a dh : TauRat) (ha : 4 * |a.toRat| ≤ 1) (hah : 4 * |(a.add dh).toRat| ≤ 1) :
    TauReal.equiv
      ((TauReal.tangent_defect (a.add dh)).sub (TauReal.tangent_defect a))
      (((((TauReal.cis_arctan_re a).add
              ((TauReal.fromTauRat a).mul (TauReal.cis_arctan_im a))).mul
            (TauComplex.cisTauReal
              ((TauReal.arctan_of_rat_seq (a.add dh)).sub
                (TauReal.arctan_of_rat_seq a))).im).add
          ((TauReal.tangent_defect a).mul
            (((TauComplex.cisTauReal
                ((TauReal.arctan_of_rat_seq (a.add dh)).sub
                  (TauReal.arctan_of_rat_seq a))).re).sub TauReal.one))).sub
        ((TauReal.fromTauRat dh).mul (TauReal.cis_arctan_re (a.add dh)))) := by
  -- Use 6.M5.B to convert LHS, then prove the algebraic simplification pointwise.
  -- The simplification: 6.M5.B RHS ≈_TR 6.M5.C RHS at every .approx n.
  apply TauReal.equiv_trans
    (TauReal.tangent_defect_increment_via_6c10b_full a dh ha hah)
  apply TauReal.equiv_of_pointwise
  intro n
  rw [equiv_iff_toRat_eq]
  -- Both sides are pointwise equal at .approx n .toRat after using T(a) = B - a·A.
  -- Strategy: rewrite using TauReal.tangent_defect_approx_toRat in the goal, then ring.
  -- The goal is structurally `(LHS).approx n .toRat = (RHS).approx n .toRat`.
  -- Each side unfolds via the @[simp] lemmas for sub/add/mul of TauReal (definitional).
  -- After distributing .toRat through toRat_add/mul/negate, we get Rat expressions.
  simp only [show ∀ (x y : TauReal) (m : Nat), ((x.sub y).approx m).toRat
               = (x.approx m).toRat - (y.approx m).toRat from by
                 intros x y m
                 show (TauRat.add (x.approx m) (y.approx m).negate).toRat = _
                 rw [toRat_add, toRat_negate]; ring,
             show ∀ (x y : TauReal) (m : Nat), ((x.add y).approx m).toRat
               = (x.approx m).toRat + (y.approx m).toRat from by
                 intros x y m
                 show (TauRat.add (x.approx m) (y.approx m)).toRat = _
                 rw [toRat_add],
             show ∀ (x y : TauReal) (m : Nat), ((x.mul y).approx m).toRat
               = (x.approx m).toRat * (y.approx m).toRat from by
                 intros x y m
                 show (TauRat.mul (x.approx m) (y.approx m)).toRat = _
                 rw [toRat_mul],
             show ((TauReal.one).approx n).toRat = 1 from by
               show (TauRat.one).toRat = _; rw [toRat_one],
             show ((TauReal.fromTauRat dh).approx n).toRat = dh.toRat from rfl,
             show ((TauReal.fromTauRat a).approx n).toRat = a.toRat from rfl,
             TauReal.tangent_defect_approx_toRat]
  ring

/-! ## Sub-Wave 6.M5.D — Gronwall walk foundation

  Two foundational pieces:
  1. **Pointwise base case**: `T(0).approx K .toRat = 0` at every depth K.
  2. **Gronwall wrapper**: given a per-step increment bound, derive the final
     Gronwall bound via `Rat.discrete_gronwall_abs`.

  The wrapper takes the increment bound as a HYPOTHESIS — the increment bound
  discharge (from 6.M5.C + 6.M2 + 6.M3 + 6.M4.D.3) is the analytical content
  to be filled in at the application site.
-/

/-- **Pointwise base case** — `T(0).approx K .toRat = 0` at every depth. -/
theorem TauReal.tangent_defect_zero_approx_toRat (K : Nat) :
    ((TauReal.tangent_defect TauRat.zero).approx K).toRat = 0 := by
  rw [TauReal.tangent_defect_approx_toRat,
      TauReal.cis_arctan_im_at_zero_approx_zero K]
  show (0 : Rat) - TauRat.zero.toRat * _ = 0
  rw [toRat_zero]
  ring

/-- **6.M5.D (Gronwall wrapper)** — Given a base-case-zero walk and a per-step
    increment bound `|T(a_{n+1}) − T(a_n)|.approx K .toRat ≤ M·|T(a_n)| + δ`,
    derive the final Gronwall bound via `Rat.discrete_gronwall_abs`. -/
theorem TauReal.tangent_defect_gronwall_walk_bound
    (K : Nat) (M δ : Rat) (hM : 0 ≤ M) (hδ : 0 ≤ δ)
    (a_seq : Nat → TauRat)
    (h_a_0 : a_seq 0 = TauRat.zero)
    (h_step_bound : ∀ n,
      |((TauReal.tangent_defect (a_seq (n+1))).approx K).toRat
        - ((TauReal.tangent_defect (a_seq n)).approx K).toRat|
      ≤ M * |((TauReal.tangent_defect (a_seq n)).approx K).toRat| + δ) :
    ∀ N, |((TauReal.tangent_defect (a_seq N)).approx K).toRat|
          ≤ (N : Rat) * (1+M)^N * δ := by
  -- Define v(n) := T(a_seq n).approx K .toRat
  set v : Nat → Rat := fun n => ((TauReal.tangent_defect (a_seq n)).approx K).toRat
  -- v(0) = 0 (base case)
  have h_v_0 : v 0 = 0 := by
    show ((TauReal.tangent_defect (a_seq 0)).approx K).toRat = 0
    rw [h_a_0, TauReal.tangent_defect_zero_approx_toRat]
  have h_v_0_abs : |v 0| ≤ 0 := by rw [h_v_0]; simp
  -- Step bound: |v(n+1)| ≤ (1+M) · |v n| + δ
  -- Derived from h_step_bound via triangle inequality
  have h_v_step : ∀ n, |v (n+1)| ≤ (1+M) * |v n| + δ := by
    intro n
    show |((TauReal.tangent_defect (a_seq (n+1))).approx K).toRat|
          ≤ (1+M) * |((TauReal.tangent_defect (a_seq n)).approx K).toRat| + δ
    have h_inc := h_step_bound n
    -- |T_{n+1}| ≤ |T_{n+1} - T_n| + |T_n|
    set v_n := ((TauReal.tangent_defect (a_seq n)).approx K).toRat
    set v_n1 := ((TauReal.tangent_defect (a_seq (n+1))).approx K).toRat
    have h_tri : |v_n1| ≤ |v_n1 - v_n| + |v_n| := by
      have := abs_add_le (v_n1 - v_n) v_n
      simpa using this
    linarith
  -- Apply Rat.discrete_gronwall_abs with ε₀ = 0
  have h_ε₀_nn : (0 : Rat) ≤ 0 := by norm_num
  have h_gronwall := Rat.discrete_gronwall_abs v M δ (0 : Rat) hM hδ
    h_ε₀_nn h_v_0_abs h_v_step
  intro N
  have h_N := h_gronwall N
  -- u_N ≤ (1+M)^N * 0 + N * (1+M)^N * δ = N * (1+M)^N * δ
  have h_simp : (1+M)^N * 0 + (N : Rat) * (1+M)^N * δ = (N : Rat) * (1+M)^N * δ := by ring
  linarith

/-! ## Sub-Wave 6.M5.D-application — Walk construction

  Defines a TauRat walk from 0 to `a` in N steps, used to instantiate the
  Gronwall wrapper. The walk step is `n·a/N` represented as a TauRat by
  scaling the numerator by `n` and the denominator by `N`.
-/

/-- **Gronwall walk step** — TauRat representing `n·a/N` for `n ≤ N`. -/
def TauRat.gronwallWalkStep (a : TauRat) (n N : Nat) (hN : 0 < N) : TauRat :=
  ⟨a.num.mul (TauInt.fromNat n), a.den * N, Nat.mul_pos a.den_pos hN⟩

/-- The walk-step .toRat is `(n : Rat) · a.toRat / N`. -/
theorem TauRat.gronwallWalkStep_toRat (a : TauRat) (n N : Nat) (hN : 0 < N) :
    (TauRat.gronwallWalkStep a n N hN).toRat = (n : Rat) * a.toRat / (N : Rat) := by
  show ((a.num.mul (TauInt.fromNat n)).toInt : Rat) / ((a.den * N : Nat) : Rat) = _
  rw [toInt_mul, toInt_fromNat]
  unfold TauRat.toRat
  push_cast
  have h_a_den_pos : (0 : Rat) < (a.den : Rat) := by exact_mod_cast a.den_pos
  have h_N_pos : (0 : Rat) < (N : Rat) := by exact_mod_cast hN
  field_simp

/-- At `n = 0`, the walk step has `.toRat = 0`. -/
theorem TauRat.gronwallWalkStep_zero_toRat (a : TauRat) (N : Nat) (hN : 0 < N) :
    (TauRat.gronwallWalkStep a 0 N hN).toRat = 0 := by
  rw [TauRat.gronwallWalkStep_toRat]
  simp

/-- At `n = N`, the walk step has `.toRat = a.toRat` (endpoint matches). -/
theorem TauRat.gronwallWalkStep_full_toRat (a : TauRat) (N : Nat) (hN : 0 < N) :
    (TauRat.gronwallWalkStep a N N hN).toRat = a.toRat := by
  rw [TauRat.gronwallWalkStep_toRat]
  have h_N_pos : (0 : Rat) < (N : Rat) := by exact_mod_cast hN
  field_simp

/-! ## Sub-Wave 6.M5.D-application — Per-step increment bound at .approx K

  The analytical heart of the Gronwall walk discharge. Combines:
  - 6.M5.C TauReal-equiv at `.approx K` (spending the Cauchy modulus
    from `cisTauReal_add` propagation)
  - 6.M4.D.3 linear-term extraction (pointwise at Rat level)
  - 6.M2 small-angle bounds (pointwise at Rat level)
  - 6.M3 secant Taylor (pointwise at Rat level)
  - 6.M4.D.1 magnitude bounds (pointwise at Rat level)

  Yields the Gronwall recurrence form:
  ```
  |T(a+dh).approx K_eff - T(a).approx K_eff|
    ≤ M(K_eff,dh) · |T(a).approx K_eff| + δ(K_eff,dh)
  ```

  where the linear coefficient `M` comes from `(R−1) + dh·a·d_K` and the
  absolute term `δ` bounds all the O(dh²·K²) and exponentially-small
  `a^(4K)` errors, plus the modulus error from 6.M5.C.
-/

/-- **Destructure helper** — Extract the modulus from 6.M5.C's TauReal-equiv,
    exposing an explicit `K_M` (the modulus) and the pointwise bound at .approx K
    for all K ≥ K_M. -/
theorem TauReal.tangent_defect_increment_simplified_at_K
    (a dh : TauRat) (ha : 4 * |a.toRat| ≤ 1) (hah : 4 * |(a.add dh).toRat| ≤ 1) :
    ∃ μ_5C : Nat → Nat, ∀ k_M K, μ_5C k_M ≤ K →
      |((TauReal.tangent_defect (a.add dh)).approx K).toRat
        - ((TauReal.tangent_defect a).approx K).toRat
        - ((((((TauReal.cis_arctan_re a).add
                ((TauReal.fromTauRat a).mul (TauReal.cis_arctan_im a))).mul
              (TauComplex.cisTauReal
                ((TauReal.arctan_of_rat_seq (a.add dh)).sub
                  (TauReal.arctan_of_rat_seq a))).im).add
            ((TauReal.tangent_defect a).mul
              (((TauComplex.cisTauReal
                  ((TauReal.arctan_of_rat_seq (a.add dh)).sub
                    (TauReal.arctan_of_rat_seq a))).re).sub TauReal.one))).sub
          ((TauReal.fromTauRat dh).mul
            (TauReal.cis_arctan_re (a.add dh)))).approx K).toRat|
      < 1 / ((k_M : Rat) + 1) := by
  obtain ⟨μ_5C, hμ_5C⟩ :=
    TauReal.tangent_defect_increment_simplified a dh ha hah
  refine ⟨μ_5C, ?_⟩
  intro k_M K hK
  have h := hμ_5C k_M K hK
  unfold TauRat.lt at h
  rw [TauRat.toRat_abs, toRat_sub, TauRat.ofNatRecip_toRat] at h
  -- h has (T(a+dh).sub T(a)).approx K .toRat; we want T(a+dh).approx K .toRat - T(a).approx K .toRat
  -- These are equal via toRat_add + toRat_negate (since .sub = .add . negate definitionally).
  have h_sub :
      (((TauReal.tangent_defect (a.add dh)).sub
          (TauReal.tangent_defect a)).approx K).toRat
        = ((TauReal.tangent_defect (a.add dh)).approx K).toRat
          - ((TauReal.tangent_defect a).approx K).toRat := by
    show (TauRat.add ((TauReal.tangent_defect (a.add dh)).approx K)
            ((TauReal.tangent_defect a).approx K).negate).toRat = _
    rw [toRat_add, toRat_negate]; ring
  rw [h_sub] at h
  exact h

/-! ## F.1b helpers — bounds on `d_K`, `|A+a·B|`, and `|δ_K|`

  Three small Rat-level helpers used in F.1b:
  - `|d_K| ≤ 1` (under Path β, from geometric identity)
  - `|A_K + a·B_K| ≤ 10` (uniform bound)
  - `|δ_K| ≤ 2·dh` (under hypothesis `2·K²·dh ≤ 1`)
-/

/-- **Helper for F.1b** — Under Path β, `|d_K| ≤ 1`. -/
theorem arctan_deriv_partial_rat_abs_le_one (a : TauRat) (ha : 4 * |a.toRat| ≤ 1) (K : Nat) :
    |arctan_deriv_partial_rat a.toRat K| ≤ 1 := by
  -- From d_K · (1+a²) = 1 - a^(4K), we have d_K = (1 - a^(4K)) / (1+a²).
  -- |1 - a^(4K)| ≤ 1 since 0 ≤ a^(4K) ≤ 1 (Path β + 4K even).
  -- (1+a²) ≥ 1. So |d_K| ≤ 1.
  have h_geom := arctan_deriv_partial_rat_geometric_identity a.toRat K
  -- h_geom : d_K · (1 + a²) = 1 - a^(4K)
  have h_a_abs : |a.toRat| ≤ 1/4 := by linarith [_root_.abs_nonneg a.toRat]
  have h_a_pow_nn : (0 : Rat) ≤ a.toRat^(4*K) := by
    have h_even : ∃ m, 4 * K = 2 * m := ⟨2 * K, by ring⟩
    obtain ⟨m, hm⟩ := h_even
    rw [hm, pow_mul]
    exact pow_nonneg (sq_nonneg _) m
  have h_a_pow_le_one : a.toRat^(4*K) ≤ 1 := by
    have h_le_abs : a.toRat^(4*K) ≤ |a.toRat^(4*K)| := le_abs_self _
    rw [abs_pow] at h_le_abs
    have h_abs_le_one : |a.toRat| ≤ 1 := by linarith
    have h_abs_pow_le_one : |a.toRat|^(4*K) ≤ 1 :=
      pow_le_one₀ (_root_.abs_nonneg _) h_abs_le_one
    linarith
  have h_one_minus_pow_bound : |1 - a.toRat^(4*K)| ≤ 1 := by
    rw [abs_of_nonneg]
    · linarith
    · linarith
  have h_one_plus_sq_pos : (0 : Rat) < 1 + a.toRat^2 := by positivity
  have h_one_plus_sq_ge_one : (1 : Rat) ≤ 1 + a.toRat^2 := by
    have : (0 : Rat) ≤ a.toRat^2 := sq_nonneg _
    linarith
  -- |d_K| · (1+a²) = |d_K · (1+a²)| = |1 - a^(4K)| ≤ 1
  -- (1+a²) ≥ 1, so |d_K| ≤ 1.
  have h_abs_product : |arctan_deriv_partial_rat a.toRat K| * (1 + a.toRat^2)
                       = |1 - a.toRat^(4*K)| := by
    rw [show |arctan_deriv_partial_rat a.toRat K| * (1 + a.toRat^2)
          = |arctan_deriv_partial_rat a.toRat K * (1 + a.toRat^2)| from by
            rw [abs_mul, abs_of_pos h_one_plus_sq_pos]]
    rw [h_geom]
  have h_d_K_nn : (0 : Rat) ≤ |arctan_deriv_partial_rat a.toRat K| := _root_.abs_nonneg _
  nlinarith [h_abs_product, h_one_minus_pow_bound, h_one_plus_sq_ge_one, h_d_K_nn]

/-- **Helper for F.1b** — Under Path β, `|A_K + a·B_K| ≤ 10`. -/
theorem TauReal.cis_arctan_re_plus_a_cis_arctan_im_abs_le_ten
    (a : TauRat) (ha : 4 * |a.toRat| ≤ 1) (K : Nat) :
    |((TauReal.cis_arctan_re a).approx K).toRat
       + a.toRat * ((TauReal.cis_arctan_im a).approx K).toRat| ≤ 10 := by
  have ha2 : 2 * |a.toRat| ≤ 1 := by linarith [_root_.abs_nonneg a.toRat]
  have h_a_abs : |a.toRat| ≤ 1/4 := by linarith [_root_.abs_nonneg a.toRat]
  have h_A_K : ((TauReal.cis_arctan_re a).approx K).abs.toRat ≤ 8 :=
    TauReal.cis_arctan_re_approx_abs_le_8 a ha2 K
  have h_B_K : ((TauReal.cis_arctan_im a).approx K).abs.toRat ≤ 8 :=
    TauReal.cis_arctan_im_approx_abs_le_8 a ha2 K
  rw [TauRat.toRat_abs] at h_A_K h_B_K
  have h_tri : |((TauReal.cis_arctan_re a).approx K).toRat
                  + a.toRat * ((TauReal.cis_arctan_im a).approx K).toRat|
                ≤ |((TauReal.cis_arctan_re a).approx K).toRat|
                  + |a.toRat * ((TauReal.cis_arctan_im a).approx K).toRat| :=
    abs_add_le _ _
  have h_aB_abs : |a.toRat * ((TauReal.cis_arctan_im a).approx K).toRat|
                = |a.toRat| * |((TauReal.cis_arctan_im a).approx K).toRat| := abs_mul _ _
  have h_aB_bound : |a.toRat| * |((TauReal.cis_arctan_im a).approx K).toRat| ≤ (1/4) * 8 := by
    have h_a_nn : (0 : Rat) ≤ |a.toRat| := _root_.abs_nonneg _
    have h_B_nn : (0 : Rat) ≤ |((TauReal.cis_arctan_im a).approx K).toRat| := _root_.abs_nonneg _
    nlinarith [h_a_abs, h_B_K, h_a_nn, h_B_nn]
  linarith [h_tri, h_A_K, h_aB_abs, h_aB_bound]

/-! ## F.1b Sub-helpers — Per-piece bounds on δ_K, |R-1|, |I-δ|

  Three small Rat-level helpers that bound the key δ_K-related quantities
  under the hypothesis `2·K²·dh ≤ 1`:
  - `|δ_K| ≤ 2·dh` (using 6.M3 + |d_K| ≤ 1)
  - `|R_K − 1| ≤ 4·K·dh²` (using 6.M2 re + |δ_K| ≤ 2·dh)
  - `|I_K − δ_K| ≤ 8·K·dh³` (using 6.M2 im + |δ_K| ≤ 2·dh)
-/

/-- **F.1b Sub-helper** — Under `2·K²·dh ≤ 1`, `|δ_K| ≤ 2·dh`. -/
theorem TauReal.arctan_increment_abs_le_two_dh
    (a dh : TauRat) (ha : 4 * |a.toRat| ≤ 1)
    (hdh_nn : 0 ≤ dh.toRat) (hdh_le_half : dh.toRat ≤ 1/2)
    (K : Nat) (hKdh : 2 * (K : Rat)^2 * dh.toRat ≤ 1) :
    |(((TauReal.arctan_of_rat_seq (a.add dh)).sub
        (TauReal.arctan_of_rat_seq a)).approx K).toRat| ≤ 2 * dh.toRat := by
  have h_M3 := TauReal.arctan_increment_secant_taylor_bound a dh ha hdh_nn hdh_le_half K
  have h_d_K := arctan_deriv_partial_rat_abs_le_one a ha K
  have h_dh_d_abs : |dh.toRat * arctan_deriv_partial_rat a.toRat K| ≤ dh.toRat := by
    rw [abs_mul, abs_of_nonneg hdh_nn]
    have := mul_le_mul_of_nonneg_left h_d_K hdh_nn
    linarith
  have h_K_pow_dh : dh.toRat^2 * 2 * (K : Rat)^2 ≤ dh.toRat := by
    have h_K_sq_nn : (0 : Rat) ≤ (K : Rat)^2 := sq_nonneg _
    have h_dh_sq : (0 : Rat) ≤ dh.toRat^2 := sq_nonneg _
    nlinarith [hKdh, hdh_nn, h_K_sq_nn, h_dh_sq]
  have h_tri : |(((TauReal.arctan_of_rat_seq (a.add dh)).sub
                  (TauReal.arctan_of_rat_seq a)).approx K).toRat|
      ≤ |(((TauReal.arctan_of_rat_seq (a.add dh)).sub
            (TauReal.arctan_of_rat_seq a)).approx K).toRat
          - dh.toRat * arctan_deriv_partial_rat a.toRat K|
        + |dh.toRat * arctan_deriv_partial_rat a.toRat K| := by
    have := abs_add_le
      ((((TauReal.arctan_of_rat_seq (a.add dh)).sub
          (TauReal.arctan_of_rat_seq a)).approx K).toRat
        - dh.toRat * arctan_deriv_partial_rat a.toRat K)
      (dh.toRat * arctan_deriv_partial_rat a.toRat K)
    have h_eq : (((TauReal.arctan_of_rat_seq (a.add dh)).sub
                  (TauReal.arctan_of_rat_seq a)).approx K).toRat
                - dh.toRat * arctan_deriv_partial_rat a.toRat K
                + dh.toRat * arctan_deriv_partial_rat a.toRat K
                = (((TauReal.arctan_of_rat_seq (a.add dh)).sub
                    (TauReal.arctan_of_rat_seq a)).approx K).toRat := by ring
    rw [h_eq] at this
    exact this
  linarith

/-- **F.1b Sub-helper** — Under `2·K²·dh ≤ 1`, `|R_K − 1| ≤ 4·K·dh²`. -/
theorem TauReal.R_K_minus_1_abs_le_four_K_dh_sq
    (a dh : TauRat) (ha : 4 * |a.toRat| ≤ 1) (hah : 4 * |(a.add dh).toRat| ≤ 1)
    (hdh_nn : 0 ≤ dh.toRat) (hdh_le_half : dh.toRat ≤ 1/2)
    (K : Nat) (hK : 1 ≤ K) (hKdh : 2 * (K : Rat)^2 * dh.toRat ≤ 1) :
    |((TauComplex.cisTauReal
        ((TauReal.arctan_of_rat_seq (a.add dh)).sub
          (TauReal.arctan_of_rat_seq a))).re.approx K).toRat - 1|
      ≤ 4 * (K : Rat) * dh.toRat^2 := by
  have h_M2_re := TauReal.cisTauReal_arctan_increment_re_small_angle a dh ha hah K hK
  have h_δ_abs := TauReal.arctan_increment_abs_le_two_dh a dh ha hdh_nn hdh_le_half K hKdh
  set δ_K : Rat := (((TauReal.arctan_of_rat_seq (a.add dh)).sub
                    (TauReal.arctan_of_rat_seq a)).approx K).toRat
  have h_δ_sq_bound : δ_K^2 ≤ (2 * dh.toRat)^2 := by
    have h_δ_abs_sq : δ_K^2 = |δ_K|^2 := by rw [sq_abs]
    rw [h_δ_abs_sq]
    have h_δ_abs_nn : (0 : Rat) ≤ |δ_K| := _root_.abs_nonneg _
    exact pow_le_pow_left₀ h_δ_abs_nn h_δ_abs 2
  have h_K_nn : (0 : Rat) ≤ (K : Rat) := Nat.cast_nonneg _
  have h_K_step : (K : Rat) * δ_K^2 ≤ (K : Rat) * (2 * dh.toRat)^2 :=
    mul_le_mul_of_nonneg_left h_δ_sq_bound h_K_nn
  have h_4_K_dh_sq : (K : Rat) * (2 * dh.toRat)^2 = 4 * (K : Rat) * dh.toRat^2 := by ring
  linarith [h_M2_re]

/-- **F.1b Sub-helper** — Under `2·K²·dh ≤ 1`, `|I_K − δ_K| ≤ 8·K·dh³`. -/
theorem TauReal.I_K_minus_delta_K_abs_le_eight_K_dh_cube
    (a dh : TauRat) (ha : 4 * |a.toRat| ≤ 1) (hah : 4 * |(a.add dh).toRat| ≤ 1)
    (hdh_nn : 0 ≤ dh.toRat) (hdh_le_half : dh.toRat ≤ 1/2)
    (K : Nat) (hK : 2 ≤ K) (hKdh : 2 * (K : Rat)^2 * dh.toRat ≤ 1) :
    |((TauComplex.cisTauReal
        ((TauReal.arctan_of_rat_seq (a.add dh)).sub
          (TauReal.arctan_of_rat_seq a))).im.approx K).toRat
      - (((TauReal.arctan_of_rat_seq (a.add dh)).sub
          (TauReal.arctan_of_rat_seq a)).approx K).toRat|
      ≤ 8 * (K : Rat) * dh.toRat^3 := by
  have h_M2_im := TauReal.cisTauReal_arctan_increment_im_small_angle a dh ha hah K hK
  have h_δ_abs := TauReal.arctan_increment_abs_le_two_dh a dh ha hdh_nn hdh_le_half K hKdh
  set δ_K : Rat := (((TauReal.arctan_of_rat_seq (a.add dh)).sub
                    (TauReal.arctan_of_rat_seq a)).approx K).toRat
  have h_δ_cube_bound : |δ_K|^3 ≤ (2 * dh.toRat)^3 := by
    have h_δ_abs_nn : (0 : Rat) ≤ |δ_K| := _root_.abs_nonneg _
    exact pow_le_pow_left₀ h_δ_abs_nn h_δ_abs 3
  have h_K_nn : (0 : Rat) ≤ (K : Rat) := Nat.cast_nonneg _
  have h_K_step : (K : Rat) * |δ_K|^3 ≤ (K : Rat) * (2 * dh.toRat)^3 :=
    mul_le_mul_of_nonneg_left h_δ_cube_bound h_K_nn
  have h_8_K_dh_cube : (K : Rat) * (2 * dh.toRat)^3 = 8 * (K : Rat) * dh.toRat^3 := by ring
  linarith [h_M2_im]

/-! ## Helper A — Pure TauReal→Rat unfolding of the 6.M5.C RHS

  This isolates the deeply-nested TauReal expression normalization into
  a single small theorem. The technique is identical to the inline
  unfold in `tangent_defect_increment_simplified` (line 1248-1268).

  By extracting the unfold into its own theorem, F.1b's main proof can
  `rw` with this lemma in O(1) rather than re-doing the whnf-heavy
  `show + simp only + ring` ritual inside the deeply-set-bound context.
-/

/-- **Helper A** — Pure TauReal→Rat bridge for the 6.M5.C RHS at .approx K. -/
theorem TauReal.RHS_5C_at_K_toRat_unfold (a dh : TauRat) (K : Nat) :
    ((((((TauReal.cis_arctan_re a).add
            ((TauReal.fromTauRat a).mul (TauReal.cis_arctan_im a))).mul
          (TauComplex.cisTauReal
            ((TauReal.arctan_of_rat_seq (a.add dh)).sub
              (TauReal.arctan_of_rat_seq a))).im).add
        ((TauReal.tangent_defect a).mul
          (((TauComplex.cisTauReal
              ((TauReal.arctan_of_rat_seq (a.add dh)).sub
                (TauReal.arctan_of_rat_seq a))).re).sub TauReal.one))).sub
      ((TauReal.fromTauRat dh).mul (TauReal.cis_arctan_re (a.add dh)))).approx K).toRat
      = (((TauReal.cis_arctan_re a).approx K).toRat
          + a.toRat * ((TauReal.cis_arctan_im a).approx K).toRat)
        * ((TauComplex.cisTauReal
            ((TauReal.arctan_of_rat_seq (a.add dh)).sub
              (TauReal.arctan_of_rat_seq a))).im.approx K).toRat
        + ((TauReal.tangent_defect a).approx K).toRat
          * (((TauComplex.cisTauReal
              ((TauReal.arctan_of_rat_seq (a.add dh)).sub
                (TauReal.arctan_of_rat_seq a))).re.approx K).toRat - 1)
        - dh.toRat * ((TauReal.cis_arctan_re (a.add dh)).approx K).toRat := by
  show (TauRat.add
          (TauRat.add
            ((TauRat.add ((TauReal.cis_arctan_re a).approx K)
                (((TauReal.fromTauRat a).approx K).mul
                  ((TauReal.cis_arctan_im a).approx K))).mul
              ((TauComplex.cisTauReal _).im.approx K))
            (((TauReal.tangent_defect a).approx K).mul
              (TauRat.add ((TauComplex.cisTauReal _).re.approx K) TauRat.one.negate)))
          (((TauReal.fromTauRat dh).approx K).mul
            ((TauReal.cis_arctan_re (a.add dh)).approx K)).negate).toRat = _
  simp only [toRat_add, toRat_negate, toRat_mul, toRat_one,
             show ((TauReal.fromTauRat dh).approx K).toRat = dh.toRat from rfl,
             show ((TauReal.fromTauRat a).approx K).toRat = a.toRat from rfl]
  ring

/-! ## Helper B — Pure Rat-level analytical heart of F.1b

  Bounds the 6.M5.C RHS at Rat level, with all `.approx K .toRat`
  quantities passed as parameters and all needed bounds passed as
  hypotheses. The proof operates ONLY on Rat arithmetic — no TauReal
  unfolding, no `set` abbreviations — letting `linarith`/`nlinarith`/
  `linear_combination` excel.

  ```
  |(A + a·B)·I + T_a·(R−1) − dh·re_h|
    ≤ (dh/2 + 9·K·dh²)·|T_a|
      + 200·K²·dh² + 10·dh·|a|^(4K)
  ```

  The four piece bounds compose with generous constants (4 → 9; 20 + 20
  + 2 = 42 ≤ 200; 8 ≤ 10).
-/

set_option maxHeartbeats 1600000 in
/-- **Helper B** — Pure Rat-level analytical bound for the 6.M5.C RHS. -/
theorem TauReal.tangent_defect_step_bound_explicit
    (a_R dh_R A_K B_K R_K I_K re_h_K T_a_K δ_K d_K : Rat) (K : Nat)
    (h_T_def : T_a_K = B_K - a_R * A_K)
    (h_d_K_abs : |d_K| ≤ 1)
    (h_AaB_abs : |A_K + a_R * B_K| ≤ 10)
    (h_δ_abs : |δ_K| ≤ 2 * dh_R)
    (h_R_minus_1 : |R_K - 1| ≤ 4 * (K : Rat) * dh_R^2)
    (h_I_minus_δ : |I_K - δ_K| ≤ 8 * (K : Rat) * dh_R^3)
    (h_D3 : |δ_K * (A_K + a_R * B_K) - dh_R * a_R * d_K * T_a_K
              - dh_R * A_K * (1 - a_R^(4*K))|
              ≤ |A_K + a_R * B_K| * (dh_R^2 * 2 * (K : Rat)^2))
    (h_F1a : |dh_R * re_h_K - dh_R * A_K * (1 - a_R^(4*K))|
              ≤ |dh_R| * (K : Rat) * |δ_K| + |dh_R| * 8 * |a_R|^(4*K))
    (h_a_abs : |a_R| ≤ 1/4)
    (h_dh_nn : 0 ≤ dh_R) (h_dh_le_half : dh_R ≤ 1/2)
    (h_K_ge_2 : 2 ≤ K)
    (h_K_dh : 2 * (K : Rat)^2 * dh_R ≤ 1) :
    |(A_K + a_R * B_K) * I_K + T_a_K * (R_K - 1) - dh_R * re_h_K|
      ≤ (dh_R / 2 + 9 * (K : Rat) * dh_R^2) * |T_a_K|
        + 200 * (K : Rat)^2 * dh_R^2
        + 10 * dh_R * |a_R|^(4*K) := by
  have h_K_nn : (0 : Rat) ≤ (K : Rat) := Nat.cast_nonneg _
  have h_K_ge_2_R : (2 : Rat) ≤ (K : Rat) := by exact_mod_cast h_K_ge_2
  have h_K_ge_1 : (1 : Rat) ≤ (K : Rat) := by linarith
  have h_dh_sq_nn : 0 ≤ dh_R^2 := sq_nonneg _
  have h_T_nn : 0 ≤ |T_a_K| := _root_.abs_nonneg _
  have h_dh_abs_eq : |dh_R| = dh_R := abs_of_nonneg h_dh_nn
  -- Step 1: algebraic identity (no abs)
  have h_target_eq :
      (A_K + a_R * B_K) * I_K + T_a_K * (R_K - 1) - dh_R * re_h_K
        = (dh_R * a_R * d_K * T_a_K + T_a_K * (R_K - 1))
          + (δ_K * (A_K + a_R * B_K)
             - dh_R * a_R * d_K * T_a_K
             - dh_R * A_K * (1 - a_R^(4*K)))
          + (A_K + a_R * B_K) * (I_K - δ_K)
          - (dh_R * re_h_K - dh_R * A_K * (1 - a_R^(4*K))) := by
    ring
  -- Step 2: triangle on h_target_eq
  have h_tri :
      |(A_K + a_R * B_K) * I_K + T_a_K * (R_K - 1) - dh_R * re_h_K|
        ≤ |dh_R * a_R * d_K * T_a_K + T_a_K * (R_K - 1)|
          + |δ_K * (A_K + a_R * B_K) - dh_R * a_R * d_K * T_a_K
              - dh_R * A_K * (1 - a_R^(4*K))|
          + |(A_K + a_R * B_K) * (I_K - δ_K)|
          + |dh_R * re_h_K - dh_R * A_K * (1 - a_R^(4*K))| := by
    rw [h_target_eq]
    have h1 := abs_add_le
      ((dh_R * a_R * d_K * T_a_K + T_a_K * (R_K - 1))
        + (δ_K * (A_K + a_R * B_K) - dh_R * a_R * d_K * T_a_K
            - dh_R * A_K * (1 - a_R^(4*K))))
      ((A_K + a_R * B_K) * (I_K - δ_K))
    have h2 := abs_add_le
      (dh_R * a_R * d_K * T_a_K + T_a_K * (R_K - 1))
      (δ_K * (A_K + a_R * B_K) - dh_R * a_R * d_K * T_a_K
        - dh_R * A_K * (1 - a_R^(4*K)))
    have h3 := abs_sub
      ((dh_R * a_R * d_K * T_a_K + T_a_K * (R_K - 1))
        + (δ_K * (A_K + a_R * B_K) - dh_R * a_R * d_K * T_a_K
            - dh_R * A_K * (1 - a_R^(4*K)))
        + (A_K + a_R * B_K) * (I_K - δ_K))
      (dh_R * re_h_K - dh_R * A_K * (1 - a_R^(4*K)))
    linarith [h1, h2, h3]
  -- Step 3 (piece 1): linear-in-T_a_K coefficient: |dh·a·d·T + T·(R-1)| ≤ (dh/4 + 4K·dh²)·|T|
  have h_piece_lin :
      |dh_R * a_R * d_K * T_a_K + T_a_K * (R_K - 1)|
        ≤ (dh_R / 4 + 4 * (K : Rat) * dh_R^2) * |T_a_K| := by
    -- |a · d_K| ≤ 1/4 · 1 = 1/4
    have h_a_d : |a_R * d_K| ≤ 1/4 := by
      rw [abs_mul]
      have h_a_nn : 0 ≤ |a_R| := _root_.abs_nonneg _
      nlinarith [h_a_abs, h_d_K_abs, h_a_nn]
    -- |dh·a·d| ≤ dh · 1/4
    have h_dh_a_d : |dh_R * a_R * d_K| ≤ dh_R / 4 := by
      rw [show dh_R * a_R * d_K = dh_R * (a_R * d_K) from by ring, abs_mul,
          abs_of_nonneg h_dh_nn]
      nlinarith [h_a_d, h_dh_nn]
    -- |dh·a·d·T| ≤ (dh/4)·|T|
    have h_dh_a_d_T : |dh_R * a_R * d_K * T_a_K| ≤ (dh_R / 4) * |T_a_K| := by
      rw [show dh_R * a_R * d_K * T_a_K = (dh_R * a_R * d_K) * T_a_K from by ring,
          abs_mul]
      exact mul_le_mul_of_nonneg_right h_dh_a_d h_T_nn
    -- |T·(R-1)| ≤ |T|·|R-1| ≤ |T|·(4K·dh²)
    have h_R1_T : |T_a_K * (R_K - 1)| ≤ |T_a_K| * (4 * (K : Rat) * dh_R^2) := by
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left h_R_minus_1 h_T_nn
    -- Combine via triangle
    have h_split :=
      abs_add_le (dh_R * a_R * d_K * T_a_K) (T_a_K * (R_K - 1))
    nlinarith [h_split, h_dh_a_d_T, h_R1_T, h_T_nn, h_dh_nn]
  -- Step 4 (piece 2): D3 error ≤ 20·K²·dh²
  have h_piece_D3 :
      |δ_K * (A_K + a_R * B_K) - dh_R * a_R * d_K * T_a_K
        - dh_R * A_K * (1 - a_R^(4*K))|
        ≤ 20 * (K : Rat)^2 * dh_R^2 := by
    have h_AaB_nn : 0 ≤ |A_K + a_R * B_K| := _root_.abs_nonneg _
    have h_K_sq_nn : 0 ≤ (K : Rat)^2 := sq_nonneg _
    have h_step : |A_K + a_R * B_K| * (dh_R^2 * 2 * (K : Rat)^2)
                  ≤ 10 * (dh_R^2 * 2 * (K : Rat)^2) := by
      have h_prod_nn : 0 ≤ dh_R^2 * 2 * (K : Rat)^2 := by positivity
      exact mul_le_mul_of_nonneg_right h_AaB_abs h_prod_nn
    nlinarith [h_D3, h_step]
  -- Step 5 (piece 3): |(A+a·B)·(I-δ)| ≤ 20·K²·dh²
  -- Path: 10 · 8K·dh³ = 80K·dh³.
  -- 80K·dh³ = (40K·dh²)·(2·dh) ≤ (40K·dh²)·1 = 40K·dh².
  -- 40K·dh² ≤ 20·K²·dh² since 2K ≤ K² (K ≥ 2).
  have h_piece_Iδ :
      |(A_K + a_R * B_K) * (I_K - δ_K)| ≤ 20 * (K : Rat)^2 * dh_R^2 := by
    rw [abs_mul]
    have h_Iδ_nn : 0 ≤ |I_K - δ_K| := _root_.abs_nonneg _
    -- |A+a·B|·|I-δ| ≤ 10 · 8·K·dh³ = 80·K·dh³
    have h_prod : |A_K + a_R * B_K| * |I_K - δ_K| ≤ 10 * (8 * (K : Rat) * dh_R^3) :=
      mul_le_mul h_AaB_abs h_I_minus_δ h_Iδ_nn (by linarith)
    -- Pre-establish polynomial slack: dh^3 = dh^2 * dh
    have h_dh_cube : dh_R^3 = dh_R^2 * dh_R := by ring
    -- 80·K·dh² ≥ 0
    have h_80K_dh_sq_nn : 0 ≤ 80 * (K : Rat) * dh_R^2 := by positivity
    -- 80·K·dh³ ≤ 80·K·dh² · (1/2) = 40·K·dh² (using dh ≤ 1/2)
    have h_80_cube_le_half : 10 * (8 * (K : Rat) * dh_R^3) ≤ 40 * (K : Rat) * dh_R^2 := by
      rw [show 10 * (8 * (K : Rat) * dh_R^3) = 80 * (K : Rat) * dh_R^2 * dh_R from by ring]
      have h_le : 80 * (K : Rat) * dh_R^2 * dh_R ≤ 80 * (K : Rat) * dh_R^2 * (1/2) :=
        mul_le_mul_of_nonneg_left h_dh_le_half h_80K_dh_sq_nn
      linarith
    -- 40·K·dh² ≤ 20·K²·dh² (using 2K ≤ K², ie K ≥ 2)
    have h_K_sq_ge_2K : 2 * (K : Rat) ≤ (K : Rat)^2 := by nlinarith [h_K_ge_2_R, h_K_nn]
    have h_40_le_20K : 40 * (K : Rat) * dh_R^2 ≤ 20 * (K : Rat)^2 * dh_R^2 := by
      have h_step : 40 * (K : Rat) = 20 * (2 * (K : Rat)) := by ring
      have h_step2 : 20 * (2 * (K : Rat)) ≤ 20 * (K : Rat)^2 := by linarith
      nlinarith [h_step2, h_dh_sq_nn]
    linarith [h_prod, h_80_cube_le_half, h_40_le_20K]
  -- Step 6 (piece 4): F.1a residual ≤ 2·K²·dh² + 8·dh·|a|^(4K)
  have h_piece_F1a :
      |dh_R * re_h_K - dh_R * A_K * (1 - a_R^(4*K))|
        ≤ 2 * (K : Rat)^2 * dh_R^2 + 8 * dh_R * |a_R|^(4*K) := by
    have h_F1a_dh : |dh_R * re_h_K - dh_R * A_K * (1 - a_R^(4*K))|
                  ≤ dh_R * (K : Rat) * |δ_K| + dh_R * 8 * |a_R|^(4*K) := by
      rw [h_dh_abs_eq] at h_F1a
      exact h_F1a
    have h_dh_K_nn : 0 ≤ dh_R * (K : Rat) := mul_nonneg h_dh_nn h_K_nn
    -- dh·K·|δ| ≤ dh·K·2·dh = 2·K·dh²
    have h_δ_step : dh_R * (K : Rat) * |δ_K| ≤ dh_R * (K : Rat) * (2 * dh_R) :=
      mul_le_mul_of_nonneg_left h_δ_abs h_dh_K_nn
    have h_simp_2K : dh_R * (K : Rat) * (2 * dh_R) = 2 * (K : Rat) * dh_R^2 := by ring
    -- 2·K·dh² ≤ 2·K²·dh² (using K ≤ K² for K ≥ 1)
    have h_K_le_K_sq : (K : Rat) ≤ (K : Rat)^2 := by
      have h_K_step : (K : Rat)^2 - (K : Rat) = (K : Rat) * ((K : Rat) - 1) := by ring
      have h_K_minus_1_nn : (0 : Rat) ≤ (K : Rat) - 1 := by linarith
      nlinarith [h_K_step, h_K_nn, h_K_minus_1_nn]
    have h_2K_le_2K_sq : 2 * (K : Rat) * dh_R^2 ≤ 2 * (K : Rat)^2 * dh_R^2 := by
      have h_step : 2 * (K : Rat) ≤ 2 * (K : Rat)^2 := by linarith
      nlinarith [h_step, h_dh_sq_nn]
    -- dh · 8 · |a|^4K = 8 · dh · |a|^4K (commute)
    have h_a_pow_nn : 0 ≤ |a_R|^(4*K) := by positivity
    have h_simp_8 : dh_R * 8 * |a_R|^(4*K) = 8 * dh_R * |a_R|^(4*K) := by ring
    linarith [h_F1a_dh, h_δ_step, h_simp_2K, h_2K_le_2K_sq, h_simp_8]
  -- Final closure: combine 4 pieces via h_tri
  -- target ≤ piece_lin + piece_D3 + piece_Iδ + piece_F1a
  --        ≤ (dh/4 + 4K·dh²)·|T| + 20K²·dh² + 20K²·dh² + (2K²·dh² + 8·dh·|a|^4K)
  --        ≤ (dh/2 + 9K·dh²)·|T| + 200K²·dh² + 10·dh·|a|^4K
  -- Need: (dh/4 + 4K·dh²)·|T| ≤ (dh/2 + 9K·dh²)·|T| (using |T| ≥ 0)
  --       20 + 20 + 2 = 42 ≤ 200 (trivial)
  --       8 ≤ 10 (trivial)
  have h_K_dh_sq_nn : 0 ≤ (K : Rat) * dh_R^2 := mul_nonneg h_K_nn h_dh_sq_nn
  have h_K_sq_dh_sq_nn : 0 ≤ (K : Rat)^2 * dh_R^2 :=
    mul_nonneg (sq_nonneg _) h_dh_sq_nn
  have h_M_step : (dh_R / 4 + 4 * (K : Rat) * dh_R^2) * |T_a_K|
                  ≤ (dh_R / 2 + 9 * (K : Rat) * dh_R^2) * |T_a_K| := by
    have h_step : (dh_R / 4 + 4 * (K : Rat) * dh_R^2)
                ≤ (dh_R / 2 + 9 * (K : Rat) * dh_R^2) := by linarith
    exact mul_le_mul_of_nonneg_right h_step h_T_nn
  have h_a_pow_nn : 0 ≤ |a_R|^(4*K) := by positivity
  have h_dh_a_pow_nn : 0 ≤ dh_R * |a_R|^(4*K) := mul_nonneg h_dh_nn h_a_pow_nn
  linarith [h_tri, h_piece_lin, h_piece_D3, h_piece_Iδ, h_piece_F1a, h_M_step,
            h_dh_a_pow_nn, h_K_dh_sq_nn, h_K_sq_dh_sq_nn]

/-! ## Sub-Wave F.1b — Per-step Gronwall increment bound (WRAPPER, completes Phase A)

  Thin TauReal-aware wrapper that assembles Helper A (TauReal→Rat unfold)
  + Helper B (pure Rat-level analytical bound) + the 8 shipped sub-helpers
  + 6.M5.D destructure into the Gronwall step form.

  ```
  |T(a+dh).K − T(a).K|
    ≤ (dh/2 + 9·K·dh²) · |T(a).K|
      + 200·K²·dh² + 10·dh·|a|^(4K) + 1/(k_M+1)
  ```
-/

set_option maxHeartbeats 1600000 in
/-- **F.1b** — Per-step Gronwall increment bound at .approx K (THE CAPSTONE). -/
theorem TauReal.tangent_defect_step_bound_at_K
    (a dh : TauRat) (ha : 4 * |a.toRat| ≤ 1) (hah : 4 * |(a.add dh).toRat| ≤ 1)
    (hdh_nn : 0 ≤ dh.toRat) (hdh_le_half : dh.toRat ≤ 1/2) :
    ∃ μ_5C : Nat → Nat, ∀ k_M K, μ_5C k_M ≤ K → 2 ≤ K →
      2 * (K : Rat)^2 * dh.toRat ≤ 1 →
      |((TauReal.tangent_defect (a.add dh)).approx K).toRat
        - ((TauReal.tangent_defect a).approx K).toRat|
        ≤ (dh.toRat / 2 + 9 * (K : Rat) * dh.toRat^2)
            * |((TauReal.tangent_defect a).approx K).toRat|
          + 200 * (K : Rat)^2 * dh.toRat^2
          + 10 * dh.toRat * |a.toRat|^(4*K)
          + 1 / ((k_M : Rat) + 1) := by
  -- Step 1: destructure 6.M5.D, get μ_5C and the existential bound
  obtain ⟨μ_5C, hμ_5C⟩ :=
    TauReal.tangent_defect_increment_simplified_at_K a dh ha hah
  refine ⟨μ_5C, ?_⟩
  intro k_M K hμ_le hK hK_dh
  have h_5C := hμ_5C k_M K hμ_le
  -- Step 2: unfold RHS_5C via Helper A
  rw [TauReal.RHS_5C_at_K_toRat_unfold a dh K] at h_5C
  -- Now h_5C is in pure Rat-algebra form using the 8 _K quantities directly.
  -- Step 3: instantiate the 8 shipped pointwise bounds
  have h_d_K   := arctan_deriv_partial_rat_abs_le_one a ha K
  have h_AaB   := TauReal.cis_arctan_re_plus_a_cis_arctan_im_abs_le_ten a ha K
  have h_δ_abs := TauReal.arctan_increment_abs_le_two_dh a dh ha hdh_nn hdh_le_half K hK_dh
  have h_R_m1  := TauReal.R_K_minus_1_abs_le_four_K_dh_sq a dh ha hah hdh_nn hdh_le_half K
                    (by omega : 1 ≤ K) hK_dh
  have h_I_m_δ := TauReal.I_K_minus_delta_K_abs_le_eight_K_dh_cube a dh ha hah
                    hdh_nn hdh_le_half K hK hK_dh
  have h_D3    := TauReal.M4_D3_linear_extraction_bound a dh ha hdh_nn hdh_le_half K
  have h_F1a   := TauReal.tangent_defect_re_residual_bound a dh ha hah K
  have h_a_abs : |a.toRat| ≤ 1/4 := by linarith [_root_.abs_nonneg a.toRat]
  have h_T_def : ((TauReal.tangent_defect a).approx K).toRat
              = ((TauReal.cis_arctan_im a).approx K).toRat
                - a.toRat * ((TauReal.cis_arctan_re a).approx K).toRat :=
    TauReal.tangent_defect_approx_toRat a K
  -- Step 4: apply Helper B with the 8 Rat-level quantities
  have h_explicit := TauReal.tangent_defect_step_bound_explicit
      a.toRat dh.toRat
      ((TauReal.cis_arctan_re a).approx K).toRat
      ((TauReal.cis_arctan_im a).approx K).toRat
      ((TauComplex.cisTauReal
          ((TauReal.arctan_of_rat_seq (a.add dh)).sub
            (TauReal.arctan_of_rat_seq a))).re.approx K).toRat
      ((TauComplex.cisTauReal
          ((TauReal.arctan_of_rat_seq (a.add dh)).sub
            (TauReal.arctan_of_rat_seq a))).im.approx K).toRat
      ((TauReal.cis_arctan_re (a.add dh)).approx K).toRat
      ((TauReal.tangent_defect a).approx K).toRat
      (((TauReal.arctan_of_rat_seq (a.add dh)).sub
          (TauReal.arctan_of_rat_seq a)).approx K).toRat
      (arctan_deriv_partial_rat a.toRat K)
      K h_T_def h_d_K h_AaB h_δ_abs h_R_m1 h_I_m_δ h_D3 h_F1a
      h_a_abs hdh_nn hdh_le_half hK hK_dh
  -- Step 5: close via triangle: |T_h - T_a| ≤ |T_h - T_a - RHS_form| + |RHS_form|
  --        < 1/(k_M+1) + bound (Helper B)
  have h_tri_abs : ∀ x y : Rat, |x| ≤ |x - y| + |y| := fun x y => by
    have := abs_add_le (x - y) y
    have h_eq : x - y + y = x := by ring
    rw [h_eq] at this
    exact this
  linarith [h_5C, h_explicit, h_tri_abs
    (((TauReal.tangent_defect (a.add dh)).approx K).toRat
      - ((TauReal.tangent_defect a).approx K).toRat)
    ((((TauReal.cis_arctan_re a).approx K).toRat
       + a.toRat * ((TauReal.cis_arctan_im a).approx K).toRat)
        * ((TauComplex.cisTauReal
            ((TauReal.arctan_of_rat_seq (a.add dh)).sub
              (TauReal.arctan_of_rat_seq a))).im.approx K).toRat
      + ((TauReal.tangent_defect a).approx K).toRat
        * (((TauComplex.cisTauReal
            ((TauReal.arctan_of_rat_seq (a.add dh)).sub
              (TauReal.arctan_of_rat_seq a))).re.approx K).toRat - 1)
      - dh.toRat * ((TauReal.cis_arctan_re (a.add dh)).approx K).toRat)]

/-! ## Sub-Wave F.1b — Per-step Gronwall increment bound (NEXT SESSION)

  F.1b combines the modulus destructure (6.M5.D), 6.M4.D.3 (linear-term
  extraction), 6.M2 (small-angle bounds), 6.M3 (secant Taylor), F.1a
  (re-residual), and the helpers `|d_K| ≤ 1`, `|A+a·B| ≤ 10` to derive
  the Gronwall recurrence form.

  This is the HIGH RISK piece per the red team's plan — ~200 LOC of
  intricate polynomial bound composition. Deferred to next focused
  session.

  Bound formula (verified by hand-analysis):
  ```
  |T(a+dh).K − T(a).K|
    ≤ (dh/2 + 9·K·dh²) · |T(a).K|             [M_step]
      + 100·K²·dh² + 10·dh·|a|^(4K) + 1/(k_M+1)  [δ_step]
  ```

  Under hypothesis `2·K²·dh ≤ 1` (satisfied with N = K⁴), the polynomial
  degrees work out for Gronwall convergence at K = k+2, N = (k+2)⁴.
-/

/-
F.1b proof skeleton (~200 LOC, for next session):

theorem TauReal.tangent_defect_step_bound_at_K
    (a dh : TauRat) (ha : 4 * |a.toRat| ≤ 1) (hah : 4 * |(a.add dh).toRat| ≤ 1)
    (hdh_nn : 0 ≤ dh.toRat) (hdh_le_half : dh.toRat ≤ 1/2) :
    ∃ μ_5C : Nat → Nat, ∀ k_M K, μ_5C k_M ≤ K → 2 ≤ K →
      2 * (K : Rat)^2 * dh.toRat ≤ 1 →
      |T(a+dh).K - T(a).K|
        ≤ (dh/2 + 9·K·dh²) · |T(a).K|
          + 100·K²·dh² + 10·dh·|a|^(4K) + 1/(k_M+1)

Proof structure:
1. Destructure 6.M5.C → μ_5C
2. Set Rat abbreviations (A_K, B_K, R_K, I_K, re_h_K, T_a_K, T_h_K, δ_K, d_K)
3. Pointwise bounds (h_5C, h_d_K, h_AaB, h_M3, h_δ_abs, h_M2_re, h_M2_im, h_F1a, h_D3)
4. Algebraic decomposition of RHS_5C via 6.M4.D.3 + F.1a
5. Triangle inequalities (5 terms)
6. Final linarith with all hypotheses
-/

/-! ## Path 2 Step 1 — `cisTauReal_add` explicit error at depth K

  Foundation for Path 2 (replacing F.1b's equiv-level Cauchy modulus with
  explicit pointwise bounds; see atlas memo
  `2026-05-19-F2-impossibility-from-F1b.md` for the architectural
  motivation).

  Derived from `cauchy_product_bound_re/im` with the standard geometric
  bound `C = 11` (from `exp_term_re_im_geom_bound` for
  pureIm_of_real-bounded-by-1 TauComplex).

  The bound `242·K / 2^(K−1)` decays super-exponentially in K, so the
  resulting Gronwall walk can close with K = O(k) and N = O(k³) — versus
  the F.1b path which is jointly unsatisfiable for any K.
-/

/-- **Explicit error bound at depth K for `cisTauReal_add`**.

    For TauReals `x, y` with `|x.approx _| ≤ 1` and similarly for `y`,
    and any depth `K ≥ 1`:

    `|cisTauReal(x+y).re.approx K .toRat - (cisTauReal x · cisTauReal y).re.approx K .toRat|
       ≤ 242·K / 2^(K−1)`

    and similarly for `.im`. The constant `242 = 2·11²` comes from the
    M3 endpoint's geometric exp_term bound; the bound decays
    super-exponentially in K. -/
theorem TauComplex.cisTauReal_add_explicit_error_at_K
    (x y : TauReal)
    (hx : ∀ n, (x.approx n).abs.toRat ≤ 1)
    (hy : ∀ n, (y.approx n).abs.toRat ≤ 1)
    (K : Nat) (hK : 1 ≤ K) :
    |((TauComplex.cisTauReal (TauReal.add x y)).re.approx K).toRat
      - (((TauComplex.cisTauReal x).mul (TauComplex.cisTauReal y)).re.approx K).toRat|
    ≤ 242 * (K : Rat) / 2 ^ (K - 1)
    ∧
    |((TauComplex.cisTauReal (TauReal.add x y)).im.approx K).toRat
      - (((TauComplex.cisTauReal x).mul (TauComplex.cisTauReal y)).im.approx K).toRat|
    ≤ 242 * (K : Rat) / 2 ^ (K - 1) := by
  -- Unfold cisTauReal := exp ∘ pureIm_of_real
  set z1 := TauComplex.pureIm_of_real x with hz1_def
  set z2 := TauComplex.pureIm_of_real y with hz2_def
  set z_sum := TauComplex.pureIm_of_real (TauReal.add x y) with hzsum_def
  -- BoundedBy bounds for z1, z2 from BoundedBy of x, y
  have h_bound_z1 : TauComplex.BoundedBy z1 1 :=
    TauComplex.pureIm_of_real_BoundedBy x 1 (by omega) hx
  have h_bound_z2 : TauComplex.BoundedBy z2 1 :=
    TauComplex.pureIm_of_real_BoundedBy y 1 (by omega) hy
  -- exp_term geometric bounds for z1, z2 at any depth m
  have h_bound_z1_re := fun i m =>
    (TauComplex.exp_term_re_im_geom_bound z1 h_bound_z1 i m).1
  have h_bound_z1_im := fun i m =>
    (TauComplex.exp_term_re_im_geom_bound z1 h_bound_z1 i m).2
  have h_bound_z2_re := fun j m =>
    (TauComplex.exp_term_re_im_geom_bound z2 h_bound_z2 j m).1
  have h_bound_z2_im := fun j m =>
    (TauComplex.exp_term_re_im_geom_bound z2 h_bound_z2 j m).2
  -- z_sum and z1.add z2 have componentwise equal toRats at every .approx n
  have h_zre : ∀ n, (z_sum.re.approx n).toRat = ((z1.add z2).re.approx n).toRat := by
    intro n
    show (TauRat.zero).toRat = (TauRat.add TauRat.zero TauRat.zero).toRat
    rw [toRat_add, toRat_zero]; ring
  have h_zim : ∀ n, (z_sum.im.approx n).toRat = ((z1.add z2).im.approx n).toRat := fun _ => rfl
  -- Apply cauchy_product_bound at depth K for re and im
  have h_cpb_re := TauComplex.cauchy_product_bound_re
                    (TauComplex.exp_term z1) (TauComplex.exp_term z2)
                    11 (by norm_num)
                    h_bound_z1_re h_bound_z1_im
                    h_bound_z2_re h_bound_z2_im
                    K hK K
  have h_cpb_im := TauComplex.cauchy_product_bound_im
                    (TauComplex.exp_term z1) (TauComplex.exp_term z2)
                    11 (by norm_num)
                    h_bound_z1_re h_bound_z1_im
                    h_bound_z2_re h_bound_z2_im
                    K hK K
  -- Convert 2·K·11²/2^(K-1) form to 242·K/2^(K-1)
  have h_const_eq : (2 : Rat) * (K : Rat) * 11^2 / 2 ^ (K - 1)
                  = 242 * (K : Rat) / 2 ^ (K - 1) := by
    rw [show (2 * (K : Rat) * 11 ^ 2 : Rat) = 242 * (K : Rat) from by ring]
  rw [h_const_eq] at h_cpb_re h_cpb_im
  -- Partial-sum identity: exp_partial (z1.add z2) K's .re/.im.approx K
  -- = cauchyPStar (exp_term z1) (exp_term z2) K's .re/.im.approx K
  obtain ⟨h_re_part, h_im_part⟩ :=
    TauComplex.exp_partial_add_re_im_approx_toRat z1 z2 K K
  refine ⟨?_, ?_⟩
  · -- .re component
    -- Rewrite LHS: cisTauReal(x+y).re.approx K .toRat
    --   = exp z_sum .re.approx K .toRat
    --   = exp_partial z_sum K .re.approx K .toRat        (via exp_re_approx)
    --   = exp_partial (z1.add z2) K .re.approx K .toRat  (via exp_partial_re_im_toRat_eq_of_componentwise)
    --   = cauchyPStar(exp_term z1, exp_term z2) K .re.approx K .toRat  (via h_re_part)
    have h_lhs : ((TauComplex.cisTauReal (TauReal.add x y)).re.approx K).toRat
              = ((TauComplex.cauchyPStar (TauComplex.exp_term z1)
                                          (TauComplex.exp_term z2) K).re.approx K).toRat := by
      show ((TauComplex.exp z_sum).re.approx K).toRat = _
      rw [TauComplex.exp_re_approx,
          (TauComplex.exp_partial_re_im_toRat_eq_of_componentwise
              z_sum (z1.add z2) h_zre h_zim K K).1]
      exact h_re_part
    -- Rewrite RHS: (cisTauReal x · cisTauReal y).re.approx K .toRat
    --   = ((exp z1) · (exp z2)).re.approx K .toRat
    --   = ((exp_partial z1 K) · (exp_partial z2 K)).re.approx K .toRat
    have h_rhs : (((TauComplex.cisTauReal x).mul (TauComplex.cisTauReal y)).re.approx K).toRat
              = (((TauComplex.exp_partial z1 K).mul
                  (TauComplex.exp_partial z2 K)).re.approx K).toRat := by
      show (((TauComplex.exp z1).mul (TauComplex.exp z2)).re.approx K).toRat = _
      rw [TauComplex.mul_re_approx, TauComplex.mul_re_approx]
      simp only [TauComplex.exp_re_approx, TauComplex.exp_im_approx]
    rw [h_lhs, h_rhs]
    -- Flip abs sub to match h_cpb_re
    rw [abs_sub_comm]
    -- h_cpb_re uses `sum (exp_term z) K` which is defeq to `exp_partial z K`.
    exact h_cpb_re
  · -- .im component (parallel to .re)
    have h_lhs : ((TauComplex.cisTauReal (TauReal.add x y)).im.approx K).toRat
              = ((TauComplex.cauchyPStar (TauComplex.exp_term z1)
                                          (TauComplex.exp_term z2) K).im.approx K).toRat := by
      show ((TauComplex.exp z_sum).im.approx K).toRat = _
      rw [TauComplex.exp_im_approx,
          (TauComplex.exp_partial_re_im_toRat_eq_of_componentwise
              z_sum (z1.add z2) h_zre h_zim K K).2]
      exact h_im_part
    have h_rhs : (((TauComplex.cisTauReal x).mul (TauComplex.cisTauReal y)).im.approx K).toRat
              = (((TauComplex.exp_partial z1 K).mul
                  (TauComplex.exp_partial z2 K)).im.approx K).toRat := by
      show (((TauComplex.exp z1).mul (TauComplex.exp z2)).im.approx K).toRat = _
      rw [TauComplex.mul_im_approx, TauComplex.mul_im_approx]
      simp only [TauComplex.exp_re_approx, TauComplex.exp_im_approx]
    rw [h_lhs, h_rhs]
    rw [abs_sub_comm]
    exact h_cpb_im

/-! ## Path 2 Step 2 — `cis_arctan_re/im_add_factored` explicit error at depth K

  Lifts Step 1 (`cisTauReal_add_explicit_error_at_K`) via depth-locality
  to give the explicit error bound on the cis_arctan_re/im add-factored
  form at .approx K.

  Apply Step 1 with `x := arctan_of_rat_seq(a)` and
  `y := arctan_of_rat_seq(a+h).sub arctan_of_rat_seq(a)` (= δ).
  Boundedness comes from:
  - `arctan_of_rat_seq_bounded a (ha_2 : 2|a|≤1)` for x bounded by 1
  - `arctan_increment_bounded a h ha hah` for δ bounded by 1

  The bridge from `cisTauReal(x+y)` to `cisTauReal(arctan_of_rat_seq(a+h))`
  at .approx K is exact via depth-locality
  (`cisTauReal_re/im_approx_toRat`).
-/

/-- **Path 2 Step 2** — Explicit error bound for `cis_arctan_re/im` add-factored
    form at depth K.

    Replaces the equiv-level Cauchy modulus error in `cis_arctan_re/im_add_factored`
    by an explicit super-exponentially-decaying bound `242·K/2^(K−1)`.

    Form (.re): `cos(α+β) = cos α · cos β − sin α · sin β`
    Form (.im): `sin(α+β) = cos α · sin β + sin α · cos β`
    (truncated at depth K with explicit error). -/
theorem TauReal.cis_arctan_add_factored_explicit_error_at_K
    (a h : TauRat) (ha : 4 * |a.toRat| ≤ 1) (hah : 4 * |(a.add h).toRat| ≤ 1)
    (K : Nat) (hK : 1 ≤ K) :
    |((TauReal.cis_arctan_re (a.add h)).approx K).toRat
      - ((TauReal.sub
            (TauReal.mul (TauReal.cis_arctan_re a)
              (TauComplex.cisTauReal
                ((TauReal.arctan_of_rat_seq (a.add h)).sub
                  (TauReal.arctan_of_rat_seq a))).re)
            (TauReal.mul (TauReal.cis_arctan_im a)
              (TauComplex.cisTauReal
                ((TauReal.arctan_of_rat_seq (a.add h)).sub
                  (TauReal.arctan_of_rat_seq a))).im)).approx K).toRat|
    ≤ 242 * (K : Rat) / 2 ^ (K - 1)
    ∧
    |((TauReal.cis_arctan_im (a.add h)).approx K).toRat
      - ((TauReal.add
            (TauReal.mul (TauReal.cis_arctan_re a)
              (TauComplex.cisTauReal
                ((TauReal.arctan_of_rat_seq (a.add h)).sub
                  (TauReal.arctan_of_rat_seq a))).im)
            (TauReal.mul (TauReal.cis_arctan_im a)
              (TauComplex.cisTauReal
                ((TauReal.arctan_of_rat_seq (a.add h)).sub
                  (TauReal.arctan_of_rat_seq a))).re)).approx K).toRat|
    ≤ 242 * (K : Rat) / 2 ^ (K - 1) := by
  -- Setup: bounds on Step 1's x, y
  have ha_2 : 2 * |a.toRat| ≤ 1 := by linarith
  have h_x_bound := TauReal.arctan_of_rat_seq_bounded a ha_2
  have h_y_bound := TauReal.arctan_increment_bounded a h ha hah
  -- Apply Step 1 with x = arctan(a), y = δ
  obtain ⟨h_step1_re, h_step1_im⟩ := TauComplex.cisTauReal_add_explicit_error_at_K
    (TauReal.arctan_of_rat_seq a)
    ((TauReal.arctan_of_rat_seq (a.add h)).sub (TauReal.arctan_of_rat_seq a))
    h_x_bound h_y_bound K hK
  -- Pointwise toRat: arctan(a) + δ and arctan(a+h) agree at every .approx n .toRat
  have h_inner_eq :
      (((TauReal.arctan_of_rat_seq a).add
          ((TauReal.arctan_of_rat_seq (a.add h)).sub
            (TauReal.arctan_of_rat_seq a))).approx K).toRat
        = ((TauReal.arctan_of_rat_seq (a.add h)).approx K).toRat := by
    show (((TauReal.arctan_of_rat_seq a).approx K).add
           (((TauReal.arctan_of_rat_seq (a.add h)).approx K).add
             ((TauReal.arctan_of_rat_seq a).approx K).negate)).toRat = _
    rw [toRat_add, toRat_add, toRat_negate]; ring
  -- Bridge LHS at .approx K via depth-locality:
  --   cisTauReal(arctan(a) + δ).re.approx K .toRat = cisTauReal(arctan(a+h)).re.approx K .toRat
  -- because cisTauReal_re_approx_toRat depends only on inner.approx K .toRat,
  -- and arctan(a)+δ and arctan(a+h) agree there.
  have h_bridge_re :
      ((TauComplex.cisTauReal
          ((TauReal.arctan_of_rat_seq a).add
            ((TauReal.arctan_of_rat_seq (a.add h)).sub
              (TauReal.arctan_of_rat_seq a)))).re.approx K).toRat
        = ((TauReal.cis_arctan_re (a.add h)).approx K).toRat := by
    rw [cisTauReal_re_approx_toRat]
    show _ = ((TauComplex.cisTauReal (TauReal.arctan_of_rat_seq (a.add h))).re.approx K).toRat
    rw [cisTauReal_re_approx_toRat, h_inner_eq]
  have h_bridge_im :
      ((TauComplex.cisTauReal
          ((TauReal.arctan_of_rat_seq a).add
            ((TauReal.arctan_of_rat_seq (a.add h)).sub
              (TauReal.arctan_of_rat_seq a)))).im.approx K).toRat
        = ((TauReal.cis_arctan_im (a.add h)).approx K).toRat := by
    rw [cisTauReal_im_approx_toRat]
    show _ = ((TauComplex.cisTauReal (TauReal.arctan_of_rat_seq (a.add h))).im.approx K).toRat
    rw [cisTauReal_im_approx_toRat, h_inner_eq]
  -- Substitute the LHS bridges into Step 1's bound
  rw [h_bridge_re] at h_step1_re
  rw [h_bridge_im] at h_step1_im
  refine ⟨?_, ?_⟩
  · -- .re component
    -- h_step1_re: |cis_arctan_re(a+h).approx K .toRat
    --              - ((cisTauReal arctan(a)).mul (cisTauReal δ)).re.approx K .toRat| ≤ ...
    -- Want: |cis_arctan_re(a+h).approx K .toRat
    --         - ((cis_arctan_re a · cisTauReal δ .re).sub (cis_arctan_im a · cisTauReal δ .im)).approx K .toRat| ≤ ...
    -- Bridge the RHS: both equal a common Rat expression via mul_re_approx + toRat_sub/mul.
    have h_rhs_re :
        (((TauComplex.cisTauReal (TauReal.arctan_of_rat_seq a)).mul
            (TauComplex.cisTauReal
              ((TauReal.arctan_of_rat_seq (a.add h)).sub
                (TauReal.arctan_of_rat_seq a)))).re.approx K).toRat
          = ((TauReal.sub
                (TauReal.mul (TauReal.cis_arctan_re a)
                  (TauComplex.cisTauReal
                    ((TauReal.arctan_of_rat_seq (a.add h)).sub
                      (TauReal.arctan_of_rat_seq a))).re)
                (TauReal.mul (TauReal.cis_arctan_im a)
                  (TauComplex.cisTauReal
                    ((TauReal.arctan_of_rat_seq (a.add h)).sub
                      (TauReal.arctan_of_rat_seq a))).im)).approx K).toRat := by
      rw [TauComplex.mul_re_approx]
      show (TauRat.sub
             (TauRat.mul ((TauComplex.cisTauReal (TauReal.arctan_of_rat_seq a)).re.approx K) _)
             (TauRat.mul ((TauComplex.cisTauReal (TauReal.arctan_of_rat_seq a)).im.approx K) _)).toRat
            = (TauRat.add
                (TauRat.mul ((TauReal.cis_arctan_re a).approx K) _)
                ((TauRat.mul ((TauReal.cis_arctan_im a).approx K) _).negate)).toRat
      rw [toRat_sub, toRat_mul, toRat_mul, toRat_add, toRat_negate, toRat_mul, toRat_mul]
      simp only [TauReal.cis_arctan_re_approx, TauReal.cis_arctan_im_approx]
      ring
    rw [h_rhs_re] at h_step1_re
    exact h_step1_re
  · -- .im component
    have h_rhs_im :
        (((TauComplex.cisTauReal (TauReal.arctan_of_rat_seq a)).mul
            (TauComplex.cisTauReal
              ((TauReal.arctan_of_rat_seq (a.add h)).sub
                (TauReal.arctan_of_rat_seq a)))).im.approx K).toRat
          = ((TauReal.add
                (TauReal.mul (TauReal.cis_arctan_re a)
                  (TauComplex.cisTauReal
                    ((TauReal.arctan_of_rat_seq (a.add h)).sub
                      (TauReal.arctan_of_rat_seq a))).im)
                (TauReal.mul (TauReal.cis_arctan_im a)
                  (TauComplex.cisTauReal
                    ((TauReal.arctan_of_rat_seq (a.add h)).sub
                      (TauReal.arctan_of_rat_seq a))).re)).approx K).toRat := by
      rw [TauComplex.mul_im_approx]
      show (TauRat.add
             (TauRat.mul ((TauComplex.cisTauReal (TauReal.arctan_of_rat_seq a)).re.approx K) _)
             (TauRat.mul ((TauComplex.cisTauReal (TauReal.arctan_of_rat_seq a)).im.approx K) _)).toRat
            = (TauRat.add
                (TauRat.mul ((TauReal.cis_arctan_re a).approx K) _)
                (TauRat.mul ((TauReal.cis_arctan_im a).approx K) _)).toRat
      rw [toRat_add, toRat_mul, toRat_mul, toRat_add, toRat_mul, toRat_mul]
      simp only [TauReal.cis_arctan_re_approx, TauReal.cis_arctan_im_approx]
    rw [h_rhs_im] at h_step1_im
    exact h_step1_im

/-! ## Path 2 Step 3 — `cis_arctan_re/im_diff_factored` explicit error at depth K

  Derives the "diff_factored" tight error form from Step 2's "add_factored"
  form via algebraic rearrangement at .approx K .toRat. The diff form is
  what `tangent_defect_increment_simplified` ultimately uses (the increment
  of cis_arctan_re/im across a → a+h).

  Algebraic identity: `diff_RHS.approx K .toRat = add_RHS.approx K .toRat
  - cis_arctan_re/im(a).approx K .toRat`, so subtracting `cis_arctan_re/im(a)`
  from both sides of Step 2's bound preserves the inequality.
-/

/-- **Path 2 Step 3** — Explicit error bound for `cis_arctan_re/im` diff-factored
    form at depth K.

    Form (.re): `cos(α+β) − cos α = cos α·(cos β − 1) − sin α · sin β`
    Form (.im): `sin(α+β) − sin α = cos α·sin β + sin α·(cos β − 1)`
    (truncated at depth K with explicit error 242·K/2^(K−1)). -/
theorem TauReal.cis_arctan_diff_factored_explicit_error_at_K
    (a h : TauRat) (ha : 4 * |a.toRat| ≤ 1) (hah : 4 * |(a.add h).toRat| ≤ 1)
    (K : Nat) (hK : 1 ≤ K) :
    |(((TauReal.cis_arctan_re (a.add h)).sub (TauReal.cis_arctan_re a)).approx K).toRat
      - ((TauReal.sub
            (TauReal.mul (TauReal.cis_arctan_re a)
              ((TauComplex.cisTauReal
                  ((TauReal.arctan_of_rat_seq (a.add h)).sub
                    (TauReal.arctan_of_rat_seq a))).re.sub TauReal.one))
            (TauReal.mul (TauReal.cis_arctan_im a)
              (TauComplex.cisTauReal
                ((TauReal.arctan_of_rat_seq (a.add h)).sub
                  (TauReal.arctan_of_rat_seq a))).im)).approx K).toRat|
    ≤ 242 * (K : Rat) / 2 ^ (K - 1)
    ∧
    |(((TauReal.cis_arctan_im (a.add h)).sub (TauReal.cis_arctan_im a)).approx K).toRat
      - ((TauReal.add
            (TauReal.mul (TauReal.cis_arctan_re a)
              (TauComplex.cisTauReal
                ((TauReal.arctan_of_rat_seq (a.add h)).sub
                  (TauReal.arctan_of_rat_seq a))).im)
            (TauReal.mul (TauReal.cis_arctan_im a)
              ((TauComplex.cisTauReal
                  ((TauReal.arctan_of_rat_seq (a.add h)).sub
                    (TauReal.arctan_of_rat_seq a))).re.sub TauReal.one))).approx K).toRat|
    ≤ 242 * (K : Rat) / 2 ^ (K - 1) := by
  -- Step 2 gives the add-factored bound
  obtain ⟨h_step2_re, h_step2_im⟩ :=
    TauReal.cis_arctan_add_factored_explicit_error_at_K a h ha hah K hK
  -- Helper: unfold (X.sub Y).approx K .toRat = X.approx K .toRat - Y.approx K .toRat
  have h_sub_toRat : ∀ (X Y : TauReal),
      ((X.sub Y).approx K).toRat = (X.approx K).toRat - (Y.approx K).toRat := by
    intros X Y
    show (TauRat.add (X.approx K) (Y.approx K).negate).toRat = _
    rw [toRat_add, toRat_negate]; ring
  -- Helper: unfold (X.mul Y).approx K .toRat = X.approx K .toRat * Y.approx K .toRat
  have h_mul_toRat : ∀ (X Y : TauReal),
      ((X.mul Y).approx K).toRat = (X.approx K).toRat * (Y.approx K).toRat := by
    intros X Y
    show (TauRat.mul (X.approx K) (Y.approx K)).toRat = _
    rw [toRat_mul]
  -- Helper: unfold (X.add Y).approx K .toRat = X.approx K .toRat + Y.approx K .toRat
  have h_add_toRat : ∀ (X Y : TauReal),
      ((X.add Y).approx K).toRat = (X.approx K).toRat + (Y.approx K).toRat := by
    intros X Y
    show (TauRat.add (X.approx K) (Y.approx K)).toRat = _
    rw [toRat_add]
  -- Helper: TauReal.one.approx K .toRat = 1
  have h_one_toRat : (TauReal.one.approx K).toRat = 1 := by
    show (TauRat.one).toRat = _
    rw [toRat_one]
  refine ⟨?_, ?_⟩
  · -- .re: identity diff_LHS - diff_RHS = add_LHS - add_RHS
    have h_alg :
        (((TauReal.cis_arctan_re (a.add h)).sub (TauReal.cis_arctan_re a)).approx K).toRat
          - ((TauReal.sub
                (TauReal.mul (TauReal.cis_arctan_re a)
                  ((TauComplex.cisTauReal
                      ((TauReal.arctan_of_rat_seq (a.add h)).sub
                        (TauReal.arctan_of_rat_seq a))).re.sub TauReal.one))
                (TauReal.mul (TauReal.cis_arctan_im a)
                  (TauComplex.cisTauReal
                    ((TauReal.arctan_of_rat_seq (a.add h)).sub
                      (TauReal.arctan_of_rat_seq a))).im)).approx K).toRat
        = ((TauReal.cis_arctan_re (a.add h)).approx K).toRat
          - ((TauReal.sub
                (TauReal.mul (TauReal.cis_arctan_re a)
                  (TauComplex.cisTauReal
                    ((TauReal.arctan_of_rat_seq (a.add h)).sub
                      (TauReal.arctan_of_rat_seq a))).re)
                (TauReal.mul (TauReal.cis_arctan_im a)
                  (TauComplex.cisTauReal
                    ((TauReal.arctan_of_rat_seq (a.add h)).sub
                      (TauReal.arctan_of_rat_seq a))).im)).approx K).toRat := by
      simp only [h_sub_toRat, h_mul_toRat, h_add_toRat, h_one_toRat]
      ring
    rw [h_alg]
    exact h_step2_re
  · -- .im: analogous
    have h_alg :
        (((TauReal.cis_arctan_im (a.add h)).sub (TauReal.cis_arctan_im a)).approx K).toRat
          - ((TauReal.add
                (TauReal.mul (TauReal.cis_arctan_re a)
                  (TauComplex.cisTauReal
                    ((TauReal.arctan_of_rat_seq (a.add h)).sub
                      (TauReal.arctan_of_rat_seq a))).im)
                (TauReal.mul (TauReal.cis_arctan_im a)
                  ((TauComplex.cisTauReal
                      ((TauReal.arctan_of_rat_seq (a.add h)).sub
                        (TauReal.arctan_of_rat_seq a))).re.sub TauReal.one))).approx K).toRat
        = ((TauReal.cis_arctan_im (a.add h)).approx K).toRat
          - ((TauReal.add
                (TauReal.mul (TauReal.cis_arctan_re a)
                  (TauComplex.cisTauReal
                    ((TauReal.arctan_of_rat_seq (a.add h)).sub
                      (TauReal.arctan_of_rat_seq a))).im)
                (TauReal.mul (TauReal.cis_arctan_im a)
                  (TauComplex.cisTauReal
                    ((TauReal.arctan_of_rat_seq (a.add h)).sub
                      (TauReal.arctan_of_rat_seq a))).re)).approx K).toRat := by
      simp only [h_sub_toRat, h_mul_toRat, h_add_toRat, h_one_toRat]
      ring
    rw [h_alg]
    exact h_step2_im

/-! ## Path 2 Step 4 — `tangent_defect_increment_simplified_at_K_tight`

  Replaces F.1b's modulus-error increment bound (which has the
  unsatisfiable Cauchy modulus coupling) with an explicit error at
  .approx K.

  Combines:
  - Algebraic rearrangement (tangent_defect_approx_toRat: T(a+dh).K - T(a).K
    = im_diff.K - dh·re(a+dh).K - a·re_diff.K) — exact at .approx K.
  - Step 3 .im (cis_arctan_im_diff_factored at .approx K): error 242·K/2^(K−1).
  - Step 3 .re (cis_arctan_re_diff_factored at .approx K), scaled by |a| ≤ 1/4:
    error |a|·242·K/2^(K−1).
  - Algebraic rearrangement to RHS_5C form (matching
    `tangent_defect_increment_simplified`) — exact at .approx K.

  Triangle inequality: total error ≤ (1 + |a|)·242·K/2^(K−1) ≤ 484·K/2^(K−1).
-/

/-- **Path 2 Step 4** — Tight increment bound at depth K, no Cauchy modulus.

    The RHS_5C form matches `tangent_defect_increment_simplified` exactly,
    but the bound is explicit and decays super-exponentially in K. -/
theorem TauReal.tangent_defect_increment_simplified_at_K_tight
    (a dh : TauRat) (ha : 4 * |a.toRat| ≤ 1) (hah : 4 * |(a.add dh).toRat| ≤ 1)
    (K : Nat) (hK : 1 ≤ K) :
    |((TauReal.tangent_defect (a.add dh)).approx K).toRat
        - ((TauReal.tangent_defect a).approx K).toRat
        - ((((((TauReal.cis_arctan_re a).add
                ((TauReal.fromTauRat a).mul (TauReal.cis_arctan_im a))).mul
              (TauComplex.cisTauReal
                ((TauReal.arctan_of_rat_seq (a.add dh)).sub
                  (TauReal.arctan_of_rat_seq a))).im).add
            ((TauReal.tangent_defect a).mul
              (((TauComplex.cisTauReal
                  ((TauReal.arctan_of_rat_seq (a.add dh)).sub
                    (TauReal.arctan_of_rat_seq a))).re).sub TauReal.one))).sub
          ((TauReal.fromTauRat dh).mul (TauReal.cis_arctan_re (a.add dh)))).approx K).toRat|
    ≤ 484 * (K : Rat) / 2 ^ (K - 1) := by
  -- Step 3 gives explicit error bounds for im_diff and re_diff at .approx K
  obtain ⟨h_step3_re, h_step3_im⟩ :=
    TauReal.cis_arctan_diff_factored_explicit_error_at_K a dh ha hah K hK
  -- toRat-level helpers for unfolding TauReal arithmetic
  have h_sub_toRat : ∀ (X Y : TauReal),
      ((X.sub Y).approx K).toRat = (X.approx K).toRat - (Y.approx K).toRat := by
    intros X Y
    show (TauRat.add (X.approx K) (Y.approx K).negate).toRat = _
    rw [toRat_add, toRat_negate]; ring
  have h_mul_toRat : ∀ (X Y : TauReal),
      ((X.mul Y).approx K).toRat = (X.approx K).toRat * (Y.approx K).toRat := by
    intros X Y
    show (TauRat.mul (X.approx K) (Y.approx K)).toRat = _
    rw [toRat_mul]
  have h_add_toRat : ∀ (X Y : TauReal),
      ((X.add Y).approx K).toRat = (X.approx K).toRat + (Y.approx K).toRat := by
    intros X Y
    show (TauRat.add (X.approx K) (Y.approx K)).toRat = _
    rw [toRat_add]
  have h_one_toRat : (TauReal.one.approx K).toRat = 1 := by
    show (TauRat.one).toRat = _
    rw [toRat_one]
  have h_fromTauRat_toRat : ∀ (q : TauRat),
      ((TauReal.fromTauRat q).approx K).toRat = q.toRat := fun _ => rfl
  -- Key algebraic identity at .approx K .toRat:
  --   T(a+dh).K - T(a).K - RHS_5C.K
  --     = (im_diff.K - im_factored.K) - a · (re_diff.K - re_factored.K)
  --   where the RHS uses Step 3's diff_factored expressions.
  -- Let:
  --   D_im := im_diff.K .toRat - im_factored.K .toRat   (Step 3 .im residual)
  --   D_re := re_diff.K .toRat - re_factored.K .toRat   (Step 3 .re residual)
  -- Step 3 gives |D_im| ≤ 242·K/2^(K-1), |D_re| ≤ 242·K/2^(K-1).
  -- We show T(a+dh).K - T(a).K - RHS_5C.K = D_im - a · D_re,
  -- so |…| ≤ |D_im| + |a| · |D_re| ≤ (1 + |a|) · 242·K/2^(K-1) ≤ 484·K/2^(K-1).
  set δ := (TauReal.arctan_of_rat_seq (a.add dh)).sub (TauReal.arctan_of_rat_seq a) with hδ_def
  set im_factored : TauReal :=
    TauReal.add
      (TauReal.mul (TauReal.cis_arctan_re a) (TauComplex.cisTauReal δ).im)
      (TauReal.mul (TauReal.cis_arctan_im a)
        ((TauComplex.cisTauReal δ).re.sub TauReal.one)) with him_factored_def
  set re_factored : TauReal :=
    TauReal.sub
      (TauReal.mul (TauReal.cis_arctan_re a)
        ((TauComplex.cisTauReal δ).re.sub TauReal.one))
      (TauReal.mul (TauReal.cis_arctan_im a) (TauComplex.cisTauReal δ).im) with hre_factored_def
  have h_step3_im_res :
      |(((TauReal.cis_arctan_im (a.add dh)).sub (TauReal.cis_arctan_im a)).approx K).toRat
         - (im_factored.approx K).toRat|
        ≤ 242 * (K : Rat) / 2 ^ (K - 1) := h_step3_im
  have h_step3_re_res :
      |(((TauReal.cis_arctan_re (a.add dh)).sub (TauReal.cis_arctan_re a)).approx K).toRat
         - (re_factored.approx K).toRat|
        ≤ 242 * (K : Rat) / 2 ^ (K - 1) := h_step3_re
  -- Algebraic identity: T(a+dh).K - T(a).K - RHS_5C.K = D_im - a · D_re
  have h_alg :
      ((TauReal.tangent_defect (a.add dh)).approx K).toRat
        - ((TauReal.tangent_defect a).approx K).toRat
        - ((((((TauReal.cis_arctan_re a).add
                ((TauReal.fromTauRat a).mul (TauReal.cis_arctan_im a))).mul
              (TauComplex.cisTauReal δ).im).add
            ((TauReal.tangent_defect a).mul
              ((TauComplex.cisTauReal δ).re.sub TauReal.one))).sub
          ((TauReal.fromTauRat dh).mul (TauReal.cis_arctan_re (a.add dh)))).approx K).toRat
      = ((((TauReal.cis_arctan_im (a.add dh)).sub (TauReal.cis_arctan_im a)).approx K).toRat
         - (im_factored.approx K).toRat)
        - a.toRat * ((((TauReal.cis_arctan_re (a.add dh)).sub (TauReal.cis_arctan_re a)).approx K).toRat
                     - (re_factored.approx K).toRat) := by
    rw [TauReal.tangent_defect_approx_toRat, TauReal.tangent_defect_approx_toRat]
    simp only [h_sub_toRat, h_mul_toRat, h_add_toRat, h_one_toRat, h_fromTauRat_toRat,
               TauReal.tangent_defect_approx_toRat,
               him_factored_def, hre_factored_def, toRat_add]
    ring
  rw [h_alg]
  -- Triangle inequality: |D_im - a · D_re| ≤ |D_im| + |a| · |D_re| ≤ 2 · 242·K/2^(K-1) (using |a| ≤ 1)
  have h_a_abs : |a.toRat| ≤ 1 := by
    have h_a_quarter : |a.toRat| ≤ 1/4 := by linarith [_root_.abs_nonneg a.toRat]
    linarith
  have h_tri :
      |((((TauReal.cis_arctan_im (a.add dh)).sub (TauReal.cis_arctan_im a)).approx K).toRat
        - (im_factored.approx K).toRat)
       - a.toRat * ((((TauReal.cis_arctan_re (a.add dh)).sub (TauReal.cis_arctan_re a)).approx K).toRat
                    - (re_factored.approx K).toRat)|
      ≤ |(((TauReal.cis_arctan_im (a.add dh)).sub (TauReal.cis_arctan_im a)).approx K).toRat
         - (im_factored.approx K).toRat|
        + |a.toRat| * |(((TauReal.cis_arctan_re (a.add dh)).sub (TauReal.cis_arctan_re a)).approx K).toRat
                      - (re_factored.approx K).toRat| := by
    have h_sub_abs := abs_sub
        ((((TauReal.cis_arctan_im (a.add dh)).sub (TauReal.cis_arctan_im a)).approx K).toRat
         - (im_factored.approx K).toRat)
        (a.toRat * ((((TauReal.cis_arctan_re (a.add dh)).sub (TauReal.cis_arctan_re a)).approx K).toRat
                    - (re_factored.approx K).toRat))
    -- abs_sub: |x - y| ≤ |x| + |y|
    have h_abs_mul :
        |a.toRat * ((((TauReal.cis_arctan_re (a.add dh)).sub (TauReal.cis_arctan_re a)).approx K).toRat
                    - (re_factored.approx K).toRat)|
        = |a.toRat| * |(((TauReal.cis_arctan_re (a.add dh)).sub (TauReal.cis_arctan_re a)).approx K).toRat
                       - (re_factored.approx K).toRat| := abs_mul _ _
    linarith [h_sub_abs, h_abs_mul]
  have h_combine :
      |(((TauReal.cis_arctan_im (a.add dh)).sub (TauReal.cis_arctan_im a)).approx K).toRat
         - (im_factored.approx K).toRat|
        + |a.toRat| * |(((TauReal.cis_arctan_re (a.add dh)).sub (TauReal.cis_arctan_re a)).approx K).toRat
                      - (re_factored.approx K).toRat|
      ≤ 242 * (K : Rat) / 2 ^ (K - 1) + 1 * (242 * (K : Rat) / 2 ^ (K - 1)) := by
    have h_a_nn : 0 ≤ |a.toRat| := _root_.abs_nonneg _
    have h_K_div_nn : 0 ≤ 242 * (K : Rat) / 2 ^ (K - 1) := by
      apply div_nonneg
      · positivity
      · positivity
    have := mul_le_mul h_a_abs h_step3_re_res (_root_.abs_nonneg _) (by linarith)
    -- this : |a.toRat| * |re_diff - re_factored| ≤ 1 * 242·K/2^(K-1)
    linarith [h_step3_im_res]
  have h_final_eq : (242 : Rat) * (K : Rat) / 2 ^ (K - 1) + 1 * (242 * (K : Rat) / 2 ^ (K - 1))
                  = 484 * (K : Rat) / 2 ^ (K - 1) := by ring
  linarith [h_tri, h_combine, h_final_eq]

/-! ## Path 2 Step 5a — `tangent_defect_step_bound_at_K_tight` (tight wrapper)

  Replaces F.1b's wrapper (`tangent_defect_step_bound_at_K`) which carries the
  unsatisfiable Cauchy modulus `+ 1/(k_M+1)`. The tight wrapper uses Step 4's
  explicit `484·K/2^(K−1)` error instead, eliminating the constraint coupling.

  Structure mirrors F.1b's wrapper exactly: combines Step 4's tight increment
  bound with Helper A (`RHS_5C_at_K_toRat_unfold`) + Helper B
  (`tangent_defect_step_bound_explicit`) + F.1b's 8 pointwise bounds, then
  closes via triangle inequality.
-/

set_option maxHeartbeats 1600000 in
/-- **Path 2 Step 5a (tight F.1b wrapper)** — Per-step Gronwall increment bound
    at .approx K with explicit super-exponential error 484·K/2^(K−1). -/
theorem TauReal.tangent_defect_step_bound_at_K_tight
    (a dh : TauRat) (ha : 4 * |a.toRat| ≤ 1) (hah : 4 * |(a.add dh).toRat| ≤ 1)
    (hdh_nn : 0 ≤ dh.toRat) (hdh_le_half : dh.toRat ≤ 1/2)
    (K : Nat) (hK : 2 ≤ K) (hK_dh : 2 * (K : Rat)^2 * dh.toRat ≤ 1) :
    |((TauReal.tangent_defect (a.add dh)).approx K).toRat
      - ((TauReal.tangent_defect a).approx K).toRat|
      ≤ (dh.toRat / 2 + 9 * (K : Rat) * dh.toRat^2)
          * |((TauReal.tangent_defect a).approx K).toRat|
        + 200 * (K : Rat)^2 * dh.toRat^2
        + 10 * dh.toRat * |a.toRat|^(4*K)
        + 484 * (K : Rat) / 2 ^ (K - 1) := by
  -- Step 1: Apply Step 4 (tight increment) to get the explicit error bound
  have hK_ge_1 : 1 ≤ K := by omega
  have h_5C := TauReal.tangent_defect_increment_simplified_at_K_tight a dh ha hah K hK_ge_1
  -- Step 2: unfold RHS_5C via Helper A
  rw [TauReal.RHS_5C_at_K_toRat_unfold a dh K] at h_5C
  -- Step 3: instantiate the 8 shipped pointwise bounds (same as F.1b wrapper)
  have h_d_K   := arctan_deriv_partial_rat_abs_le_one a ha K
  have h_AaB   := TauReal.cis_arctan_re_plus_a_cis_arctan_im_abs_le_ten a ha K
  have h_δ_abs := TauReal.arctan_increment_abs_le_two_dh a dh ha hdh_nn hdh_le_half K hK_dh
  have h_R_m1  := TauReal.R_K_minus_1_abs_le_four_K_dh_sq a dh ha hah hdh_nn hdh_le_half K
                    (by omega : 1 ≤ K) hK_dh
  have h_I_m_δ := TauReal.I_K_minus_delta_K_abs_le_eight_K_dh_cube a dh ha hah
                    hdh_nn hdh_le_half K hK hK_dh
  have h_D3    := TauReal.M4_D3_linear_extraction_bound a dh ha hdh_nn hdh_le_half K
  have h_F1a   := TauReal.tangent_defect_re_residual_bound a dh ha hah K
  have h_a_abs : |a.toRat| ≤ 1/4 := by linarith [_root_.abs_nonneg a.toRat]
  have h_T_def : ((TauReal.tangent_defect a).approx K).toRat
              = ((TauReal.cis_arctan_im a).approx K).toRat
                - a.toRat * ((TauReal.cis_arctan_re a).approx K).toRat :=
    TauReal.tangent_defect_approx_toRat a K
  -- Step 4: apply Helper B with the 8 Rat-level quantities (same as F.1b wrapper)
  have h_explicit := TauReal.tangent_defect_step_bound_explicit
      a.toRat dh.toRat
      ((TauReal.cis_arctan_re a).approx K).toRat
      ((TauReal.cis_arctan_im a).approx K).toRat
      ((TauComplex.cisTauReal
          ((TauReal.arctan_of_rat_seq (a.add dh)).sub
            (TauReal.arctan_of_rat_seq a))).re.approx K).toRat
      ((TauComplex.cisTauReal
          ((TauReal.arctan_of_rat_seq (a.add dh)).sub
            (TauReal.arctan_of_rat_seq a))).im.approx K).toRat
      ((TauReal.cis_arctan_re (a.add dh)).approx K).toRat
      ((TauReal.tangent_defect a).approx K).toRat
      (((TauReal.arctan_of_rat_seq (a.add dh)).sub
          (TauReal.arctan_of_rat_seq a)).approx K).toRat
      (arctan_deriv_partial_rat a.toRat K)
      K h_T_def h_d_K h_AaB h_δ_abs h_R_m1 h_I_m_δ h_D3 h_F1a
      h_a_abs hdh_nn hdh_le_half hK hK_dh
  -- Step 5: close via triangle |T_h - T_a| ≤ |T_h - T_a - RHS_form| + |RHS_form|
  --         ≤ 484·K/2^(K-1) + Helper B bound
  have h_tri_abs : ∀ x y : Rat, |x| ≤ |x - y| + |y| := fun x y => by
    have := abs_add_le (x - y) y
    have h_eq : x - y + y = x := by ring
    rw [h_eq] at this
    exact this
  linarith [h_5C, h_explicit, h_tri_abs
    (((TauReal.tangent_defect (a.add dh)).approx K).toRat
      - ((TauReal.tangent_defect a).approx K).toRat)
    ((((TauReal.cis_arctan_re a).approx K).toRat
       + a.toRat * ((TauReal.cis_arctan_im a).approx K).toRat)
        * ((TauComplex.cisTauReal
            ((TauReal.arctan_of_rat_seq (a.add dh)).sub
              (TauReal.arctan_of_rat_seq a))).im.approx K).toRat
      + ((TauReal.tangent_defect a).approx K).toRat
        * (((TauComplex.cisTauReal
            ((TauReal.arctan_of_rat_seq (a.add dh)).sub
              (TauReal.arctan_of_rat_seq a))).re.approx K).toRat - 1)
      - dh.toRat * ((TauReal.cis_arctan_re (a.add dh)).approx K).toRat)]

/-! ## Sub-Wave 6.M5.E (base case) — target_A at a = 0

  The Module 6 target proposition `cisTauReal_tangent_target_A`, instantiated
  at `a = TauRat.zero`. Both sides are ≈_TR 0:
  - LHS: `(cisTauReal (arctan 0)).im ≈_TR 0` (by cis_arctan_im_zero_equiv_zero)
  - RHS: `(fromTauRat 0) · (cisTauReal (arctan 0)).re ≈_TR 0` (since fromTauRat 0 ≈ 0)

  This is the analytical base case that anchors the Gronwall walk in
  `tangent_defect_equiv_zero` (next sub-piece).
-/

/-- **target_A at a = 0** — The tangent identity holds at `a = 0` directly. -/
theorem TauReal.tangent_target_A_at_zero :
    TauReal.equiv
      (TauComplex.cisTauReal (TauReal.arctan_of_rat_seq TauRat.zero)).im
      ((TauReal.fromTauRat TauRat.zero).mul
        (TauComplex.cisTauReal (TauReal.arctan_of_rat_seq TauRat.zero)).re) := by
  -- Both sides ≈_TR 0; chain via tangent_defect_at_zero_equiv structure.
  apply TauReal.equiv_of_pointwise
  intro n
  rw [equiv_iff_toRat_eq]
  show ((TauComplex.cisTauReal (TauReal.arctan_of_rat_seq TauRat.zero)).im.approx n).toRat
      = (TauRat.mul ((TauReal.fromTauRat TauRat.zero).approx n)
          ((TauComplex.cisTauReal (TauReal.arctan_of_rat_seq TauRat.zero)).re.approx n)).toRat
  rw [toRat_mul]
  show ((TauReal.cis_arctan_im TauRat.zero).approx n).toRat
      = TauRat.zero.toRat * ((TauReal.cis_arctan_re TauRat.zero).approx n).toRat
  rw [TauReal.cis_arctan_im_at_zero_approx_zero n, toRat_zero]
  ring

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

  Today's deliverable (this file): the FOUNDATION (definition + base case)
  + 6.M4 helpers (parity, secant Taylor, magnitude bounds).
  Subsequent sub-Waves: 6.M4.D.2-D.4 + 6.M5.A-E.
-/

end Tau.Boundary
