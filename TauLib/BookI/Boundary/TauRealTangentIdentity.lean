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
