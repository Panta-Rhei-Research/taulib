import TauLib.BookI.Boundary.TauRealTangentIdentity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity

/-!
# TauLib.BookI.Boundary.TauRealArctanAdd

**Phase C / arctan addition formula at the cisTauReal multiplicativity level**.

After Phase B closed with F.6 / target_A path-β (the τ-native tangent
identity `sin(arctan a) ≈ a · cos(arctan a)` for `4·|a.toRat| ≤ 1`), this
file ships the first step toward Machin's formula:

> **arctan addition at the cisTauReal level**: for TauRats `a, b` with
> `2·|a.toRat| ≤ 1` and `2·|b.toRat| ≤ 1`,
>
>   `cisTauReal (arctan a + arctan b) ≈ cisTauReal (arctan a) · cisTauReal (arctan b)`.

This is the cisTauReal-level form of the classical
`arctan(a) + arctan(b) = arctan((a+b)/(1-ab))` identity — it asserts the
multiplicative behavior of the complex exponential at arctan-image angles,
without requiring angle injectivity (the classical-arctan output form).

The result follows immediately from `TauComplex.cisTauReal_add` (the general
multiplicativity statement at TauReal-input level, shipped in
`TauRealSinCos.lean`, line 1882) combined with
`TauReal.arctan_of_rat_seq_bounded` (the `|arctan_partial_rat a| ≤ 1` bound,
shipped in `TauRealCisDeriv.lean`, line 107).

### Why this is enough for Machin

For Machin's formula `π/4 = 4·arctan(1/5) − arctan(1/239)`, the strategy is
to work at the `cisTauReal` level throughout:
- Each arctan in the sum corresponds to a `cisTauReal` factor.
- Compositions of arctan additions become products of `cisTauReal` factors.
- The Machin identity becomes an equation between products of `cisTauReal`
  factors and `cisTauReal(π/4)` — verifiable by re/im component-matching.

This avoids the need to prove arctan injectivity on the principal branch
(which would require a substantial development of monotonicity properties
plus the open-mapping theorem at TauReal-equiv level).

### Companion: explicit re/im decomposition (via F.6)

We also ship the re/im decomposition of the product
`cisTauReal(arctan a) · cisTauReal(arctan b)`:

  `.re ≈ cos(arctan a) · cos(arctan b) − sin(arctan a) · sin(arctan b)`
        ≈ cos(arctan a) · cos(arctan b) · (1 − a·b)`  (using F.6 on each `sin`)

  `.im ≈ cos(arctan a) · sin(arctan b) + sin(arctan a) · cos(arctan b)`
        ≈ cos(arctan a) · cos(arctan b) · (a + b)`    (using F.6 on each `sin`)

These give the arctan addition formula at the **re/im level** without
needing angle injectivity.

## Module name

This file does not register a module under TauLib/ via `BookI.lean`; it
is picked up by the `.submodules` glob in `lakefile.lean` and built when
referenced.
-/

set_option autoImplicit false

namespace Tau.Boundary

open Tau.Denotation

-- ============================================================
-- PART 1: THE cisTauReal-LEVEL ARCTAN ADDITION FORMULA
-- ============================================================

/-! ## The cisTauReal-level arctan addition

  The first headline theorem: `cisTauReal` is multiplicative on the image
  of `arctan_of_rat_seq` under the standard `2·|a.toRat| ≤ 1` arctan
  domain hypothesis. This is the τ-native form of the classical fact that
  `exp(i(α + β)) = exp(iα) · exp(iβ)` when α, β are arctan-image angles.

  Proof: direct application of `cisTauReal_add` (TauRealSinCos.lean:1882)
  with the boundedness witnesses supplied by `arctan_of_rat_seq_bounded`
  (TauRealCisDeriv.lean:107).
-/

/-- **🎯 Phase C / arctan addition (cisTauReal multiplicativity level)** —
    for TauRats `a, b` with `2·|a.toRat| ≤ 1` and `2·|b.toRat| ≤ 1`,

        `cisTauReal (arctan a + arctan b) ≈ cisTauReal (arctan a) · cisTauReal (arctan b)`.

    This is the first step toward Machin's formula. It asserts that the
    complex-exponential map `cisTauReal` is multiplicative on the arctan
    image, without requiring angle injectivity. -/
theorem TauReal.cisTauReal_arctan_add (a b : TauRat)
    (ha : 2 * |a.toRat| ≤ 1) (hb : 2 * |b.toRat| ≤ 1) :
    TauComplex.equiv
      (TauComplex.cisTauReal
        ((TauReal.arctan_of_rat_seq a).add (TauReal.arctan_of_rat_seq b)))
      ((TauComplex.cisTauReal (TauReal.arctan_of_rat_seq a)).mul
        (TauComplex.cisTauReal (TauReal.arctan_of_rat_seq b))) :=
  TauComplex.cisTauReal_add
    (TauReal.arctan_of_rat_seq a) (TauReal.arctan_of_rat_seq b)
    (TauReal.arctan_of_rat_seq_bounded a ha)
    (TauReal.arctan_of_rat_seq_bounded b hb)

-- ============================================================
-- PART 2: F.6-BASED re/im DECOMPOSITION
-- ============================================================

/-! ## F.6-based decomposition of the product

  Using F.6 (`cisTauReal_tangent_target_A_path_beta`), which expresses
  `sin(arctan a)` as `a · cos(arctan a)` (for `4·|a.toRat| ≤ 1`), we obtain
  the explicit re/im expressions for the product
  `cisTauReal(arctan a) · cisTauReal(arctan b)`:

      .re ≈ cos(arctan a) · cos(arctan b) − sin(arctan a) · sin(arctan b)
          ≈ cos(arctan a) · cos(arctan b) − (a · cos(arctan a)) · (b · cos(arctan b))
          ≈ cos(arctan a) · cos(arctan b) · (1 − a·b)         [via F.6 twice]

      .im ≈ cos(arctan a) · sin(arctan b) + sin(arctan a) · cos(arctan b)
          ≈ cos(arctan a) · (b · cos(arctan b)) + (a · cos(arctan a)) · cos(arctan b)
          ≈ cos(arctan a) · cos(arctan b) · (a + b)            [via F.6 twice]

  We ship the **structural .re/.im decomposition** of the product first
  (a definitional unfold), then the F.6-substituted forms. The classical
  arctan addition formula at the re/im level is the consequence:
  the product is equivalent to `K · (1 − a·b, a + b)` where
  `K = cos(arctan a) · cos(arctan b)` plays the role of the magnitude
  scaling factor of `cisTauReal(arctan((a+b)/(1-ab)))`.
-/

/-- **Structural re-decomposition** of the cisTauReal product:

        `(cisTauReal(arctan a) · cisTauReal(arctan b)).re`
            = `cos(arctan a) · cos(arctan b) − sin(arctan a) · sin(arctan b)`

    where `cos(arctan a) = (cisTauReal(arctan a)).re` and
    `sin(arctan a) = (cisTauReal(arctan a)).im`, by τ-canon naming.

    This is a **definitional equality** (`rfl`) at the `.re` field of
    `TauComplex.mul`; supplied here as a named handle for downstream
    chaining. -/
theorem TauReal.cisTauReal_arctan_mul_re_eq (a b : TauRat) :
    ((TauComplex.cisTauReal (TauReal.arctan_of_rat_seq a)).mul
      (TauComplex.cisTauReal (TauReal.arctan_of_rat_seq b))).re
      = ((TauComplex.cisTauReal (TauReal.arctan_of_rat_seq a)).re.mul
          (TauComplex.cisTauReal (TauReal.arctan_of_rat_seq b)).re).sub
          ((TauComplex.cisTauReal (TauReal.arctan_of_rat_seq a)).im.mul
            (TauComplex.cisTauReal (TauReal.arctan_of_rat_seq b)).im) := rfl

/-- **Structural im-decomposition** of the cisTauReal product:

        `(cisTauReal(arctan a) · cisTauReal(arctan b)).im`
            = `cos(arctan a) · sin(arctan b) + sin(arctan a) · cos(arctan b)`

    Definitional equality at the `.im` field of `TauComplex.mul`. -/
theorem TauReal.cisTauReal_arctan_mul_im_eq (a b : TauRat) :
    ((TauComplex.cisTauReal (TauReal.arctan_of_rat_seq a)).mul
      (TauComplex.cisTauReal (TauReal.arctan_of_rat_seq b))).im
      = ((TauComplex.cisTauReal (TauReal.arctan_of_rat_seq a)).re.mul
          (TauComplex.cisTauReal (TauReal.arctan_of_rat_seq b)).im).add
          ((TauComplex.cisTauReal (TauReal.arctan_of_rat_seq a)).im.mul
            (TauComplex.cisTauReal (TauReal.arctan_of_rat_seq b)).re) := rfl

-- ============================================================
-- PART 3: F.6 SUBSTITUTION — THE arctan ADDITION FORMULA AT re/im LEVEL
-- ============================================================

/-! ## F.6 substitution for the product re/im

  Using `cisTauReal_tangent_target_A_path_beta` (F.6), we substitute
  `sin(arctan a) ≈ (fromTauRat a) · cos(arctan a)` (and symmetrically for `b`)
  into the structural re/im expressions, obtaining the arctan addition
  formula at the re/im level.

  These are the **pointwise re/im** statements: the product's re-component
  approximation `.toRat` at depth `n` is the algebraic expression
  `cos·cos − a·b·cos·cos`, and the im-component is `(a+b)·cos·cos`.

  We formalize this via the `.approx n .toRat` form, which avoids
  the need to invoke `mul_respects_equiv_*` chains at the TauReal level
  and instead reduces to a purely rational computation at every depth.
-/

/-- **Pointwise re-decomposition** of the cisTauReal product at depth `n`:

        `((cisTauReal(arctan a) · cisTauReal(arctan b)).re.approx n).toRat`
          = `cos_re_n · cos_re_n' − sin_im_n · sin_im_n'`

    where `cos_re_n := ((cisTauReal(arctan a)).re.approx n).toRat`,
          `sin_im_n := ((cisTauReal(arctan a)).im.approx n).toRat`,
          `cos_re_n' := ((cisTauReal(arctan b)).re.approx n).toRat`,
          `sin_im_n' := ((cisTauReal(arctan b)).im.approx n).toRat`. -/
theorem TauReal.cisTauReal_arctan_mul_re_approx_toRat (a b : TauRat) (n : Nat) :
    (((TauComplex.cisTauReal (TauReal.arctan_of_rat_seq a)).mul
        (TauComplex.cisTauReal (TauReal.arctan_of_rat_seq b))).re.approx n).toRat
      = ((TauComplex.cisTauReal (TauReal.arctan_of_rat_seq a)).re.approx n).toRat
          * ((TauComplex.cisTauReal (TauReal.arctan_of_rat_seq b)).re.approx n).toRat
        - ((TauComplex.cisTauReal (TauReal.arctan_of_rat_seq a)).im.approx n).toRat
          * ((TauComplex.cisTauReal (TauReal.arctan_of_rat_seq b)).im.approx n).toRat := by
  rw [TauReal.cisTauReal_arctan_mul_re_eq]
  show (TauRat.add
          (((TauComplex.cisTauReal (TauReal.arctan_of_rat_seq a)).re.approx n).mul
            ((TauComplex.cisTauReal (TauReal.arctan_of_rat_seq b)).re.approx n))
          (TauRat.negate
            (((TauComplex.cisTauReal (TauReal.arctan_of_rat_seq a)).im.approx n).mul
              ((TauComplex.cisTauReal (TauReal.arctan_of_rat_seq b)).im.approx n)))).toRat = _
  rw [toRat_add, toRat_negate, toRat_mul, toRat_mul]
  ring

/-- **Pointwise im-decomposition** of the cisTauReal product at depth `n`. -/
theorem TauReal.cisTauReal_arctan_mul_im_approx_toRat (a b : TauRat) (n : Nat) :
    (((TauComplex.cisTauReal (TauReal.arctan_of_rat_seq a)).mul
        (TauComplex.cisTauReal (TauReal.arctan_of_rat_seq b))).im.approx n).toRat
      = ((TauComplex.cisTauReal (TauReal.arctan_of_rat_seq a)).re.approx n).toRat
          * ((TauComplex.cisTauReal (TauReal.arctan_of_rat_seq b)).im.approx n).toRat
        + ((TauComplex.cisTauReal (TauReal.arctan_of_rat_seq a)).im.approx n).toRat
          * ((TauComplex.cisTauReal (TauReal.arctan_of_rat_seq b)).re.approx n).toRat := by
  rw [TauReal.cisTauReal_arctan_mul_im_eq]
  show (TauRat.add
          (((TauComplex.cisTauReal (TauReal.arctan_of_rat_seq a)).re.approx n).mul
            ((TauComplex.cisTauReal (TauReal.arctan_of_rat_seq b)).im.approx n))
          (((TauComplex.cisTauReal (TauReal.arctan_of_rat_seq a)).im.approx n).mul
            ((TauComplex.cisTauReal (TauReal.arctan_of_rat_seq b)).re.approx n))).toRat = _
  rw [toRat_add, toRat_mul, toRat_mul]

/-! ## F.6-substituted re/im formulas

  Applying `cisTauReal_tangent_target_A_path_beta` (F.6) to substitute
  `sin(arctan a) ≈ a · cos(arctan a)` (and the same for `b`), we obtain the
  classical addition formulas at the re/im level. The hypotheses
  `4·|a.toRat| ≤ 1` and `4·|b.toRat| ≤ 1` are inherited from F.6's
  path-β domain.

  The substituted form is most naturally expressed via TauReal-equiv on
  the .im component (using F.6 for each arctan-image angle):

      (cisTauReal(arctan a) · cisTauReal(arctan b)).im
          ≈  cos(arctan a) · sin(arctan b) + sin(arctan a) · cos(arctan b)
          ≈  cos(arctan a) · (b · cos(arctan b)) + (a · cos(arctan a)) · cos(arctan b)
          ≈  (a + b) · (cos(arctan a) · cos(arctan b))

  The chain involves bilateral `mul_respects_equiv_both` applications;
  the bounds for those come from the cisTauReal pointwise bounds
  (`cisTauReal_re_pointwise_abs_le_one` etc., or via Pythagoras).

  We document this at the toRat-pointwise level here (which is the most
  immediately useful form for downstream `equiv_of_pointwise` and modulus
  chasing); the full TauReal-equiv form is left for downstream callers
  to discharge when they need it.
-/

/-- **F.6-substituted re-form at depth `n`** — using F.6's tangent identity
    `sin(arctan a) ≈ a · cos(arctan a)` substituted into the structural
    re-decomposition. This is the *pointwise toRat* expression of
    `(cisTauReal(arctan a) · cisTauReal(arctan b)).re` in terms of the
    arctan-image cosines plus the `(1 − a·b)` factor.

    The hypothesis here is the **structural** depth-`n` toRat substitution:
    we assume the .im/.re values match `a · re`-form pointwise at depth `n`
    (which is the strongest form of F.6, and exactly the path-β-region
    F.6 path-β provides at the Cauchy-equiv level).

    Most callers will compose this with F.6 at the `TauReal.equiv` level
    via the standard mul-congruence machinery; the pointwise form is
    given as a structural tool. -/
theorem TauReal.cisTauReal_arctan_mul_re_substituted (a b : TauRat) (n : Nat)
    (ha_im_re : ((TauComplex.cisTauReal (TauReal.arctan_of_rat_seq a)).im.approx n).toRat
                  = a.toRat
                    * ((TauComplex.cisTauReal (TauReal.arctan_of_rat_seq a)).re.approx n).toRat)
    (hb_im_re : ((TauComplex.cisTauReal (TauReal.arctan_of_rat_seq b)).im.approx n).toRat
                  = b.toRat
                    * ((TauComplex.cisTauReal (TauReal.arctan_of_rat_seq b)).re.approx n).toRat) :
    (((TauComplex.cisTauReal (TauReal.arctan_of_rat_seq a)).mul
        (TauComplex.cisTauReal (TauReal.arctan_of_rat_seq b))).re.approx n).toRat
      = ((TauComplex.cisTauReal (TauReal.arctan_of_rat_seq a)).re.approx n).toRat
        * ((TauComplex.cisTauReal (TauReal.arctan_of_rat_seq b)).re.approx n).toRat
        * (1 - a.toRat * b.toRat) := by
  rw [TauReal.cisTauReal_arctan_mul_re_approx_toRat, ha_im_re, hb_im_re]
  ring

/-- **F.6-substituted im-form at depth `n`** — the classical
    arctan addition formula at the im level:
    `cos(arctan a) · cos(arctan b) · (a + b)`. -/
theorem TauReal.cisTauReal_arctan_mul_im_substituted (a b : TauRat) (n : Nat)
    (ha_im_re : ((TauComplex.cisTauReal (TauReal.arctan_of_rat_seq a)).im.approx n).toRat
                  = a.toRat
                    * ((TauComplex.cisTauReal (TauReal.arctan_of_rat_seq a)).re.approx n).toRat)
    (hb_im_re : ((TauComplex.cisTauReal (TauReal.arctan_of_rat_seq b)).im.approx n).toRat
                  = b.toRat
                    * ((TauComplex.cisTauReal (TauReal.arctan_of_rat_seq b)).re.approx n).toRat) :
    (((TauComplex.cisTauReal (TauReal.arctan_of_rat_seq a)).mul
        (TauComplex.cisTauReal (TauReal.arctan_of_rat_seq b))).im.approx n).toRat
      = ((TauComplex.cisTauReal (TauReal.arctan_of_rat_seq a)).re.approx n).toRat
        * ((TauComplex.cisTauReal (TauReal.arctan_of_rat_seq b)).re.approx n).toRat
        * (a.toRat + b.toRat) := by
  rw [TauReal.cisTauReal_arctan_mul_im_approx_toRat, ha_im_re, hb_im_re]
  ring

-- ============================================================
-- PART 4: TauReal-EQUIV LEVEL F.6 APPLICATION TO THE .im COMPONENT
-- ============================================================

/-! ## TauReal-equiv-level F.6 application to the product

  Combining `cisTauReal_arctan_mul_im_eq` (structural) with F.6 (the
  tangent identity `sin(arctan a) ≈ a · cos(arctan a)` for `4·|a.toRat| ≤ 1`),
  we obtain the arctan addition formula on the .im component of the
  product **at the TauReal.equiv level**:

      .im_product ≈ cisA.re · (fromTauRat b · cisB.re)
                  + (fromTauRat a · cisA.re) · cisB.re

  The chain:
  1. `.im_product = cisA.re · cisB.im + cisA.im · cisB.re`  (structural)
  2. `cisA.re · cisB.im ≈ cisA.re · (fromTauRat b · cisB.re)`  (F.6 on b)
  3. `cisA.im · cisB.re ≈ (fromTauRat a · cisA.re) · cisB.re`  (F.6 on a)
  4. Combine via `equiv_add_congr`.

  The bounds for mul-congruence come from:
  - `cisA.re`, `cisB.re` bounded by 8 (via `cis_arctan_re_approx_abs_le_8`)
  - `cisA.im`, `cisB.im` bounded by 8 (via `cis_arctan_im_approx_abs_le_8`)
  - `fromTauRat a · cisA.re`, `fromTauRat b · cisB.re` bounded by 1·8 = 8
    (since `|a|, |b| ≤ 1` and `|cisA.re| ≤ 8`)

  We choose `M = 8` as a uniform bound for all these. -/

/-- **Pointwise abs.toRat of fromTauRat**: `((fromTauRat q).approx n).abs.toRat = |q.toRat|`. -/
private theorem TauReal.fromTauRat_approx_abs_toRat_eq (q : TauRat) (n : Nat) :
    ((TauReal.fromTauRat q).approx n).abs.toRat = |q.toRat| := by
  show (q.abs).toRat = |q.toRat|
  rw [TauRat.toRat_abs]

/-- Pointwise bound on `(fromTauRat q).mul x` by 8 from
    `|q.toRat| ≤ 1` and pointwise bound `|x.approx n| ≤ 8`. -/
private theorem TauReal.fromTauRat_mul_bounded_by_eight
    (q : TauRat) (x : TauReal)
    (hq : |q.toRat| ≤ 1)
    (hx : ∀ n, (x.approx n).abs.toRat ≤ 8) :
    ∀ n, (((TauReal.fromTauRat q).mul x).approx n).abs.toRat ≤ 8 := by
  intro n
  show ((TauRat.mul ((TauReal.fromTauRat q).approx n) (x.approx n)).abs).toRat ≤ 8
  rw [TauRat.toRat_abs, toRat_mul]
  show |q.toRat * (x.approx n).toRat| ≤ 8
  have h_abs_mul : |q.toRat * (x.approx n).toRat|
                    = |q.toRat| * |(x.approx n).toRat| := by
    rw [abs_mul]
  rw [h_abs_mul]
  have h_x_n := hx n
  rw [TauRat.toRat_abs] at h_x_n
  have h_q_nn : 0 ≤ |q.toRat| := _root_.abs_nonneg _
  have h_x_nn : 0 ≤ |(x.approx n).toRat| := _root_.abs_nonneg _
  -- |q.toRat| · |x.approx n .toRat| ≤ 1 · 8 = 8
  calc |q.toRat| * |(x.approx n).toRat|
      ≤ 1 * |(x.approx n).toRat| := by
        apply mul_le_mul_of_nonneg_right hq h_x_nn
    _ ≤ 1 * 8 := by
        apply mul_le_mul_of_nonneg_left h_x_n (by norm_num : (0 : Rat) ≤ 1)
    _ = 8 := by ring

/-- **🎯 TauReal-equiv arctan addition on .im** — the classical formula
    `sin(α + β) = sin α · cos β + cos α · sin β` substituted with F.6's
    `sin(arctan x) ≈ x · cos(arctan x)`:

        `(cisTauReal(arctan a) · cisTauReal(arctan b)).im`
          `≈ cos(arctan a) · (fromTauRat b · cos(arctan b))`
              `+ (fromTauRat a · cos(arctan a)) · cos(arctan b)`

    via bilateral mul-congruence. This is the **TauReal-equiv-level**
    form (no pointwise hypotheses needed; the hypotheses `4·|a.toRat| ≤ 1`
    and `4·|b.toRat| ≤ 1` are inherited from F.6's path-β domain). -/
theorem TauReal.cisTauReal_arctan_mul_im_equiv_F6_form (a b : TauRat)
    (ha : 4 * |a.toRat| ≤ 1) (hb : 4 * |b.toRat| ≤ 1) :
    TauReal.equiv
      ((TauComplex.cisTauReal (TauReal.arctan_of_rat_seq a)).mul
        (TauComplex.cisTauReal (TauReal.arctan_of_rat_seq b))).im
      (((TauComplex.cisTauReal (TauReal.arctan_of_rat_seq a)).re.mul
          ((TauReal.fromTauRat b).mul
            (TauComplex.cisTauReal (TauReal.arctan_of_rat_seq b)).re)).add
        (((TauReal.fromTauRat a).mul
            (TauComplex.cisTauReal (TauReal.arctan_of_rat_seq a)).re).mul
          (TauComplex.cisTauReal (TauReal.arctan_of_rat_seq b)).re)) := by
  -- Path-β ⇒ 2·|·| ≤ 1
  have ha2 : 2 * |a.toRat| ≤ 1 := by
    have := _root_.abs_nonneg a.toRat; linarith
  have hb2 : 2 * |b.toRat| ≤ 1 := by
    have := _root_.abs_nonneg b.toRat; linarith
  have ha1 : |a.toRat| ≤ 1 := by
    have := _root_.abs_nonneg a.toRat; linarith
  have hb1 : |b.toRat| ≤ 1 := by
    have := _root_.abs_nonneg b.toRat; linarith
  -- F.6 on a and b
  have h_F6_a : TauReal.equiv
      (TauComplex.cisTauReal (TauReal.arctan_of_rat_seq a)).im
      ((TauReal.fromTauRat a).mul (TauComplex.cisTauReal (TauReal.arctan_of_rat_seq a)).re) :=
    TauReal.cisTauReal_tangent_target_A_path_beta a ha
  have h_F6_b : TauReal.equiv
      (TauComplex.cisTauReal (TauReal.arctan_of_rat_seq b)).im
      ((TauReal.fromTauRat b).mul (TauComplex.cisTauReal (TauReal.arctan_of_rat_seq b)).re) :=
    TauReal.cisTauReal_tangent_target_A_path_beta b hb
  -- Pointwise bounds on cis_arctan re/im (≤ 8)
  have h_cisA_re_bd : ∀ n,
      ((TauComplex.cisTauReal (TauReal.arctan_of_rat_seq a)).re.approx n).abs.toRat ≤ 8 := by
    intro n
    have := TauReal.cis_arctan_re_approx_abs_le_8 a ha2 n
    show ((TauReal.cis_arctan_re a).approx n).abs.toRat ≤ 8
    exact this
  have h_cisB_re_bd : ∀ n,
      ((TauComplex.cisTauReal (TauReal.arctan_of_rat_seq b)).re.approx n).abs.toRat ≤ 8 := by
    intro n
    have := TauReal.cis_arctan_re_approx_abs_le_8 b hb2 n
    show ((TauReal.cis_arctan_re b).approx n).abs.toRat ≤ 8
    exact this
  have h_cisA_im_bd : ∀ n,
      ((TauComplex.cisTauReal (TauReal.arctan_of_rat_seq a)).im.approx n).abs.toRat ≤ 8 := by
    intro n
    have := TauReal.cis_arctan_im_approx_abs_le_8 a ha2 n
    show ((TauReal.cis_arctan_im a).approx n).abs.toRat ≤ 8
    exact this
  have h_cisB_im_bd : ∀ n,
      ((TauComplex.cisTauReal (TauReal.arctan_of_rat_seq b)).im.approx n).abs.toRat ≤ 8 := by
    intro n
    have := TauReal.cis_arctan_im_approx_abs_le_8 b hb2 n
    show ((TauReal.cis_arctan_im b).approx n).abs.toRat ≤ 8
    exact this
  -- Bound on (fromTauRat a · cisA.re) by 8
  have h_a_mul_cisA_re_bd : ∀ n,
      (((TauReal.fromTauRat a).mul
          (TauComplex.cisTauReal (TauReal.arctan_of_rat_seq a)).re).approx n).abs.toRat ≤ 8 :=
    TauReal.fromTauRat_mul_bounded_by_eight a _ ha1 h_cisA_re_bd
  -- Bound on (fromTauRat b · cisB.re) by 8
  have h_b_mul_cisB_re_bd : ∀ n,
      (((TauReal.fromTauRat b).mul
          (TauComplex.cisTauReal (TauReal.arctan_of_rat_seq b)).re).approx n).abs.toRat ≤ 8 :=
    TauReal.fromTauRat_mul_bounded_by_eight b _ hb1 h_cisB_re_bd
  -- Apply equiv_mul_congr to each summand
  -- Left summand: cisA.re · cisB.im ≈ cisA.re · (fromTauRat b · cisB.re)
  -- Use right_of_bound: a := cisB.im, b := fromTauRat b · cisB.re, c := cisA.re, bound on c
  -- But mul_respects_equiv_right_of_bound gives a·c ≈ b·c, but we want cisA.re·cisB.im ≈ cisA.re·(...)
  -- So we need to swap to use commutativity, OR use equiv_mul_congr.
  have h_left : TauReal.equiv
      ((TauComplex.cisTauReal (TauReal.arctan_of_rat_seq a)).re.mul
        (TauComplex.cisTauReal (TauReal.arctan_of_rat_seq b)).im)
      ((TauComplex.cisTauReal (TauReal.arctan_of_rat_seq a)).re.mul
        ((TauReal.fromTauRat b).mul
          (TauComplex.cisTauReal (TauReal.arctan_of_rat_seq b)).re)) := by
    -- a := cisA.re, a' := cisA.re, b := cisB.im, b' := fromTauRat b · cisB.re
    -- bound on a' = cisA.re (Ma = 8); bound on b = cisB.im (Mb = 8)
    apply TauReal.equiv_mul_congr (Ma := 8) (Mb := 8) (by norm_num) (by norm_num)
    · exact h_cisA_re_bd
    · exact h_cisB_im_bd
    · exact TauReal.equiv_refl _
    · exact h_F6_b
  -- Right summand: cisA.im · cisB.re ≈ (fromTauRat a · cisA.re) · cisB.re
  have h_right : TauReal.equiv
      ((TauComplex.cisTauReal (TauReal.arctan_of_rat_seq a)).im.mul
        (TauComplex.cisTauReal (TauReal.arctan_of_rat_seq b)).re)
      (((TauReal.fromTauRat a).mul
          (TauComplex.cisTauReal (TauReal.arctan_of_rat_seq a)).re).mul
        (TauComplex.cisTauReal (TauReal.arctan_of_rat_seq b)).re) := by
    -- a := cisA.im, a' := fromTauRat a · cisA.re, b := cisB.re, b' := cisB.re
    -- bound on a' = fromTauRat a · cisA.re (Ma = 8); bound on b = cisB.re (Mb = 8)
    apply TauReal.equiv_mul_congr (Ma := 8) (Mb := 8) (by norm_num) (by norm_num)
    · exact h_a_mul_cisA_re_bd
    · exact h_cisB_re_bd
    · exact h_F6_a
    · exact TauReal.equiv_refl _
  -- Combine via equiv_add_congr (no bounds needed)
  -- LHS .im is definitionally  cisA.re · cisB.im + cisA.im · cisB.re
  show TauReal.equiv
      (((TauComplex.cisTauReal (TauReal.arctan_of_rat_seq a)).re.mul
          (TauComplex.cisTauReal (TauReal.arctan_of_rat_seq b)).im).add
        ((TauComplex.cisTauReal (TauReal.arctan_of_rat_seq a)).im.mul
          (TauComplex.cisTauReal (TauReal.arctan_of_rat_seq b)).re))
      _
  exact TauReal.equiv_add_congr h_left h_right

/-- **🎯 TauReal-equiv arctan addition on .re** — the classical formula
    `cos(α + β) = cos α · cos β − sin α · sin β` substituted with F.6's
    `sin(arctan x) ≈ x · cos(arctan x)`:

        `(cisTauReal(arctan a) · cisTauReal(arctan b)).re`
          `≈ cos(arctan a) · cos(arctan b)`
              `− (fromTauRat a · cos(arctan a)) · (fromTauRat b · cos(arctan b))`

    via bilateral mul-congruence + sub-congruence. -/
theorem TauReal.cisTauReal_arctan_mul_re_equiv_F6_form (a b : TauRat)
    (ha : 4 * |a.toRat| ≤ 1) (hb : 4 * |b.toRat| ≤ 1) :
    TauReal.equiv
      ((TauComplex.cisTauReal (TauReal.arctan_of_rat_seq a)).mul
        (TauComplex.cisTauReal (TauReal.arctan_of_rat_seq b))).re
      (((TauComplex.cisTauReal (TauReal.arctan_of_rat_seq a)).re.mul
          (TauComplex.cisTauReal (TauReal.arctan_of_rat_seq b)).re).sub
        (((TauReal.fromTauRat a).mul
            (TauComplex.cisTauReal (TauReal.arctan_of_rat_seq a)).re).mul
          ((TauReal.fromTauRat b).mul
            (TauComplex.cisTauReal (TauReal.arctan_of_rat_seq b)).re))) := by
  -- Path-β ⇒ 2·|·| ≤ 1
  have ha2 : 2 * |a.toRat| ≤ 1 := by
    have := _root_.abs_nonneg a.toRat; linarith
  have hb2 : 2 * |b.toRat| ≤ 1 := by
    have := _root_.abs_nonneg b.toRat; linarith
  have ha1 : |a.toRat| ≤ 1 := by
    have := _root_.abs_nonneg a.toRat; linarith
  have hb1 : |b.toRat| ≤ 1 := by
    have := _root_.abs_nonneg b.toRat; linarith
  -- F.6 on a and b
  have h_F6_a : TauReal.equiv
      (TauComplex.cisTauReal (TauReal.arctan_of_rat_seq a)).im
      ((TauReal.fromTauRat a).mul (TauComplex.cisTauReal (TauReal.arctan_of_rat_seq a)).re) :=
    TauReal.cisTauReal_tangent_target_A_path_beta a ha
  have h_F6_b : TauReal.equiv
      (TauComplex.cisTauReal (TauReal.arctan_of_rat_seq b)).im
      ((TauReal.fromTauRat b).mul (TauComplex.cisTauReal (TauReal.arctan_of_rat_seq b)).re) :=
    TauReal.cisTauReal_tangent_target_A_path_beta b hb
  -- Pointwise bounds (≤ 8)
  have h_cisA_im_bd : ∀ n,
      ((TauComplex.cisTauReal (TauReal.arctan_of_rat_seq a)).im.approx n).abs.toRat ≤ 8 := by
    intro n
    show ((TauReal.cis_arctan_im a).approx n).abs.toRat ≤ 8
    exact TauReal.cis_arctan_im_approx_abs_le_8 a ha2 n
  have h_cisB_im_bd : ∀ n,
      ((TauComplex.cisTauReal (TauReal.arctan_of_rat_seq b)).im.approx n).abs.toRat ≤ 8 := by
    intro n
    show ((TauReal.cis_arctan_im b).approx n).abs.toRat ≤ 8
    exact TauReal.cis_arctan_im_approx_abs_le_8 b hb2 n
  have h_cisA_re_bd : ∀ n,
      ((TauComplex.cisTauReal (TauReal.arctan_of_rat_seq a)).re.approx n).abs.toRat ≤ 8 := by
    intro n
    show ((TauReal.cis_arctan_re a).approx n).abs.toRat ≤ 8
    exact TauReal.cis_arctan_re_approx_abs_le_8 a ha2 n
  have h_cisB_re_bd : ∀ n,
      ((TauComplex.cisTauReal (TauReal.arctan_of_rat_seq b)).re.approx n).abs.toRat ≤ 8 := by
    intro n
    show ((TauReal.cis_arctan_re b).approx n).abs.toRat ≤ 8
    exact TauReal.cis_arctan_re_approx_abs_le_8 b hb2 n
  have h_a_mul_cisA_re_bd : ∀ n,
      (((TauReal.fromTauRat a).mul
          (TauComplex.cisTauReal (TauReal.arctan_of_rat_seq a)).re).approx n).abs.toRat ≤ 8 :=
    TauReal.fromTauRat_mul_bounded_by_eight a _ ha1 h_cisA_re_bd
  have h_b_mul_cisB_re_bd : ∀ n,
      (((TauReal.fromTauRat b).mul
          (TauComplex.cisTauReal (TauReal.arctan_of_rat_seq b)).re).approx n).abs.toRat ≤ 8 :=
    TauReal.fromTauRat_mul_bounded_by_eight b _ hb1 h_cisB_re_bd
  -- Mul-mul (right): cisA.re · cisB.re ≈ cisA.re · cisB.re  (refl, no work)
  have h_re_re : TauReal.equiv
      ((TauComplex.cisTauReal (TauReal.arctan_of_rat_seq a)).re.mul
        (TauComplex.cisTauReal (TauReal.arctan_of_rat_seq b)).re)
      ((TauComplex.cisTauReal (TauReal.arctan_of_rat_seq a)).re.mul
        (TauComplex.cisTauReal (TauReal.arctan_of_rat_seq b)).re) :=
    TauReal.equiv_refl _
  -- Mul-mul (im-im): cisA.im · cisB.im ≈ (fromTauRat a · cisA.re) · (fromTauRat b · cisB.re)
  have h_im_im : TauReal.equiv
      ((TauComplex.cisTauReal (TauReal.arctan_of_rat_seq a)).im.mul
        (TauComplex.cisTauReal (TauReal.arctan_of_rat_seq b)).im)
      (((TauReal.fromTauRat a).mul
          (TauComplex.cisTauReal (TauReal.arctan_of_rat_seq a)).re).mul
        ((TauReal.fromTauRat b).mul
          (TauComplex.cisTauReal (TauReal.arctan_of_rat_seq b)).re)) := by
    apply TauReal.equiv_mul_congr (Ma := 8) (Mb := 8) (by norm_num) (by norm_num)
    · exact h_a_mul_cisA_re_bd
    · exact h_cisB_im_bd
    · exact h_F6_a
    · exact h_F6_b
  -- Combine via equiv_sub_congr.
  -- LHS .re is definitionally  cisA.re · cisB.re - cisA.im · cisB.im
  show TauReal.equiv
      (((TauComplex.cisTauReal (TauReal.arctan_of_rat_seq a)).re.mul
          (TauComplex.cisTauReal (TauReal.arctan_of_rat_seq b)).re).sub
        ((TauComplex.cisTauReal (TauReal.arctan_of_rat_seq a)).im.mul
          (TauComplex.cisTauReal (TauReal.arctan_of_rat_seq b)).im))
      _
  exact TauReal.equiv_sub_congr h_re_re h_im_im

/-! ## Notes for Phase D — Machin's formula

  This file ships **Option 3** (cisTauReal-level arctan addition), which is
  sufficient for Machin's formula via the strategy:

  - `arctan(1/5)` and `arctan(1/239)` each lift to `cisTauReal` values.
  - The Machin identity `π/4 = 4·arctan(1/5) − arctan(1/239)` becomes
    `cisTauReal(π/4) ≈ cisTauReal(arctan(1/5))^4 · cisTauReal(-arctan(1/239))`
    (using `cisTauReal_arctan_add` iteratively).
  - The RHS is computed entirely from the rational data
    `1/5` and `1/239` via the F.6-substituted re/im formulas.
  - The LHS `cisTauReal(π/4) ≈ (1/√2, 1/√2)` matches the RHS by
    direct Rat-level computation (with the magnitude scaling factor
    `cos(arctan(1/5))^4 · cos(arctan(1/239))` absorbed into the
    `equiv` modulus chase).

  The angle-level addition formula (Option 1) would require **arctan
  injectivity on the principal branch**, which is a Phase E concern
  (not needed for the Machin / BBPLeibniz keystone).
-/

end Tau.Boundary
