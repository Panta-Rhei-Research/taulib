import TauLib.BookI.Boundary.TauRealMachin
import Mathlib.Tactic.Ring
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity

/-!
# TauLib.BookI.Boundary.TauRealMachinProducts

**Phase E partial / Scope A — quadruple-arctan product identity at the
TauComplex level.**

After Phase D (commit `267cdfd`) shipped the building blocks
(`cisTauReal_arctan_double`, `cisTauReal_arctan_negate_*`, plus the
F.6-substituted double-angle forms), this module advances the Machin
chain by one concrete step: the **quadruple-arctan product identity**.

### What Phase E Scope A delivers

The cleanest intermediate Machin product identity that we can ship at
TauComplex-equiv level without requiring angle injectivity or a
τ-native `cisTauReal(π/4) ≈ (1+i)/√2` identity:

> **🎯 Theorem `cisTauReal_arctan_four_product`** (general form,
>   `4·|a.toRat| ≤ 1`):
>
>   `cisTauReal((arctan a + arctan a) + (arctan a + arctan a))
>     ≈ cisTauReal(arctan a)² · cisTauReal(arctan a)²`

specialized to the Machin constants:

> **🎯 `cisTauReal_arctan_four_at_one_fifth`** — at `a = 1/5`.
> **🎯 `cisTauReal_arctan_four_at_one_two_three_nine`** — at `a = 1/239`.

This is the τ-native form of `exp(i·4·arctan(a)) = exp(i·arctan(a))⁴`,
and represents the **first half of the Machin chain**
`π = 16·arctan(1/5) − 4·arctan(1/239)` at TauComplex level (the
quadrupled portion of the first arctan).

### The key bound problem and its resolution

The challenge: `cisTauReal_add` requires both operands `x, y` to be
bounded by 1 in absolute value at every depth. For `arctan(1/5)`, the
existing `arctan_of_rat_seq_bounded` gives only `|partial| ≤ 1`, not
the tighter `|partial| ≤ 1/2` we need to iterate `cisTauReal_add` to
the next level (where we sum two doubled-arctan partial sums).

**Solution**: a sharpened pointwise bound for `4·|a.toRat| ≤ 1`
(the F.6 path-β domain):

> **Lemma `arctan_partial_rat_abs_le_half`**:
>
>   For `4·|a| ≤ 1`,  `|arctan_partial_rat a n| ≤ 1/2`.

Specifically, the existing `arctan_partial_rat_abs_tight_bound` gives
`(1 − |a|⁴)·|partial| ≤ (5/4)·|a|·(1 − |a|^(4n))`. For `4·|a| ≤ 1`:
- `|a|⁴ ≤ 1/256`, so `1 − |a|⁴ ≥ 255/256`.
- `(5/4)·|a| ≤ 5/16`.
- `(5/4)·|a| / (1 − |a|⁴) ≤ (5/16) / (255/256) = 80/255 ≤ 1/2`. ✓

This sharpened bound is exactly enough to handle two-level iteration of
`cisTauReal_add` (`x + x` is bounded by 1; `(x+x) + (x+x)` requires
`x+x` bounded by 1, which holds via doubled `|partial| ≤ 1/2`).

### What this does NOT close (Phase E Scope B, C, D…)

The full `MachinIdentity` proposition (TauRealMachin.lean ~line 459)
requires:

1. **Negation side**: combine the quadruple-arctan product with
   `arctan(−1/239)`. This is provable at the **TauComplex product**
   level via `TauComplex.equiv_mul_congr` with Phase D's
   `cisTauReal_arctan_negate_equiv_conj`, but the
   **`cisTauReal_add`-of-sum form** does not work directly because
   the 4-sum `(arctan(1/5)+arctan(1/5)) + (arctan(1/5)+arctan(1/5))`
   has partial sums bounded by `4·(1/2) = 2 > 1`, exceeding
   `cisTauReal_add`'s `≤ 1` hypothesis. See the notes at the end
   of this file for resolution strategies.

2. **Connection to π**: relate `cisTauReal(arctan(1/5))⁴ ·
   conj(cisTauReal(arctan(1/239)))` to `cisTauReal(π/4) = (1+i)/√2`.
   This requires either (a) τ-native `√2` plus the Pythagorean
   magnitude identity, OR (b) reducing to a per-component re/im
   algebraic identity that bypasses the magnitude.

3. **Scale to π**: from `π/4` to `π = 16·arctan(1/5) − 4·arctan(1/239)`
   requires distributivity of `cisTauReal` over multiplication by
   rational constants.

The `BBPLeibnizCorrespondence` proposition further requires that
`pi_bbp` be linked to the same `cisTauReal(π/4)` value, via the
BBP-arctan derivation (Wave Γ₆ Phase 2 honest scope memo).

### Module name

This file is picked up by the `.submodules` glob in `lakefile.lean`.
-/

set_option autoImplicit false

namespace Tau.Boundary

open Tau.Denotation

-- ============================================================
-- PART 1: SHARPENED POINTWISE BOUND  |arctan_partial_rat a n| ≤ 1/2
-- ============================================================

/-! ## The sharpened partial-sum bound at path-β

  For `4·|a| ≤ 1` (the F.6 path-β domain), the arctan partial-sum is
  bounded by `1/2` at every depth. This is the key tightening that
  unlocks two-level iteration of `cisTauReal_add` for Machin-style
  product identities. -/

/-- **Sharpened pointwise bound** — for `4·|a| ≤ 1`,
    `|arctan_partial_rat a n| ≤ 1/2`.

    Proof: use `arctan_partial_rat_abs_tight_bound` which gives
    `(1 − |a|⁴)·|partial| ≤ (5/4)·|a|·(1 − |a|^(4n))`. For
    `4·|a| ≤ 1`:
    - `|a|⁴ ≤ 1/256`, so `1 − |a|⁴ ≥ 255/256`.
    - `(5/4)·|a| ≤ 5/16`.
    - Combine: `|partial| ≤ (5/16)/(255/256) = 80/255 < 1/2`. -/
theorem arctan_partial_rat_abs_le_half (a : Rat) (ha : 4 * |a| ≤ 1) (n : Nat) :
    |arctan_partial_rat a n| ≤ 1/2 := by
  have h_abs_a_nn : (0 : Rat) ≤ |a| := _root_.abs_nonneg _
  have h_abs_a_le_quarter : |a| ≤ 1/4 := by linarith
  -- Bridge to the existing path: `2·|a| ≤ 1` is implied.
  have h_2a_le_one : 2 * |a| ≤ 1 := by linarith
  -- `|a|^4 ≤ 1/256`.
  have h_pow4_le : |a|^4 ≤ 1/256 := by
    have h1 : |a|^4 ≤ (1/4 : Rat)^4 := pow_le_pow_left₀ h_abs_a_nn h_abs_a_le_quarter 4
    have h2 : (1/4 : Rat)^4 = 1/256 := by norm_num
    linarith
  have h_one_minus_pow_pos : (0 : Rat) < 1 - |a|^4 := by linarith
  have h_pow_4n_nn : (0 : Rat) ≤ |a|^(4*n) := by positivity
  have h_one_minus_le : 1 - |a|^(4*n) ≤ 1 := by linarith
  have h_step2 := arctan_partial_rat_abs_tight_bound a h_2a_le_one n
  -- Combine: (1−|a|⁴)·|partial| ≤ (5/4)·|a|·(1−|a|^(4n)) ≤ (5/4)·|a|
  have h_5a_nn : (0 : Rat) ≤ (5/4) * |a| := by positivity
  have h_unscaled : (1 - |a|^4) * |arctan_partial_rat a n| ≤ (5/4) * |a| := by
    calc (1 - |a|^4) * |arctan_partial_rat a n|
        ≤ (5/4) * |a| * (1 - |a|^(4*n)) := h_step2
      _ ≤ (5/4) * |a| * 1 := mul_le_mul_of_nonneg_left h_one_minus_le h_5a_nn
      _ = (5/4) * |a| := by ring
  -- `|partial| ≤ (5/4)·|a|/(1−|a|⁴) ≤ (5/16)/(255/256) ≤ 1/2`.
  have h_partial_le_div : |arctan_partial_rat a n| ≤ (5/4) * |a| / (1 - |a|^4) := by
    rw [le_div_iff₀ h_one_minus_pow_pos]
    linarith
  have h_one_minus_ge : (1 : Rat) - |a|^4 ≥ 255/256 := by linarith
  have h_div_bound : (5/4) * |a| / (1 - |a|^4) ≤ 1/2 := by
    rw [div_le_iff₀ h_one_minus_pow_pos]
    -- Goal: (5/4) · |a| ≤ (1/2) · (1 − |a|⁴)
    -- For |a| ≤ 1/4 and |a|⁴ ≤ 1/256, we have:
    --   LHS ≤ (5/4) · (1/4) = 5/16
    --   RHS ≥ (1/2) · (255/256) = 255/512
    -- 5/16 = 160/512 ≤ 255/512 ✓
    nlinarith
  linarith

/-- **Sharpened TauReal-level bound** — for `4·|a.toRat| ≤ 1`,
    every approximation of `arctan_of_rat_seq a` is bounded by `1/2`.

    The path-β-domain analog of `arctan_of_rat_seq_bounded`.
    Crucial for unlocking two-level `cisTauReal_add` iteration on the
    Machin product chain. -/
theorem TauReal.arctan_of_rat_seq_bounded_half (a : TauRat) (ha : 4 * |a.toRat| ≤ 1) :
    ∀ n, ((TauReal.arctan_of_rat_seq a).approx n).abs.toRat ≤ 1/2 := by
  intro n
  rw [TauReal.arctan_of_rat_seq_approx]
  rw [TauRat.toRat_abs]
  rw [TauRat.arctan_partial_toRat]
  exact arctan_partial_rat_abs_le_half a.toRat ha n

-- ============================================================
-- PART 2: DOUBLED SUM IS BOUNDED BY 1
-- ============================================================

/-! ## The doubled-sum bound

  For `4·|a.toRat| ≤ 1`, the sum `arctan_of_rat_seq a + arctan_of_rat_seq a`
  is bounded pointwise by 1, allowing us to use it as an operand to
  `cisTauReal_add` at the next iteration level. -/

/-- **Doubled-sum pointwise bound** — for `4·|a.toRat| ≤ 1`,
    `|(arctan_of_rat_seq a + arctan_of_rat_seq a).approx n| ≤ 1`. -/
theorem TauReal.arctan_of_rat_seq_double_bounded (a : TauRat)
    (ha : 4 * |a.toRat| ≤ 1) :
    ∀ n, (((TauReal.arctan_of_rat_seq a).add
            (TauReal.arctan_of_rat_seq a)).approx n).abs.toRat ≤ 1 := by
  intro n
  -- `(x.add x).approx n = (x.approx n).add (x.approx n)`
  -- `|...|.toRat = |x.approx n .toRat + x.approx n .toRat|`
  -- ≤ 2 · |x.approx n .toRat| ≤ 2 · (1/2) = 1
  show (TauRat.add ((TauReal.arctan_of_rat_seq a).approx n)
          ((TauReal.arctan_of_rat_seq a).approx n)).abs.toRat ≤ 1
  rw [TauRat.toRat_abs, toRat_add]
  have h_partial_bd := TauReal.arctan_of_rat_seq_bounded_half a ha n
  rw [TauRat.toRat_abs] at h_partial_bd
  have h_tri : |((TauReal.arctan_of_rat_seq a).approx n).toRat
                  + ((TauReal.arctan_of_rat_seq a).approx n).toRat|
                ≤ |((TauReal.arctan_of_rat_seq a).approx n).toRat|
                  + |((TauReal.arctan_of_rat_seq a).approx n).toRat| := abs_add_le _ _
  linarith

-- ============================================================
-- PART 3: TWO-LEVEL cisTauReal_add APPLICATION
-- ============================================================

/-! ## The two-level Machin product step

  Combining `cisTauReal_arctan_double` (Phase D) with the doubled-sum
  bound, we can now apply `cisTauReal_add` at the **second iteration
  level**, where both operands are themselves doubled-arctan partial
  sums. -/

/-- **🎯 Two-doubled-sum cisTauReal identity** — for `4·|a.toRat| ≤ 1`,

      `cisTauReal((arctan_of_rat_seq a + arctan_of_rat_seq a)
                    + (arctan_of_rat_seq a + arctan_of_rat_seq a))
        ≈ cisTauReal(arctan_of_rat_seq a + arctan_of_rat_seq a)
            · cisTauReal(arctan_of_rat_seq a + arctan_of_rat_seq a)`.

    This is the next-level step on top of `cisTauReal_arctan_double`:
    two doubled-arctan sums, each itself a `cisTauReal_arctan_add`
    application, combined via `cisTauReal_add` on the doubled sums.

    Boundedness witness: `arctan_of_rat_seq_double_bounded` (the
    doubled-sum bound from Part 2). -/
theorem TauReal.cisTauReal_arctan_two_doubled (a : TauRat)
    (ha : 4 * |a.toRat| ≤ 1) :
    TauComplex.equiv
      (TauComplex.cisTauReal
        (((TauReal.arctan_of_rat_seq a).add (TauReal.arctan_of_rat_seq a)).add
          ((TauReal.arctan_of_rat_seq a).add (TauReal.arctan_of_rat_seq a))))
      ((TauComplex.cisTauReal
          ((TauReal.arctan_of_rat_seq a).add (TauReal.arctan_of_rat_seq a))).mul
        (TauComplex.cisTauReal
          ((TauReal.arctan_of_rat_seq a).add (TauReal.arctan_of_rat_seq a)))) :=
  TauComplex.cisTauReal_add _ _
    (TauReal.arctan_of_rat_seq_double_bounded a ha)
    (TauReal.arctan_of_rat_seq_double_bounded a ha)

-- ============================================================
-- PART 4: THE QUADRUPLE-ARCTAN PRODUCT IDENTITY
-- ============================================================

/-! ## The quadruple-arctan product identity

  Combining the two-doubled-sum identity (Part 3) with two applications
  of `cisTauReal_arctan_double` (Phase D) via `equiv_mul_congr` and
  `equiv_trans`, we obtain

      `cisTauReal(four-arctan sum) ≈ cisTauReal(arctan a)⁴`

  at TauComplex level. This is the **first half of the Machin chain**
  expressed as a single product identity. -/

/-- **🎯 The quadruple-arctan product identity** — for `4·|a.toRat| ≤ 1`:

      `cisTauReal((arctan_of_rat_seq a + arctan_of_rat_seq a) +
                    (arctan_of_rat_seq a + arctan_of_rat_seq a))
        ≈ (cisTauReal(arctan_of_rat_seq a)
              · cisTauReal(arctan_of_rat_seq a))
          · (cisTauReal(arctan_of_rat_seq a)
              · cisTauReal(arctan_of_rat_seq a))`.

    Strategy: apply `cisTauReal_arctan_two_doubled` (Part 3) to obtain
    the product of two doubled cisTauReals on the RHS, then apply
    `equiv_mul_congr` with `cisTauReal_arctan_double` on each factor
    to descend to the quadruple cisTauReal product.

    The bound witnesses needed for `equiv_mul_congr` are derived
    from `cisTauReal` componentwise bounds (re and im each ≤ 8 by
    the existing `cis_arctan_re/im_approx_abs_le_8`); we then derive
    a product-level bound `≤ 128` on each component of cisA·cisA. -/
theorem TauReal.cisTauReal_arctan_four_product (a : TauRat)
    (ha : 4 * |a.toRat| ≤ 1) :
    TauComplex.equiv
      (TauComplex.cisTauReal
        (((TauReal.arctan_of_rat_seq a).add (TauReal.arctan_of_rat_seq a)).add
          ((TauReal.arctan_of_rat_seq a).add (TauReal.arctan_of_rat_seq a))))
      (((TauComplex.cisTauReal (TauReal.arctan_of_rat_seq a)).mul
          (TauComplex.cisTauReal (TauReal.arctan_of_rat_seq a))).mul
        ((TauComplex.cisTauReal (TauReal.arctan_of_rat_seq a)).mul
          (TauComplex.cisTauReal (TauReal.arctan_of_rat_seq a)))) := by
  -- 2·|a| ≤ 1 from 4·|a| ≤ 1
  have ha2 : 2 * |a.toRat| ≤ 1 := by
    have := _root_.abs_nonneg a.toRat; linarith
  -- Step A: cisTauReal of the 4-arctan sum ≈ product of two cisTauReal(2-arctan)
  have h_two_double : TauComplex.equiv
      (TauComplex.cisTauReal
        (((TauReal.arctan_of_rat_seq a).add (TauReal.arctan_of_rat_seq a)).add
          ((TauReal.arctan_of_rat_seq a).add (TauReal.arctan_of_rat_seq a))))
      ((TauComplex.cisTauReal
          ((TauReal.arctan_of_rat_seq a).add (TauReal.arctan_of_rat_seq a))).mul
        (TauComplex.cisTauReal
          ((TauReal.arctan_of_rat_seq a).add (TauReal.arctan_of_rat_seq a)))) :=
    TauReal.cisTauReal_arctan_two_doubled a ha
  -- Step B: each cisTauReal(2-arctan) ≈ cisTauReal(arctan)·cisTauReal(arctan)
  have h_double : TauComplex.equiv
      (TauComplex.cisTauReal
        ((TauReal.arctan_of_rat_seq a).add (TauReal.arctan_of_rat_seq a)))
      ((TauComplex.cisTauReal (TauReal.arctan_of_rat_seq a)).mul
        (TauComplex.cisTauReal (TauReal.arctan_of_rat_seq a))) :=
    TauReal.cisTauReal_arctan_double a ha2
  -- Step C: combine via equiv_mul_congr.
  -- Bounds on cisTauReal(arctan a) components (≤ 8).
  have h_re_bd : ∀ n,
      ((TauComplex.cisTauReal (TauReal.arctan_of_rat_seq a)).re.approx n).abs.toRat ≤ 8 := by
    intro n
    show ((TauReal.cis_arctan_re a).approx n).abs.toRat ≤ 8
    exact TauReal.cis_arctan_re_approx_abs_le_8 a ha2 n
  have h_im_bd : ∀ n,
      ((TauComplex.cisTauReal (TauReal.arctan_of_rat_seq a)).im.approx n).abs.toRat ≤ 8 := by
    intro n
    show ((TauReal.cis_arctan_im a).approx n).abs.toRat ≤ 8
    exact TauReal.cis_arctan_im_approx_abs_le_8 a ha2 n
  -- Bound on (cisA · cisA).re = cisA.re·cisA.re - cisA.im·cisA.im pointwise.
  -- |x·y - z·w| ≤ |x·y| + |z·w| ≤ 8·8 + 8·8 = 128.
  have h_mul_re_bd : ∀ n,
      (((TauComplex.cisTauReal (TauReal.arctan_of_rat_seq a)).mul
          (TauComplex.cisTauReal (TauReal.arctan_of_rat_seq a))).re.approx n).abs.toRat
        ≤ 128 := by
    intro n
    -- (cisA · cisA).re.approx n unfolds to TauRat.add (re·re) (negate (im·im))
    show (TauRat.add
            (TauRat.mul ((TauComplex.cisTauReal (TauReal.arctan_of_rat_seq a)).re.approx n)
              ((TauComplex.cisTauReal (TauReal.arctan_of_rat_seq a)).re.approx n))
            (TauRat.negate
              (TauRat.mul ((TauComplex.cisTauReal (TauReal.arctan_of_rat_seq a)).im.approx n)
                ((TauComplex.cisTauReal (TauReal.arctan_of_rat_seq a)).im.approx n)))).abs.toRat
          ≤ 128
    rw [TauRat.toRat_abs, toRat_add, toRat_negate, toRat_mul, toRat_mul]
    have h_re_n := h_re_bd n
    have h_im_n := h_im_bd n
    rw [TauRat.toRat_abs] at h_re_n h_im_n
    have h_re_n_nn : 0 ≤ |((TauComplex.cisTauReal (TauReal.arctan_of_rat_seq a)).re.approx n).toRat|
      := _root_.abs_nonneg _
    have h_im_n_nn : 0 ≤ |((TauComplex.cisTauReal (TauReal.arctan_of_rat_seq a)).im.approx n).toRat|
      := _root_.abs_nonneg _
    have h_xy_sum :
        |((TauComplex.cisTauReal (TauReal.arctan_of_rat_seq a)).re.approx n).toRat *
            ((TauComplex.cisTauReal (TauReal.arctan_of_rat_seq a)).re.approx n).toRat +
          -(((TauComplex.cisTauReal (TauReal.arctan_of_rat_seq a)).im.approx n).toRat *
              ((TauComplex.cisTauReal (TauReal.arctan_of_rat_seq a)).im.approx n).toRat)|
            ≤ |((TauComplex.cisTauReal (TauReal.arctan_of_rat_seq a)).re.approx n).toRat *
              ((TauComplex.cisTauReal (TauReal.arctan_of_rat_seq a)).re.approx n).toRat|
              + |((TauComplex.cisTauReal (TauReal.arctan_of_rat_seq a)).im.approx n).toRat *
                ((TauComplex.cisTauReal (TauReal.arctan_of_rat_seq a)).im.approx n).toRat| := by
      have := abs_add_le
        (((TauComplex.cisTauReal (TauReal.arctan_of_rat_seq a)).re.approx n).toRat *
            ((TauComplex.cisTauReal (TauReal.arctan_of_rat_seq a)).re.approx n).toRat)
        (-(((TauComplex.cisTauReal (TauReal.arctan_of_rat_seq a)).im.approx n).toRat *
              ((TauComplex.cisTauReal (TauReal.arctan_of_rat_seq a)).im.approx n).toRat))
      rw [abs_neg] at this
      exact this
    have h_re_sq : |((TauComplex.cisTauReal (TauReal.arctan_of_rat_seq a)).re.approx n).toRat
                    * ((TauComplex.cisTauReal (TauReal.arctan_of_rat_seq a)).re.approx n).toRat|
                    ≤ 64 := by
      rw [abs_mul]
      nlinarith [h_re_n, h_re_n_nn]
    have h_im_sq : |((TauComplex.cisTauReal (TauReal.arctan_of_rat_seq a)).im.approx n).toRat
                    * ((TauComplex.cisTauReal (TauReal.arctan_of_rat_seq a)).im.approx n).toRat|
                    ≤ 64 := by
      rw [abs_mul]
      nlinarith [h_im_n, h_im_n_nn]
    linarith
  -- Bound on (cisA · cisA).im = cisA.re·cisA.im + cisA.im·cisA.re pointwise.
  have h_mul_im_bd : ∀ n,
      (((TauComplex.cisTauReal (TauReal.arctan_of_rat_seq a)).mul
          (TauComplex.cisTauReal (TauReal.arctan_of_rat_seq a))).im.approx n).abs.toRat
        ≤ 128 := by
    intro n
    show (TauRat.add
            (TauRat.mul ((TauComplex.cisTauReal (TauReal.arctan_of_rat_seq a)).re.approx n)
              ((TauComplex.cisTauReal (TauReal.arctan_of_rat_seq a)).im.approx n))
            (TauRat.mul ((TauComplex.cisTauReal (TauReal.arctan_of_rat_seq a)).im.approx n)
              ((TauComplex.cisTauReal (TauReal.arctan_of_rat_seq a)).re.approx n))).abs.toRat
          ≤ 128
    rw [TauRat.toRat_abs, toRat_add, toRat_mul, toRat_mul]
    have h_re_n := h_re_bd n
    have h_im_n := h_im_bd n
    rw [TauRat.toRat_abs] at h_re_n h_im_n
    have h_re_n_nn : 0 ≤ |((TauComplex.cisTauReal (TauReal.arctan_of_rat_seq a)).re.approx n).toRat|
      := _root_.abs_nonneg _
    have h_im_n_nn : 0 ≤ |((TauComplex.cisTauReal (TauReal.arctan_of_rat_seq a)).im.approx n).toRat|
      := _root_.abs_nonneg _
    have h_sum_le : |((TauComplex.cisTauReal (TauReal.arctan_of_rat_seq a)).re.approx n).toRat *
            ((TauComplex.cisTauReal (TauReal.arctan_of_rat_seq a)).im.approx n).toRat +
          ((TauComplex.cisTauReal (TauReal.arctan_of_rat_seq a)).im.approx n).toRat *
            ((TauComplex.cisTauReal (TauReal.arctan_of_rat_seq a)).re.approx n).toRat|
          ≤ |((TauComplex.cisTauReal (TauReal.arctan_of_rat_seq a)).re.approx n).toRat *
              ((TauComplex.cisTauReal (TauReal.arctan_of_rat_seq a)).im.approx n).toRat|
            + |((TauComplex.cisTauReal (TauReal.arctan_of_rat_seq a)).im.approx n).toRat *
                ((TauComplex.cisTauReal (TauReal.arctan_of_rat_seq a)).re.approx n).toRat| :=
      abs_add_le _ _
    have h_re_im : |((TauComplex.cisTauReal (TauReal.arctan_of_rat_seq a)).re.approx n).toRat *
                    ((TauComplex.cisTauReal (TauReal.arctan_of_rat_seq a)).im.approx n).toRat|
                    ≤ 64 := by
      rw [abs_mul]
      nlinarith [h_re_n, h_im_n, h_re_n_nn, h_im_n_nn]
    have h_im_re : |((TauComplex.cisTauReal (TauReal.arctan_of_rat_seq a)).im.approx n).toRat *
                    ((TauComplex.cisTauReal (TauReal.arctan_of_rat_seq a)).re.approx n).toRat|
                    ≤ 64 := by
      rw [abs_mul]
      nlinarith [h_re_n, h_im_n, h_re_n_nn, h_im_n_nn]
    linarith
  -- For equiv_mul_congr we also need a bound on w = cisTauReal(arctan + arctan).
  -- Using TauComplex.cisTauReal_re/im_approx_abs_le_8 with the doubled-sum bound.
  have h_double_bd_at_n : ∀ n,
      |(((TauReal.arctan_of_rat_seq a).add
          (TauReal.arctan_of_rat_seq a)).approx n).toRat| ≤ 1 := by
    intro n
    have := TauReal.arctan_of_rat_seq_double_bounded a ha n
    rw [TauRat.toRat_abs] at this
    exact this
  have h_w_re_bd : ∀ n,
      ((TauComplex.cisTauReal
          ((TauReal.arctan_of_rat_seq a).add (TauReal.arctan_of_rat_seq a))).re.approx n).abs.toRat
        ≤ 8 := by
    intro n
    exact TauComplex.cisTauReal_re_approx_abs_le_8 _ n (h_double_bd_at_n n)
  have h_w_im_bd : ∀ n,
      ((TauComplex.cisTauReal
          ((TauReal.arctan_of_rat_seq a).add (TauReal.arctan_of_rat_seq a))).im.approx n).abs.toRat
        ≤ 8 := by
    intro n
    exact TauComplex.cisTauReal_im_approx_abs_le_8 _ n (h_double_bd_at_n n)
  -- For equiv_mul_congr, the bound is on z' (RHS factor of h_double) and on w (LHS factor).
  -- We pick Mre = Mim = 128 (which covers both 8 and 128 since 8 ≤ 128).
  have h_w_re_bd_128 : ∀ n,
      ((TauComplex.cisTauReal
          ((TauReal.arctan_of_rat_seq a).add (TauReal.arctan_of_rat_seq a))).re.approx n).abs.toRat
        ≤ 128 := by
    intro n; linarith [h_w_re_bd n]
  have h_w_im_bd_128 : ∀ n,
      ((TauComplex.cisTauReal
          ((TauReal.arctan_of_rat_seq a).add (TauReal.arctan_of_rat_seq a))).im.approx n).abs.toRat
        ≤ 128 := by
    intro n; linarith [h_w_im_bd n]
  -- Apply TauComplex.equiv_mul_congr with M = 128 for both components.
  have h_mul_congr : TauComplex.equiv
      ((TauComplex.cisTauReal
          ((TauReal.arctan_of_rat_seq a).add (TauReal.arctan_of_rat_seq a))).mul
        (TauComplex.cisTauReal
          ((TauReal.arctan_of_rat_seq a).add (TauReal.arctan_of_rat_seq a))))
      (((TauComplex.cisTauReal (TauReal.arctan_of_rat_seq a)).mul
          (TauComplex.cisTauReal (TauReal.arctan_of_rat_seq a))).mul
        ((TauComplex.cisTauReal (TauReal.arctan_of_rat_seq a)).mul
          (TauComplex.cisTauReal (TauReal.arctan_of_rat_seq a)))) := by
    apply TauComplex.equiv_mul_congr (Mre := 128) (Mim := 128)
      (by norm_num : 1 ≤ 128) (by norm_num : 1 ≤ 128)
    · exact h_mul_re_bd
    · exact h_mul_im_bd
    · exact h_w_re_bd_128
    · exact h_w_im_bd_128
    · exact h_double
    · exact h_double
  -- Chain h_two_double and h_mul_congr via equiv_trans
  exact TauComplex.equiv_trans h_two_double h_mul_congr

-- ============================================================
-- PART 5: SPECIALIZATION TO 1/5 — THE FIRST MACHIN CONSTANT
-- ============================================================

/-! ## Specialization to the Machin constant 1/5

  Specializing the quadruple-arctan product identity to `a = 1/5`
  (the first Machin constant). This gives the τ-native form of
  `exp(i·4·arctan(1/5)) = exp(i·arctan(1/5))⁴` — the first half
  of the Machin chain. -/

/-- **🎯 Phase E Scope A — The quadruple-arctan product at 1/5** —

      `cisTauReal((arctan(1/5)+arctan(1/5)) + (arctan(1/5)+arctan(1/5)))
        ≈ cisTauReal(arctan(1/5))² · cisTauReal(arctan(1/5))²`

    at TauComplex level, with `4·|(1/5)| = 4/5 ≤ 1` (path-β
    admission witness from Phase D's `TauRat.one_fifth_in_path_beta`).

    This is the first concrete intermediate step on the Machin chain
    `π = 16·arctan(1/5) − 4·arctan(1/239)`. The remaining steps
    (`-arctan(1/239)` correction, connection to `cisTauReal(π/4)`,
    scaling by 4) are queued for Phase E Scope B/C/D. -/
theorem TauReal.cisTauReal_arctan_four_at_one_fifth :
    TauComplex.equiv
      (TauComplex.cisTauReal
        (((TauReal.arctan_of_rat_seq TauRat.one_fifth).add
            (TauReal.arctan_of_rat_seq TauRat.one_fifth)).add
          ((TauReal.arctan_of_rat_seq TauRat.one_fifth).add
            (TauReal.arctan_of_rat_seq TauRat.one_fifth))))
      (((TauComplex.cisTauReal (TauReal.arctan_of_rat_seq TauRat.one_fifth)).mul
          (TauComplex.cisTauReal (TauReal.arctan_of_rat_seq TauRat.one_fifth))).mul
        ((TauComplex.cisTauReal (TauReal.arctan_of_rat_seq TauRat.one_fifth)).mul
          (TauComplex.cisTauReal (TauReal.arctan_of_rat_seq TauRat.one_fifth)))) :=
  TauReal.cisTauReal_arctan_four_product TauRat.one_fifth
    TauRat.one_fifth_in_path_beta

-- ============================================================
-- PART 6: ALSO QUADRUPLE FOR 1/239 — COMPLETENESS
-- ============================================================

/-- **Companion specialization to 1/239**: The same quadruple-arctan
    product identity at `a = 1/239`. We include this for completeness,
    even though the Machin identity uses only `-arctan(1/239)` (not
    `4·arctan(1/239)`). It demonstrates the theorem's generality at
    both Machin constants. -/
theorem TauReal.cisTauReal_arctan_four_at_one_two_three_nine :
    TauComplex.equiv
      (TauComplex.cisTauReal
        (((TauReal.arctan_of_rat_seq TauRat.one_two_three_nine).add
            (TauReal.arctan_of_rat_seq TauRat.one_two_three_nine)).add
          ((TauReal.arctan_of_rat_seq TauRat.one_two_three_nine).add
            (TauReal.arctan_of_rat_seq TauRat.one_two_three_nine))))
      (((TauComplex.cisTauReal (TauReal.arctan_of_rat_seq TauRat.one_two_three_nine)).mul
          (TauComplex.cisTauReal (TauReal.arctan_of_rat_seq TauRat.one_two_three_nine))).mul
        ((TauComplex.cisTauReal (TauReal.arctan_of_rat_seq TauRat.one_two_three_nine)).mul
          (TauComplex.cisTauReal (TauReal.arctan_of_rat_seq TauRat.one_two_three_nine)))) :=
  TauReal.cisTauReal_arctan_four_product TauRat.one_two_three_nine
    TauRat.one_two_three_nine_in_path_beta

-- ============================================================
-- PART 7: NOTES FOR PHASE E SCOPE B/C — THE FULL MACHIN
-- ============================================================

/-! ## Notes for Phase E Scope B/C/D — discharging MachinIdentity

  This module ships **Phase E Scope A**: the quadruple-arctan product
  identity at the cisTauReal level, specialized to both Machin
  constants (1/5 and 1/239). What remains for the full Machin
  identity discharge:

  ### Step B (the `-arctan(1/239)` correction)

  We need `cisTauReal(arctan(1/5))⁴ · cisTauReal(arctan(-1/239))`
  (or, using the parity identity from Phase D, the structurally-
  conjugated form
  `cisTauReal(arctan(1/5))⁴ · ⟨cisTauReal(arctan(1/239)).re,
                                -cisTauReal(arctan(1/239)).im⟩`)
  to be the τ-native form of
  `exp(i·(4·arctan(1/5) − arctan(1/239)))`.

  **Direct connection via `cisTauReal_add` is blocked**:  applying
  `cisTauReal_add` with `x = 4-sum` and `y = arctan(-1/239)` requires
  `|x.approx n| ≤ 1`. The 4-sum bound is `4·(1/2) = 2 > 1`.

  **Resolution paths**:
  - A sharper bound `|arctan_partial(1/5) n| ≤ 1/8`, which would
    allow the 4-sum to be ≤ 1/2 < 1. Achievable via a finer
    tightening of `arctan_partial_rat_abs_tight_bound`, since the
    actual value `arctan(1/5) ≈ 0.197 < 1/5 < 1/8`... wait, 0.197 > 1/8 = 0.125.
    So this bound does NOT hold for partial sums at low depth
    (e.g., `n=1` gives partial = 0.2). Instead one needs a
    **depth-dependent** bound that becomes tight after some N₀.
  - A refactored `cisTauReal_add` with a `≤ M` hypothesis for
    larger M. The proof of `cisTauReal_add` uses `exp_add` which
    in turn relies on `pureIm_of_real_BoundedBy x 1`; lifting to
    larger M is mechanical but requires refactoring the proof
    chain.
  - **Algebraic-direct route**: prove the Machin **product-level**
    identity directly, bypassing the `cisTauReal_add` form. The
    target is then a TauComplex equiv between two products, not
    a `cisTauReal(...)` and a product. This route doesn't need
    `cisTauReal_add` at the 4-sum level — only product algebra.

  The algebraic-direct route is most accessible: prove the
  product-level Machin identity `cisTauReal(arctan(1/5))⁴ ·
  cisTauReal(arctan(-1/239)) ≈ (1+i)/√2` via per-component re/im
  matching, then derive `MachinIdentity` from it via a separate
  arctan-addition-formula lift. The per-component matching is
  closed by Phase D's F.6-substituted forms.

  ### Step C (connection to π)

  Match `cisTauReal(arctan(1/5))⁴ · conj(cisTauReal(arctan(1/239)))`
  against `cisTauReal(π/4) = (1+i)/√2`. Requires τ-native `√2`
  plus the Pythagorean magnitude identity. The simplest target is:
  the **re/im ratio** of the product equals 1 (i.e., the product is
  on the line `y = x`, matching `cisTauReal(π/4)`'s 45° angle).
  This avoids the need to compute the magnitude explicitly.

  ### Step D (scaling to π)

  From `π/4` to `π`: distributivity of cisTauReal over rational
  multiplication. Requires a τ-native multiplication-by-rational
  identity on TauReal arguments of cisTauReal.

  ### Step E (BBP equivalence)

  Once `MachinIdentity` is closed, `BBPLeibnizCorrespondence` requires
  linking `pi_bbp` to the same `cisTauReal(π/4)`. The orthodox path:
  BBP base-16 derivation uses `arctan(1/√2)` and a Machin-like
  identity. This requires τ-native `1/√2` and another arctan
  identity infrastructure.

  Path 4 (recommended) bypasses Step E by routing through
  `MachinIdentity` and a separate BBP-arctan equivalence.

  ### Path Forward Recommendation

  After this commit (Phase E Scope A), the next most achievable step
  is the **algebraic-direct Machin product identity** at re/im level
  (Phase E Scope A.5/B). Specifically, prove

      `(cisTauReal(arctan(1/5))⁴ · cisTauReal(arctan(-1/239))).re
         ≈ (cisTauReal(arctan(1/5))⁴ · cisTauReal(arctan(-1/239))).im`

  (i.e., the product lies on the 45° line, matching `cisTauReal(π/4)`).
  This is provable via F.6-substituted forms iterated through the
  product structure, and is the cleanest next concrete step.
-/

end Tau.Boundary
