import TauLib.BookI.Boundary.TauRealArctanAdd
import Mathlib.Tactic.Ring
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity

/-!
# TauLib.BookI.Boundary.TauRealMachin

**Phase D / Machin's identity at the cisTauReal level — building blocks**.

After Phase B/C closed (cisTauReal multiplicativity at arctan-image angles,
plus F.6-substituted re/im decompositions), this module ships the first
building blocks for Machin's classical identity

> **π/4 = 4·arctan(1/5) − arctan(1/239)**,

formulated τ-natively as a chain of `cisTauReal` identities.

### Scope (honest)

Machin's identity at the **full angle level** would require:
- arctan injectivity on the principal branch, OR
- a `cisTauReal(π) ≈ −1` identity at TauReal-equiv level.

Neither is shipped (Phase E concerns). What we ship here is the
**cisTauReal-multiplicativity scaffolding** at the rational constants
that appear in Machin's chain (1/5, 1/239) plus the doubling identity
on the arctan image.

### Mathematical background — the Machin chain

The classical Machin chain (using the arctan addition formula
`arctan(a) + arctan(b) = arctan((a+b)/(1−ab))`) goes:

1. `2·arctan(1/5) = arctan(5/12)`  (since `(2/5)/(1−1/25) = (2/5)·(25/24) = 5/12`)
2. `4·arctan(1/5) = arctan(120/119)`  (iterate: `(10/12)/(1−25/144) = 120/119`)
3. `arctan(120/119) − arctan(1/239) = arctan(1)`  (since
   `(120/119 − 1/239)/(1 + 120/(119·239)) = 28561/28561 = 1`)
4. Combining: `4·arctan(1/5) − arctan(1/239) = arctan(1) = π/4`.
5. Multiplying by 4: `16·arctan(1/5) − 4·arctan(1/239) = π`.

### Domain constraint

The F.6 path-β domain `4·|a| ≤ 1` is satisfied at:
- `a = 1/5`     (`4/5 ≤ 1` ✓)
- `a = 1/239`   (`4/239 ≪ 1` ✓)

But **fails** at:
- `a = 5/12`    (`4·(5/12) = 5/3 > 1`)
- `a = 120/119` (`4·(120/119) ≈ 4.03 > 1`)
- `a = 1`       (`4 > 1`)

This means we **cannot** apply F.6 directly at `arctan(5/12)`, `arctan(120/119)`,
or `arctan(1)`. The intermediate steps of the Machin chain therefore
require additional infrastructure beyond what Phases B/C ship.

### What we ship in this module

* **TauRat constants for the Machin chain** — `1/5`, `1/239`, `5/12`,
  `120/119`, `1` — with `.toRat` simp lemmas.
* **Verification of the F.6 domain admission for `1/5` and `1/239`**.
* **`cisTauReal_arctan_double`** — `cisTauReal(arctan a + arctan a) ≈
  cisTauReal(arctan a)²` (specialization of Phase C with `b := a`).
* **`cisTauReal_arctan_double_re/im_equiv_F6_form`** — re/im decomposition
  with `a = b` substituted into Phase C's F.6 form.
* **`cisTauReal_arctan_neg`** — the parity identity for `cisTauReal` of
  `arctan(−a)` at the structural level.
* **The `MachinIdentity` proposition** — named target for the full
  Machin identity at TauReal-equiv level (a Phase E concern).

### What is queued for Phase E

1. **cisTauReal-multiplicativity at angles whose `cisTauReal` is NOT in
   the arctan-image**: for `arctan(5/12)`, the angle lies outside the
   path-β domain, so Phase C's congruence chain doesn't apply directly.
   Future infrastructure: extend the F.6 substitution to angles obtained
   as sums of path-β angles (via the multiplicativity).
2. **Connecting cisTauReal(π/4) ≈ (1+i)/√2 to the Leibniz partial sum**.
   The Leibniz-pair series `TauReal.pi` doesn't admit a direct cisTauReal
   reading without further work.

## Module name

This file is picked up by the `.submodules` glob in `lakefile.lean`.
-/

set_option autoImplicit false

namespace Tau.Boundary

open Tau.Denotation

-- ============================================================
-- PART 1: TauRat CONSTANTS FOR THE MACHIN CHAIN
-- ============================================================

/-! ## TauRat constants for the Machin identity

  The five rationals appearing in the Machin chain. Each is a TauRat with
  an associated `.toRat` simp lemma giving its rational value.

  Encoded via the `⟨⟨num_pos, num_neg⟩, den, den_pos⟩` form. -/

/-- The TauRat constant `1/5`. -/
def TauRat.one_fifth : TauRat := ⟨⟨1, 0⟩, 5, by norm_num⟩

/-- The TauRat constant `1/239`. -/
def TauRat.one_two_three_nine : TauRat := ⟨⟨1, 0⟩, 239, by norm_num⟩

/-- The TauRat constant `5/12`. (Outside F.6 path-β; documented for the
    Machin chain narrative.) -/
def TauRat.five_twelfths : TauRat := ⟨⟨5, 0⟩, 12, by norm_num⟩

/-- The TauRat constant `120/119`. (Outside F.6 path-β; documented for the
    Machin chain narrative.) -/
def TauRat.one_twenty_over_119 : TauRat := ⟨⟨120, 0⟩, 119, by norm_num⟩

/-- The TauRat constant `1/1` (`= 1`). Note: this is `TauRat.one` definitionally.
    (Outside F.6 path-β; documented for the Machin chain narrative.) -/
def TauRat.one_canonical : TauRat := TauRat.one

@[simp] theorem TauRat.one_fifth_toRat : TauRat.one_fifth.toRat = 1 / 5 := by
  unfold TauRat.one_fifth TauRat.toRat
  simp only [TauInt.toInt]
  push_cast
  ring

@[simp] theorem TauRat.one_two_three_nine_toRat :
    TauRat.one_two_three_nine.toRat = 1 / 239 := by
  unfold TauRat.one_two_three_nine TauRat.toRat
  simp only [TauInt.toInt]
  push_cast
  ring

@[simp] theorem TauRat.five_twelfths_toRat : TauRat.five_twelfths.toRat = 5 / 12 := by
  unfold TauRat.five_twelfths TauRat.toRat
  simp only [TauInt.toInt]
  push_cast
  ring

@[simp] theorem TauRat.one_twenty_over_119_toRat :
    TauRat.one_twenty_over_119.toRat = 120 / 119 := by
  unfold TauRat.one_twenty_over_119 TauRat.toRat
  simp only [TauInt.toInt]
  push_cast
  ring

@[simp] theorem TauRat.one_canonical_toRat : TauRat.one_canonical.toRat = 1 := by
  unfold TauRat.one_canonical
  exact toRat_one

-- ============================================================
-- PART 2: F.6 PATH-β DOMAIN MEMBERSHIP FOR MACHIN CONSTANTS
-- ============================================================

/-! ## F.6 path-β admission for `1/5` and `1/239`

  Both `1/5` and `1/239` satisfy `4·|a| ≤ 1`, hence they are in F.6's
  path-β domain. This means we can apply
  `cisTauReal_tangent_target_A_path_beta` at these constants directly. -/

/-- `4·|(1/5)| ≤ 1`. -/
theorem TauRat.one_fifth_in_path_beta : 4 * |TauRat.one_fifth.toRat| ≤ 1 := by
  rw [TauRat.one_fifth_toRat]
  rw [show |((1 : Rat) / 5)| = 1/5 from abs_of_pos (by norm_num)]
  norm_num

/-- `4·|(1/239)| ≤ 1`. -/
theorem TauRat.one_two_three_nine_in_path_beta :
    4 * |TauRat.one_two_three_nine.toRat| ≤ 1 := by
  rw [TauRat.one_two_three_nine_toRat]
  rw [show |((1 : Rat) / 239)| = 1/239 from abs_of_pos (by norm_num)]
  norm_num

/-- `2·|(1/5)| ≤ 1`. (Phase C arctan-addition prerequisite.) -/
theorem TauRat.one_fifth_in_arctan_add_domain :
    2 * |TauRat.one_fifth.toRat| ≤ 1 := by
  have := TauRat.one_fifth_in_path_beta
  have := _root_.abs_nonneg TauRat.one_fifth.toRat
  linarith

/-- `2·|(1/239)| ≤ 1`. (Phase C arctan-addition prerequisite.) -/
theorem TauRat.one_two_three_nine_in_arctan_add_domain :
    2 * |TauRat.one_two_three_nine.toRat| ≤ 1 := by
  have := TauRat.one_two_three_nine_in_path_beta
  have := _root_.abs_nonneg TauRat.one_two_three_nine.toRat
  linarith

-- ============================================================
-- PART 3: cisTauReal_arctan_double — THE DOUBLING IDENTITY
-- ============================================================

/-! ## The arctan doubling identity at the cisTauReal level

  Specialization of Phase C's `cisTauReal_arctan_add` to `b := a`:

      cisTauReal(arctan a + arctan a) ≈ cisTauReal(arctan a) · cisTauReal(arctan a)

  This is the first step toward `4·arctan(1/5)` in the Machin chain:
  iterate this identity twice to obtain `arctan(1/5)^4` at the cisTauReal
  level.
-/

/-- **🎯 cisTauReal_arctan_double** — the multiplicativity of `cisTauReal`
    on the doubled arctan-image angle. For `2·|a.toRat| ≤ 1`:

        `cisTauReal (arctan a + arctan a) ≈ cisTauReal(arctan a) · cisTauReal(arctan a)`.

    Direct application of `cisTauReal_arctan_add` with `b := a`. -/
theorem TauReal.cisTauReal_arctan_double (a : TauRat)
    (ha : 2 * |a.toRat| ≤ 1) :
    TauComplex.equiv
      (TauComplex.cisTauReal
        ((TauReal.arctan_of_rat_seq a).add (TauReal.arctan_of_rat_seq a)))
      ((TauComplex.cisTauReal (TauReal.arctan_of_rat_seq a)).mul
        (TauComplex.cisTauReal (TauReal.arctan_of_rat_seq a))) :=
  TauReal.cisTauReal_arctan_add a a ha ha

-- ============================================================
-- PART 4: STRUCTURAL re/im DECOMPOSITION OF THE DOUBLED ANGLE
-- ============================================================

/-! ## Structural re/im decomposition for the doubled angle

  Specializing Phase C's `cisTauReal_arctan_mul_re/im_eq` to `b := a`:

      (cisTauReal(arctan a) · cisTauReal(arctan a)).re
          = cisA.re · cisA.re − cisA.im · cisA.im
          = (cisA.re)² − (cisA.im)²

      (cisTauReal(arctan a) · cisTauReal(arctan a)).im
          = cisA.re · cisA.im + cisA.im · cisA.re
          = 2 · cisA.re · cisA.im

  This is the classical double-angle formula `cos(2α) = cos²α − sin²α` and
  `sin(2α) = 2·sin α · cos α`, instantiated at `α = arctan a`. -/

/-- **Structural re-decomposition** of the cisTauReal square:

        `(cisTauReal(arctan a) · cisTauReal(arctan a)).re
           = cis_arctan_re a · cis_arctan_re a − cis_arctan_im a · cis_arctan_im a`.

    Definitional equality at the `.re` field of `TauComplex.mul`. -/
theorem TauReal.cisTauReal_arctan_square_re_eq (a : TauRat) :
    ((TauComplex.cisTauReal (TauReal.arctan_of_rat_seq a)).mul
      (TauComplex.cisTauReal (TauReal.arctan_of_rat_seq a))).re
      = ((TauComplex.cisTauReal (TauReal.arctan_of_rat_seq a)).re.mul
          (TauComplex.cisTauReal (TauReal.arctan_of_rat_seq a)).re).sub
          ((TauComplex.cisTauReal (TauReal.arctan_of_rat_seq a)).im.mul
            (TauComplex.cisTauReal (TauReal.arctan_of_rat_seq a)).im) := rfl

/-- **Structural im-decomposition** of the cisTauReal square:

        `(cisTauReal(arctan a) · cisTauReal(arctan a)).im
           = cis_arctan_re a · cis_arctan_im a + cis_arctan_im a · cis_arctan_re a`.

    (Twice the cos-times-sin product, by symmetry.) -/
theorem TauReal.cisTauReal_arctan_square_im_eq (a : TauRat) :
    ((TauComplex.cisTauReal (TauReal.arctan_of_rat_seq a)).mul
      (TauComplex.cisTauReal (TauReal.arctan_of_rat_seq a))).im
      = ((TauComplex.cisTauReal (TauReal.arctan_of_rat_seq a)).re.mul
          (TauComplex.cisTauReal (TauReal.arctan_of_rat_seq a)).im).add
          ((TauComplex.cisTauReal (TauReal.arctan_of_rat_seq a)).im.mul
            (TauComplex.cisTauReal (TauReal.arctan_of_rat_seq a)).re) := rfl

-- ============================================================
-- PART 5: F.6-SUBSTITUTED DOUBLE-ANGLE FORMULAS
-- ============================================================

/-! ## F.6-substituted double-angle re/im at TauReal-equiv level

  Specializing Phase C's `cisTauReal_arctan_mul_re/im_equiv_F6_form`
  with `b := a`, we obtain the classical double-angle formulas at the
  cisTauReal-product level:

      (cisTauReal(arctan a) · cisTauReal(arctan a)).re
          ≈ cis_arctan_re a · cis_arctan_re a
              − (fromTauRat a · cis_arctan_re a) · (fromTauRat a · cis_arctan_re a)

      (cisTauReal(arctan a) · cisTauReal(arctan a)).im
          ≈ cis_arctan_re a · (fromTauRat a · cis_arctan_re a)
              + (fromTauRat a · cis_arctan_re a) · cis_arctan_re a

  These are the **τ-native double-angle identities** at the path-β
  domain `4·|a| ≤ 1`, obtained by F.6-substituting `sin(arctan a) ≈
  a · cos(arctan a)` into the structural decompositions. -/

/-- **🎯 F.6-substituted double-angle re-form** — the τ-native version of
    `cos(2α) = cos²α − sin²α` at `α = arctan a`, with F.6's
    `sin(arctan a) ≈ a · cos(arctan a)` substituted. For `4·|a.toRat| ≤ 1`:

        `(cisTauReal(arctan a) · cisTauReal(arctan a)).re`
          `≈ cis_arctan_re a · cis_arctan_re a`
              `− (fromTauRat a · cis_arctan_re a) · (fromTauRat a · cis_arctan_re a)`.

    Direct application of `cisTauReal_arctan_mul_re_equiv_F6_form` with
    `b := a`. -/
theorem TauReal.cisTauReal_arctan_square_re_equiv_F6_form (a : TauRat)
    (ha : 4 * |a.toRat| ≤ 1) :
    TauReal.equiv
      ((TauComplex.cisTauReal (TauReal.arctan_of_rat_seq a)).mul
        (TauComplex.cisTauReal (TauReal.arctan_of_rat_seq a))).re
      (((TauComplex.cisTauReal (TauReal.arctan_of_rat_seq a)).re.mul
          (TauComplex.cisTauReal (TauReal.arctan_of_rat_seq a)).re).sub
        (((TauReal.fromTauRat a).mul
            (TauComplex.cisTauReal (TauReal.arctan_of_rat_seq a)).re).mul
          ((TauReal.fromTauRat a).mul
            (TauComplex.cisTauReal (TauReal.arctan_of_rat_seq a)).re))) :=
  TauReal.cisTauReal_arctan_mul_re_equiv_F6_form a a ha ha

/-- **🎯 F.6-substituted double-angle im-form** — the τ-native version of
    `sin(2α) = 2·sin α · cos α` at `α = arctan a`. For `4·|a.toRat| ≤ 1`:

        `(cisTauReal(arctan a) · cisTauReal(arctan a)).im`
          `≈ cis_arctan_re a · (fromTauRat a · cis_arctan_re a)`
              `+ (fromTauRat a · cis_arctan_re a) · cis_arctan_re a`.

    Direct application of `cisTauReal_arctan_mul_im_equiv_F6_form` with
    `b := a`. -/
theorem TauReal.cisTauReal_arctan_square_im_equiv_F6_form (a : TauRat)
    (ha : 4 * |a.toRat| ≤ 1) :
    TauReal.equiv
      ((TauComplex.cisTauReal (TauReal.arctan_of_rat_seq a)).mul
        (TauComplex.cisTauReal (TauReal.arctan_of_rat_seq a))).im
      (((TauComplex.cisTauReal (TauReal.arctan_of_rat_seq a)).re.mul
          ((TauReal.fromTauRat a).mul
            (TauComplex.cisTauReal (TauReal.arctan_of_rat_seq a)).re)).add
        (((TauReal.fromTauRat a).mul
            (TauComplex.cisTauReal (TauReal.arctan_of_rat_seq a)).re).mul
          (TauComplex.cisTauReal (TauReal.arctan_of_rat_seq a)).re)) :=
  TauReal.cisTauReal_arctan_mul_im_equiv_F6_form a a ha ha

-- ============================================================
-- PART 6: PARITY — cisTauReal AT NEGATED arctan
-- ============================================================

/-! ## Parity identity for negated arctan input

  Since `arctan` is odd (`arctan(−a) = −arctan(a)`), `cisTauReal` at the
  negated arctan-image angle is the conjugate of the original:

      (cisTauReal(arctan(−a))).re ≈ (cisTauReal(arctan a)).re
      (cisTauReal(arctan(−a))).im ≈ −(cisTauReal(arctan a)).im

  These follow from:
  1. `arctan_of_rat_seq` is odd at the pointwise `.toRat` level
     (shipped as `arctan_partial_rat_neg`).
  2. `cisTauReal` has even `.re` and odd `.im` in its TauReal angle
     argument (shipped as `cisTauReal_negate_re/im_equiv`).

  This is the parity tool needed to handle the negative sign in
  Machin's `+ 4·arctan(1/5) − arctan(1/239)`. -/

/-- **🎯 cisTauReal_arctan_negate_re_equiv** — parity of the real part:

        `(cisTauReal(arctan_of_rat_seq (negate a))).re ≈ (cisTauReal(arctan_of_rat_seq a)).re`.

    Proof: pointwise reduction to `cos(-θ) = cos(θ)`, equivalently
    `expPartial_pureIm_re_rat(-x) = expPartial_pureIm_re_rat(x)` (even). -/
theorem TauReal.cisTauReal_arctan_negate_re_equiv (a : TauRat) :
    TauReal.equiv
      (TauComplex.cisTauReal (TauReal.arctan_of_rat_seq (TauRat.negate a))).re
      (TauComplex.cisTauReal (TauReal.arctan_of_rat_seq a)).re := by
  apply TauReal.equiv_of_pointwise
  intro n
  rw [equiv_iff_toRat_eq]
  rw [cisTauReal_re_approx_toRat, cisTauReal_re_approx_toRat,
      TauReal.arctan_of_rat_seq_approx, TauReal.arctan_of_rat_seq_approx,
      TauRat.arctan_partial_toRat, TauRat.arctan_partial_toRat,
      toRat_negate, arctan_partial_rat_neg, expPartial_pureIm_re_rat_neg]

/-- **🎯 cisTauReal_arctan_negate_im_equiv** — parity of the imaginary part:

        `(cisTauReal(arctan_of_rat_seq (negate a))).im ≈ negate (cisTauReal(arctan_of_rat_seq a)).im`.

    Proof: pointwise reduction to `sin(-θ) = -sin(θ)`, equivalently
    `expPartial_pureIm_im_rat(-x) = -expPartial_pureIm_im_rat(x)` (odd). -/
theorem TauReal.cisTauReal_arctan_negate_im_equiv (a : TauRat) :
    TauReal.equiv
      (TauComplex.cisTauReal (TauReal.arctan_of_rat_seq (TauRat.negate a))).im
      (TauReal.negate (TauComplex.cisTauReal (TauReal.arctan_of_rat_seq a)).im) := by
  apply TauReal.equiv_of_pointwise
  intro n
  rw [equiv_iff_toRat_eq]
  -- LHS at depth n .toRat = expPartial_pureIm_im_rat (arctan_partial_rat (-a.toRat) n) n
  --                       = expPartial_pureIm_im_rat (-(arctan_partial_rat a.toRat n)) n
  --                       = -(expPartial_pureIm_im_rat (arctan_partial_rat a.toRat n) n)
  -- RHS at depth n .toRat = -((cisTauReal (arctan_of_rat_seq a)).im.approx n).toRat
  --                       = -(expPartial_pureIm_im_rat (arctan_partial_rat a.toRat n) n)
  rw [cisTauReal_im_approx_toRat,
      TauReal.arctan_of_rat_seq_approx,
      TauRat.arctan_partial_toRat,
      toRat_negate, arctan_partial_rat_neg, expPartial_pureIm_im_rat_neg]
  -- LHS now: -(expPartial_pureIm_im_rat (arctan_partial_rat a.toRat n) n)
  -- RHS: ((TauReal.negate (cisTauReal (arctan_of_rat_seq a)).im).approx n).toRat
  --    = (TauRat.negate ((cisTauReal (arctan_of_rat_seq a)).im.approx n)).toRat
  --    = -((cisTauReal (arctan_of_rat_seq a)).im.approx n).toRat
  --    = -(expPartial_pureIm_im_rat (arctan_partial_rat a.toRat n) n)
  change -(expPartial_pureIm_im_rat (arctan_partial_rat a.toRat n) n)
       = (TauRat.negate ((TauComplex.cisTauReal (TauReal.arctan_of_rat_seq a)).im.approx n)).toRat
  rw [toRat_negate, cisTauReal_im_approx_toRat,
      TauReal.arctan_of_rat_seq_approx,
      TauRat.arctan_partial_toRat]

/-- **🎯 cisTauReal_arctan_negate_equiv_conj** — the full parity identity:

        `cisTauReal(arctan_of_rat_seq (negate a))
           ≈ ⟨(cisTauReal(arctan_of_rat_seq a)).re,
              negate (cisTauReal(arctan_of_rat_seq a)).im⟩`.

    This is the TauComplex-level "conjugate of cisTauReal at arctan(−a)".
    It says: replacing `a → −a` in the arctan input is the same as taking
    the complex conjugate of the cisTauReal value. -/
theorem TauReal.cisTauReal_arctan_negate_equiv_conj (a : TauRat) :
    TauComplex.equiv
      (TauComplex.cisTauReal (TauReal.arctan_of_rat_seq (TauRat.negate a)))
      ⟨(TauComplex.cisTauReal (TauReal.arctan_of_rat_seq a)).re,
       TauReal.negate (TauComplex.cisTauReal (TauReal.arctan_of_rat_seq a)).im⟩ :=
  ⟨TauReal.cisTauReal_arctan_negate_re_equiv a,
   TauReal.cisTauReal_arctan_negate_im_equiv a⟩

-- ============================================================
-- PART 7: THE MACHIN IDENTITY — NAMED TARGET PROPOSITION
-- ============================================================

/-! ## The Machin identity as a named proposition

  The full Machin identity at the TauReal level requires angle injectivity
  (Phase E). We name it as a target proposition so consumers can route
  through it abstractly, mirroring the `BBPLeibnizCorrespondence`
  proposition in `TauRealBBP.lean`. -/

/-- **The Machin identity proposition** (Phase D target, Phase E discharge).

    Asserts the classical identity

        `16·arctan(1/5) − 4·arctan(1/239) ≈ pi_leibniz`

    at TauReal-equiv level, where `pi_leibniz` is the Leibniz-pair series
    `TauReal.pi`.

    A discharge of this proposition would close the Machin chain, providing
    an exponentially-convergent route to π that decouples from the
    sub-quadratic Leibniz series.

    For now, this is a `def` (a target, not a proven fact). Phase E will
    discharge it via:
    1. Iterate `cisTauReal_arctan_add` 3× to obtain `cisTauReal(4·arctan 1/5)`
       at re/im level.
    2. Combine with `cisTauReal_arctan_negate_equiv_conj` to get
       `cisTauReal(4·arctan 1/5 − arctan 1/239)` at re/im level.
    3. Show this matches `cisTauReal(π/4) = (1+i)/√2` (or equivalent
       fraction representation modulo a `cos(...)` scaling factor).
    4. Lift to angle-equivalence via injectivity or a direct equiv chain. -/
def MachinIdentity : Prop :=
  TauReal.equiv
    (TauReal.sub
      ((TauReal.fromTauRat ⟨⟨16, 0⟩, 1, by norm_num⟩).mul
        (TauReal.arctan_of_rat_seq TauRat.one_fifth))
      ((TauReal.fromTauRat ⟨⟨4, 0⟩, 1, by norm_num⟩).mul
        (TauReal.arctan_of_rat_seq TauRat.one_two_three_nine)))
    TauReal.pi

/-! ## Notes for Phase E — discharging MachinIdentity

  The classical Machin chain at the cisTauReal level can be built up
  step-by-step from the doubling identity:

  **Step 1**: `cisTauReal(2·arctan(1/5)) ≈ cisTauReal(arctan(1/5))²`
              [`cisTauReal_arctan_double` at `a = 1/5`]

  **Step 2**: `cisTauReal(4·arctan(1/5)) ≈ cisTauReal(arctan(1/5))⁴`
              [iterate the doubling identity once more]

  **Step 3**: `cisTauReal(4·arctan(1/5) − arctan(1/239))
                  ≈ cisTauReal(arctan(1/5))⁴ · conj(cisTauReal(arctan(1/239)))`
              [Phase C arctan-add + Part 6 parity]

  **Step 4**: Connect the RHS to `cisTauReal(π/4)` by computing the
              re/im of `cisTauReal(arctan(1/5))⁴ · conj(cisTauReal(arctan(1/239)))`
              via F.6-substituted forms and matching against `(1+i)/√2`
              (modulo a scaling cos-factor that integrates over the
              equiv modulus chase).

  **Step 5**: Multiply both sides by 4 to recover Machin's full form
              `16·arctan(1/5) − 4·arctan(1/239) ≈ pi_leibniz`.

  Steps 1-3 are accessible from the Phase B/C/D infrastructure shipped
  here. Step 4 requires either (a) computing `cisTauReal(π/4)` directly
  (which needs a τ-native √2 plus the Pythagorean magnitude identity),
  or (b) reducing to a per-component re/im algebraic identity that bypasses
  the magnitude.

  Step 5 requires a τ-native distributivity over multiplication by
  rational constants, plus the `4·arctan(1) ≈ pi_leibniz` connection
  (which is `pi_partial_rat n = pi_leibniz_partial_rat`'s renumbering).
-/

end Tau.Boundary
