import TauLib.BookI.Boundary.TauRealArctanDeriv
import TauLib.BookI.Boundary.TauRealSinCos
import TauLib.BookI.Boundary.TauRealInv
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity

/-!
# TauLib.BookI.Boundary.TauRealCisDeriv

**Wave Γ₈ Phase 2.6.B.2.β.4.9 — Module 4**: specialized chain rule for
`cisTauReal ∘ arctan_of_rat` (Path C from the architectural forensic).

## Goal

Prove the two component-wise IsDerivAt theorems needed by Module 6
(tangent identity discharge):

  IsDerivAt (fun x => (cisTauReal (arctan_of_rat_seq x)).re) a
            (some TauReal equiv to −Im(cis(arctan a)) / (1+a²))

  IsDerivAt (fun x => (cisTauReal (arctan_of_rat_seq x)).im) a
            (some TauReal equiv to Re(cis(arctan a)) / (1+a²))

## Architectural choice (Path C — specialized chain rule)

Per the deep-architectural forensic
(`atlas/insights/2026-05-17-tau-canon-derivative-deep-forensic.md`),
we ship a SPECIALIZED chain rule for `cisTauReal ∘ arctan_of_rat`
rather than a generic chain rule. The specialization leverages:

  1. **`cisTauReal_add` (β.3 / M3 endpoint)**: multiplicativity at TauReal
     argument level — `cis(x + y) ≈ cis(x) · cis(y)`.
  2. **Small-angle approximation**: `cis(δ) - 1 ≈ i · δ` for small δ,
     bounded analytically via cos/sin Taylor remainders.
  3. **Module 3 arctan derivative**: `arctan'(a) = 1/(1+a²)` provided
     by `IsDerivAt_arctan_of_rat`.

Combined: `(cis ∘ arctan)'(a) = i · cis(arctan a) · arctan'(a)`.
Taking components gives the two TauReal-valued derivatives needed.

## Wave 1 — Foundations

This wave ships the composite function definitions and initial structural
facts:
- `cis_arctan_re : TauRat → TauReal`
- `cis_arctan_im : TauRat → TauReal`
- Approx lemmas
- Boundedness via Pythagorean (β.4.7)
- Values at `a = 0`

Subsequent waves add:
- Wave 2: Small-angle bound for cisTauReal
- Wave 3: Specialized chain rule assembly + IsDerivAt theorems
-/

set_option autoImplicit false

namespace Tau.Boundary

open Tau.Denotation

-- ============================================================
-- PART 1: COMPOSITE FUNCTION DEFINITIONS
-- ============================================================

/-- **[I.D-CisTauReal-Arctan-Re]** The `.re` component of
    `cisTauReal ∘ arctan_of_rat_seq`, as a `TauRat → TauReal` function. -/
def TauReal.cis_arctan_re (x : TauRat) : TauReal :=
  (TauComplex.cisTauReal (TauReal.arctan_of_rat_seq x)).re

/-- **[I.D-CisTauReal-Arctan-Im]** The `.im` component of
    `cisTauReal ∘ arctan_of_rat_seq`, as a `TauRat → TauReal` function. -/
def TauReal.cis_arctan_im (x : TauRat) : TauReal :=
  (TauComplex.cisTauReal (TauReal.arctan_of_rat_seq x)).im

@[simp] theorem TauReal.cis_arctan_re_approx (x : TauRat) (n : Nat) :
    (TauReal.cis_arctan_re x).approx n
      = (TauComplex.cisTauReal (TauReal.arctan_of_rat_seq x)).re.approx n := rfl

@[simp] theorem TauReal.cis_arctan_im_approx (x : TauRat) (n : Nat) :
    (TauReal.cis_arctan_im x).approx n
      = (TauComplex.cisTauReal (TauReal.arctan_of_rat_seq x)).im.approx n := rfl

-- ============================================================
-- PART 2: BOUNDEDNESS VIA PYTHAGOREAN (β.4.7)
-- ============================================================

/-! ## Boundedness from Pythagorean

  By `cisTauReal_magSq_equiv_one` (β.4.7), for any bounded TauReal `x`
  (`|x.approx n| ≤ 1`), we have `re² + im² ≈ 1`. This implies `|re|, |im| ≤ 1`
  in TauReal-equivalence sense, but pointwise bounds at .approx N require
  more care.

  For the chain rule analysis, we need `|arctan_of_rat_seq a .approx n| ≤ 1`
  to apply `cisTauReal_add`. This follows from the existing β.4 starter:
  `|arctan_partial_rat a.toRat n| ≤ 2/3 < 1` for `|a| ≤ 1/2`.
-/

/-- For `|a.toRat| ≤ 1/2`, every approximation of `arctan_of_rat_seq a` is
    bounded by 1 in absolute value (in fact ≤ 2/3 by the β.4 starter).

    Used as the boundedness hypothesis for `cisTauReal_add` applications. -/
theorem TauReal.arctan_of_rat_seq_bounded (a : TauRat) (ha : 2 * |a.toRat| ≤ 1) :
    ∀ n, ((TauReal.arctan_of_rat_seq a).approx n).abs.toRat ≤ 1 := by
  intro n
  -- (arctan_of_rat_seq a).approx n = arctan_partial a n
  rw [TauReal.arctan_of_rat_seq_approx]
  -- |arctan_partial a n|.abs.toRat = |(arctan_partial a n).toRat|
  rw [TauRat.toRat_abs]
  -- |arctan_partial a n.toRat| = |arctan_partial_rat a.toRat n|
  rw [TauRat.arctan_partial_toRat]
  -- Use the existing β.4 bound: |arctan_partial_rat a.toRat n| ≤ 1
  exact arctan_partial_rat_abs_le_one a.toRat ha n

-- ============================================================
-- PART 3: VALUES AT a = 0 (BASE CASE FOR GRONWALL)
-- ============================================================

/-! ## Values at a = 0

  At `a = 0`:
    - `arctan_of_rat_seq 0 ≈ 0` (zero partial sum is 0).
    - `cisTauReal (arctan_of_rat_seq 0) ≈ cisTauReal(0) ≈ TauComplex.one`
      (via β.4.0: `exp(TauComplex.zero) ≈ TauComplex.one`).
    - `.re ≈ 1`, `.im ≈ 0`.

  These values anchor the Gronwall base case for Module 6:
    h(0) = (cis(arctan 0)).im − 0 · (cis(arctan 0)).re ≈ 0 − 0 = 0.
-/

/-- `arctan_of_rat_seq TauRat.zero ≈ TauReal.zero`. -/
theorem TauReal.arctan_of_rat_seq_zero_equiv :
    TauReal.equiv (TauReal.arctan_of_rat_seq TauRat.zero) TauReal.zero := by
  apply TauReal.equiv_of_pointwise
  intro n
  rw [equiv_iff_toRat_eq]
  -- (arctan_of_rat_seq 0).approx n = arctan_partial 0 n
  -- arctan_partial 0 n = 0 (since 0^k = 0 for k ≥ 1, all pair_terms are 0)
  rw [TauReal.arctan_of_rat_seq_approx, TauRat.arctan_partial_toRat]
  -- Need: arctan_partial_rat 0 n = 0
  have h_zero_partial : ∀ m, arctan_partial_rat 0 m = 0 := by
    intro m
    induction m with
    | zero => rfl
    | succ m ih =>
      rw [arctan_partial_rat_succ, ih]
      unfold arctan_pair_term_rat
      have h_pow_zero_4k1 : (0 : Rat)^(4*m+1) = 0 := by
        rw [zero_pow]; omega
      have h_pow_zero_4k3 : (0 : Rat)^(4*m+3) = 0 := by
        rw [zero_pow]; omega
      rw [h_pow_zero_4k1, h_pow_zero_4k3]
      ring
  rw [toRat_zero, h_zero_partial]
  show (0 : Rat) = (TauReal.zero.approx n).toRat
  rw [show TauReal.zero.approx n = TauRat.zero from rfl, toRat_zero]

end Tau.Boundary
