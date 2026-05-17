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

-- ============================================================
-- PART 4: Wave 2 — cis_arctan at a = 0 (GRONWALL BASE CASE)
-- ============================================================

/-! ## Wave 2 — Base case at a = 0

  The Gronwall base case for Module 6: `h(0) ≈ 0` where
  `h(a) := cis_arctan_im a − a · cis_arctan_re a`.

  This decomposes into:
  - `cis_arctan_re 0 ≈ 1`  (real part of cis(0) = 1)
  - `cis_arctan_im 0 ≈ 0`  (imaginary part of cis(0) = 0)
  - Together with `(fromTauRat 0) ≈ 0`: gives `h(0) ≈ 0 − 0·1 = 0`.

  These are proved by direct computation at `.approx N .toRat` level:
  for `N ≥ 1`, the partial sums of `expPartial_pureIm_re_rat 0 N = 1`
  and `expPartial_pureIm_im_rat 0 N = 0` exactly.

  The key chain:
    arctan_of_rat_seq(0).approx N .toRat = arctan_partial_rat 0 N = 0
    ⟹ cisTauReal(arctan_of_rat_seq 0).re.approx N .toRat
       = expPartial_pureIm_re_rat 0 N
       = 1   (for N ≥ 1)
-/

/-- For `k ≥ 1`, `pureIm_pow_re_im_rat 0 k = (0, 0)`. -/
theorem pureIm_pow_re_im_rat_zero_succ (k : Nat) :
    pureIm_pow_re_im_rat 0 (k+1) = (0, 0) := by
  induction k with
  | zero =>
    show pureIm_pow_re_im_rat 0 1 = (0, 0)
    rw [pureIm_pow_re_im_rat_succ, pureIm_pow_re_im_rat_zero]
    show (-(0 : Rat) * 0, (1 : Rat) * 0) = (0, 0)
    simp
  | succ k ih =>
    rw [pureIm_pow_re_im_rat_succ, ih]
    show (-(0 : Rat) * 0, (0 : Rat) * 0) = (0, 0)
    simp

/-- For `N ≥ 1`, `expPartial_pureIm_re_rat 0 N = 1`. (Renamed to avoid
    name conflict with the existing `expPartial_pureIm_re_rat_zero`
    `@[simp]` lemma for `expPartial_pureIm_re_rat xR 0 = 0`.) -/
theorem expPartial_pureIm_re_rat_at_zero (N : Nat) (hN : 1 ≤ N) :
    expPartial_pureIm_re_rat 0 N = 1 := by
  induction N, hN using Nat.le_induction with
  | base =>
    -- N = 1: 0 + (pureIm_pow_re_im_rat 0 0).1 / 0! = 0 + 1/1 = 1
    show expPartial_pureIm_re_rat 0 1 = 1
    rw [expPartial_pureIm_re_rat_succ, expPartial_pureIm_re_rat_zero,
        pureIm_pow_re_im_rat_zero]
    simp
  | succ N hN ih =>
    -- expPartial_pureIm_re_rat 0 (N+1) = 1 + 0/N! = 1 (using pureIm_pow_re_im_rat 0 N = (0, 0) for N ≥ 1)
    rw [expPartial_pureIm_re_rat_succ, ih]
    -- Need: pureIm_pow_re_im_rat 0 N = (0, 0). N ≥ 1 (from Nat.le_induction).
    have hN_succ : ∃ m, N = m + 1 := by
      exact ⟨N - 1, by omega⟩
    obtain ⟨m, hm⟩ := hN_succ
    rw [hm, pureIm_pow_re_im_rat_zero_succ]
    show (1 : Rat) + (0 : Rat) / ((m + 1).factorial : Rat) = 1
    rw [zero_div, add_zero]

/-- For all `N`, `expPartial_pureIm_im_rat 0 N = 0`. (Renamed to avoid
    name conflict with the existing `expPartial_pureIm_im_rat_zero`
    `@[simp]` lemma for `expPartial_pureIm_im_rat xR 0 = 0`.) -/
theorem expPartial_pureIm_im_rat_at_zero (N : Nat) :
    expPartial_pureIm_im_rat 0 N = 0 := by
  induction N with
  | zero => rfl
  | succ N ih =>
    rw [expPartial_pureIm_im_rat_succ, ih]
    rcases N with _ | m
    · simp [pureIm_pow_re_im_rat_zero]
    · rw [pureIm_pow_re_im_rat_zero_succ]
      simp

/-- Helper: `arctan_partial_rat 0 N = 0` for all `N`. -/
theorem arctan_partial_rat_at_zero (N : Nat) : arctan_partial_rat 0 N = 0 := by
  induction N with
  | zero => rfl
  | succ N ih =>
    rw [arctan_partial_rat_succ, ih]
    unfold arctan_pair_term_rat
    have h_pow_4k1 : (0 : Rat)^(4*N+1) = 0 := zero_pow (by omega)
    have h_pow_4k3 : (0 : Rat)^(4*N+3) = 0 := zero_pow (by omega)
    rw [h_pow_4k1, h_pow_4k3]; ring

/-- **[I.T-CisArctanRe-Zero]** `cis_arctan_re 0 ≈ TauReal.one`. -/
theorem TauReal.cis_arctan_re_zero_equiv_one :
    TauReal.equiv (TauReal.cis_arctan_re TauRat.zero) TauReal.one := by
  refine ⟨fun _ => 1, fun k N hN => ?_⟩
  have hN_ge : 1 ≤ N := hN
  unfold TauRat.lt
  rw [TauRat.toRat_abs, toRat_sub, TauRat.ofNatRecip_toRat]
  rw [TauReal.cis_arctan_re_approx, cisTauReal_re_approx_toRat]
  rw [TauReal.arctan_of_rat_seq_approx, TauRat.arctan_partial_toRat]
  rw [show TauRat.zero.toRat = (0 : Rat) from toRat_zero]
  rw [arctan_partial_rat_at_zero N]
  rw [expPartial_pureIm_re_rat_at_zero N hN_ge]
  show |(1 : Rat) - (TauReal.one.approx N).toRat| < 1 / ((k : Rat) + 1)
  rw [show TauReal.one.approx N = TauRat.one from rfl, toRat_one]
  rw [sub_self, abs_zero]
  have h_pos : (0 : Rat) < (k : Rat) + 1 := by
    have : (0 : Rat) ≤ (k : Rat) := by exact_mod_cast Nat.zero_le k
    linarith
  exact div_pos (by norm_num : (0 : Rat) < 1) h_pos

/-- **[I.T-CisArctanIm-Zero]** `cis_arctan_im 0 ≈ TauReal.zero`. -/
theorem TauReal.cis_arctan_im_zero_equiv_zero :
    TauReal.equiv (TauReal.cis_arctan_im TauRat.zero) TauReal.zero := by
  refine ⟨fun _ => 0, fun k N _ => ?_⟩
  unfold TauRat.lt
  rw [TauRat.toRat_abs, toRat_sub, TauRat.ofNatRecip_toRat]
  rw [TauReal.cis_arctan_im_approx, cisTauReal_im_approx_toRat]
  rw [TauReal.arctan_of_rat_seq_approx, TauRat.arctan_partial_toRat]
  rw [show TauRat.zero.toRat = (0 : Rat) from toRat_zero]
  rw [arctan_partial_rat_at_zero N]
  rw [expPartial_pureIm_im_rat_at_zero N]
  show |(0 : Rat) - (TauReal.zero.approx N).toRat| < 1 / ((k : Rat) + 1)
  rw [show TauReal.zero.approx N = TauRat.zero from rfl, toRat_zero]
  rw [sub_self, abs_zero]
  have h_pos : (0 : Rat) < (k : Rat) + 1 := by
    have : (0 : Rat) ≤ (k : Rat) := by exact_mod_cast Nat.zero_le k
    linarith
  exact div_pos (by norm_num : (0 : Rat) < 1) h_pos

-- ============================================================
-- PART 5: Wave 3 — SMALL-ANGLE EXPANSIONS AT DEPTH 3
-- ============================================================

/-! ## Wave 3 — small-angle Taylor expansion at depth 3

  Closed-form values of the exp pureIm partial sums at depth 3:

      expPartial_pureIm_re_rat α 3 = 1 − α²/2
      expPartial_pureIm_im_rat α 3 = α

  These are the EXACT second-order Taylor expansions of cos and sin
  at depth 3 — there is no truncation error because the depth-3 sum
  has reached the next-after-leading term in each component.

  These closed forms are foundational for the chain rule analysis:
  they let us write

      |cisTauReal(δ).re.approx N .toRat − 1| ≤ |α|²/2   (for N = 3)
      |cisTauReal(δ).im.approx N .toRat − α| = 0         (for N = 3)

  where α = δ.approx N .toRat. Subsequent waves extend these to
  arbitrary depths via Taylor remainder bounds.

  The cyclotomic-4 structure of `pureIm_pow_re_im_rat`:
    k=0 → (1, 0)    k=1 → (0, α)    k=2 → (−α², 0)    k=3 → (0, −α³)
  means the partial sum at depth N gets contributions from .1 only
  at even k and from .2 only at odd k. -/

/-- **Closed form at depth 3 — real part**:
    `expPartial_pureIm_re_rat α 3 = 1 − α²/2`. -/
theorem expPartial_pureIm_re_rat_three (α : Rat) :
    expPartial_pureIm_re_rat α 3 = 1 - α^2 / 2 := by
  -- Unfold step by step (avoiding looping `Nat = k+1` rewrites)
  rw [show (3 : Nat) = 2 + 1 from rfl, expPartial_pureIm_re_rat_succ]
  rw [show (2 : Nat) = 1 + 1 from rfl, expPartial_pureIm_re_rat_succ,
      pureIm_pow_re_im_rat_succ]
  rw [show (1 : Nat) = 0 + 1 from rfl, expPartial_pureIm_re_rat_succ,
      pureIm_pow_re_im_rat_succ]
  rw [expPartial_pureIm_re_rat_zero, pureIm_pow_re_im_rat_zero]
  simp [Nat.factorial, pow_two]
  ring

/-- **Closed form at depth 3 — imaginary part**:
    `expPartial_pureIm_im_rat α 3 = α`. -/
theorem expPartial_pureIm_im_rat_three (α : Rat) :
    expPartial_pureIm_im_rat α 3 = α := by
  rw [show (3 : Nat) = 2 + 1 from rfl, expPartial_pureIm_im_rat_succ]
  rw [show (2 : Nat) = 1 + 1 from rfl, expPartial_pureIm_im_rat_succ,
      pureIm_pow_re_im_rat_succ]
  rw [show (1 : Nat) = 0 + 1 from rfl, expPartial_pureIm_im_rat_succ,
      pureIm_pow_re_im_rat_succ]
  rw [expPartial_pureIm_im_rat_zero, pureIm_pow_re_im_rat_zero]
  simp [Nat.factorial]

/-- **Small-angle bound for re at depth 3**:
    `|expPartial_pureIm_re_rat α 3 − 1| = |α|²/2 ≤ α²` for any `α`. -/
theorem expPartial_pureIm_re_rat_three_small_angle (α : Rat) :
    |expPartial_pureIm_re_rat α 3 - 1| = α^2 / 2 := by
  rw [expPartial_pureIm_re_rat_three]
  -- |1 - α²/2 - 1| = |-α²/2| = α²/2 (since α² ≥ 0)
  have h_neg : (1 : Rat) - α^2 / 2 - 1 = -(α^2 / 2) := by ring
  rw [h_neg, abs_neg]
  have h_sq_nn : (0 : Rat) ≤ α^2 / 2 := by positivity
  exact abs_of_nonneg h_sq_nn

/-- **Small-angle exact equality for im at depth 3**:
    `expPartial_pureIm_im_rat α 3 − α = 0`. -/
theorem expPartial_pureIm_im_rat_three_small_angle (α : Rat) :
    expPartial_pureIm_im_rat α 3 - α = 0 := by
  rw [expPartial_pureIm_im_rat_three]; ring

-- ============================================================
-- PART 6: Wave 4 — SMALL-ANGLE BOUND AT ARBITRARY DEPTH N ≥ 1
-- ============================================================

/-! ## Wave 4 — small-angle bound for cisTauReal partial sum at any depth

  Generalizes the Wave 3 depth-3 closed form to arbitrary depth via a
  LOOSE linear-in-N bound:

      |expPartial_pureIm_re_rat α N − 1| ≤ N · α²    (N ≥ 1, |α| ≤ 1)
      |expPartial_pureIm_im_rat α N − α| ≤ N · |α|³  (similarly)

  Proof structure (loose linear bound, no alternating-series machinery):
  1. Structural bound on `(pureIm_pow_re_im_rat α N)`:
       |.1|, |.2| ≤ |α|^N
  2. Triangle inequality + induction:
       T_{N+1} = T_N + contribution_N
       |T_{N+1}| ≤ |T_N| + |α|^N / N!
                ≤ N·α² + α²/N!  (for N ≥ 2, |α|^N ≤ α²)
                ≤ N·α² + α²     (1/N! ≤ 1)
                = (N+1)·α²

  The linear-in-N bound is loose (tight would be `α²/2` independent of N
  via alternating-series first-term dominance), but it's provable by
  simple induction and sufficient for the chain rule: in the IsDerivAt
  context, α = O(1/2^N) so N·α² = O(N/4^N) → 0 as N → ∞.
-/

/-- **Structural bound**: `|.1|, |.2| of pureIm_pow_re_im_rat α N| ≤ |α|^N`. -/
theorem pureIm_pow_re_im_rat_abs_bound (α : Rat) (N : Nat) :
    |(pureIm_pow_re_im_rat α N).1| ≤ |α|^N ∧ |(pureIm_pow_re_im_rat α N).2| ≤ |α|^N := by
  induction N with
  | zero =>
    refine ⟨?_, ?_⟩
    · show |((1 : Rat), (0 : Rat)).1| ≤ |α|^0
      simp
    · show |((1 : Rat), (0 : Rat)).2| ≤ |α|^0
      simp
  | succ N ih =>
    rw [pureIm_pow_re_im_rat_succ]
    refine ⟨?_, ?_⟩
    · -- .1 of (-(prev).2·α, (prev).1·α) = -(prev).2 · α
      show |-(pureIm_pow_re_im_rat α N).2 * α| ≤ |α|^(N+1)
      rw [show -(pureIm_pow_re_im_rat α N).2 * α
            = -((pureIm_pow_re_im_rat α N).2 * α) from by ring]
      rw [abs_neg, abs_mul]
      calc |(pureIm_pow_re_im_rat α N).2| * |α|
          ≤ |α|^N * |α| := mul_le_mul_of_nonneg_right ih.2 (_root_.abs_nonneg _)
        _ = |α|^(N+1) := by rw [pow_succ]
    · -- .2 of (-(prev).2·α, (prev).1·α) = (prev).1 · α
      show |(pureIm_pow_re_im_rat α N).1 * α| ≤ |α|^(N+1)
      rw [abs_mul]
      calc |(pureIm_pow_re_im_rat α N).1| * |α|
          ≤ |α|^N * |α| := mul_le_mul_of_nonneg_right ih.1 (_root_.abs_nonneg _)
        _ = |α|^(N+1) := by rw [pow_succ]

/-- **Helper**: For `N ≥ 2` and `|α| ≤ 1`, `|α|^N ≤ α²`. -/
theorem pow_le_sq_of_abs_le_one (α : Rat) (hα : |α| ≤ 1) (N : Nat) (hN : 2 ≤ N) :
    |α|^N ≤ α^2 := by
  have h_abs_nn : (0 : Rat) ≤ |α| := _root_.abs_nonneg _
  have h_abs_sq : |α|^2 = α^2 := by rw [sq_abs]
  have h_decreasing : |α|^N ≤ |α|^2 := by
    have h_le : |α|^N ≤ |α|^2 :=
      pow_le_pow_of_le_one h_abs_nn hα hN
    exact h_le
  linarith [h_abs_sq.symm.le, h_decreasing]

/-- **Helper**: `(1 : Rat) / (Nat.factorial N : Rat) ≤ 1` for any `N`. -/
theorem one_div_factorial_le_one (N : Nat) :
    (1 : Rat) / ((N.factorial : Nat) : Rat) ≤ 1 := by
  have h_pos : (0 : Rat) < (N.factorial : Rat) := by
    have : 0 < N.factorial := Nat.factorial_pos _
    exact_mod_cast this
  have h_ge_one : (1 : Rat) ≤ (N.factorial : Rat) := by
    have : 1 ≤ N.factorial := Nat.factorial_pos N
    exact_mod_cast this
  rw [div_le_one h_pos]
  exact h_ge_one

/-- **Wave 4 — linear-in-N small-angle bound for re part**:

      |expPartial_pureIm_re_rat α N − 1| ≤ N · α²

    for `N ≥ 1` and `|α| ≤ 1`. -/
theorem expPartial_pureIm_re_rat_small_angle_bound
    (α : Rat) (hα : |α| ≤ 1) (N : Nat) (hN : 1 ≤ N) :
    |expPartial_pureIm_re_rat α N - 1| ≤ (N : Rat) * α^2 := by
  induction N, hN using Nat.le_induction with
  | base =>
    -- N = 1: expPartial_pureIm_re_rat α 1 = 1
    have h_one : expPartial_pureIm_re_rat α 1 = 1 := by
      rw [show (1 : Nat) = 0 + 1 from rfl, expPartial_pureIm_re_rat_succ,
          expPartial_pureIm_re_rat_zero, pureIm_pow_re_im_rat_zero]
      simp
    rw [h_one]
    show |(1 : Rat) - 1| ≤ ((1 : Nat) : Rat) * α^2
    rw [sub_self, abs_zero]
    have h_sq : (0 : Rat) ≤ α^2 := sq_nonneg _
    have h_one_rat : ((1 : Nat) : Rat) = 1 := by norm_num
    rw [h_one_rat]
    linarith
  | succ N hN_ge ih =>
    -- Step N → N+1 (for N ≥ 1)
    rw [expPartial_pureIm_re_rat_succ]
    have h_rearrange :
        expPartial_pureIm_re_rat α N + (pureIm_pow_re_im_rat α N).1 / (N.factorial : Rat) - 1
        = (expPartial_pureIm_re_rat α N - 1)
          + (pureIm_pow_re_im_rat α N).1 / (N.factorial : Rat) := by ring
    rw [h_rearrange]
    have h_struct := (pureIm_pow_re_im_rat_abs_bound α N).1
    have h_fact_pos : (0 : Rat) < (N.factorial : Rat) := by
      have : 0 < N.factorial := Nat.factorial_pos _
      exact_mod_cast this
    have h_fact_ge_one : (1 : Rat) ≤ (N.factorial : Rat) := by
      have : 1 ≤ N.factorial := Nat.factorial_pos N
      exact_mod_cast this
    have h_sq_nn : (0 : Rat) ≤ α^2 := sq_nonneg _
    -- Case split: N = 1 (contribution = 0) vs N ≥ 2 (use pow bound)
    by_cases h_N1 : N = 1
    · subst h_N1
      have h_pow_zero : (pureIm_pow_re_im_rat α 1).1 = 0 := by
        rw [show (1 : Nat) = 0 + 1 from rfl, pureIm_pow_re_im_rat_succ,
            pureIm_pow_re_im_rat_zero]
        simp
      rw [h_pow_zero, zero_div, add_zero]
      have h_cast : ((1+1 : Nat) : Rat) = 2 := by norm_num
      have h_cast1 : ((1 : Nat) : Rat) = 1 := by norm_num
      rw [h_cast]
      rw [h_cast1] at ih
      linarith
    · have hN_ge_2 : 2 ≤ N := by omega
      have h_pow_bound : |α|^N ≤ α^2 := pow_le_sq_of_abs_le_one α hα N hN_ge_2
      -- |pureIm.1| ≤ |α|^N ≤ α²
      have h_num_le_sq : |(pureIm_pow_re_im_rat α N).1| ≤ α^2 := le_trans h_struct h_pow_bound
      -- |pureIm.1| ≤ α² · N!  (since N! ≥ 1, α² ≥ 0)
      have h_num_le_prod : |(pureIm_pow_re_im_rat α N).1| ≤ α^2 * (N.factorial : Rat) := by
        calc |(pureIm_pow_re_im_rat α N).1|
            ≤ α^2 := h_num_le_sq
          _ = α^2 * 1 := by ring
          _ ≤ α^2 * (N.factorial : Rat) :=
              mul_le_mul_of_nonneg_left h_fact_ge_one h_sq_nn
      -- |pureIm.1 / N!| ≤ α²
      have h_div_bound :
          |(pureIm_pow_re_im_rat α N).1 / (N.factorial : Rat)| ≤ α^2 := by
        rw [abs_div, abs_of_pos h_fact_pos]
        rw [div_le_iff₀ h_fact_pos]
        exact h_num_le_prod
      -- Triangle + IH + h_div_bound
      have h_cast : ((N + 1 : Nat) : Rat) = ((N : Nat) : Rat) + 1 := by push_cast; ring
      rw [h_cast]
      calc |(expPartial_pureIm_re_rat α N - 1)
            + (pureIm_pow_re_im_rat α N).1 / (N.factorial : Rat)|
          ≤ |expPartial_pureIm_re_rat α N - 1|
            + |(pureIm_pow_re_im_rat α N).1 / (N.factorial : Rat)| := abs_add_le _ _
        _ ≤ ((N : Nat) : Rat) * α^2 + α^2 := by linarith
        _ = (((N : Nat) : Rat) + 1) * α^2 := by ring

-- ============================================================
-- PART 7: Wave 5 — SMALL-ANGLE BOUND FOR IM AT ARBITRARY DEPTH N ≥ 2
-- ============================================================

/-! ## Wave 5 — small-angle bound for cisTauReal partial sum (im part)

  Parallel to Wave 4: linear-in-N bound for the sin partial sum.

      |expPartial_pureIm_im_rat α N − α| ≤ N · |α|³   (N ≥ 2, |α| ≤ 1)

  Note: the threshold is `N ≥ 2` (not `N ≥ 1` as in Wave 4) because at
  N = 1 the sum is still 0 — the first non-zero contribution to the
  imaginary part comes at step N = 1 (contributing α at k = 1), giving
  the first useful approximation at N = 2.

  Proof structure parallels Wave 4: induction on N from base 2 with
  case split on N = 2 (contribution at step 2 vanishes since
  `(pureIm_pow α 2).2 = 0` by cyclotomic-4) vs N ≥ 3 (use
  `|α|^N ≤ |α|³`).
-/

/-- **Closed form at depth 2 — imaginary part**:
    `expPartial_pureIm_im_rat α 2 = α`. -/
theorem expPartial_pureIm_im_rat_two (α : Rat) :
    expPartial_pureIm_im_rat α 2 = α := by
  rw [show (2 : Nat) = 1 + 1 from rfl, expPartial_pureIm_im_rat_succ]
  rw [show (1 : Nat) = 0 + 1 from rfl, expPartial_pureIm_im_rat_succ,
      pureIm_pow_re_im_rat_succ]
  rw [expPartial_pureIm_im_rat_zero, pureIm_pow_re_im_rat_zero]
  simp

/-- **Helper**: For `N ≥ 3` and `|α| ≤ 1`, `|α|^N ≤ |α|^3`. -/
theorem pow_le_cube_of_abs_le_one (α : Rat) (hα : |α| ≤ 1) (N : Nat) (hN : 3 ≤ N) :
    |α|^N ≤ |α|^3 := by
  apply pow_le_pow_of_le_one (_root_.abs_nonneg _) hα hN

/-- **Wave 5 — linear-in-N small-angle bound for im part**:

      |expPartial_pureIm_im_rat α N − α| ≤ N · |α|³

    for `N ≥ 2` and `|α| ≤ 1`. -/
theorem expPartial_pureIm_im_rat_small_angle_bound
    (α : Rat) (hα : |α| ≤ 1) (N : Nat) (hN : 2 ≤ N) :
    |expPartial_pureIm_im_rat α N - α| ≤ (N : Rat) * |α|^3 := by
  induction N, hN using Nat.le_induction with
  | base =>
    -- N = 2: expPartial_pureIm_im_rat α 2 = α
    rw [expPartial_pureIm_im_rat_two]
    show |α - α| ≤ ((2 : Nat) : Rat) * |α|^3
    rw [sub_self, abs_zero]
    have h_pow_nn : (0 : Rat) ≤ |α|^3 := by positivity
    have h_two_cast : ((2 : Nat) : Rat) = 2 := by norm_num
    rw [h_two_cast]
    linarith
  | succ N hN_ge ih =>
    -- Step N → N+1 (for N ≥ 2)
    rw [expPartial_pureIm_im_rat_succ]
    have h_rearrange :
        expPartial_pureIm_im_rat α N + (pureIm_pow_re_im_rat α N).2 / (N.factorial : Rat) - α
        = (expPartial_pureIm_im_rat α N - α)
          + (pureIm_pow_re_im_rat α N).2 / (N.factorial : Rat) := by ring
    rw [h_rearrange]
    have h_struct := (pureIm_pow_re_im_rat_abs_bound α N).2
    have h_fact_pos : (0 : Rat) < (N.factorial : Rat) := by
      have : 0 < N.factorial := Nat.factorial_pos _
      exact_mod_cast this
    have h_fact_ge_one : (1 : Rat) ≤ (N.factorial : Rat) := by
      have : 1 ≤ N.factorial := Nat.factorial_pos N
      exact_mod_cast this
    have h_pow_nn : (0 : Rat) ≤ |α|^3 := by positivity
    -- Case split: N = 2 (contribution = 0 via cyclotomic-4) vs N ≥ 3
    by_cases h_N2 : N = 2
    · subst h_N2
      have h_pow_zero : (pureIm_pow_re_im_rat α 2).2 = 0 := by
        rw [show (2 : Nat) = 1 + 1 from rfl, pureIm_pow_re_im_rat_succ,
            show (1 : Nat) = 0 + 1 from rfl, pureIm_pow_re_im_rat_succ,
            pureIm_pow_re_im_rat_zero]
        simp
      rw [h_pow_zero, zero_div, add_zero]
      have h_cast : ((2+1 : Nat) : Rat) = 3 := by norm_num
      have h_cast2 : ((2 : Nat) : Rat) = 2 := by norm_num
      rw [h_cast]
      rw [h_cast2] at ih
      linarith
    · have hN_ge_3 : 3 ≤ N := by omega
      have h_pow_bound : |α|^N ≤ |α|^3 := pow_le_cube_of_abs_le_one α hα N hN_ge_3
      -- |pureIm.2| ≤ |α|^N ≤ |α|³
      have h_num_le_cube : |(pureIm_pow_re_im_rat α N).2| ≤ |α|^3 := le_trans h_struct h_pow_bound
      -- |pureIm.2| ≤ |α|³ · N! (since N! ≥ 1)
      have h_num_le_prod :
          |(pureIm_pow_re_im_rat α N).2| ≤ |α|^3 * (N.factorial : Rat) := by
        calc |(pureIm_pow_re_im_rat α N).2|
            ≤ |α|^3 := h_num_le_cube
          _ = |α|^3 * 1 := by ring
          _ ≤ |α|^3 * (N.factorial : Rat) :=
              mul_le_mul_of_nonneg_left h_fact_ge_one h_pow_nn
      -- |pureIm.2 / N!| ≤ |α|³
      have h_div_bound :
          |(pureIm_pow_re_im_rat α N).2 / (N.factorial : Rat)| ≤ |α|^3 := by
        rw [abs_div, abs_of_pos h_fact_pos]
        rw [div_le_iff₀ h_fact_pos]
        exact h_num_le_prod
      have h_cast : ((N + 1 : Nat) : Rat) = ((N : Nat) : Rat) + 1 := by push_cast; ring
      rw [h_cast]
      calc |(expPartial_pureIm_im_rat α N - α)
            + (pureIm_pow_re_im_rat α N).2 / (N.factorial : Rat)|
          ≤ |expPartial_pureIm_im_rat α N - α|
            + |(pureIm_pow_re_im_rat α N).2 / (N.factorial : Rat)| := abs_add_le _ _
        _ ≤ ((N : Nat) : Rat) * |α|^3 + |α|^3 := by linarith
        _ = (((N : Nat) : Rat) + 1) * |α|^3 := by ring

-- ============================================================
-- PART 8: Wave 6a — TAUREAL-LEVEL SMALL-ANGLE BOUNDS
-- ============================================================

/-! ## Wave 6a — Lift small-angle bounds to TauReal cisTauReal level

  Using the bridges:
    cisTauReal_re_approx_toRat:
      ((cisTauReal x).re.approx n).toRat = expPartial_pureIm_re_rat ((x.approx n).toRat) n
    cisTauReal_im_approx_toRat:
      ((cisTauReal x).im.approx n).toRat = expPartial_pureIm_im_rat ((x.approx n).toRat) n

  we lift Wave 4 and Wave 5 bounds to the TauReal-cisTauReal interface:

      |((cisTauReal x).re.approx n).toRat − 1|     ≤ n · α²      (n ≥ 1, |α| ≤ 1)
      |((cisTauReal x).im.approx n).toRat − α|     ≤ n · |α|³   (n ≥ 2, |α| ≤ 1)

  where α := (x.approx n).toRat. These pointwise (at fixed depth n) bounds
  are exactly the inputs needed for the IsDerivAt chain rule analysis.
-/

open TauComplex in
/-- **Wave 6a (re)** — Small-angle bound for `(cisTauReal x).re.approx n`. -/
theorem TauReal.cisTauReal_re_approx_small_angle_bound
    (x : TauReal) (n : Nat) (hn : 1 ≤ n)
    (hα : |((x.approx n).toRat)| ≤ 1) :
    |((TauComplex.cisTauReal x).re.approx n).toRat - 1|
      ≤ (n : Rat) * ((x.approx n).toRat)^2 := by
  rw [cisTauReal_re_approx_toRat]
  exact expPartial_pureIm_re_rat_small_angle_bound ((x.approx n).toRat) hα n hn

open TauComplex in
/-- **Wave 6a (im)** — Small-angle bound for `(cisTauReal x).im.approx n`. -/
theorem TauReal.cisTauReal_im_approx_small_angle_bound
    (x : TauReal) (n : Nat) (hn : 2 ≤ n)
    (hα : |((x.approx n).toRat)| ≤ 1) :
    |((TauComplex.cisTauReal x).im.approx n).toRat - ((x.approx n).toRat)|
      ≤ (n : Rat) * |((x.approx n).toRat)|^3 := by
  rw [cisTauReal_im_approx_toRat]
  exact expPartial_pureIm_im_rat_small_angle_bound ((x.approx n).toRat) hα n hn

-- ============================================================
-- PART 9: Wave 6b — cis_arctan SMALL-ANGLE AT cis_arctan LEVEL
-- ============================================================

/-! ## Wave 6b — Small-angle bound at cis_arctan_re/im level

  Composing Wave 6a with the arctan boundedness theorem
  (`arctan_of_rat_seq_bounded`), we obtain small-angle bounds directly
  at the `cis_arctan_re/im` interface for TauRat inputs with `|a| ≤ 1/2`:

      |((cis_arctan_re a).approx n).toRat − 1| ≤ n · α²
      |((cis_arctan_im a).approx n).toRat − α| ≤ n · |α|³

  where α := ((arctan_of_rat_seq a).approx n).toRat = arctan_partial_rat a.toRat n.

  The `2 · |a| ≤ 1` hypothesis ensures `|arctan_partial| ≤ 2/3 < 1` for all n,
  so the small-angle hypothesis of Wave 6a is met.

  These bounds are the final input for the chain rule (Wave 6c).
-/

/-- **Wave 6b (re)** — Small-angle bound for `(cis_arctan_re a).approx n`. -/
theorem TauReal.cis_arctan_re_approx_small_angle_bound
    (a : TauRat) (ha : 2 * |a.toRat| ≤ 1) (n : Nat) (hn : 1 ≤ n) :
    |((TauReal.cis_arctan_re a).approx n).toRat - 1|
      ≤ (n : Rat) * (((TauReal.arctan_of_rat_seq a).approx n).toRat)^2 := by
  -- cis_arctan_re a = (cisTauReal (arctan_of_rat_seq a)).re
  -- So ((cis_arctan_re a).approx n).toRat = ((cisTauReal (...)).re.approx n).toRat
  show |((TauComplex.cisTauReal (TauReal.arctan_of_rat_seq a)).re.approx n).toRat - 1|
        ≤ (n : Rat) * (((TauReal.arctan_of_rat_seq a).approx n).toRat)^2
  apply TauReal.cisTauReal_re_approx_small_angle_bound (TauReal.arctan_of_rat_seq a) n hn
  -- Need: |((arctan_of_rat_seq a).approx n).toRat| ≤ 1
  have h_bound := TauReal.arctan_of_rat_seq_bounded a ha n
  rw [TauRat.toRat_abs] at h_bound
  exact h_bound

/-- **Wave 6b (im)** — Small-angle bound for `(cis_arctan_im a).approx n`. -/
theorem TauReal.cis_arctan_im_approx_small_angle_bound
    (a : TauRat) (ha : 2 * |a.toRat| ≤ 1) (n : Nat) (hn : 2 ≤ n) :
    |((TauReal.cis_arctan_im a).approx n).toRat
       - (((TauReal.arctan_of_rat_seq a).approx n).toRat)|
      ≤ (n : Rat) * |((TauReal.arctan_of_rat_seq a).approx n).toRat|^3 := by
  show |((TauComplex.cisTauReal (TauReal.arctan_of_rat_seq a)).im.approx n).toRat
         - (((TauReal.arctan_of_rat_seq a).approx n).toRat)|
        ≤ (n : Rat) * |((TauReal.arctan_of_rat_seq a).approx n).toRat|^3
  apply TauReal.cisTauReal_im_approx_small_angle_bound (TauReal.arctan_of_rat_seq a) n hn
  have h_bound := TauReal.arctan_of_rat_seq_bounded a ha n
  rw [TauRat.toRat_abs] at h_bound
  exact h_bound

end Tau.Boundary
