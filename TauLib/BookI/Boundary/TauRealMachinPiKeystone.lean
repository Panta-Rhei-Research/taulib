import TauLib.BookI.Boundary.TauRealMachinPiBridge
import TauLib.BookI.Boundary.TauRealMachinFortyFiveDegree
import TauLib.BookI.Boundary.TauRealBBP
import Mathlib.Tactic.Ring
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity

/-!
# TauLib.BookI.Boundary.TauRealMachinPiKeystone

**Phase E Scope 2D — Structural keystone reductions toward `pi_machin.equiv pi`**.

After Scope 2A-lift (`TauRealMachinFortyFiveDegree.lean`) shipped the
45°-line cisTauReal identity at TauReal-equiv level, Scope 2B
(`TauRealPiLeibniz.lean`) shipped `pi ≈ 4·arctan_of_rat_seq(1)`, and
Scope 2C (`TauRealMachinPiBridge.lean`) shipped the structural bridge
`MachinIdentity ↔ pi_machin.equiv pi`, this module ships **further
structural reductions** that decompose the keystone identity into
its most refined named form.

## What this module ships

* **`pi_machin_arctan_quarter`** — a TauReal explicitly equal to
  `4·arctan_of_rat_seq(1/5) − arctan_of_rat_seq(1/239)`, i.e., the
  τ-native form of `pi_machin/4`. (This is `4·arctan(1/5) −
  arctan(1/239)` at TauReal-arctan-of-rat-seq level.)

* **`MachinSlashFourIdentity`** — a named target proposition:
  `equiv pi_machin_arctan_quarter (arctan_of_rat_seq 1)`. This is
  the "/4" form of MachinIdentity: it asserts that
  `4·arctan(1/5) − arctan(1/239) ≈ arctan(1)` at TauReal level,
  matching the classical Machin identity `π/4 = 4·arctan(1/5) −
  arctan(1/239)` in τ-native form.

* **`pi_machin_arctan_form_equiv_four_quarter`** — the structural
  scaling: `pi_machin_arctan_form ≈ 4 · pi_machin_arctan_quarter`,
  expressing the algebraic relationship `16·arctan(1/5) − 4·arctan(1/239)
  = 4·(4·arctan(1/5) − arctan(1/239))`.

* **`equiv_of_four_mul_equiv`** / **`four_mul_equiv_of_equiv`** —
  the direct bidirectional scaling lemma: `4·a ≈ 4·b ↔ a ≈ b`. Both
  directions proved via explicit modulus chases, avoiding the need
  for the heavier `equiv_mul_congr` bounding machinery.

* **`MachinIdentity_iff_MachinSlashFourIdentity`** — the load-bearing
  structural reduction:
  `MachinIdentity ↔ MachinSlashFourIdentity`. The "/4" form is
  logically equivalent to MachinIdentity via Scope 2B's
  `pi ≈ 4·arctan(1)`.

* **`pi_machin_equiv_pi_iff_MachinSlashFourIdentity`** — composing
  this with Scope 2C's bridge:
  `TauReal.equiv pi_machin pi ↔ MachinSlashFourIdentity`.

## Why this is meaningful progress

The original `MachinIdentity` target had two forms of "weight":
1. The structural scaling factor of 4 (combining the 4·arctan(1)
   and the 16·/4· coefficient asymmetry).
2. The genuine analytic content `4·arctan(1/5) − arctan(1/239) ≈ arctan(1)`.

This module **completely discharges component 1** as a structural
theorem and exposes component 2 as the named, focused
`MachinSlashFourIdentity` — a proposition with a single arctan on each
side. This is the cleanest possible structural reduction of
MachinIdentity short of discharging the analytic content itself.

## What remains for the full discharge

The residual `MachinSlashFourIdentity` still requires either:
- **cisTauReal injectivity on the principal branch** (lifting Scope
  2A-lift's 45°-line identity to angle equality), OR
- **A direct partial-sum analytic argument** bounding
  `|4·arctan_partial(1/5) n − arctan_partial(1/239) n − arctan_partial(1) n|`,
  which classically requires the Machin identity at the limit.

Both paths are independent deep infrastructure (Phase F concerns).

## Registry Cross-References

* [I.D-Pi-Machin] `TauReal.pi_machin` (TauRealArctan Part 10)
* [I.D-MachinIdentity] `MachinIdentity` (TauRealMachin.lean:459)
* [I.T-MachinIdentity-iff-PiMachinEquivPi] `MachinIdentity_iff_pi_machin_equiv_pi`
  (Scope 2C)
* [I.T-PiMachinEquivMachinCombinationArctanOfRatSeq]
  `pi_machin_equiv_machin_combination_arctan_of_rat_seq` (Scope 2C)
* [I.T-PiEquivFourArctanOne] `TauReal.pi_equiv_four_arctan_one`
  (Scope 2B)

## Build state

* `sorry` count: 0
* Axiom count: 3 (kernel: `propext`, `Classical.choice`, `Quot.sound`)
* Imports: `TauRealMachinPiBridge` + `TauRealMachinFortyFiveDegree`
  (which transitively imports the whole Phase B/C/D/E stack) +
  Mathlib tactics only.

## Module name

This file is picked up by the `.submodules` glob in `lakefile.lean`.
-/

set_option autoImplicit false

namespace Tau.Boundary

open Tau.Denotation

-- ============================================================
-- PART 1: THE pi_machin_arctan_quarter TAU-REAL
-- ============================================================

/-! ## The τ-native form of `pi_machin/4`

  The classical Machin identity says `π/4 = 4·arctan(1/5) − arctan(1/239)`.
  We define the τ-native "/4" form using `arctan_of_rat_seq` at the
  Machin constants. -/

/-- **The τ-native form of `pi_machin/4`** (Scope 2D):
    `pi_machin_arctan_quarter = 4·arctan(1/5) − arctan(1/239)`,
    where the coefficients are `TauReal.fromTauRat` of the rational
    constants 4 and 1, and the arctans are `arctan_of_rat_seq` of
    `one_fifth` and `one_two_three_nine`. -/
noncomputable def TauReal.pi_machin_arctan_quarter : TauReal :=
  ((TauReal.fromTauRat ⟨⟨4, 0⟩, 1, by norm_num⟩).mul
      (TauReal.arctan_of_rat_seq TauRat.one_fifth)).sub
    (TauReal.arctan_of_rat_seq TauRat.one_two_three_nine)

-- ============================================================
-- PART 2: pi_machin_arctan_form ≈ 4 · pi_machin_arctan_quarter
-- ============================================================

/-! ## Structural scaling identity

  The combination `16·arctan(1/5) − 4·arctan(1/239) = 4·(4·arctan(1/5) −
  arctan(1/239))` is an algebraic identity in TauReal that needs to be
  verified pointwise.

  At every depth `n`:
  `(16·a_5_n − 4·a_239_n) = 4·(4·a_5_n − a_239_n)`
  where `a_5_n := arctan_partial_rat(1/5) n.toRat` etc. This holds by
  ring arithmetic on rationals. The Cauchy-equiv lifts via
  `equiv_of_pointwise`. -/

/-- **Auxiliary: pointwise toRat identity for the scaling**.

    The `arctan_of_rat_seq`-form of `pi_machin` equals 4 times
    `pi_machin_arctan_quarter` pointwise. -/
theorem TauReal.pi_machin_arctan_form_approx_toRat_eq_four_times_quarter_approx_toRat
    (n : Nat) :
    ((((TauReal.fromTauRat ⟨⟨16, 0⟩, 1, by norm_num⟩).mul
          (TauReal.arctan_of_rat_seq TauRat.one_fifth)).sub
        ((TauReal.fromTauRat ⟨⟨4, 0⟩, 1, by norm_num⟩).mul
          (TauReal.arctan_of_rat_seq TauRat.one_two_three_nine))).approx n).toRat
      = (((TauReal.fromTauRat ⟨⟨4, 0⟩, 1, by norm_num⟩).mul
            TauReal.pi_machin_arctan_quarter).approx n).toRat := by
  -- LHS: (16·a_5_n - 4·a_239_n)
  -- RHS: 4·(4·a_5_n - a_239_n)
  show (TauRat.add
          (TauRat.mul ((TauReal.fromTauRat ⟨⟨16, 0⟩, 1, by norm_num⟩).approx n)
                     ((TauReal.arctan_of_rat_seq TauRat.one_fifth).approx n))
          (TauRat.negate
            (TauRat.mul ((TauReal.fromTauRat ⟨⟨4, 0⟩, 1, by norm_num⟩).approx n)
                       ((TauReal.arctan_of_rat_seq TauRat.one_two_three_nine).approx n)))).toRat
        = _
  rw [toRat_add, toRat_negate, toRat_mul, toRat_mul]
  -- RHS structural unfolding
  show _
    = (TauRat.mul ((TauReal.fromTauRat ⟨⟨4, 0⟩, 1, by norm_num⟩).approx n)
        (TauReal.pi_machin_arctan_quarter.approx n)).toRat
  rw [toRat_mul]
  unfold TauReal.pi_machin_arctan_quarter
  show _ = _ * (TauRat.add
                  (TauRat.mul ((TauReal.fromTauRat ⟨⟨4, 0⟩, 1, by norm_num⟩).approx n)
                              ((TauReal.arctan_of_rat_seq TauRat.one_fifth).approx n))
                  (TauRat.negate ((TauReal.arctan_of_rat_seq TauRat.one_two_three_nine).approx n))).toRat
  rw [toRat_add, toRat_mul, toRat_negate]
  have h_16 : (((TauReal.fromTauRat ⟨⟨16, 0⟩, 1, by norm_num⟩ : TauReal).approx n).toRat
                : Rat) = 16 := by
    show ((⟨⟨16, 0⟩, 1, by norm_num⟩ : TauRat).toRat : Rat) = 16
    unfold TauRat.toRat
    simp only [TauInt.toInt]
    push_cast
    ring
  have h_4 : (((TauReal.fromTauRat ⟨⟨4, 0⟩, 1, by norm_num⟩ : TauReal).approx n).toRat
                : Rat) = 4 := by
    show ((⟨⟨4, 0⟩, 1, by norm_num⟩ : TauRat).toRat : Rat) = 4
    unfold TauRat.toRat
    simp only [TauInt.toInt]
    push_cast
    ring
  rw [h_16, h_4]
  ring

/-- **Structural scaling identity** (Scope 2D):
    `pi_machin_arctan_form ≈ 4 · pi_machin_arctan_quarter`.

    The arctan_of_rat_seq form of `pi_machin` (i.e.,
    `16·arctan(1/5) − 4·arctan(1/239)`) is Cauchy-equivalent to
    four times `pi_machin_arctan_quarter` (i.e., `4·(4·arctan(1/5) −
    arctan(1/239))`).

    Proof: via `equiv_of_pointwise` on the per-depth toRat identity
    (algebraic ring arithmetic). -/
theorem TauReal.pi_machin_arctan_form_equiv_four_quarter :
    TauReal.equiv
      (((TauReal.fromTauRat ⟨⟨16, 0⟩, 1, by norm_num⟩).mul
          (TauReal.arctan_of_rat_seq TauRat.one_fifth)).sub
        ((TauReal.fromTauRat ⟨⟨4, 0⟩, 1, by norm_num⟩).mul
          (TauReal.arctan_of_rat_seq TauRat.one_two_three_nine)))
      ((TauReal.fromTauRat ⟨⟨4, 0⟩, 1, by norm_num⟩).mul
        TauReal.pi_machin_arctan_quarter) := by
  apply TauReal.equiv_of_pointwise
  intro n
  rw [equiv_iff_toRat_eq]
  exact TauReal.pi_machin_arctan_form_approx_toRat_eq_four_times_quarter_approx_toRat n

-- ============================================================
-- PART 3: THE MachinSlashFourIdentity PROPOSITION
-- ============================================================

/-! ## The "/4" form of MachinIdentity

  The classical Machin identity at the "/4" level:

  >  `4·arctan(1/5) − arctan(1/239) = arctan(1) = π/4`.

  τ-natively: `pi_machin_arctan_quarter ≈ arctan_of_rat_seq(1)`.

  This is the **most compact** named form of the Machin identity:
  a single arctan on each side, no scalar coefficients beyond the 4
  on `arctan(1/5)`. -/

/-- **The "/4" form of the Machin identity** (Scope 2D target):

    `pi_machin_arctan_quarter ≈ arctan_of_rat_seq(1)`.

    Asserts that `4·arctan(1/5) − arctan(1/239)` is Cauchy-equivalent
    to `arctan(1)` at TauReal level. Equivalently, by Scope 2B's
    `pi ≈ 4·arctan(1)` plus the structural scaling identity,
    `MachinSlashFourIdentity` is logically equivalent to
    `MachinIdentity` (and hence to `pi_machin.equiv pi`).

    This is the **cleanest named structural reduction** of the
    keystone identity: the residual analytic content reduces to a
    single TauReal-equiv at the "/4" level. -/
def MachinSlashFourIdentity : Prop :=
  TauReal.equiv
    TauReal.pi_machin_arctan_quarter
    (TauReal.arctan_of_rat_seq TauRat.one_canonical)

-- ============================================================
-- PART 4: SCALING CANCELLATION  4·a ≈ 4·b ↔ a ≈ b
-- ============================================================

/-! ## Scaling cancellation / scaling-up lemmas

  Bidirectional: `4·a ≈ 4·b ↔ a ≈ b`. Both directions proved by
  explicit modulus chases.

  **Forward** (`equiv_of_four_mul_equiv`): given `(fromTauRat 4)·a
  ≈ (fromTauRat 4)·b`, conclude `a ≈ b`. The 4-scaled equiv gives
  `|4·(a - b)| < 1/(k+1)` at some modulus; we extract
  `|a - b| < 1/(4·(k+1)) ≤ 1/(k+1)` after rescaling.

  **Reverse** (`four_mul_equiv_of_equiv`): given `a ≈ b`, conclude
  `(fromTauRat 4)·a ≈ (fromTauRat 4)·b`. At depth `n ≥ μ(4k+3)`,
  `|a - b| < 1/(4k+4)`, hence `|4·(a - b)| < 4/(4k+4) = 1/(k+1)`. -/

/-- **Pointwise expansion of `(fromTauRat 4 · a).approx n .toRat`**. -/
private theorem TauReal.four_mul_approx_toRat (a : TauReal) (n : Nat) :
    (((TauReal.fromTauRat ⟨⟨4, 0⟩, 1, by norm_num⟩).mul a).approx n).toRat
      = 4 * (a.approx n).toRat := by
  show (TauRat.mul ((⟨⟨4, 0⟩, 1, by norm_num⟩ : TauRat))
                   (a.approx n)).toRat = _
  rw [toRat_mul]
  congr 1
  unfold TauRat.toRat
  simp only [TauInt.toInt]
  push_cast
  ring

/-- **Cancellation of `(fromTauRat 4) · _`**: if
    `(fromTauRat 4) · a ≈ (fromTauRat 4) · b`, then `a ≈ b`.

    Proof: from the modulus `μ` of the 4-scaled equiv, build a new
    modulus `μ'(k) := μ(4 * k + 3)`. At any `n ≥ μ'(k)`, we have
    `|4·(a.approx n .toRat) - 4·(b.approx n .toRat)| < 1/(4k+4)`,
    hence `|(a.approx n).toRat - (b.approx n).toRat| < 1/(16k+16) ≤
    1/(k+1)`. -/
theorem TauReal.equiv_of_four_mul_equiv (a b : TauReal)
    (h : ((TauReal.fromTauRat ⟨⟨4, 0⟩, 1, by norm_num⟩).mul a).equiv
         ((TauReal.fromTauRat ⟨⟨4, 0⟩, 1, by norm_num⟩).mul b)) :
    a.equiv b := by
  obtain ⟨μ, hμ⟩ := h
  refine ⟨fun k => μ (4 * k + 3), fun k n hkn => ?_⟩
  have h_orig := hμ (4 * k + 3) n hkn
  unfold TauRat.lt at h_orig ⊢
  rw [TauRat.toRat_abs, toRat_sub] at h_orig
  rw [TauRat.ofNatRecip_toRat] at h_orig
  rw [TauReal.four_mul_approx_toRat, TauReal.four_mul_approx_toRat] at h_orig
  rw [TauRat.toRat_abs, toRat_sub, TauRat.ofNatRecip_toRat]
  -- h_orig: |4·(a.approx n).toRat - 4·(b.approx n).toRat| < 1/((4k+3)+1)
  have h_factor : (4 : Rat) * (a.approx n).toRat - 4 * (b.approx n).toRat
                    = 4 * ((a.approx n).toRat - (b.approx n).toRat) := by ring
  rw [h_factor] at h_orig
  rw [abs_mul] at h_orig
  rw [show |(4 : Rat)| = 4 from by norm_num] at h_orig
  -- h_orig: 4 * |...| < 1/((4k+3:Nat)+1)
  have h_cast : (((4 * k + 3 : Nat) : Rat) + 1) = 4 * (k : Rat) + 4 := by push_cast; ring
  rw [h_cast] at h_orig
  -- h_orig: 4 * |...| < 1/(4k+4)
  have h_recip_pos : (0 : Rat) < (4 * (k : Rat) + 4) := by
    have : (0 : Rat) ≤ (k : Rat) := by exact_mod_cast Nat.zero_le k
    linarith
  have h_k1_pos : (0 : Rat) < (k : Rat) + 1 := by
    have : (0 : Rat) ≤ (k : Rat) := by exact_mod_cast Nat.zero_le k
    linarith
  -- |a - b| ≤ |4·(a - b)|/4 < (1/(4k+4))/4 = 1/(16k+16) ≤ 1/(k+1)
  have h_lt_div : |(a.approx n).toRat - (b.approx n).toRat| < (1 : Rat) / (4 * (4 * (k : Rat) + 4)) := by
    rw [lt_div_iff₀ (by linarith : (0 : Rat) < 4 * (4 * (k : Rat) + 4))]
    have h_rearr : |(a.approx n).toRat - (b.approx n).toRat| * (4 * (4 * (k : Rat) + 4))
                    = 4 * |(a.approx n).toRat - (b.approx n).toRat| * (4 * (k : Rat) + 4) := by ring
    rw [h_rearr]
    have h_lt := h_orig
    rw [lt_div_iff₀ h_recip_pos] at h_lt
    linarith
  -- Chain: 1/(16k+16) ≤ 1/(k+1) since 16k+16 ≥ k+1 ≥ 0
  have h_chain : (1 : Rat) / (4 * (4 * (k : Rat) + 4)) ≤ 1 / ((k : Rat) + 1) := by
    rw [div_le_div_iff₀ (by linarith : (0 : Rat) < 4 * (4 * (k : Rat) + 4)) h_k1_pos]
    nlinarith
  linarith

/-- **Reverse: scaling-up of equiv via `(fromTauRat 4) · _`**: if
    `a ≈ b`, then `(fromTauRat 4) · a ≈ (fromTauRat 4) · b`.

    Proof: from the modulus `μ` of `a ≈ b`, build a new modulus
    `μ'(k) := μ(4 * k + 3)`. At any `n ≥ μ'(k)`, we have
    `|a.approx n .toRat - b.approx n .toRat| < 1/(4k+4)`, hence
    `|4·(a - b)| < 4/(4k+4) = 1/(k+1)`. -/
theorem TauReal.four_mul_equiv_of_equiv (a b : TauReal) (h : a.equiv b) :
    ((TauReal.fromTauRat ⟨⟨4, 0⟩, 1, by norm_num⟩).mul a).equiv
    ((TauReal.fromTauRat ⟨⟨4, 0⟩, 1, by norm_num⟩).mul b) := by
  obtain ⟨μ, hμ⟩ := h
  refine ⟨fun k => μ (4 * k + 3), fun k n hkn => ?_⟩
  have h_orig := hμ (4 * k + 3) n hkn
  unfold TauRat.lt at h_orig ⊢
  rw [TauRat.toRat_abs, toRat_sub] at h_orig
  rw [TauRat.ofNatRecip_toRat] at h_orig
  rw [TauRat.toRat_abs, toRat_sub, TauRat.ofNatRecip_toRat]
  rw [TauReal.four_mul_approx_toRat, TauReal.four_mul_approx_toRat]
  -- Goal: |4·(a.approx n .toRat) - 4·(b.approx n .toRat)| < 1/(k+1)
  -- = 4·|a - b| < 1/(k+1)
  have h_factor : (4 : Rat) * (a.approx n).toRat - 4 * (b.approx n).toRat
                    = 4 * ((a.approx n).toRat - (b.approx n).toRat) := by ring
  rw [h_factor, abs_mul, show |(4 : Rat)| = 4 from by norm_num]
  -- h_orig: |a - b| < 1/((4k+3:Nat)+1) = 1/(4k+4)
  have h_cast : (((4 * k + 3 : Nat) : Rat) + 1) = 4 * (k : Rat) + 4 := by push_cast; ring
  rw [h_cast] at h_orig
  -- h_orig: |a - b| < 1/(4k+4)
  have h_recip_pos : (0 : Rat) < (4 * (k : Rat) + 4) := by
    have : (0 : Rat) ≤ (k : Rat) := by exact_mod_cast Nat.zero_le k
    linarith
  have h_k1_pos : (0 : Rat) < (k : Rat) + 1 := by
    have : (0 : Rat) ≤ (k : Rat) := by exact_mod_cast Nat.zero_le k
    linarith
  -- 4·|a-b| < 4/(4k+4) = 1/(k+1)
  have h_chain : 4 * |(a.approx n).toRat - (b.approx n).toRat| < 4 / (4 * (k : Rat) + 4) := by
    have h_step : 4 * |(a.approx n).toRat - (b.approx n).toRat|
                    < 4 * (1 / (4 * (k : Rat) + 4)) := by
      apply mul_lt_mul_of_pos_left h_orig (by norm_num)
    rw [show (4 : Rat) * (1 / (4 * (k : Rat) + 4)) = 4 / (4 * (k : Rat) + 4) from by ring] at h_step
    exact h_step
  -- 4/(4k+4) = 1/(k+1)
  have h_eq : (4 : Rat) / (4 * (k : Rat) + 4) = 1 / ((k : Rat) + 1) := by
    field_simp
  rw [h_eq] at h_chain
  exact h_chain

-- ============================================================
-- PART 5: STRUCTURAL EQUIVALENCE — MachinIdentity ↔ MachinSlashFourIdentity
-- ============================================================

/-! ## Forward direction: MachinIdentity → MachinSlashFourIdentity

  Given `MachinIdentity` (`pi_machin_arctan_form ≈ pi`), we obtain
  `MachinSlashFourIdentity` (`pi_machin_arctan_quarter ≈ arctan(1)`)
  via:
  1. `pi_machin_arctan_form ≈ pi` (hypothesis).
  2. `pi ≈ 4·arctan(1)` (Scope 2B).
  3. `pi_machin_arctan_form ≈ 4·pi_machin_arctan_quarter` (Scope 2D Part 2).
  4. So `4·pi_machin_arctan_quarter ≈ 4·arctan(1)`.
  5. Cancel: `pi_machin_arctan_quarter ≈ arctan(1)`. -/

theorem MachinIdentity_implies_MachinSlashFourIdentity :
    MachinIdentity → MachinSlashFourIdentity := by
  intro h_machin
  unfold MachinIdentity at h_machin
  have h_form_eq_4q := TauReal.pi_machin_arctan_form_equiv_four_quarter
  have h_pi_eq_4arc1 := TauReal.pi_equiv_four_arctan_one
  -- Chain: 4·quarter ≈ form (symm) ≈ pi ≈ 4·arctan(1)
  have h_chain : ((TauReal.fromTauRat ⟨⟨4, 0⟩, 1, by norm_num⟩).mul
                    TauReal.pi_machin_arctan_quarter).equiv
                 ((TauReal.fromTauRat ⟨⟨4, 0⟩, 1, by norm_num⟩).mul
                    (TauReal.arctan_of_rat_seq TauRat.one_canonical)) := by
    have h1 : ((TauReal.fromTauRat ⟨⟨4, 0⟩, 1, by norm_num⟩).mul
                  TauReal.pi_machin_arctan_quarter).equiv
               (((TauReal.fromTauRat ⟨⟨16, 0⟩, 1, by norm_num⟩).mul
                  (TauReal.arctan_of_rat_seq TauRat.one_fifth)).sub
                ((TauReal.fromTauRat ⟨⟨4, 0⟩, 1, by norm_num⟩).mul
                  (TauReal.arctan_of_rat_seq TauRat.one_two_three_nine))) :=
      TauReal.equiv_symm h_form_eq_4q
    exact TauReal.equiv_trans (TauReal.equiv_trans h1 h_machin) h_pi_eq_4arc1
  exact TauReal.equiv_of_four_mul_equiv _ _ h_chain

/-! ## Reverse direction: MachinSlashFourIdentity → MachinIdentity

  Given `MachinSlashFourIdentity` (`pi_machin_arctan_quarter ≈ arctan(1)`),
  we obtain `MachinIdentity` (`pi_machin_arctan_form ≈ pi`) via:
  1. Scale up by 4: `4·pi_machin_arctan_quarter ≈ 4·arctan(1)`
     (via `four_mul_equiv_of_equiv`).
  2. Use Scope 2D Part 2: `pi_machin_arctan_form ≈ 4·pi_machin_arctan_quarter`.
  3. Use Scope 2B (symm): `4·arctan(1) ≈ pi`.
  4. Chain. -/

theorem MachinSlashFourIdentity_implies_MachinIdentity :
    MachinSlashFourIdentity → MachinIdentity := by
  intro h_slash_four
  unfold MachinSlashFourIdentity at h_slash_four
  -- Scale up
  have h_scaled : ((TauReal.fromTauRat ⟨⟨4, 0⟩, 1, by norm_num⟩).mul
                      TauReal.pi_machin_arctan_quarter).equiv
                   ((TauReal.fromTauRat ⟨⟨4, 0⟩, 1, by norm_num⟩).mul
                      (TauReal.arctan_of_rat_seq TauRat.one_canonical)) :=
    TauReal.four_mul_equiv_of_equiv _ _ h_slash_four
  -- Chain: form ≈ 4·quarter ≈ 4·arctan(1) ≈ pi
  show TauReal.equiv _ TauReal.pi
  have h_form_eq_4q := TauReal.pi_machin_arctan_form_equiv_four_quarter
  have h_pi_eq_4arc1_symm := TauReal.equiv_symm TauReal.pi_equiv_four_arctan_one
  exact TauReal.equiv_trans (TauReal.equiv_trans h_form_eq_4q h_scaled) h_pi_eq_4arc1_symm

/-- **🎯 Phase E Scope 2D headline structural reduction theorem**:

    `MachinIdentity ↔ MachinSlashFourIdentity`.

    The Machin identity `16·arctan(1/5) − 4·arctan(1/239) ≈ pi` is
    logically equivalent to the more compact "/4" form:
    `4·arctan(1/5) − arctan(1/239) ≈ arctan(1)`.

    This completely discharges the structural scaling component of
    MachinIdentity, exposing the residual analytic content as the
    cleanest possible named form. -/
theorem MachinIdentity_iff_MachinSlashFourIdentity :
    MachinIdentity ↔ MachinSlashFourIdentity :=
  ⟨MachinIdentity_implies_MachinSlashFourIdentity,
   MachinSlashFourIdentity_implies_MachinIdentity⟩

-- ============================================================
-- PART 6: KEYSTONE EQUIVALENCE — pi_machin.equiv pi ↔ MachinSlashFourIdentity
-- ============================================================

/-! ## Composition with Scope 2C's bridge

  Combining Scope 2D's structural reduction with Scope 2C's
  `MachinIdentity_iff_pi_machin_equiv_pi`, we obtain the cleanest
  named form of the keystone identity:

  `TauReal.equiv pi_machin pi ↔ MachinSlashFourIdentity`. -/

/-- **🎯 Phase E Scope 2D keystone equivalence**:

    `TauReal.equiv TauReal.pi_machin TauReal.pi ↔ MachinSlashFourIdentity`.

    The keystone identity (`pi_machin.equiv pi`, originally the Wave Γ₇
    Phase 3F target) is logically equivalent to the compact
    `MachinSlashFourIdentity` (`4·arctan(1/5) − arctan(1/239) ≈
    arctan(1)`).

    This means: discharging `MachinSlashFourIdentity` would complete
    the entire τ-native Machin pipeline, including:
    * `MachinIdentity` (via Scope 2D structural reduction)
    * `pi_machin.equiv pi` (via Scope 2C bridge)
    * (Future) the `BBPLeibnizCorrespondence` via `pi_bbp.equiv pi`. -/
theorem pi_machin_equiv_pi_iff_MachinSlashFourIdentity :
    TauReal.equiv TauReal.pi_machin TauReal.pi ↔ MachinSlashFourIdentity := by
  constructor
  · intro h_pi_machin_eq_pi
    apply MachinIdentity_implies_MachinSlashFourIdentity
    exact MachinIdentity_iff_pi_machin_equiv_pi.mpr h_pi_machin_eq_pi
  · intro h_slash_four
    apply MachinIdentity_iff_pi_machin_equiv_pi.mp
    exact MachinSlashFourIdentity_implies_MachinIdentity h_slash_four

-- ============================================================
-- PART 7: RAT-LEVEL DIFFERENCE FORMULATION OF MachinSlashFourIdentity
-- ============================================================

/-! ## Rat-level difference characterisation

  By the `equiv_of_rat_difference_modulus` framework theorem
  (TauRealBBP.lean), TauReal-equivalence at the Cauchy level
  reduces to a Rat-level modulus condition on `.toRat`-differences.
  We expose this characterisation for `MachinSlashFourIdentity`
  to make the residual analytic content fully concrete and
  inspectable. -/

/-- **Rat-level characterisation of MachinSlashFourIdentity**:
    the proposition is equivalent to the existence of a modulus
    such that the Rat-level difference of partial sums is bounded
    appropriately.

    Specifically: if there exists `μ : Nat → Nat` such that for all
    `k n : Nat` with `μ k ≤ n`,
    `|4·arctan_partial_rat(1/5) n − arctan_partial_rat(1/239) n −
      arctan_partial_rat(1) n| < 1/(k+1)`,
    then `MachinSlashFourIdentity` holds.

    Conversely, `MachinSlashFourIdentity` (by definition) implies
    such a modulus exists.

    This characterisation **exposes the residual analytic content
    of MachinSlashFourIdentity as a concrete Rat-level diagonal
    bound condition**, which is the most computation-friendly form
    for future τ-native arctan tail-error analysis. -/
theorem MachinSlashFourIdentity_iff_rat_modulus :
    MachinSlashFourIdentity ↔
    ∃ μ : Nat → Nat, ∀ k n : Nat, μ k ≤ n →
      |(4 * arctan_partial_rat ((1 : Rat) / 5) n - arctan_partial_rat ((1 : Rat) / 239) n)
        - arctan_partial_rat 1 n| < 1 / ((k : Rat) + 1) := by
  unfold MachinSlashFourIdentity
  constructor
  · intro ⟨μ, hμ⟩
    refine ⟨μ, fun k n hkn => ?_⟩
    have h_orig := hμ k n hkn
    unfold TauRat.lt at h_orig
    rw [TauRat.toRat_abs, toRat_sub, TauRat.ofNatRecip_toRat] at h_orig
    -- LHS unfold
    show |(4 * arctan_partial_rat ((1 : Rat) / 5) n - arctan_partial_rat ((1 : Rat) / 239) n)
          - arctan_partial_rat 1 n| < 1 / ((k : Rat) + 1)
    -- Goal: convert to (quarter.approx n).toRat - (arctan_of_rat_seq one_canonical .approx n).toRat
    have h_quarter_toRat :
        (TauReal.pi_machin_arctan_quarter.approx n).toRat
          = 4 * arctan_partial_rat ((1 : Rat) / 5) n - arctan_partial_rat ((1 : Rat) / 239) n := by
      unfold TauReal.pi_machin_arctan_quarter
      show (TauRat.add (TauRat.mul ((TauReal.fromTauRat ⟨⟨4, 0⟩, 1, by norm_num⟩).approx n)
                                ((TauReal.arctan_of_rat_seq TauRat.one_fifth).approx n))
                       (TauRat.negate ((TauReal.arctan_of_rat_seq TauRat.one_two_three_nine).approx n))).toRat
            = _
      rw [toRat_add, toRat_mul, toRat_negate]
      have h_4 : (((TauReal.fromTauRat ⟨⟨4, 0⟩, 1, by norm_num⟩ : TauReal).approx n).toRat
                    : Rat) = 4 := by
        show ((⟨⟨4, 0⟩, 1, by norm_num⟩ : TauRat).toRat : Rat) = 4
        unfold TauRat.toRat
        simp only [TauInt.toInt]
        push_cast
        ring
      rw [h_4]
      rw [TauReal.arctan_of_rat_seq_approx, TauReal.arctan_of_rat_seq_approx]
      rw [TauRat.arctan_partial_toRat, TauRat.arctan_partial_toRat]
      rw [TauRat.one_fifth_toRat, TauRat.one_two_three_nine_toRat]
      ring
    have h_arc1_toRat :
        ((TauReal.arctan_of_rat_seq TauRat.one_canonical).approx n).toRat
          = arctan_partial_rat 1 n := by
      rw [TauReal.arctan_of_rat_seq_approx]
      rw [TauRat.arctan_partial_toRat]
      rw [TauRat.one_canonical_toRat]
    rw [h_quarter_toRat, h_arc1_toRat] at h_orig
    exact h_orig
  · intro ⟨μ, hμ⟩
    apply TauReal.equiv_of_rat_difference_modulus _ _ μ
    intro k n hkn
    have h_diff := hμ k n hkn
    -- Recover the pointwise toRat structure
    have h_quarter_toRat :
        (TauReal.pi_machin_arctan_quarter.approx n).toRat
          = 4 * arctan_partial_rat ((1 : Rat) / 5) n - arctan_partial_rat ((1 : Rat) / 239) n := by
      unfold TauReal.pi_machin_arctan_quarter
      show (TauRat.add (TauRat.mul ((TauReal.fromTauRat ⟨⟨4, 0⟩, 1, by norm_num⟩).approx n)
                                ((TauReal.arctan_of_rat_seq TauRat.one_fifth).approx n))
                       (TauRat.negate ((TauReal.arctan_of_rat_seq TauRat.one_two_three_nine).approx n))).toRat
            = _
      rw [toRat_add, toRat_mul, toRat_negate]
      have h_4 : (((TauReal.fromTauRat ⟨⟨4, 0⟩, 1, by norm_num⟩ : TauReal).approx n).toRat
                    : Rat) = 4 := by
        show ((⟨⟨4, 0⟩, 1, by norm_num⟩ : TauRat).toRat : Rat) = 4
        unfold TauRat.toRat
        simp only [TauInt.toInt]
        push_cast
        ring
      rw [h_4]
      rw [TauReal.arctan_of_rat_seq_approx, TauReal.arctan_of_rat_seq_approx]
      rw [TauRat.arctan_partial_toRat, TauRat.arctan_partial_toRat]
      rw [TauRat.one_fifth_toRat, TauRat.one_two_three_nine_toRat]
      ring
    have h_arc1_toRat :
        ((TauReal.arctan_of_rat_seq TauRat.one_canonical).approx n).toRat
          = arctan_partial_rat 1 n := by
      rw [TauReal.arctan_of_rat_seq_approx]
      rw [TauRat.arctan_partial_toRat]
      rw [TauRat.one_canonical_toRat]
    rw [h_quarter_toRat, h_arc1_toRat]
    exact h_diff

/-! ## Path forward to the full keystone

  With Scope 2D shipped, the structural pipeline from F.2 / B.3 /
  Phase B/C/D/E/2A/2B/2C/2D is complete in its non-analytic content.
  The single remaining target is `MachinSlashFourIdentity`:

  >  `4·arctan(1/5) − arctan(1/239) ≈ arctan(1)` (at TauReal level).

  Equivalently (by `MachinSlashFourIdentity_iff_rat_modulus`), the
  residual analytic content is the **explicit Rat-level modulus**:

  >  `∃ μ, ∀ k n, μ k ≤ n →
  >     |4·arctan_partial(1/5, n) − arctan_partial(1/239, n) − arctan_partial(1, n)|
  >       < 1/(k+1)`.

  Candidate paths for Phase F:

  **Path F.A (cisTauReal injectivity)** — lift the Scope 2A-lift
  45°-line identity (`(cisA⁴ · ⟨cisB.re, -cisB.im⟩).re ≈ .im`)
  to angle equality via principal-branch injectivity of cisTauReal.
  This is the orthodox classical proof structure (cf. Mathlib's
  `Real.arctan` development), requiring τ-native principal-branch
  arctan injectivity.

  **Path F.B (direct partial-sum analysis)** — bound the differences
  `|4·arctan_partial(1/5, n) − arctan_partial(1/239, n) − arctan_partial(1, n)|`
  at finite depth n. Classically the limit is 0 (the Machin identity),
  but finite-depth bounds require the classical identity. May fall
  back to a programme axiom.

  Both paths are independent deep infrastructure (Phase F concerns).
  Scope 2D's contribution: makes the residual content **as compact
  as possible**, eliminating all structural-scaling weight and
  exposing the bare Rat-level modulus condition.
-/

end Tau.Boundary
