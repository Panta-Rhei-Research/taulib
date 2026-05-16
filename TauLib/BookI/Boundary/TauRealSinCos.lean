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

-- ============================================================
-- PART 4: NAMED TARGETS for Euler bridge + sin/cos addition formulae
-- ============================================================

/-! ## Phase 1C-1D — Named targets (recursive discharge pattern)

The Euler bridge `(exp (pureIm x)).re ≈ cos_of_rat x, .im ≈ sin_of_rat x`
and the resulting sin/cos addition formulae are queued for focused
follow-up commits. They are stated here as **named target propositions**
(per the `named-target-discharge-pattern` from atlas/insights), which
allows downstream consumers to assume them while the discharge is
underway.

The named-target pattern has been validated 10+ times in the τ-canon
programme; each target is paired with a conditional theorem that
discharges when the target is later proved. -/

/-- **[I.D-EulerRe-Target]** The Euler bridge for the real part.

    For `|x.toRat| ≤ 1`, the real part of `exp(i·x)` matches the τ-native
    cosine series `TauReal.cos_of_rat x` as TauReal equivalence.

    **Discharge strategy** (Phase 1C, queued): expand
    `(exp (pureIm x)).re.approx n = (exp_partial (pureIm x) n).re.approx n`
    via the diagonal construction, then use the cyclotomic-4 cycle
    (Phase 1A) to identify even-power terms with `cos_partial` paired
    sums. Modulus `k + 3` follows the standard Cauchy-bound template. -/
def TauComplex.exp_pureIm_re_eq_cos_target : Prop :=
  ∀ (x : TauRat), |x.toRat| ≤ 1 →
    TauReal.equiv (TauComplex.exp (TauComplex.pureIm x)).re (TauReal.cos_of_rat x)

/-- **[I.D-EulerIm-Target]** The Euler bridge for the imaginary part.

    For `|x.toRat| ≤ 1`, the imaginary part of `exp(i·x)` matches the
    τ-native sine series `TauReal.sin_of_rat x` as TauReal equivalence.

    Discharge strategy parallel to `exp_pureIm_re_eq_cos_target`, using
    the cyclotomic-4 cycle to identify odd-power terms with `sin_partial`
    paired sums. -/
def TauComplex.exp_pureIm_im_eq_sin_target : Prop :=
  ∀ (x : TauRat), |x.toRat| ≤ 1 →
    TauReal.equiv (TauComplex.exp (TauComplex.pureIm x)).im (TauReal.sin_of_rat x)

/-- **[I.D-CosAdd-Target]** Cosine addition formula.

    For `|x₁.toRat|, |x₂.toRat| ≤ 1` (Machin's formula uses arguments
    `arctan(1/5) ≈ 0.197` and `arctan(1/239) ≈ 0.004`, well within bounds),
    `cos(x₁+x₂) ≈ cos x₁ · cos x₂ − sin x₁ · sin x₂`.

    **Conditional discharge** (queued): given
    `exp_pureIm_re_eq_cos_target ∧ exp_pureIm_im_eq_sin_target`, derive
    from `TauComplex.exp_add` applied to `pureIm x₁` and `pureIm x₂`,
    then project to `.re` via componentwise `TauReal.equiv`. -/
def TauComplex.cos_add_target : Prop :=
  ∀ (x₁ x₂ : TauRat), |x₁.toRat| ≤ 1 → |x₂.toRat| ≤ 1 →
    TauReal.equiv (TauReal.cos_of_rat (x₁.add x₂))
                  ((TauReal.cos_of_rat x₁).mul (TauReal.cos_of_rat x₂)
                    |>.sub ((TauReal.sin_of_rat x₁).mul (TauReal.sin_of_rat x₂)))

/-- **[I.D-SinAdd-Target]** Sine addition formula.

    `sin(x₁+x₂) ≈ sin x₁ · cos x₂ + cos x₁ · sin x₂`. -/
def TauComplex.sin_add_target : Prop :=
  ∀ (x₁ x₂ : TauRat), |x₁.toRat| ≤ 1 → |x₂.toRat| ≤ 1 →
    TauReal.equiv (TauReal.sin_of_rat (x₁.add x₂))
                  ((TauReal.sin_of_rat x₁).mul (TauReal.cos_of_rat x₂)
                    |>.add ((TauReal.cos_of_rat x₁).mul (TauReal.sin_of_rat x₂)))

-- ============================================================
-- PART 5: CYCLOTOMIC-4 STRUCTURE OF (pureIm x).pow k AT toRat LEVEL
-- ============================================================

/-! ## Phase 1C — Cyclotomic-4 structural lemmas for `(pureIm x).pow k`

For `pureIm x = ⟨0, x⟩` (the τ-canon lift of `i · x`), iterated powers cycle
at TauRat-toRat level through the four-element pattern:

  k % 4 = 0  →  .re_toRat =  x^k,   .im_toRat =  0
  k % 4 = 1  →  .re_toRat =  0,     .im_toRat =  x^k
  k % 4 = 2  →  .re_toRat = -x^k,   .im_toRat =  0
  k % 4 = 3  →  .re_toRat =  0,     .im_toRat = -x^k

The recurrence underneath, via `TauComplex.mul (pow k) (pureIm x)` expansion
+ the rfl simp lemmas `pureIm_re_approx`/`pureIm_im_approx`, is:

  (r_(k+1), i_(k+1)) = (-i_k · x.toRat, r_k · x.toRat)

with base `(r_0, i_0) = (1, 0)` from `TauComplex.one = ⟨TauReal.one, TauReal.zero⟩`.

The cyclotomic-4 closed form follows by `k = 4j+r` case analysis (Part 5b). -/

/-- **[I.D-PureImPow-RatPair]** Recurrence-defined Rat-level expected pair
    `(r_k, i_k)` for the `.re_toRat`/`.im_toRat` of `((pureIm x).pow k)` at
    any TauRat approximation depth. -/
def pureIm_pow_re_im_rat (xR : Rat) : Nat → Rat × Rat
  | 0     => (1, 0)
  | k + 1 =>
    let p := pureIm_pow_re_im_rat xR k
    (-p.2 * xR, p.1 * xR)

@[simp] theorem pureIm_pow_re_im_rat_zero (xR : Rat) :
    pureIm_pow_re_im_rat xR 0 = (1, 0) := rfl

@[simp] theorem pureIm_pow_re_im_rat_succ (xR : Rat) (k : Nat) :
    pureIm_pow_re_im_rat xR (k+1)
      = (-(pureIm_pow_re_im_rat xR k).2 * xR,
         (pureIm_pow_re_im_rat xR k).1 * xR) := rfl

/-- **[I.T-PureImPow-Recurrence-Re]** The .re-toRat of `((pureIm x).pow (k+1))`
    equals `-(.im-toRat of (pureIm x).pow k) · x.toRat`.

    Unfolds `TauComplex.mul` + `pureIm_re_approx`/`pureIm_im_approx` (rfl
    simp lemmas) + toRat operations. -/
theorem pureIm_pow_succ_re_approx_toRat (x : TauRat) (k n : Nat) :
    (((TauComplex.pureIm x).pow (k+1)).re.approx n).toRat
      = -(((TauComplex.pureIm x).pow k).im.approx n).toRat * x.toRat := by
  -- pow (k+1) = (pow k).mul (pureIm x) by pow_succ (rfl)
  -- (a.mul b).re.approx n = TauRat.sub (mul a.re.approx n b.re.approx n)
  --                                    (mul a.im.approx n b.im.approx n)
  -- by unfolding TauComplex.mul + TauReal.sub/mul defs
  show (TauRat.sub
          (TauRat.mul (((TauComplex.pureIm x).pow k).re.approx n)
                      ((TauComplex.pureIm x).re.approx n))
          (TauRat.mul (((TauComplex.pureIm x).pow k).im.approx n)
                      ((TauComplex.pureIm x).im.approx n))).toRat
       = -(((TauComplex.pureIm x).pow k).im.approx n).toRat * x.toRat
  rw [TauComplex.pureIm_re_approx, TauComplex.pureIm_im_approx,
      toRat_sub, toRat_mul, toRat_mul, toRat_zero]
  ring

/-- **[I.T-PureImPow-Recurrence-Im]** The .im-toRat of `((pureIm x).pow (k+1))`
    equals `(.re-toRat of (pureIm x).pow k) · x.toRat`. -/
theorem pureIm_pow_succ_im_approx_toRat (x : TauRat) (k n : Nat) :
    (((TauComplex.pureIm x).pow (k+1)).im.approx n).toRat
      = (((TauComplex.pureIm x).pow k).re.approx n).toRat * x.toRat := by
  show (TauRat.add
          (TauRat.mul (((TauComplex.pureIm x).pow k).re.approx n)
                      ((TauComplex.pureIm x).im.approx n))
          (TauRat.mul (((TauComplex.pureIm x).pow k).im.approx n)
                      ((TauComplex.pureIm x).re.approx n))).toRat
       = (((TauComplex.pureIm x).pow k).re.approx n).toRat * x.toRat
  rw [TauComplex.pureIm_re_approx, TauComplex.pureIm_im_approx,
      toRat_add, toRat_mul, toRat_mul, toRat_zero]
  ring

/-- **[I.T-PureImPow-Base-Re]** The .re-toRat of `((pureIm x).pow 0) = 1`. -/
theorem pureIm_pow_zero_re_approx_toRat (x : TauRat) (n : Nat) :
    (((TauComplex.pureIm x).pow 0).re.approx n).toRat = 1 := by
  show ((TauReal.one).approx n).toRat = 1
  show (TauRat.one).toRat = 1
  exact toRat_one

/-- **[I.T-PureImPow-Base-Im]** The .im-toRat of `((pureIm x).pow 0) = 0`. -/
theorem pureIm_pow_zero_im_approx_toRat (x : TauRat) (n : Nat) :
    (((TauComplex.pureIm x).pow 0).im.approx n).toRat = 0 := by
  show ((TauReal.zero).approx n).toRat = 0
  show (TauRat.zero).toRat = 0
  exact toRat_zero

/-- **[I.T-PureImPow-Bridge]** `((pureIm x).pow k).re.approx n .toRat` and
    `.im.approx n .toRat` match the recurrence pair `pureIm_pow_re_im_rat`.

    Joint induction on k using the recurrence theorems + base cases. -/
theorem pureIm_pow_re_im_approx_toRat (x : TauRat) (k n : Nat) :
    (((TauComplex.pureIm x).pow k).re.approx n).toRat
      = (pureIm_pow_re_im_rat x.toRat k).1 ∧
    (((TauComplex.pureIm x).pow k).im.approx n).toRat
      = (pureIm_pow_re_im_rat x.toRat k).2 := by
  induction k with
  | zero =>
    refine ⟨?_, ?_⟩
    · rw [pureIm_pow_zero_re_approx_toRat]; rfl
    · rw [pureIm_pow_zero_im_approx_toRat]; rfl
  | succ k IH =>
    obtain ⟨ih_re, ih_im⟩ := IH
    refine ⟨?_, ?_⟩
    · rw [pureIm_pow_succ_re_approx_toRat, ih_im, pureIm_pow_re_im_rat_succ]
    · rw [pureIm_pow_succ_im_approx_toRat, ih_re, pureIm_pow_re_im_rat_succ]

-- ============================================================
-- PART 5b: CYCLOTOMIC-4 CLOSED FORMS for pureIm_pow_re_im_rat
-- ============================================================

/-- Helper: one-step recurrence with explicit Prod components.

    `pair (k+1) = (-i_k · xR, r_k · xR)` where `(r_k, i_k) = pair k`. -/
private theorem pair_succ_eq_iff (xR : Rat) (k : Nat) (a b : Rat)
    (h : pureIm_pow_re_im_rat xR k = (a, b)) :
    pureIm_pow_re_im_rat xR (k+1) = (-b * xR, a * xR) := by
  rw [pureIm_pow_re_im_rat_succ, h]

/-- **[I.T-PureImPow-Closed-4j]** The four-step closed form of the
    `pureIm_pow_re_im_rat` recurrence, proved by simultaneous induction on j.

    At indices `4j, 4j+1, 4j+2, 4j+3` the recurrence cycles through:
        (xR^(4j), 0)  →  (0, xR^(4j+1))  →  (-xR^(4j+2), 0)  →  (0, -xR^(4j+3))
    and the next 4-step begins with `(xR^(4(j+1)), 0)`. -/
theorem pureIm_pow_re_im_rat_cyclo4 (xR : Rat) (j : Nat) :
    pureIm_pow_re_im_rat xR (4*j) = (xR^(4*j), 0) ∧
    pureIm_pow_re_im_rat xR (4*j+1) = (0, xR^(4*j+1)) ∧
    pureIm_pow_re_im_rat xR (4*j+2) = (-(xR^(4*j+2)), 0) ∧
    pureIm_pow_re_im_rat xR (4*j+3) = (0, -(xR^(4*j+3))) := by
  induction j with
  | zero =>
    refine ⟨?_, ?_, ?_, ?_⟩
    · show pureIm_pow_re_im_rat xR 0 = (xR^0, 0)
      rw [pureIm_pow_re_im_rat_zero, pow_zero]
    · show pureIm_pow_re_im_rat xR 1 = (0, xR^1)
      rw [pair_succ_eq_iff xR 0 1 0 (by rw [pureIm_pow_re_im_rat_zero])]
      ext <;> simp <;> ring
    · show pureIm_pow_re_im_rat xR 2 = (-(xR^2), 0)
      have h1 : pureIm_pow_re_im_rat xR 1 = (0, xR^1) := by
        rw [pair_succ_eq_iff xR 0 1 0 (by rw [pureIm_pow_re_im_rat_zero])]
        ext <;> simp <;> ring
      rw [pair_succ_eq_iff xR 1 0 (xR^1) h1]
      ext <;> simp <;> ring
    · show pureIm_pow_re_im_rat xR 3 = (0, -(xR^3))
      have h1 : pureIm_pow_re_im_rat xR 1 = (0, xR^1) := by
        rw [pair_succ_eq_iff xR 0 1 0 (by rw [pureIm_pow_re_im_rat_zero])]
        ext <;> simp <;> ring
      have h2 : pureIm_pow_re_im_rat xR 2 = (-(xR^2), 0) := by
        rw [pair_succ_eq_iff xR 1 0 (xR^1) h1]
        ext <;> simp <;> ring
      rw [pair_succ_eq_iff xR 2 (-(xR^2)) 0 h2]
      ext <;> simp <;> ring
  | succ j IH =>
    obtain ⟨h0, h1, h2, h3⟩ := IH
    -- Build h4, h5, h6, h7 via the one-step recurrence helper.
    have h4 : pureIm_pow_re_im_rat xR (4*j+4) = (xR^(4*j+4), 0) := by
      have step : 4*j+4 = (4*j+3)+1 := by ring
      rw [step, pair_succ_eq_iff xR (4*j+3) 0 (-(xR^(4*j+3))) h3]
      ext <;> simp <;> ring
    have h5 : pureIm_pow_re_im_rat xR (4*j+5) = (0, xR^(4*j+5)) := by
      have step : 4*j+5 = (4*j+4)+1 := by ring
      rw [step, pair_succ_eq_iff xR (4*j+4) (xR^(4*j+4)) 0 h4]
      ext <;> simp <;> ring
    have h6 : pureIm_pow_re_im_rat xR (4*j+6) = (-(xR^(4*j+6)), 0) := by
      have step : 4*j+6 = (4*j+5)+1 := by ring
      rw [step, pair_succ_eq_iff xR (4*j+5) 0 (xR^(4*j+5)) h5]
      ext <;> simp <;> ring
    have h7 : pureIm_pow_re_im_rat xR (4*j+7) = (0, -(xR^(4*j+7))) := by
      have step : 4*j+7 = (4*j+6)+1 := by ring
      rw [step, pair_succ_eq_iff xR (4*j+6) (-(xR^(4*j+6))) 0 h6]
      ext <;> simp <;> ring
    refine ⟨?_, ?_, ?_, ?_⟩
    · show pureIm_pow_re_im_rat xR (4*(j+1)) = (xR^(4*(j+1)), 0)
      rw [show 4*(j+1) = 4*j+4 from by ring, h4]
    · show pureIm_pow_re_im_rat xR (4*(j+1)+1) = (0, xR^(4*(j+1)+1))
      rw [show 4*(j+1)+1 = 4*j+5 from by ring, h5]
    · show pureIm_pow_re_im_rat xR (4*(j+1)+2) = (-(xR^(4*(j+1)+2)), 0)
      rw [show 4*(j+1)+2 = 4*j+6 from by ring, h6]
    · show pureIm_pow_re_im_rat xR (4*(j+1)+3) = (0, -(xR^(4*(j+1)+3)))
      rw [show 4*(j+1)+3 = 4*j+7 from by ring, h7]

-- ============================================================
-- PART 6: exp_term (pureIm x) k AT toRat LEVEL
-- ============================================================

/-- **[I.T-ExpTerm-PureIm-Re]** The real-part of `exp_term (pureIm x) k`'s
    n-th TauRat approximation, at toRat level: cyclotomic-4 pair's `.1`
    component divided by `k!`. -/
theorem exp_term_pureIm_re_approx_toRat (x : TauRat) (k n : Nat) :
    ((TauComplex.exp_term (TauComplex.pureIm x) k).re.approx n).toRat
      = (pureIm_pow_re_im_rat x.toRat k).1 / (k.factorial : Rat) := by
  rw [TauComplex.exp_term_re, TauReal.scale_by_inv_factorial_approx,
      TauRat.scale_by_inv_factorial_toRat,
      (pureIm_pow_re_im_approx_toRat x k n).1]

/-- **[I.T-ExpTerm-PureIm-Im]** The imaginary-part of `exp_term (pureIm x) k`'s
    n-th TauRat approximation, at toRat level: cyclotomic-4 pair's `.2`
    component divided by `k!`. -/
theorem exp_term_pureIm_im_approx_toRat (x : TauRat) (k n : Nat) :
    ((TauComplex.exp_term (TauComplex.pureIm x) k).im.approx n).toRat
      = (pureIm_pow_re_im_rat x.toRat k).2 / (k.factorial : Rat) := by
  rw [TauComplex.exp_term_im, TauReal.scale_by_inv_factorial_approx,
      TauRat.scale_by_inv_factorial_toRat,
      (pureIm_pow_re_im_approx_toRat x k n).2]

-- ============================================================
-- PART 7: Rat-LEVEL INTERMEDIATE + ALIGNMENT AT DEPTH 4m
-- ============================================================

/-- **[I.D-ExpPartial-PureIm-Re-Rat]** Rat-level intermediate for
    `((exp_partial (pureIm x) k).re.approx _).toRat`.

    Recursively defined from `pureIm_pow_re_im_rat` divided by `k!`. The
    bridge theorem below shows this matches the actual TauReal-level value
    at any approximation depth. -/
def expPartial_pureIm_re_rat (xR : Rat) : Nat → Rat
  | 0     => 0
  | k + 1 => expPartial_pureIm_re_rat xR k
              + (pureIm_pow_re_im_rat xR k).1 / (k.factorial : Rat)

@[simp] theorem expPartial_pureIm_re_rat_zero (xR : Rat) :
    expPartial_pureIm_re_rat xR 0 = 0 := rfl

@[simp] theorem expPartial_pureIm_re_rat_succ (xR : Rat) (k : Nat) :
    expPartial_pureIm_re_rat xR (k+1)
      = expPartial_pureIm_re_rat xR k
          + (pureIm_pow_re_im_rat xR k).1 / (k.factorial : Rat) := rfl

/-- **[I.T-ExpPartial-PureIm-Re-Bridge]** Bridge to TauReal: the
    `((exp_partial (pureIm x) k).re.approx m_a).toRat` matches the Rat
    intermediate at any approximation depth `m_a`. -/
theorem expPartial_pureIm_re_approx_toRat_eq_rat (x : TauRat) (k m_a : Nat) :
    ((TauComplex.exp_partial (TauComplex.pureIm x) k).re.approx m_a).toRat
      = expPartial_pureIm_re_rat x.toRat k := by
  induction k with
  | zero =>
    show ((TauComplex.exp_partial (TauComplex.pureIm x) 0).re.approx m_a).toRat
        = expPartial_pureIm_re_rat x.toRat 0
    rw [TauComplex.exp_partial_zero, expPartial_pureIm_re_rat_zero]
    -- (TauComplex.zero).re.approx m_a = (TauReal.zero).approx m_a = TauRat.zero
    show (TauRat.zero).toRat = 0
    exact toRat_zero
  | succ k IH =>
    show ((TauComplex.exp_partial (TauComplex.pureIm x) (k+1)).re.approx m_a).toRat
        = expPartial_pureIm_re_rat x.toRat (k+1)
    rw [TauComplex.exp_partial_succ, expPartial_pureIm_re_rat_succ]
    -- LHS now: ((exp_partial _ k).add (exp_term _ k)).re.approx m_a .toRat
    -- (a.add b).re.approx m_a = TauRat.add (a.re.approx m_a) (b.re.approx m_a) by def
    show (TauRat.add
            ((TauComplex.exp_partial (TauComplex.pureIm x) k).re.approx m_a)
            ((TauComplex.exp_term (TauComplex.pureIm x) k).re.approx m_a)).toRat
        = expPartial_pureIm_re_rat x.toRat k
          + (pureIm_pow_re_im_rat x.toRat k).1 / (k.factorial : Rat)
    rw [toRat_add, IH, exp_term_pureIm_re_approx_toRat]

/-- **[I.T-ExpPartial-PureIm-Re-Rat-At-4m]** At Rat-level depth `4m`, the
    intermediate `expPartial_pureIm_re_rat` equals `cos_partial_rat`.

    Cyclotomic-4 closed-form alignment with the τ-native paired-cosine
    series: at every 4-step the recurrence picks up one `cos_pair_term`. -/
theorem expPartial_pureIm_re_rat_at_4m (xR : Rat) (m : Nat) :
    expPartial_pureIm_re_rat xR (4*m) = cos_partial_rat xR m := by
  induction m with
  | zero => rfl
  | succ m IH =>
    show expPartial_pureIm_re_rat xR (4*(m+1)) = cos_partial_rat xR (m+1)
    have hstep : 4*(m+1) = ((((4*m)+1)+1)+1)+1 := by ring
    rw [hstep, expPartial_pureIm_re_rat_succ, expPartial_pureIm_re_rat_succ,
        expPartial_pureIm_re_rat_succ, expPartial_pureIm_re_rat_succ, IH]
    -- Now expanded form has 4 terms: cos_partial_rat xR m + (pair (4m)).1/(4m)!
    --   + (pair (4m+1)).1/(4m+1)! + (pair (4m+2)).1/(4m+2)! + (pair (4m+3)).1/(4m+3)!
    -- Substitute cyclotomic-4 closed forms.
    obtain ⟨h0, h1, h2, h3⟩ := pureIm_pow_re_im_rat_cyclo4 xR m
    rw [h0, h1, h2, h3]
    -- Now: cos_partial_rat xR m + xR^(4m)/(4m)! + 0/(4m+1)! + (-xR^(4m+2))/(4m+2)! + 0/(4m+3)!
    -- RHS: cos_partial_rat xR (m+1) = cos_partial_rat xR m + cos_pair_term_rat xR m
    --    = cos_partial_rat xR m + xR^(4m)/(4m)! - xR^(4m+2)/(4m+2)!
    rw [cos_partial_rat_succ]
    -- Unfold cos_pair_term_rat
    unfold cos_pair_term_rat
    -- Goal: cos_partial_rat + xR^4m/(4m)! + 0/(4m+1)! + (-xR^(4m+2))/(4m+2)! + 0/(4m+3)!
    --     = cos_partial_rat + (xR^(4m)/(4m)! - xR^(4m+2)/(4m+2)!)
    -- Simplify Prod.fst on RHS of cyclo4 substitutions then ring
    simp only [Prod.fst, Prod.snd]
    ring

/-- **[I.T-ExpPartial-PureIm-Re-At-4m]** The TauReal-level alignment at
    depth `4m`: the `(exp_partial (pureIm x) (4m)).re.approx m_a` at toRat
    level equals `cos_partial_rat x.toRat m`. -/
theorem exp_partial_pureIm_re_approx_toRat_at_4m (x : TauRat) (m m_a : Nat) :
    ((TauComplex.exp_partial (TauComplex.pureIm x) (4*m)).re.approx m_a).toRat
      = cos_partial_rat x.toRat m := by
  rw [expPartial_pureIm_re_approx_toRat_eq_rat, expPartial_pureIm_re_rat_at_4m]

-- ============================================================
-- PART 8: MAGNITUDE + FACTORIAL HELPERS
-- ============================================================

/-- **Helper**: `(4m)! ≥ 2^m`. The 4 factors `(4m+1), (4m+2), (4m+3), (4m+4)`
    multiply to at least 2, while `2^m` doubles per step. Used to bound the
    residual in the Cauchy modulus discharge. -/
theorem factorial_4m_ge_two_pow_m (m : Nat) : 2^m ≤ Nat.factorial (4*m) := by
  induction m with
  | zero => simp
  | succ m ih =>
    have h_4mp1 : 4*(m+1) = 4*m + 4 := by ring
    have h_step : Nat.factorial (4*(m+1))
                = (4*m+4) * ((4*m+3) * ((4*m+2) * ((4*m+1) * Nat.factorial (4*m)))) := by
      rw [h_4mp1]
      rw [show 4*m+4 = (4*m+3)+1 from rfl, Nat.factorial_succ,
          show 4*m+3 = (4*m+2)+1 from rfl, Nat.factorial_succ,
          show 4*m+2 = (4*m+1)+1 from rfl, Nat.factorial_succ,
          show 4*m+1 = (4*m)+1 from rfl, Nat.factorial_succ]
    have h_prod_ge_2 : (2 : Nat) ≤ (4*m+4) * ((4*m+3) * ((4*m+2) * (4*m+1))) := by
      have h_inner_pos : 0 < (4*m+3) * ((4*m+2) * (4*m+1)) := by positivity
      have h_inner_ge_1 : 1 ≤ (4*m+3) * ((4*m+2) * (4*m+1)) := h_inner_pos
      have h_4_ge : 2 ≤ 4*m+4 := by omega
      calc (2 : Nat) = 2 * 1 := by ring
        _ ≤ (4*m+4) * ((4*m+3) * ((4*m+2) * (4*m+1))) :=
            Nat.mul_le_mul h_4_ge h_inner_ge_1
    have h_assoc : (4*m+4) * ((4*m+3) * ((4*m+2) * ((4*m+1) * Nat.factorial (4*m))))
                 = ((4*m+4) * ((4*m+3) * ((4*m+2) * (4*m+1)))) * Nat.factorial (4*m) := by
      ring
    calc 2^(m+1)
        = 2 * 2^m := by ring
      _ ≤ 2 * Nat.factorial (4*m) := Nat.mul_le_mul_left 2 ih
      _ ≤ ((4*m+4) * ((4*m+3) * ((4*m+2) * (4*m+1)))) * Nat.factorial (4*m) :=
          Nat.mul_le_mul_right _ h_prod_ge_2
      _ = (4*m+4) * ((4*m+3) * ((4*m+2) * ((4*m+1) * Nat.factorial (4*m)))) := h_assoc.symm
      _ = Nat.factorial (4*(m+1)) := h_step.symm

/-- **Helper**: joint magnitude bound `|(pair k).{1,2}| ≤ |xR|^k`,
    by joint induction on k using the cyclotomic-4 recurrence. -/
theorem pureIm_pow_re_im_rat_abs_le_pow (xR : Rat) (k : Nat) :
    |(pureIm_pow_re_im_rat xR k).1| ≤ |xR|^k ∧
    |(pureIm_pow_re_im_rat xR k).2| ≤ |xR|^k := by
  induction k with
  | zero =>
    refine ⟨?_, ?_⟩
    · show |(1 : Rat)| ≤ |xR|^0; simp
    · show |(0 : Rat)| ≤ |xR|^0; simp
  | succ k IH =>
    obtain ⟨ih_re, ih_im⟩ := IH
    refine ⟨?_, ?_⟩
    · show |(-(pureIm_pow_re_im_rat xR k).2 * xR)| ≤ |xR|^(k+1)
      rw [abs_mul, abs_neg, pow_succ]
      exact mul_le_mul ih_im le_rfl (abs_nonneg _) (by positivity)
    · show |((pureIm_pow_re_im_rat xR k).1 * xR)| ≤ |xR|^(k+1)
      rw [abs_mul, pow_succ]
      exact mul_le_mul ih_re le_rfl (abs_nonneg _) (by positivity)

/-- Corollary: under `|xR| ≤ 1`, `|(pair k).1| ≤ 1`. -/
theorem pureIm_pow_re_im_rat_re_abs_le_one (xR : Rat) (hxR : |xR| ≤ 1) (k : Nat) :
    |(pureIm_pow_re_im_rat xR k).1| ≤ 1 := by
  have h := (pureIm_pow_re_im_rat_abs_le_pow xR k).1
  have h_pow_one : |xR|^k ≤ 1 := pow_le_one₀ (abs_nonneg _) hxR
  linarith

-- ============================================================
-- PART 9: RESIDUAL BOUND
-- ============================================================

/-- **Residual bound**: at depth `4m + r` with `r ≤ 3`, the difference from
    the alignment value `cos_partial_rat xR m` is bounded by `r/(4m)!`.

    Proof: induction on r. At each step, `expPartial_succ` peels off one
    `(pair (4m+r)).1 / (4m+r)!` term, bounded by `1/(4m)!`. -/
theorem expPartial_pureIm_re_rat_residual_le (xR : Rat) (hxR : |xR| ≤ 1)
    (m r : Nat) (hr : r ≤ 3) :
    |expPartial_pureIm_re_rat xR (4*m + r) - cos_partial_rat xR m|
      ≤ (r : Rat) / (Nat.factorial (4*m) : Rat) := by
  induction r with
  | zero =>
    have h_fac_pos : (0 : Rat) < (Nat.factorial (4*m) : Rat) := by
      have := Nat.factorial_pos (4*m); exact_mod_cast this
    rw [Nat.add_zero, expPartial_pureIm_re_rat_at_4m, sub_self, abs_zero,
        Nat.cast_zero, zero_div]
  | succ r ih =>
    have hr_le : r ≤ 3 := by omega
    have ih' := ih hr_le
    have h_step : 4*m + (r+1) = (4*m + r) + 1 := by ring
    rw [h_step, expPartial_pureIm_re_rat_succ]
    -- LHS = (expPartial (4m+r) + (pair (4m+r)).1 / (4m+r)!) - cos_partial m
    --     = (expPartial (4m+r) - cos_partial m) + (pair (4m+r)).1 / (4m+r)!
    have rearr : expPartial_pureIm_re_rat xR (4*m + r)
                  + (pureIm_pow_re_im_rat xR (4*m + r)).1 / (Nat.factorial (4*m + r) : Rat)
                  - cos_partial_rat xR m
                = (expPartial_pureIm_re_rat xR (4*m + r) - cos_partial_rat xR m)
                  + (pureIm_pow_re_im_rat xR (4*m + r)).1 / (Nat.factorial (4*m + r) : Rat) := by
      ring
    rw [rearr]
    have h_tri := abs_add_le
      (expPartial_pureIm_re_rat xR (4*m + r) - cos_partial_rat xR m)
      ((pureIm_pow_re_im_rat xR (4*m + r)).1 / (Nat.factorial (4*m + r) : Rat))
    -- Bound the second piece: |term| ≤ 1/(4m+r)! ≤ 1/(4m)!
    have h_fac_pos_4m : (0 : Rat) < (Nat.factorial (4*m) : Rat) := by
      have := Nat.factorial_pos (4*m); exact_mod_cast this
    have h_fac_pos_4mr : (0 : Rat) < (Nat.factorial (4*m + r) : Rat) := by
      have := Nat.factorial_pos (4*m + r); exact_mod_cast this
    have h_fac_le : (Nat.factorial (4*m) : Rat) ≤ (Nat.factorial (4*m + r) : Rat) := by
      have := Nat.factorial_le (show 4*m ≤ 4*m + r by omega); exact_mod_cast this
    have h_term_abs :
        |(pureIm_pow_re_im_rat xR (4*m + r)).1 / (Nat.factorial (4*m + r) : Rat)|
          ≤ 1 / (Nat.factorial (4*m) : Rat) := by
      rw [abs_div, abs_of_pos h_fac_pos_4mr]
      rw [div_le_div_iff₀ h_fac_pos_4mr h_fac_pos_4m]
      have h_num : |(pureIm_pow_re_im_rat xR (4*m + r)).1| ≤ 1 :=
        pureIm_pow_re_im_rat_re_abs_le_one xR hxR (4*m + r)
      nlinarith
    have h_sum : (r : Rat) / (Nat.factorial (4*m) : Rat) + 1 / (Nat.factorial (4*m) : Rat)
              = ((r + 1 : Nat) : Rat) / (Nat.factorial (4*m) : Rat) := by
      push_cast; field_simp
    linarith

-- ============================================================
-- PART 10: 🎯 CAUCHY MODULUS DISCHARGE — exp_pureIm_re_eq_cos
-- ============================================================

/-- **🎯 [I.T-EulerRe]** The Euler bridge for `.re`: for `|x.toRat| ≤ 1`,
    `(TauComplex.exp (pureIm x)).re ≈ TauReal.cos_of_rat x` at TauReal
    equivalence level.

    **Modulus**: `λ k => 8*k + 19`. For `n ≥ 8k+19`, decompose `n = 4m + r`
    with `m = n/4 ≥ 2k+4` and `r ≤ 3`.

    **Bound assembly**:
    * Residual: `|expPartial xR (4m+r) − Cp(m)| ≤ r/(4m)! ≤ 3/(4m)! ≤ 4/2^m`
      (using `(4m)! ≥ 2^m`).
    * Cos tail: `|Cp(m) − Cp(n)| ≤ 4/2^m` (`cos_partial_rat_cauchy_bound`).
    * Each ≤ `4/2^m < 1/(2(k+1))` for `m ≥ 2k+4` (apply `Rat.four_div_two_pow_lt_recip`
      with shifted index `2k+1`).
    * Triangle: total `< 2 · 1/(2(k+1)) = 1/(k+1)`. -/
theorem exp_pureIm_re_eq_cos (x : TauRat) (hx : |x.toRat| ≤ 1) :
    TauReal.equiv (TauComplex.exp (TauComplex.pureIm x)).re (TauReal.cos_of_rat x) := by
  refine ⟨fun k => 8*k + 19, fun k n hn => ?_⟩
  -- hn : 8*k + 19 ≤ n. Decompose n = 4m + r with m ≥ 2k+4, r ≤ 3.
  have hr_lt : n % 4 < 4 := Nat.mod_lt n (by norm_num)
  have hr_le : n % 4 ≤ 3 := by omega
  have h_n_eq : n = 4*(n/4) + n%4 := (Nat.div_add_mod n 4).symm
  have h_m_ge : 2*k + 4 ≤ n / 4 := by
    have h1 : 8*k + 16 ≤ n := by linarith
    have h_div : (8*k + 16) / 4 ≤ n / 4 := Nat.div_le_div_right h1
    have h_compute : (8*k + 16) / 4 = 2*k + 4 := by omega
    linarith
  -- Set local abbreviations
  set m := n / 4
  set r := n % 4
  -- Unfold TauRat.lt
  unfold TauRat.lt
  rw [TauRat.toRat_abs, toRat_sub, TauRat.ofNatRecip_toRat]
  show |((TauComplex.exp (TauComplex.pureIm x)).re.approx n).toRat
        - ((TauReal.cos_of_rat x).approx n).toRat| < 1 / ((k : Rat) + 1)
  rw [TauComplex.exp_re_approx, expPartial_pureIm_re_approx_toRat_eq_rat,
      TauReal.cos_of_rat_approx, TauRat.cos_partial_toRat]
  -- Goal: |expPartial_pureIm_re_rat xR n - cos_partial_rat xR n| < 1/(k+1)
  rw [h_n_eq]
  -- Triangle inequality
  have rearr : expPartial_pureIm_re_rat x.toRat (4*m + r) - cos_partial_rat x.toRat (4*m + r)
              = (expPartial_pureIm_re_rat x.toRat (4*m + r) - cos_partial_rat x.toRat m)
                + (cos_partial_rat x.toRat m - cos_partial_rat x.toRat (4*m + r)) := by ring
  rw [rearr]
  have h_tri := abs_add_le
    (expPartial_pureIm_re_rat x.toRat (4*m + r) - cos_partial_rat x.toRat m)
    (cos_partial_rat x.toRat m - cos_partial_rat x.toRat (4*m + r))
  -- Bound the residual piece
  have h_residual : |expPartial_pureIm_re_rat x.toRat (4*m + r) - cos_partial_rat x.toRat m|
                  ≤ (r : Rat) / (Nat.factorial (4*m) : Rat) :=
    expPartial_pureIm_re_rat_residual_le x.toRat hx m r hr_le
  -- Bound the cos-tail piece
  have h_m_le : m ≤ 4*m + r := by omega
  have h_cos : |cos_partial_rat x.toRat m - cos_partial_rat x.toRat (4*m + r)|
              ≤ 4 / (2 : Rat)^m := by
    have h_swap : cos_partial_rat x.toRat m - cos_partial_rat x.toRat (4*m + r)
                = -(cos_partial_rat x.toRat (4*m + r) - cos_partial_rat x.toRat m) := by ring
    rw [h_swap, abs_neg]
    exact cos_partial_rat_cauchy_bound x.toRat hx (4*m + r) m h_m_le
  -- Convert residual r/(4m)! to a 4/2^m bound
  have h_fac_pos : (0 : Rat) < (Nat.factorial (4*m) : Rat) := by
    have := Nat.factorial_pos (4*m); exact_mod_cast this
  have h_two_pow_pos : (0 : Rat) < (2 : Rat)^m := by positivity
  have h_fac_ge_pow : ((2 : Rat))^m ≤ (Nat.factorial (4*m) : Rat) := by
    have hN := factorial_4m_ge_two_pow_m m
    have h_cast : ((2^m : Nat) : Rat) = (2 : Rat)^m := by push_cast; ring
    calc ((2 : Rat))^m
        = ((2^m : Nat) : Rat) := h_cast.symm
      _ ≤ (Nat.factorial (4*m) : Rat) := by exact_mod_cast hN
  have h_residual_le_pow : (r : Rat) / (Nat.factorial (4*m) : Rat) ≤ 4 / (2 : Rat)^m := by
    have h_r_le_4 : (r : Rat) ≤ 4 := by exact_mod_cast (by omega : r ≤ 4)
    have h_step1 : (r : Rat) / (Nat.factorial (4*m) : Rat)
                ≤ 4 / (Nat.factorial (4*m) : Rat) := by
      rw [div_le_div_iff₀ h_fac_pos h_fac_pos]
      nlinarith
    have h_step2 : (4 : Rat) / (Nat.factorial (4*m) : Rat) ≤ 4 / (2 : Rat)^m := by
      rw [div_le_div_iff₀ h_fac_pos h_two_pow_pos]
      nlinarith
    linarith
  -- Each piece is ≤ 4/2^m.
  -- Apply Rat.four_div_two_pow_lt_recip with shifted index (2k+1): get
  -- 4/2^m < 1/(2k+2) for m ≥ (2k+1)+3 = 2k+4.
  have h_m_ge_shift : (2*k+1) + 3 ≤ m := by omega
  have h_strict : 4 / (2 : Rat)^m < 1 / (((2*k+1 : Nat) : Rat) + 1) :=
    Rat.four_div_two_pow_lt_recip (2*k+1) m h_m_ge_shift
  have h_rhs : 1 / (((2*k+1 : Nat) : Rat) + 1) = 1 / (2 * ((k : Rat) + 1)) := by
    push_cast; ring
  rw [h_rhs] at h_strict
  -- Total ≤ 2 · (4/2^m) < 2 · (1/(2(k+1))) = 1/(k+1)
  have h_k_plus_1_pos : (0 : Rat) < (k : Rat) + 1 := by
    have : (0 : Rat) ≤ (k : Rat) := by exact_mod_cast Nat.zero_le k
    linarith
  have h_double : 1 / (2 * ((k : Rat) + 1)) + 1 / (2 * ((k : Rat) + 1))
                = 1 / ((k : Rat) + 1) := by
    field_simp
    ring
  -- Assemble: each piece < 1/(2(k+1)); sum < 1/(k+1).
  have h_resid_strict : (r : Rat) / (Nat.factorial (4*m) : Rat) < 1 / (2 * ((k : Rat) + 1)) := by
    linarith
  have h_cos_strict : |cos_partial_rat x.toRat m - cos_partial_rat x.toRat (4*m + r)|
                    < 1 / (2 * ((k : Rat) + 1)) := by
    linarith
  linarith

-- ============================================================
-- PART 11: NAMED TARGET DISCHARGE
-- ============================================================

/-- **🎯🎯🎯 Discharge of `TauComplex.exp_pureIm_re_eq_cos_target`** — the
    Phase 1C named-target proposition (declared in Part 4) is now provable.

    The discharge is `exp_pureIm_re_eq_cos` applied universally. -/
theorem TauComplex.exp_pureIm_re_eq_cos_target_proof :
    TauComplex.exp_pureIm_re_eq_cos_target :=
  fun x hx => exp_pureIm_re_eq_cos x hx

-- ============================================================
-- PART 12: PARALLEL .im DISCHARGE — exp(i·x).im ≈ sin_of_rat x
-- ============================================================

/-! ## Phase 1C.6 — Euler bridge for the imaginary part

Mirror structure of Parts 7-10 with `.re ↔ .im` swapped. The cyclotomic-4
closed forms and the recurrence helpers (Parts 5-6) apply equally to .im;
only the alignment with `sin_partial` (instead of `cos_partial`) differs.

Specifically: `(pair (4j)).2 = 0`, `(pair (4j+1)).2 = xR^(4j+1)`,
`(pair (4j+2)).2 = 0`, `(pair (4j+3)).2 = -xR^(4j+3)`. Pairing (4j+1, 4j+3)
gives `sin_pair_term_rat`. -/

/-- Rat-level intermediate for `((exp_partial (pureIm x) k).im.approx _).toRat`. -/
def expPartial_pureIm_im_rat (xR : Rat) : Nat → Rat
  | 0     => 0
  | k + 1 => expPartial_pureIm_im_rat xR k
              + (pureIm_pow_re_im_rat xR k).2 / (k.factorial : Rat)

@[simp] theorem expPartial_pureIm_im_rat_zero (xR : Rat) :
    expPartial_pureIm_im_rat xR 0 = 0 := rfl

@[simp] theorem expPartial_pureIm_im_rat_succ (xR : Rat) (k : Nat) :
    expPartial_pureIm_im_rat xR (k+1)
      = expPartial_pureIm_im_rat xR k
          + (pureIm_pow_re_im_rat xR k).2 / (k.factorial : Rat) := rfl

/-- Bridge: TauReal-level `(.im.approx m_a).toRat` matches Rat intermediate. -/
theorem expPartial_pureIm_im_approx_toRat_eq_rat (x : TauRat) (k m_a : Nat) :
    ((TauComplex.exp_partial (TauComplex.pureIm x) k).im.approx m_a).toRat
      = expPartial_pureIm_im_rat x.toRat k := by
  induction k with
  | zero =>
    show ((TauComplex.exp_partial (TauComplex.pureIm x) 0).im.approx m_a).toRat
        = expPartial_pureIm_im_rat x.toRat 0
    rw [TauComplex.exp_partial_zero, expPartial_pureIm_im_rat_zero]
    show (TauRat.zero).toRat = 0
    exact toRat_zero
  | succ k IH =>
    show ((TauComplex.exp_partial (TauComplex.pureIm x) (k+1)).im.approx m_a).toRat
        = expPartial_pureIm_im_rat x.toRat (k+1)
    rw [TauComplex.exp_partial_succ, expPartial_pureIm_im_rat_succ]
    show (TauRat.add
            ((TauComplex.exp_partial (TauComplex.pureIm x) k).im.approx m_a)
            ((TauComplex.exp_term (TauComplex.pureIm x) k).im.approx m_a)).toRat
        = expPartial_pureIm_im_rat x.toRat k
          + (pureIm_pow_re_im_rat x.toRat k).2 / (k.factorial : Rat)
    rw [toRat_add, IH, exp_term_pureIm_im_approx_toRat]

/-- At Rat-level depth `4m`, `expPartial_pureIm_im_rat` equals `sin_partial_rat`.

    Cyclotomic-4 alignment with the τ-native paired-sine series. -/
theorem expPartial_pureIm_im_rat_at_4m (xR : Rat) (m : Nat) :
    expPartial_pureIm_im_rat xR (4*m) = sin_partial_rat xR m := by
  induction m with
  | zero => rfl
  | succ m IH =>
    show expPartial_pureIm_im_rat xR (4*(m+1)) = sin_partial_rat xR (m+1)
    have hstep : 4*(m+1) = ((((4*m)+1)+1)+1)+1 := by ring
    rw [hstep, expPartial_pureIm_im_rat_succ, expPartial_pureIm_im_rat_succ,
        expPartial_pureIm_im_rat_succ, expPartial_pureIm_im_rat_succ, IH]
    obtain ⟨h0, h1, h2, h3⟩ := pureIm_pow_re_im_rat_cyclo4 xR m
    rw [h0, h1, h2, h3]
    rw [sin_partial_rat_succ]
    unfold sin_pair_term_rat
    simp only [Prod.fst, Prod.snd]
    ring

/-- TauReal-level alignment at depth 4m for .im. -/
theorem exp_partial_pureIm_im_approx_toRat_at_4m (x : TauRat) (m m_a : Nat) :
    ((TauComplex.exp_partial (TauComplex.pureIm x) (4*m)).im.approx m_a).toRat
      = sin_partial_rat x.toRat m := by
  rw [expPartial_pureIm_im_approx_toRat_eq_rat, expPartial_pureIm_im_rat_at_4m]

/-- Joint magnitude bound corollary for .im. -/
theorem pureIm_pow_re_im_rat_im_abs_le_one (xR : Rat) (hxR : |xR| ≤ 1) (k : Nat) :
    |(pureIm_pow_re_im_rat xR k).2| ≤ 1 := by
  have h := (pureIm_pow_re_im_rat_abs_le_pow xR k).2
  have h_pow_one : |xR|^k ≤ 1 := pow_le_one₀ (abs_nonneg _) hxR
  linarith

/-- Residual bound for .im, parallel to the .re version. -/
theorem expPartial_pureIm_im_rat_residual_le (xR : Rat) (hxR : |xR| ≤ 1)
    (m r : Nat) (hr : r ≤ 3) :
    |expPartial_pureIm_im_rat xR (4*m + r) - sin_partial_rat xR m|
      ≤ (r : Rat) / (Nat.factorial (4*m) : Rat) := by
  induction r with
  | zero =>
    have h_fac_pos : (0 : Rat) < (Nat.factorial (4*m) : Rat) := by
      have := Nat.factorial_pos (4*m); exact_mod_cast this
    rw [Nat.add_zero, expPartial_pureIm_im_rat_at_4m, sub_self, abs_zero,
        Nat.cast_zero, zero_div]
  | succ r ih =>
    have hr_le : r ≤ 3 := by omega
    have ih' := ih hr_le
    have h_step : 4*m + (r+1) = (4*m + r) + 1 := by ring
    rw [h_step, expPartial_pureIm_im_rat_succ]
    have rearr : expPartial_pureIm_im_rat xR (4*m + r)
                  + (pureIm_pow_re_im_rat xR (4*m + r)).2 / (Nat.factorial (4*m + r) : Rat)
                  - sin_partial_rat xR m
                = (expPartial_pureIm_im_rat xR (4*m + r) - sin_partial_rat xR m)
                  + (pureIm_pow_re_im_rat xR (4*m + r)).2 / (Nat.factorial (4*m + r) : Rat) := by
      ring
    rw [rearr]
    have h_tri := abs_add_le
      (expPartial_pureIm_im_rat xR (4*m + r) - sin_partial_rat xR m)
      ((pureIm_pow_re_im_rat xR (4*m + r)).2 / (Nat.factorial (4*m + r) : Rat))
    have h_fac_pos_4m : (0 : Rat) < (Nat.factorial (4*m) : Rat) := by
      have := Nat.factorial_pos (4*m); exact_mod_cast this
    have h_fac_pos_4mr : (0 : Rat) < (Nat.factorial (4*m + r) : Rat) := by
      have := Nat.factorial_pos (4*m + r); exact_mod_cast this
    have h_fac_le : (Nat.factorial (4*m) : Rat) ≤ (Nat.factorial (4*m + r) : Rat) := by
      have := Nat.factorial_le (show 4*m ≤ 4*m + r by omega); exact_mod_cast this
    have h_term_abs :
        |(pureIm_pow_re_im_rat xR (4*m + r)).2 / (Nat.factorial (4*m + r) : Rat)|
          ≤ 1 / (Nat.factorial (4*m) : Rat) := by
      rw [abs_div, abs_of_pos h_fac_pos_4mr]
      rw [div_le_div_iff₀ h_fac_pos_4mr h_fac_pos_4m]
      have h_num : |(pureIm_pow_re_im_rat xR (4*m + r)).2| ≤ 1 :=
        pureIm_pow_re_im_rat_im_abs_le_one xR hxR (4*m + r)
      nlinarith
    have h_sum : (r : Rat) / (Nat.factorial (4*m) : Rat) + 1 / (Nat.factorial (4*m) : Rat)
              = ((r + 1 : Nat) : Rat) / (Nat.factorial (4*m) : Rat) := by
      push_cast; field_simp
    linarith

/-- **🎯 [I.T-EulerIm]** The Euler bridge for `.im`: for `|x.toRat| ≤ 1`,
    `(TauComplex.exp (pureIm x)).im ≈ TauReal.sin_of_rat x` at TauReal
    equivalence level.

    Modulus and proof structure parallel `exp_pureIm_re_eq_cos`, using
    `sin_partial_rat_cauchy_bound` (which exists in TauRealSin.lean) and
    `expPartial_pureIm_im_rat_residual_le`. -/
theorem exp_pureIm_im_eq_sin (x : TauRat) (hx : |x.toRat| ≤ 1) :
    TauReal.equiv (TauComplex.exp (TauComplex.pureIm x)).im (TauReal.sin_of_rat x) := by
  refine ⟨fun k => 8*k + 19, fun k n hn => ?_⟩
  have hr_lt : n % 4 < 4 := Nat.mod_lt n (by norm_num)
  have hr_le : n % 4 ≤ 3 := by omega
  have h_n_eq : n = 4*(n/4) + n%4 := (Nat.div_add_mod n 4).symm
  have h_m_ge : 2*k + 4 ≤ n / 4 := by
    have h1 : 8*k + 16 ≤ n := by linarith
    have h_div : (8*k + 16) / 4 ≤ n / 4 := Nat.div_le_div_right h1
    have h_compute : (8*k + 16) / 4 = 2*k + 4 := by omega
    linarith
  set m := n / 4
  set r := n % 4
  unfold TauRat.lt
  rw [TauRat.toRat_abs, toRat_sub, TauRat.ofNatRecip_toRat]
  show |((TauComplex.exp (TauComplex.pureIm x)).im.approx n).toRat
        - ((TauReal.sin_of_rat x).approx n).toRat| < 1 / ((k : Rat) + 1)
  rw [TauComplex.exp_im_approx, expPartial_pureIm_im_approx_toRat_eq_rat,
      TauReal.sin_of_rat_approx, TauRat.sin_partial_toRat]
  rw [h_n_eq]
  have rearr : expPartial_pureIm_im_rat x.toRat (4*m + r) - sin_partial_rat x.toRat (4*m + r)
              = (expPartial_pureIm_im_rat x.toRat (4*m + r) - sin_partial_rat x.toRat m)
                + (sin_partial_rat x.toRat m - sin_partial_rat x.toRat (4*m + r)) := by ring
  rw [rearr]
  have h_tri := abs_add_le
    (expPartial_pureIm_im_rat x.toRat (4*m + r) - sin_partial_rat x.toRat m)
    (sin_partial_rat x.toRat m - sin_partial_rat x.toRat (4*m + r))
  have h_residual : |expPartial_pureIm_im_rat x.toRat (4*m + r) - sin_partial_rat x.toRat m|
                  ≤ (r : Rat) / (Nat.factorial (4*m) : Rat) :=
    expPartial_pureIm_im_rat_residual_le x.toRat hx m r hr_le
  have h_m_le : m ≤ 4*m + r := by omega
  have h_sin : |sin_partial_rat x.toRat m - sin_partial_rat x.toRat (4*m + r)|
              ≤ 4 / (2 : Rat)^m := by
    have h_swap : sin_partial_rat x.toRat m - sin_partial_rat x.toRat (4*m + r)
                = -(sin_partial_rat x.toRat (4*m + r) - sin_partial_rat x.toRat m) := by ring
    rw [h_swap, abs_neg]
    exact sin_partial_rat_cauchy_bound x.toRat hx (4*m + r) m h_m_le
  have h_fac_pos : (0 : Rat) < (Nat.factorial (4*m) : Rat) := by
    have := Nat.factorial_pos (4*m); exact_mod_cast this
  have h_two_pow_pos : (0 : Rat) < (2 : Rat)^m := by positivity
  have h_fac_ge_pow : ((2 : Rat))^m ≤ (Nat.factorial (4*m) : Rat) := by
    have hN := factorial_4m_ge_two_pow_m m
    have h_cast : ((2^m : Nat) : Rat) = (2 : Rat)^m := by push_cast; ring
    calc ((2 : Rat))^m
        = ((2^m : Nat) : Rat) := h_cast.symm
      _ ≤ (Nat.factorial (4*m) : Rat) := by exact_mod_cast hN
  have h_residual_le_pow : (r : Rat) / (Nat.factorial (4*m) : Rat) ≤ 4 / (2 : Rat)^m := by
    have h_r_le_4 : (r : Rat) ≤ 4 := by exact_mod_cast (by omega : r ≤ 4)
    have h_step1 : (r : Rat) / (Nat.factorial (4*m) : Rat)
                ≤ 4 / (Nat.factorial (4*m) : Rat) := by
      rw [div_le_div_iff₀ h_fac_pos h_fac_pos]
      nlinarith
    have h_step2 : (4 : Rat) / (Nat.factorial (4*m) : Rat) ≤ 4 / (2 : Rat)^m := by
      rw [div_le_div_iff₀ h_fac_pos h_two_pow_pos]
      nlinarith
    linarith
  have h_m_ge_shift : (2*k+1) + 3 ≤ m := by omega
  have h_strict : 4 / (2 : Rat)^m < 1 / (((2*k+1 : Nat) : Rat) + 1) :=
    Rat.four_div_two_pow_lt_recip (2*k+1) m h_m_ge_shift
  have h_rhs : 1 / (((2*k+1 : Nat) : Rat) + 1) = 1 / (2 * ((k : Rat) + 1)) := by
    push_cast; ring
  rw [h_rhs] at h_strict
  have h_k_plus_1_pos : (0 : Rat) < (k : Rat) + 1 := by
    have : (0 : Rat) ≤ (k : Rat) := by exact_mod_cast Nat.zero_le k
    linarith
  have h_double : 1 / (2 * ((k : Rat) + 1)) + 1 / (2 * ((k : Rat) + 1))
                = 1 / ((k : Rat) + 1) := by
    field_simp
    ring
  have h_resid_strict : (r : Rat) / (Nat.factorial (4*m) : Rat) < 1 / (2 * ((k : Rat) + 1)) := by
    linarith
  have h_sin_strict : |sin_partial_rat x.toRat m - sin_partial_rat x.toRat (4*m + r)|
                    < 1 / (2 * ((k : Rat) + 1)) := by
    linarith
  linarith

/-- **🎯🎯🎯 Discharge of `TauComplex.exp_pureIm_im_eq_sin_target`**. -/
theorem TauComplex.exp_pureIm_im_eq_sin_target_proof :
    TauComplex.exp_pureIm_im_eq_sin_target :=
  fun x hx => exp_pureIm_im_eq_sin x hx

-- ============================================================
-- PART 13: GENERALIZED EULER BRIDGE for arbitrary TauComplex
-- ============================================================

/-! ## Phase 1D — Sin/Cos addition formulae

Extends Phase 1C's Euler bridge to work with any TauComplex `z` satisfying
the toRat-level constraints `(z.re.approx _).toRat = 0` and
`(z.im.approx _).toRat = xR`. This is needed to bridge `pureIm (x₁+x₂)` and
`(pureIm x₁).add (pureIm x₂)` — equivalent but not identical (the .re/.im
components are `TauReal.add zero zero` vs `TauReal.zero`, equal at toRat).

The proof is a direct generalization of the Phase 1C bridge: same joint
induction on k, but using hypotheses `h_re`, `h_im` instead of the rfl simp
lemmas `pureIm_re_approx`, `pureIm_im_approx`. -/

/-- **Generalized power-bridge theorem**: for any TauComplex `z` whose .re
    and .im have toRat 0 and `xR` respectively at every approx depth, the
    cyclotomic-4 closed forms of `pureIm_pow_re_im_rat` apply. -/
theorem pureIm_like_pow_re_im_approx_toRat
    (z : TauComplex) (xR : Rat)
    (h_re : ∀ n, ((z.re).approx n).toRat = 0)
    (h_im : ∀ n, ((z.im).approx n).toRat = xR)
    (k n : Nat) :
    ((z.pow k).re.approx n).toRat = (pureIm_pow_re_im_rat xR k).1 ∧
    ((z.pow k).im.approx n).toRat = (pureIm_pow_re_im_rat xR k).2 := by
  induction k with
  | zero =>
    refine ⟨?_, ?_⟩
    · show ((TauComplex.one).re.approx n).toRat = 1
      show (TauRat.one).toRat = 1
      exact toRat_one
    · show ((TauComplex.one).im.approx n).toRat = 0
      show (TauRat.zero).toRat = 0
      exact toRat_zero
  | succ k IH =>
    obtain ⟨ih_re, ih_im⟩ := IH
    refine ⟨?_, ?_⟩
    · show (TauRat.sub
              (TauRat.mul ((z.pow k).re.approx n) (z.re.approx n))
              (TauRat.mul ((z.pow k).im.approx n) (z.im.approx n))).toRat
          = (pureIm_pow_re_im_rat xR (k+1)).1
      rw [toRat_sub, toRat_mul, toRat_mul, h_re n, h_im n, ih_re, ih_im,
          pureIm_pow_re_im_rat_succ]
      ring
    · show (TauRat.add
              (TauRat.mul ((z.pow k).re.approx n) (z.im.approx n))
              (TauRat.mul ((z.pow k).im.approx n) (z.re.approx n))).toRat
          = (pureIm_pow_re_im_rat xR (k+1)).2
      rw [toRat_add, toRat_mul, toRat_mul, h_re n, h_im n, ih_re, ih_im,
          pureIm_pow_re_im_rat_succ]
      ring

/-- Generalized exp_term bridge for .re. -/
theorem pureIm_like_exp_term_re_approx_toRat
    (z : TauComplex) (xR : Rat)
    (h_re : ∀ n, ((z.re).approx n).toRat = 0)
    (h_im : ∀ n, ((z.im).approx n).toRat = xR)
    (k n : Nat) :
    ((TauComplex.exp_term z k).re.approx n).toRat
      = (pureIm_pow_re_im_rat xR k).1 / (k.factorial : Rat) := by
  rw [TauComplex.exp_term_re, TauReal.scale_by_inv_factorial_approx,
      TauRat.scale_by_inv_factorial_toRat,
      (pureIm_like_pow_re_im_approx_toRat z xR h_re h_im k n).1]

/-- Generalized exp_term bridge for .im. -/
theorem pureIm_like_exp_term_im_approx_toRat
    (z : TauComplex) (xR : Rat)
    (h_re : ∀ n, ((z.re).approx n).toRat = 0)
    (h_im : ∀ n, ((z.im).approx n).toRat = xR)
    (k n : Nat) :
    ((TauComplex.exp_term z k).im.approx n).toRat
      = (pureIm_pow_re_im_rat xR k).2 / (k.factorial : Rat) := by
  rw [TauComplex.exp_term_im, TauReal.scale_by_inv_factorial_approx,
      TauRat.scale_by_inv_factorial_toRat,
      (pureIm_like_pow_re_im_approx_toRat z xR h_re h_im k n).2]

/-- Generalized exp_partial bridge for .re. -/
theorem pureIm_like_expPartial_re_approx_toRat
    (z : TauComplex) (xR : Rat)
    (h_re : ∀ n, ((z.re).approx n).toRat = 0)
    (h_im : ∀ n, ((z.im).approx n).toRat = xR)
    (k m_a : Nat) :
    ((TauComplex.exp_partial z k).re.approx m_a).toRat
      = expPartial_pureIm_re_rat xR k := by
  induction k with
  | zero =>
    show ((TauComplex.exp_partial z 0).re.approx m_a).toRat
        = expPartial_pureIm_re_rat xR 0
    rw [TauComplex.exp_partial_zero, expPartial_pureIm_re_rat_zero]
    show (TauRat.zero).toRat = 0
    exact toRat_zero
  | succ k IH =>
    show ((TauComplex.exp_partial z (k+1)).re.approx m_a).toRat
        = expPartial_pureIm_re_rat xR (k+1)
    rw [TauComplex.exp_partial_succ, expPartial_pureIm_re_rat_succ]
    show (TauRat.add
            ((TauComplex.exp_partial z k).re.approx m_a)
            ((TauComplex.exp_term z k).re.approx m_a)).toRat
        = expPartial_pureIm_re_rat xR k
          + (pureIm_pow_re_im_rat xR k).1 / (k.factorial : Rat)
    rw [toRat_add, IH, pureIm_like_exp_term_re_approx_toRat z xR h_re h_im]

/-- Generalized exp_partial bridge for .im. -/
theorem pureIm_like_expPartial_im_approx_toRat
    (z : TauComplex) (xR : Rat)
    (h_re : ∀ n, ((z.re).approx n).toRat = 0)
    (h_im : ∀ n, ((z.im).approx n).toRat = xR)
    (k m_a : Nat) :
    ((TauComplex.exp_partial z k).im.approx m_a).toRat
      = expPartial_pureIm_im_rat xR k := by
  induction k with
  | zero =>
    show ((TauComplex.exp_partial z 0).im.approx m_a).toRat
        = expPartial_pureIm_im_rat xR 0
    rw [TauComplex.exp_partial_zero, expPartial_pureIm_im_rat_zero]
    show (TauRat.zero).toRat = 0
    exact toRat_zero
  | succ k IH =>
    show ((TauComplex.exp_partial z (k+1)).im.approx m_a).toRat
        = expPartial_pureIm_im_rat xR (k+1)
    rw [TauComplex.exp_partial_succ, expPartial_pureIm_im_rat_succ]
    show (TauRat.add
            ((TauComplex.exp_partial z k).im.approx m_a)
            ((TauComplex.exp_term z k).im.approx m_a)).toRat
        = expPartial_pureIm_im_rat xR k
          + (pureIm_pow_re_im_rat xR k).2 / (k.factorial : Rat)
    rw [toRat_add, IH, pureIm_like_exp_term_im_approx_toRat z xR h_re h_im]

-- ============================================================
-- PART 14: PUREIM-SUM BRIDGE (pointwise-toRat-equal)
-- ============================================================

/-- **Bridge lemma**: `exp (pureIm (x₁+x₂)).re` and
    `exp ((pureIm x₁).add (pureIm x₂)).re` are TauReal-equivalent.

    Proof: at every approx depth `n`, both sides have the same toRat value
    (`= expPartial_pureIm_re_rat (x₁.toRat + x₂.toRat) n`). The LHS uses the
    Phase 1C-specific bridge; the RHS uses the generalized bridge with
    `(pureIm x₁).add (pureIm x₂)` having
    `.re-toRat = 0+0 = 0` and `.im-toRat = x₁.toRat + x₂.toRat`. -/
theorem exp_pureIm_sum_re_equiv (x₁ x₂ : TauRat) :
    TauReal.equiv (TauComplex.exp (TauComplex.pureIm (x₁.add x₂))).re
                  (TauComplex.exp ((TauComplex.pureIm x₁).add (TauComplex.pureIm x₂))).re := by
  apply TauReal.equiv_of_pointwise
  intro n
  rw [equiv_iff_toRat_eq]
  rw [TauComplex.exp_re_approx, TauComplex.exp_re_approx]
  -- LHS: ((exp_partial (pureIm (x₁+x₂)) n).re.approx n).toRat
  have h_lhs : ((TauComplex.exp_partial (TauComplex.pureIm (x₁.add x₂)) n).re.approx n).toRat
              = expPartial_pureIm_re_rat (x₁.toRat + x₂.toRat) n := by
    rw [expPartial_pureIm_re_approx_toRat_eq_rat, toRat_add]
  -- RHS: via generalized bridge
  have h_rhs : ((TauComplex.exp_partial ((TauComplex.pureIm x₁).add (TauComplex.pureIm x₂)) n).re.approx n).toRat
              = expPartial_pureIm_re_rat (x₁.toRat + x₂.toRat) n := by
    apply pureIm_like_expPartial_re_approx_toRat
    · -- h_re: .re.approx n' .toRat = 0 (both pureIm.re are TauReal.zero)
      intro n'
      show (TauRat.add
              ((TauComplex.pureIm x₁).re.approx n')
              ((TauComplex.pureIm x₂).re.approx n')).toRat = 0
      rw [TauComplex.pureIm_re_approx, TauComplex.pureIm_re_approx, toRat_add, toRat_zero]
      ring
    · -- h_im: .im.approx n' .toRat = x₁.toRat + x₂.toRat
      intro n'
      show (TauRat.add
              ((TauComplex.pureIm x₁).im.approx n')
              ((TauComplex.pureIm x₂).im.approx n')).toRat = x₁.toRat + x₂.toRat
      rw [TauComplex.pureIm_im_approx, TauComplex.pureIm_im_approx, toRat_add]
  rw [h_lhs, h_rhs]

/-- **Bridge lemma for .im**: parallel of `exp_pureIm_sum_re_equiv`. -/
theorem exp_pureIm_sum_im_equiv (x₁ x₂ : TauRat) :
    TauReal.equiv (TauComplex.exp (TauComplex.pureIm (x₁.add x₂))).im
                  (TauComplex.exp ((TauComplex.pureIm x₁).add (TauComplex.pureIm x₂))).im := by
  apply TauReal.equiv_of_pointwise
  intro n
  rw [equiv_iff_toRat_eq]
  rw [TauComplex.exp_im_approx, TauComplex.exp_im_approx]
  have h_lhs : ((TauComplex.exp_partial (TauComplex.pureIm (x₁.add x₂)) n).im.approx n).toRat
              = expPartial_pureIm_im_rat (x₁.toRat + x₂.toRat) n := by
    rw [expPartial_pureIm_im_approx_toRat_eq_rat, toRat_add]
  have h_rhs : ((TauComplex.exp_partial ((TauComplex.pureIm x₁).add (TauComplex.pureIm x₂)) n).im.approx n).toRat
              = expPartial_pureIm_im_rat (x₁.toRat + x₂.toRat) n := by
    apply pureIm_like_expPartial_im_approx_toRat
    · intro n'
      show (TauRat.add
              ((TauComplex.pureIm x₁).re.approx n')
              ((TauComplex.pureIm x₂).re.approx n')).toRat = 0
      rw [TauComplex.pureIm_re_approx, TauComplex.pureIm_re_approx, toRat_add, toRat_zero]
      ring
    · intro n'
      show (TauRat.add
              ((TauComplex.pureIm x₁).im.approx n')
              ((TauComplex.pureIm x₂).im.approx n')).toRat = x₁.toRat + x₂.toRat
      rw [TauComplex.pureIm_im_approx, TauComplex.pureIm_im_approx, toRat_add]
  rw [h_lhs, h_rhs]

-- ============================================================
-- PART 15: ABSOLUTE BOUNDS for cos/sin/exp partial sums
-- ============================================================

/-- `|cos_partial_rat x n| ≤ 4` for `|x| ≤ 1`. Derived from
    `cos_partial_rat_cauchy_bound` with `n=0` (cos_partial_rat _ 0 = 0). -/
theorem cos_partial_rat_abs_le_4 (x : Rat) (hx : |x| ≤ 1) (n : Nat) :
    |cos_partial_rat x n| ≤ 4 := by
  have h_bound : |cos_partial_rat x n - cos_partial_rat x 0| ≤ 4 / (2 : Rat)^0 :=
    cos_partial_rat_cauchy_bound x hx n 0 (Nat.zero_le _)
  rw [show cos_partial_rat x 0 = 0 from rfl, sub_zero] at h_bound
  have h_simp : (4 : Rat) / (2 : Rat)^0 = 4 := by norm_num
  rw [h_simp] at h_bound
  exact h_bound

/-- `|sin_partial_rat x n| ≤ 4` for `|x| ≤ 1`. -/
theorem sin_partial_rat_abs_le_4 (x : Rat) (hx : |x| ≤ 1) (n : Nat) :
    |sin_partial_rat x n| ≤ 4 := by
  have h_bound : |sin_partial_rat x n - sin_partial_rat x 0| ≤ 4 / (2 : Rat)^0 :=
    sin_partial_rat_cauchy_bound x hx n 0 (Nat.zero_le _)
  rw [show sin_partial_rat x 0 = 0 from rfl, sub_zero] at h_bound
  have h_simp : (4 : Rat) / (2 : Rat)^0 = 4 := by norm_num
  rw [h_simp] at h_bound
  exact h_bound

/-- `(cos_of_rat x).approx n .abs.toRat ≤ 4`. -/
theorem cos_of_rat_approx_abs_toRat_le_4 (x : TauRat) (hx : |x.toRat| ≤ 1) (n : Nat) :
    ((TauReal.cos_of_rat x).approx n).abs.toRat ≤ 4 := by
  rw [TauReal.cos_of_rat_approx, TauRat.toRat_abs, TauRat.cos_partial_toRat]
  exact cos_partial_rat_abs_le_4 x.toRat hx n

/-- `(sin_of_rat x).approx n .abs.toRat ≤ 4`. -/
theorem sin_of_rat_approx_abs_toRat_le_4 (x : TauRat) (hx : |x.toRat| ≤ 1) (n : Nat) :
    ((TauReal.sin_of_rat x).approx n).abs.toRat ≤ 4 := by
  rw [TauReal.sin_of_rat_approx, TauRat.toRat_abs, TauRat.sin_partial_toRat]
  exact sin_partial_rat_abs_le_4 x.toRat hx n

/-- `(exp (pureIm x)).re.approx n .abs.toRat ≤ 8` via triangle inequality
    through Phase 1C alignment + `cos_partial_rat_abs_le_4` + residual bound. -/
theorem exp_pureIm_re_approx_abs_toRat_le_8 (x : TauRat) (hx : |x.toRat| ≤ 1) (n : Nat) :
    ((TauComplex.exp (TauComplex.pureIm x)).re.approx n).abs.toRat ≤ 8 := by
  rw [TauRat.toRat_abs, TauComplex.exp_re_approx,
      expPartial_pureIm_re_approx_toRat_eq_rat]
  -- Goal: |expPartial_pureIm_re_rat x.toRat n| ≤ 8
  set m := n / 4
  set r := n % 4
  have hr_lt : r < 4 := Nat.mod_lt n (by norm_num)
  have hr_le : r ≤ 3 := by omega
  have h_n_eq : n = 4*m + r := (Nat.div_add_mod n 4).symm
  rw [h_n_eq]
  -- |expPartial xR (4m+r)| ≤ |expPartial xR (4m+r) - cos_partial xR m| + |cos_partial xR m|
  have rearr : expPartial_pureIm_re_rat x.toRat (4*m + r)
              = (expPartial_pureIm_re_rat x.toRat (4*m + r) - cos_partial_rat x.toRat m)
                + cos_partial_rat x.toRat m := by ring
  rw [rearr]
  have h_tri := abs_add_le
    (expPartial_pureIm_re_rat x.toRat (4*m + r) - cos_partial_rat x.toRat m)
    (cos_partial_rat x.toRat m)
  have h_residual : |expPartial_pureIm_re_rat x.toRat (4*m + r) - cos_partial_rat x.toRat m|
                  ≤ (r : Rat) / (Nat.factorial (4*m) : Rat) :=
    expPartial_pureIm_re_rat_residual_le x.toRat hx m r hr_le
  have h_cos : |cos_partial_rat x.toRat m| ≤ 4 := cos_partial_rat_abs_le_4 x.toRat hx m
  have h_r_le_3 : (r : Rat) ≤ 3 := by exact_mod_cast hr_le
  have h_fac_pos : (0 : Rat) < (Nat.factorial (4*m) : Rat) := by
    have := Nat.factorial_pos (4*m); exact_mod_cast this
  have h_fac_ge_1 : (1 : Rat) ≤ (Nat.factorial (4*m) : Rat) := by
    have h := Nat.factorial_pos (4*m)
    have h2 : 1 ≤ Nat.factorial (4*m) := h
    exact_mod_cast h2
  have h_residual_le_3 : (r : Rat) / (Nat.factorial (4*m) : Rat) ≤ 3 := by
    have h1 : (r : Rat) / (Nat.factorial (4*m) : Rat) ≤ 3 / (Nat.factorial (4*m) : Rat) := by
      rw [div_le_div_iff₀ h_fac_pos h_fac_pos]; nlinarith
    have h2 : (3 : Rat) / (Nat.factorial (4*m) : Rat) ≤ 3 / 1 := by
      rw [div_le_div_iff₀ h_fac_pos (by norm_num : (0:Rat) < 1)]; nlinarith
    linarith
  linarith

/-- `(exp (pureIm x)).im.approx n .abs.toRat ≤ 8` (parallel to .re). -/
theorem exp_pureIm_im_approx_abs_toRat_le_8 (x : TauRat) (hx : |x.toRat| ≤ 1) (n : Nat) :
    ((TauComplex.exp (TauComplex.pureIm x)).im.approx n).abs.toRat ≤ 8 := by
  rw [TauRat.toRat_abs, TauComplex.exp_im_approx,
      expPartial_pureIm_im_approx_toRat_eq_rat]
  set m := n / 4
  set r := n % 4
  have hr_lt : r < 4 := Nat.mod_lt n (by norm_num)
  have hr_le : r ≤ 3 := by omega
  have h_n_eq : n = 4*m + r := (Nat.div_add_mod n 4).symm
  rw [h_n_eq]
  have rearr : expPartial_pureIm_im_rat x.toRat (4*m + r)
              = (expPartial_pureIm_im_rat x.toRat (4*m + r) - sin_partial_rat x.toRat m)
                + sin_partial_rat x.toRat m := by ring
  rw [rearr]
  have h_tri := abs_add_le
    (expPartial_pureIm_im_rat x.toRat (4*m + r) - sin_partial_rat x.toRat m)
    (sin_partial_rat x.toRat m)
  have h_residual : |expPartial_pureIm_im_rat x.toRat (4*m + r) - sin_partial_rat x.toRat m|
                  ≤ (r : Rat) / (Nat.factorial (4*m) : Rat) :=
    expPartial_pureIm_im_rat_residual_le x.toRat hx m r hr_le
  have h_sin : |sin_partial_rat x.toRat m| ≤ 4 := sin_partial_rat_abs_le_4 x.toRat hx m
  have h_r_le_3 : (r : Rat) ≤ 3 := by exact_mod_cast hr_le
  have h_fac_pos : (0 : Rat) < (Nat.factorial (4*m) : Rat) := by
    have := Nat.factorial_pos (4*m); exact_mod_cast this
  have h_residual_le_3 : (r : Rat) / (Nat.factorial (4*m) : Rat) ≤ 3 := by
    have h1 : (r : Rat) / (Nat.factorial (4*m) : Rat) ≤ 3 / (Nat.factorial (4*m) : Rat) := by
      rw [div_le_div_iff₀ h_fac_pos h_fac_pos]; nlinarith
    have h2 : (3 : Rat) / (Nat.factorial (4*m) : Rat) ≤ 3 / 1 := by
      rw [div_le_div_iff₀ h_fac_pos (by norm_num : (0:Rat) < 1)]
      have h_fac_ge_1 : (1 : Rat) ≤ (Nat.factorial (4*m) : Rat) := by
        have h := Nat.factorial_pos (4*m); have h2 : 1 ≤ Nat.factorial (4*m) := h
        exact_mod_cast h2
      nlinarith
    linarith
  linarith

-- ============================================================
-- PART 16: BILATERAL MUL-EQUIV HELPER + cos_add
-- ============================================================

/-- **Bilateral mul-equiv**: with bounds on both `b` and `a'`, equivalence of
    each factor lifts to equivalence of the product. -/
theorem TauReal.mul_respects_equiv_both
    (a a' b b' : TauReal) (M : Nat) (hM : 1 ≤ M)
    (h_bound_b : ∀ n, (b.approx n).abs.toRat ≤ M)
    (h_bound_a' : ∀ n, (a'.approx n).abs.toRat ≤ M)
    (h_a : a.equiv a') (h_b : b.equiv b') :
    (a.mul b).equiv (a'.mul b') := by
  -- a · b ≈ a' · b (right-mul: bound on b, equiv on a)
  have h1 : (a.mul b).equiv (a'.mul b) :=
    TauReal.mul_respects_equiv_right_of_bound a a' b M hM h_bound_b h_a
  -- a' · b ≈ a' · b' (via mul_comm + right-mul + mul_comm)
  have h2 : (a'.mul b).equiv (a'.mul b') := by
    have h_comm1 : (a'.mul b).equiv (b.mul a') := taureal_mul_comm _ _
    have h_step : (b.mul a').equiv (b'.mul a') :=
      TauReal.mul_respects_equiv_right_of_bound b b' a' M hM h_bound_a' h_b
    have h_comm2 : (b'.mul a').equiv (a'.mul b') := taureal_mul_comm _ _
    exact TauReal.equiv_trans (TauReal.equiv_trans h_comm1 h_step) h_comm2
  exact TauReal.equiv_trans h1 h2

/-- **🎯🎯🎯 [I.T-CosAdd] Cosine addition formula** at TauReal equivalence level.

    For `|x₁.toRat|, |x₂.toRat|, |(x₁+x₂).toRat| ≤ 1`:
        `cos(x₁+x₂) ≈ cos x₁ · cos x₂ − sin x₁ · sin x₂`

    Proof chain (using M3 endpoint + Phase 1C Euler bridge):
    1. `cos_of_rat (x₁+x₂) ≈ (exp (pureIm (x₁+x₂))).re` (Phase 1C, needs |x₁+x₂| ≤ 1)
    2. `≈ (exp ((pureIm x₁).add (pureIm x₂))).re` (Part 14 bridge)
    3. `≈ ((exp (pureIm x₁)).mul (exp (pureIm x₂))).re` (M3 exp_add + .re projection)
    4. `= (e₁.re.mul e₂.re).sub (e₁.im.mul e₂.im)` (TauComplex.mul def)
    5. `≈ (cos x₁.mul cos x₂).sub (sin x₁.mul sin x₂)` (Phase 1C + bilateral mul-equiv + equiv_sub_congr) -/
theorem cos_add (x₁ x₂ : TauRat)
    (hx₁ : |x₁.toRat| ≤ 1) (hx₂ : |x₂.toRat| ≤ 1)
    (hsum : |(x₁.add x₂).toRat| ≤ 1) :
    TauReal.equiv (TauReal.cos_of_rat (x₁.add x₂))
                  (((TauReal.cos_of_rat x₁).mul (TauReal.cos_of_rat x₂)).sub
                    ((TauReal.sin_of_rat x₁).mul (TauReal.sin_of_rat x₂))) := by
  -- Step 1: cos_of_rat (x₁+x₂) ≈ (exp (pureIm (x₁+x₂))).re
  have h_cos_eq_exp_re : TauReal.equiv
      (TauReal.cos_of_rat (x₁.add x₂))
      (TauComplex.exp (TauComplex.pureIm (x₁.add x₂))).re :=
    TauReal.equiv_symm (exp_pureIm_re_eq_cos (x₁.add x₂) hsum)
  -- Step 2: ≈ (exp ((pureIm x₁).add (pureIm x₂))).re (Part 14 bridge)
  have h_bridge : TauReal.equiv
      (TauComplex.exp (TauComplex.pureIm (x₁.add x₂))).re
      (TauComplex.exp ((TauComplex.pureIm x₁).add (TauComplex.pureIm x₂))).re :=
    exp_pureIm_sum_re_equiv x₁ x₂
  -- Step 3: exp_add applied to (pureIm x₁), (pureIm x₂), then .re projection
  have h_exp_add : TauComplex.equiv
      (TauComplex.exp ((TauComplex.pureIm x₁).add (TauComplex.pureIm x₂)))
      ((TauComplex.exp (TauComplex.pureIm x₁)).mul (TauComplex.exp (TauComplex.pureIm x₂))) :=
    TauComplex.exp_add _ _ (TauComplex.pureIm_BoundedBy_1 x₁ hx₁)
                            (TauComplex.pureIm_BoundedBy_1 x₂ hx₂)
  have h_exp_add_re : TauReal.equiv
      (TauComplex.exp ((TauComplex.pureIm x₁).add (TauComplex.pureIm x₂))).re
      ((TauComplex.exp (TauComplex.pureIm x₁)).mul (TauComplex.exp (TauComplex.pureIm x₂))).re :=
    h_exp_add.1
  -- Step 4: ((exp e₁).mul (exp e₂)).re = sub (mul re re) (mul im im) by def
  -- Step 5: (mul re re).sub (mul im im) ≈ (cos · cos).sub (sin · sin)
  have h_e1_re_cos : TauReal.equiv (TauComplex.exp (TauComplex.pureIm x₁)).re
                                   (TauReal.cos_of_rat x₁) :=
    exp_pureIm_re_eq_cos x₁ hx₁
  have h_e2_re_cos : TauReal.equiv (TauComplex.exp (TauComplex.pureIm x₂)).re
                                   (TauReal.cos_of_rat x₂) :=
    exp_pureIm_re_eq_cos x₂ hx₂
  have h_e1_im_sin : TauReal.equiv (TauComplex.exp (TauComplex.pureIm x₁)).im
                                   (TauReal.sin_of_rat x₁) :=
    exp_pureIm_im_eq_sin x₁ hx₁
  have h_e2_im_sin : TauReal.equiv (TauComplex.exp (TauComplex.pureIm x₂)).im
                                   (TauReal.sin_of_rat x₂) :=
    exp_pureIm_im_eq_sin x₂ hx₂
  -- Bilateral mul-equiv with M = 8 (sufficient for both exp and cos bounds)
  have h_mul_re_re : TauReal.equiv
      ((TauComplex.exp (TauComplex.pureIm x₁)).re.mul (TauComplex.exp (TauComplex.pureIm x₂)).re)
      ((TauReal.cos_of_rat x₁).mul (TauReal.cos_of_rat x₂)) :=
    TauReal.mul_respects_equiv_both _ _ _ _ 8 (by norm_num)
      (exp_pureIm_re_approx_abs_toRat_le_8 x₂ hx₂)
      (fun n => le_trans (cos_of_rat_approx_abs_toRat_le_4 x₁ hx₁ n) (by norm_num : (4 : Rat) ≤ 8))
      h_e1_re_cos h_e2_re_cos
  have h_mul_im_im : TauReal.equiv
      ((TauComplex.exp (TauComplex.pureIm x₁)).im.mul (TauComplex.exp (TauComplex.pureIm x₂)).im)
      ((TauReal.sin_of_rat x₁).mul (TauReal.sin_of_rat x₂)) :=
    TauReal.mul_respects_equiv_both _ _ _ _ 8 (by norm_num)
      (exp_pureIm_im_approx_abs_toRat_le_8 x₂ hx₂)
      (fun n => le_trans (sin_of_rat_approx_abs_toRat_le_4 x₁ hx₁ n) (by norm_num : (4 : Rat) ≤ 8))
      h_e1_im_sin h_e2_im_sin
  -- The .re of (mul e₁ e₂) is sub (mul re re) (mul im im) by TauComplex.mul def.
  -- Combine via equiv_sub_congr.
  have h_sub : TauReal.equiv
      (((TauComplex.exp (TauComplex.pureIm x₁)).re.mul (TauComplex.exp (TauComplex.pureIm x₂)).re).sub
        ((TauComplex.exp (TauComplex.pureIm x₁)).im.mul (TauComplex.exp (TauComplex.pureIm x₂)).im))
      (((TauReal.cos_of_rat x₁).mul (TauReal.cos_of_rat x₂)).sub
        ((TauReal.sin_of_rat x₁).mul (TauReal.sin_of_rat x₂))) :=
    TauReal.equiv_sub_congr h_mul_re_re h_mul_im_im
  -- ((exp x₁).mul (exp x₂)).re definitionally equals (sub (mul re re) (mul im im)).
  -- So h_exp_add_re combined with h_sub gives the conclusion.
  have h_chain1 : TauReal.equiv
      (TauReal.cos_of_rat (x₁.add x₂))
      ((TauComplex.exp (TauComplex.pureIm x₁)).mul (TauComplex.exp (TauComplex.pureIm x₂))).re :=
    TauReal.equiv_trans h_cos_eq_exp_re (TauReal.equiv_trans h_bridge h_exp_add_re)
  exact TauReal.equiv_trans h_chain1 h_sub

/-- **🎯🎯🎯 [I.T-SinAdd] Sine addition formula** at TauReal equivalence level.

    For `|x₁.toRat|, |x₂.toRat|, |(x₁+x₂).toRat| ≤ 1`:
        `sin(x₁+x₂) ≈ sin x₁ · cos x₂ + cos x₁ · sin x₂`

    Parallel proof to `cos_add` using the .im projection of M3 exp_add. -/
theorem sin_add (x₁ x₂ : TauRat)
    (hx₁ : |x₁.toRat| ≤ 1) (hx₂ : |x₂.toRat| ≤ 1)
    (hsum : |(x₁.add x₂).toRat| ≤ 1) :
    TauReal.equiv (TauReal.sin_of_rat (x₁.add x₂))
                  (((TauReal.sin_of_rat x₁).mul (TauReal.cos_of_rat x₂)).add
                    ((TauReal.cos_of_rat x₁).mul (TauReal.sin_of_rat x₂))) := by
  -- Step 1-4 mirror cos_add for .im
  have h_sin_eq_exp_im : TauReal.equiv
      (TauReal.sin_of_rat (x₁.add x₂))
      (TauComplex.exp (TauComplex.pureIm (x₁.add x₂))).im :=
    TauReal.equiv_symm (exp_pureIm_im_eq_sin (x₁.add x₂) hsum)
  have h_bridge : TauReal.equiv
      (TauComplex.exp (TauComplex.pureIm (x₁.add x₂))).im
      (TauComplex.exp ((TauComplex.pureIm x₁).add (TauComplex.pureIm x₂))).im :=
    exp_pureIm_sum_im_equiv x₁ x₂
  have h_exp_add : TauComplex.equiv
      (TauComplex.exp ((TauComplex.pureIm x₁).add (TauComplex.pureIm x₂)))
      ((TauComplex.exp (TauComplex.pureIm x₁)).mul (TauComplex.exp (TauComplex.pureIm x₂))) :=
    TauComplex.exp_add _ _ (TauComplex.pureIm_BoundedBy_1 x₁ hx₁)
                            (TauComplex.pureIm_BoundedBy_1 x₂ hx₂)
  have h_exp_add_im : TauReal.equiv
      (TauComplex.exp ((TauComplex.pureIm x₁).add (TauComplex.pureIm x₂))).im
      ((TauComplex.exp (TauComplex.pureIm x₁)).mul (TauComplex.exp (TauComplex.pureIm x₂))).im :=
    h_exp_add.2
  -- Phase 1C bridges
  have h_e1_re_cos := exp_pureIm_re_eq_cos x₁ hx₁
  have h_e2_re_cos := exp_pureIm_re_eq_cos x₂ hx₂
  have h_e1_im_sin := exp_pureIm_im_eq_sin x₁ hx₁
  have h_e2_im_sin := exp_pureIm_im_eq_sin x₂ hx₂
  -- (mul e₁ e₂).im = add (mul e₁.re e₂.im) (mul e₁.im e₂.re) by TauComplex.mul def
  -- Need: that ≈ add (sin x₁ . cos x₂) (cos x₁ . sin x₂)
  have h_mul_re_im : TauReal.equiv
      ((TauComplex.exp (TauComplex.pureIm x₁)).re.mul (TauComplex.exp (TauComplex.pureIm x₂)).im)
      ((TauReal.cos_of_rat x₁).mul (TauReal.sin_of_rat x₂)) :=
    TauReal.mul_respects_equiv_both _ _ _ _ 8 (by norm_num)
      (exp_pureIm_im_approx_abs_toRat_le_8 x₂ hx₂)
      (fun n => le_trans (cos_of_rat_approx_abs_toRat_le_4 x₁ hx₁ n) (by norm_num : (4 : Rat) ≤ 8))
      h_e1_re_cos h_e2_im_sin
  have h_mul_im_re : TauReal.equiv
      ((TauComplex.exp (TauComplex.pureIm x₁)).im.mul (TauComplex.exp (TauComplex.pureIm x₂)).re)
      ((TauReal.sin_of_rat x₁).mul (TauReal.cos_of_rat x₂)) :=
    TauReal.mul_respects_equiv_both _ _ _ _ 8 (by norm_num)
      (exp_pureIm_re_approx_abs_toRat_le_8 x₂ hx₂)
      (fun n => le_trans (sin_of_rat_approx_abs_toRat_le_4 x₁ hx₁ n) (by norm_num : (4 : Rat) ≤ 8))
      h_e1_im_sin h_e2_re_cos
  have h_add : TauReal.equiv
      (((TauComplex.exp (TauComplex.pureIm x₁)).re.mul (TauComplex.exp (TauComplex.pureIm x₂)).im).add
        ((TauComplex.exp (TauComplex.pureIm x₁)).im.mul (TauComplex.exp (TauComplex.pureIm x₂)).re))
      (((TauReal.cos_of_rat x₁).mul (TauReal.sin_of_rat x₂)).add
        ((TauReal.sin_of_rat x₁).mul (TauReal.cos_of_rat x₂))) :=
    TauReal.equiv_add_congr h_mul_re_im h_mul_im_re
  have h_chain1 : TauReal.equiv
      (TauReal.sin_of_rat (x₁.add x₂))
      ((TauComplex.exp (TauComplex.pureIm x₁)).mul (TauComplex.exp (TauComplex.pureIm x₂))).im :=
    TauReal.equiv_trans h_sin_eq_exp_im (TauReal.equiv_trans h_bridge h_exp_add_im)
  -- Reorder: cos·sin + sin·cos = sin·cos + cos·sin via add_comm
  -- Final result has form (sin · cos).add (cos · sin).
  have h_reorder : TauReal.equiv
      (((TauReal.cos_of_rat x₁).mul (TauReal.sin_of_rat x₂)).add
        ((TauReal.sin_of_rat x₁).mul (TauReal.cos_of_rat x₂)))
      (((TauReal.sin_of_rat x₁).mul (TauReal.cos_of_rat x₂)).add
        ((TauReal.cos_of_rat x₁).mul (TauReal.sin_of_rat x₂))) :=
    taureal_add_comm _ _
  exact TauReal.equiv_trans h_chain1 (TauReal.equiv_trans h_add h_reorder)

-- ============================================================
-- PART 17: Phase 2.6.B.2.α — scaledCis ALGEBRAIC IDENTITY
-- ============================================================

/-! ## Phase 2.6.B.2.α — `scaledCis` multiplicative identity

The classical fact:

    (1, a) · (1, b) = (1 − ab, a + b)   at complex level

encodes the geometric content of "arguments add when complex numbers
multiply". Combined with `(a + b) = (1 − ab) · z` for `z = (a+b)/(1−ab)`,
this gives:

    scaledCis(a) · scaledCis(b) ≈ (1 − ab) · scaledCis(z)

where `scaledCis(a) := ⟨1, a⟩` (TauComplex with TauReal.one as real part
and `fromTauRat a` as imaginary part). **Sqrt-free** — no normalization
needed.

This is the algebraic core of arctan addition: it expresses the
multiplicative structure of arctan-images at TauComplex level without
needing `cos_of_TauReal` infrastructure. Phase 2.6.B.2.β will bridge
this algebraic identity to the actual TauReal arctan addition.
-/

/-- **[I.D-ScaledCis]** The unnormalized `cis(arctan a) · √(1+a²)`: the
    TauComplex `(1, a)` whose argument is classically `arctan(a)`.

    Direct struct constructor with `re = TauReal.one`, `im = fromTauRat a`. -/
def TauComplex.scaledCis (a : TauRat) : TauComplex :=
  ⟨TauReal.one, TauReal.fromTauRat a⟩

@[simp] theorem TauComplex.scaledCis_re_approx (a : TauRat) (n : Nat) :
    (TauComplex.scaledCis a).re.approx n = TauRat.one := rfl

@[simp] theorem TauComplex.scaledCis_im_approx (a : TauRat) (n : Nat) :
    (TauComplex.scaledCis a).im.approx n = a := rfl

/-- **[I.T-ScaledCis-Mul-Identity]** The algebraic multiplication identity:

        scaledCis(a) · scaledCis(b) ≈ fromTauReal(w) · scaledCis(z)

    given `w.toRat = 1 − a·b` and `z.toRat · w.toRat = a + b` (i.e.,
    `z = (a+b)/(1−ab)` when `w ≠ 0`).

    **Proof**: componentwise toRat-level identity via `equiv_of_pointwise`.
    - Real parts: `1·1 − a·b = w` (using `h_w`).
    - Imaginary parts: `1·b + a·1 = w·z` (using `h_z`). -/
theorem TauComplex.scaledCis_mul_identity (a b z w : TauRat)
    (h_w : w.toRat = 1 - a.toRat * b.toRat)
    (h_z : z.toRat * w.toRat = a.toRat + b.toRat) :
    TauComplex.equiv
      ((TauComplex.scaledCis a).mul (TauComplex.scaledCis b))
      ((TauComplex.fromTauReal (TauReal.fromTauRat w)).mul (TauComplex.scaledCis z)) := by
  refine ⟨?_, ?_⟩
  · -- Real parts
    apply TauReal.equiv_of_pointwise
    intro n
    rw [equiv_iff_toRat_eq]
    -- LHS.re.approx n = TauRat.sub (TauRat.mul 1 1) (TauRat.mul a b)
    -- RHS.re.approx n = TauRat.sub (TauRat.mul w 1) (TauRat.mul 0 z)
    show (TauRat.sub
            (TauRat.mul (TauRat.one) (TauRat.one))
            (TauRat.mul a b)).toRat
        = (TauRat.sub
            (TauRat.mul w (TauRat.one))
            (TauRat.mul (TauRat.zero) z)).toRat
    rw [toRat_sub, toRat_sub, toRat_mul, toRat_mul, toRat_mul, toRat_mul,
        toRat_one, toRat_zero]
    linarith
  · -- Imaginary parts
    apply TauReal.equiv_of_pointwise
    intro n
    rw [equiv_iff_toRat_eq]
    -- LHS.im.approx n = TauRat.add (TauRat.mul 1 b) (TauRat.mul a 1)
    -- RHS.im.approx n = TauRat.add (TauRat.mul w z) (TauRat.mul 0 1)
    show (TauRat.add
            (TauRat.mul (TauRat.one) b)
            (TauRat.mul a (TauRat.one))).toRat
        = (TauRat.add
            (TauRat.mul w z)
            (TauRat.mul (TauRat.zero) (TauRat.one))).toRat
    rw [toRat_add, toRat_add, toRat_mul, toRat_mul, toRat_mul, toRat_mul,
        toRat_one, toRat_zero]
    linarith

-- ============================================================
-- PART 18: Phase 2.6.B.2.β.1 — pureIm_of_real (TauReal-arg pureIm)
-- ============================================================

/-! ## Phase 2.6.B.2.β.1 — `pureIm_of_real` foundations

Extends `TauComplex.pureIm` from TauRat arguments to general TauReal
arguments. This is the structural prerequisite for `cisTauReal := exp ∘
pureIm_of_real`, which lifts the Euler bridge to TauReal angles
(needed for `cisTauReal(arctan_of_rat a)` in the eventual arctan
addition proof). -/

/-- **[I.D-PureImOfReal]** The pure-imaginary embedding of a TauReal:
    `pureIm_of_real x := ⟨TauReal.zero, x⟩`.

    Generalises `TauComplex.pureIm (x : TauRat) = ⟨TauReal.zero, fromTauRat x⟩`
    to any TauReal `x`. -/
def TauComplex.pureIm_of_real (x : TauReal) : TauComplex :=
  ⟨TauReal.zero, x⟩

@[simp] theorem TauComplex.pureIm_of_real_re_approx (x : TauReal) (n : Nat) :
    (TauComplex.pureIm_of_real x).re.approx n = TauRat.zero := rfl

@[simp] theorem TauComplex.pureIm_of_real_im_approx (x : TauReal) (n : Nat) :
    (TauComplex.pureIm_of_real x).im.approx n = x.approx n := rfl

/-- **Boundedness lifting**: if every approximation of `x` is bounded by `M`,
    then `pureIm_of_real x` has `BoundedBy M`. -/
theorem TauComplex.pureIm_of_real_BoundedBy
    (x : TauReal) (M : Nat) (hM : 1 ≤ M)
    (h_bound : ∀ n, (x.approx n).abs.toRat ≤ M) :
    TauComplex.BoundedBy (TauComplex.pureIm_of_real x) M := by
  refine ⟨?_, ?_⟩
  · -- Real part: all approximations are TauRat.zero, abs.toRat = 0 ≤ M
    intro n
    show (TauRat.zero.abs.toRat) ≤ ((M : Nat) : Rat)
    rw [TauRat.toRat_abs, toRat_zero, abs_zero]
    exact_mod_cast Nat.zero_le M
  · -- Imaginary part: approximations are x.approx n, bounded by M
    intro n
    exact h_bound n

/-- **Distributes over TauReal.add**: `pureIm_of_real (x+y) ≈ (pureIm_of_real x) + (pureIm_of_real y)`. -/
theorem TauComplex.pureIm_of_real_add (x y : TauReal) :
    TauComplex.equiv (TauComplex.pureIm_of_real (TauReal.add x y))
                     ((TauComplex.pureIm_of_real x).add (TauComplex.pureIm_of_real y)) := by
  refine ⟨?_, ?_⟩
  · -- Real parts: LHS.re = TauReal.zero; RHS.re = TauReal.add zero zero
    apply TauReal.equiv_of_pointwise
    intro n
    rw [equiv_iff_toRat_eq]
    show (TauRat.zero).toRat
        = (TauRat.add ((TauComplex.pureIm_of_real x).re.approx n)
                      ((TauComplex.pureIm_of_real y).re.approx n)).toRat
    show (TauRat.zero).toRat = (TauRat.add TauRat.zero TauRat.zero).toRat
    rw [toRat_add, toRat_zero]
    ring
  · -- Imaginary parts: LHS.im = TauReal.add x y; RHS.im = TauReal.add x y (definitionally)
    apply TauReal.equiv_of_pointwise
    intro n
    exact TauRat.equiv_refl _

/-- **Bridge to TauRat-level `pureIm`**: for a TauRat `a`,
    `pureIm_of_real (fromTauRat a)` and `pureIm a` are TauComplex-equivalent. -/
theorem TauComplex.pureIm_of_real_fromTauRat_eq_pureIm (a : TauRat) :
    TauComplex.equiv (TauComplex.pureIm_of_real (TauReal.fromTauRat a))
                     (TauComplex.pureIm a) := by
  refine ⟨?_, ?_⟩
  · -- Real parts: both are TauReal.zero
    apply TauReal.equiv_of_pointwise
    intro n
    exact TauRat.equiv_refl _
  · -- Imaginary parts: both are constant TauReal at a (= fromTauRat a)
    apply TauReal.equiv_of_pointwise
    intro n
    exact TauRat.equiv_refl _

-- ============================================================
-- PART 19: Phase 2.6.B.2.β.2 — cisTauReal (cis at TauReal angles)
-- ============================================================

/-! ## Phase 2.6.B.2.β.2 — `cisTauReal` definition + Euler bridge specialization

`cisTauReal x := TauComplex.exp (pureIm_of_real x)` for any TauReal angle `x`.
This generalises the cyclotomic-4 cis function from TauRat arguments to
general TauReal angles, leveraging `pureIm_of_real` from β.1.

**Key bridges shipped**:
- `cisTauReal (fromTauRat a) = TauComplex.exp (pureIm a)` (definitional `rfl`).
- `(cisTauReal (fromTauRat a)).re ≈ cos_of_rat a` for `|a.toRat| ≤ 1` (via Phase 1C).
- `(cisTauReal (fromTauRat a)).im ≈ sin_of_rat a` for `|a.toRat| ≤ 1` (via Phase 1C).

These are the foundational hooks downstream sub-pieces β.3 and β.4 will use. -/

/-- **[I.D-CisTauReal]** Complex exponential of a pure-imaginary TauReal:
    `cisTauReal x := exp(i · x)` where the embedding is via `pureIm_of_real`. -/
def TauComplex.cisTauReal (x : TauReal) : TauComplex :=
  TauComplex.exp (TauComplex.pureIm_of_real x)

/-- **Definitional bridge to TauRat-level cis**: for a TauRat `a`,
    `cisTauReal (fromTauRat a) = exp (pureIm a)` (literally, by definition).

    Holds because `pureIm_of_real (fromTauRat a) = ⟨TauReal.zero, fromTauRat a⟩ = pureIm a`
    is definitionally equal. -/
theorem TauComplex.cisTauReal_fromTauRat_eq (a : TauRat) :
    TauComplex.cisTauReal (TauReal.fromTauRat a)
      = TauComplex.exp (TauComplex.pureIm a) := rfl

/-- **🎯 Euler bridge for cisTauReal at TauRat input — real part**:
    for `|a.toRat| ≤ 1`,
        `(cisTauReal (fromTauRat a)).re ≈ cos_of_rat a`.

    Direct corollary of the Phase 1C Euler bridge `exp_pureIm_re_eq_cos`
    via the definitional bridge above. -/
theorem TauComplex.cisTauReal_fromTauRat_re_eq_cos (a : TauRat) (ha : |a.toRat| ≤ 1) :
    TauReal.equiv ((TauComplex.cisTauReal (TauReal.fromTauRat a)).re)
                  (TauReal.cos_of_rat a) := by
  show TauReal.equiv ((TauComplex.exp (TauComplex.pureIm a)).re) (TauReal.cos_of_rat a)
  exact exp_pureIm_re_eq_cos a ha

/-- **🎯 Euler bridge for cisTauReal at TauRat input — imaginary part**:
    for `|a.toRat| ≤ 1`,
        `(cisTauReal (fromTauRat a)).im ≈ sin_of_rat a`. -/
theorem TauComplex.cisTauReal_fromTauRat_im_eq_sin (a : TauRat) (ha : |a.toRat| ≤ 1) :
    TauReal.equiv ((TauComplex.cisTauReal (TauReal.fromTauRat a)).im)
                  (TauReal.sin_of_rat a) := by
  show TauReal.equiv ((TauComplex.exp (TauComplex.pureIm a)).im) (TauReal.sin_of_rat a)
  exact exp_pureIm_im_eq_sin a ha

end Tau.Boundary
