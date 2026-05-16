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

end Tau.Boundary
