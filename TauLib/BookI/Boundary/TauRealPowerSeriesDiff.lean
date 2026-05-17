import TauLib.BookI.Boundary.TauRealDerivative
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity

/-!
# TauLib.BookI.Boundary.TauRealPowerSeriesDiff

**Wave Γ₈ Phase 2.6.B.2.β.4.9 — Module 2**: term-by-term differentiation
for the τ-canon power-series machinery.

This module ships, in successive waves, derivative rules for natural-number
powers `x^k` and (in later waves) the arctan-shape pair-term differentiation
needed for Module 3.

## Architectural context

Per `atlas/insights/2026-05-17-tau-canon-derivative-deep-forensic.md`,
the dyadic `TauReal.IsDerivAt` from Module 1 is the τ-canon-native
realization of I.D42 D-Differentiability (eventual constancy at finite
primorial stages). Module 2's power rule and term-by-term differentiation
operate entirely within this stabilization-at-depth paradigm — no ε-δ
machinery is introduced, and none is needed.

## Wave 1 — the square rule

Concrete proof of `IsDerivAt (fun x => fromTauRat (x · x)) a (2a)` on the
disk `2·|a.toRat| ≤ 1`. Uses `IsDerivAt_mul` (Module 1's Leibniz) with
both factors equal to `fun x => fromTauRat x` (the identity-style function
from `IsDerivAt_id`). The bound parameter `M = 2` accommodates the worst-case
dyadic step `dyadicStep 0 = 1`, which can shift the input by `+1`.

This wave establishes the **Leibniz-induction pattern** that subsequent waves
extend to cubic, fourth, and general k-th-power rules.
-/

set_option autoImplicit false

namespace Tau.Boundary

open Tau.Denotation

-- ============================================================
-- PART 1: HELPERS — Bound lemmas for the square rule
-- ============================================================

/-- `|fromTauRat q . approx N|.toRat ≤ |q.toRat|`: the `.approx N` of a
    constant-sequence TauReal is just `q`. -/
private theorem fromTauRat_approx_abs_toRat (q : TauRat) (N : Nat) :
    ((TauReal.fromTauRat q).approx N).abs.toRat = |q.toRat| := by
  show (q.abs).toRat = |q.toRat|
  rw [TauRat.toRat_abs]

/-- `|a + dyadicStep N| ≤ |a| + 1`: the worst-case dyadic step shift
    bound. `dyadicStep N = 1/2^N ≤ 1` for all `N ≥ 0`. -/
private theorem dyadicStep_shift_abs_le (a : TauRat) (N : Nat) :
    |((a.add (TauRat.dyadicStep N))).toRat| ≤ |a.toRat| + 1 := by
  rw [toRat_add, TauRat.dyadicStep_toRat]
  have h_pow_pos : (0 : Rat) < (2 : Rat)^N := by positivity
  have h_pow_ge_one : (1 : Rat) ≤ (2 : Rat)^N := by
    have h_nat : 1 ≤ 2^N := Nat.one_le_pow N 2 (by norm_num)
    have h_cast : ((1 : Nat) : Rat) ≤ ((2^N : Nat) : Rat) := by exact_mod_cast h_nat
    have h_left : ((1 : Nat) : Rat) = 1 := by norm_num
    have h_right : ((2^N : Nat) : Rat) = (2 : Rat)^N := by push_cast; ring
    linarith
  have h_step_le_one : (1 : Rat) / (2 : Rat)^N ≤ 1 := by
    rw [div_le_one h_pow_pos]; exact h_pow_ge_one
  have h_step_nn : (0 : Rat) ≤ 1 / (2 : Rat)^N := by positivity
  have h_abs_step : |(1 : Rat) / (2 : Rat)^N| = 1 / (2 : Rat)^N := abs_of_nonneg h_step_nn
  calc |a.toRat + 1 / (2 : Rat)^N|
      ≤ |a.toRat| + |1 / (2 : Rat)^N| := abs_add_le _ _
    _ = |a.toRat| + 1 / (2 : Rat)^N := by rw [h_abs_step]
    _ ≤ |a.toRat| + 1 := by linarith

-- ============================================================
-- PART 2: THE SQUARE RULE
-- ============================================================

/-- **[I.T-IsDerivAt-Sq]** Square rule for the TauReal derivative:

    `IsDerivAt (fun x => fromTauRat (x · x)) a ((1·a) + (a·1))`

    on the disk `2·|a.toRat| ≤ 1` (i.e., `|a.toRat| ≤ 1/2`).

    Proof strategy: apply `IsDerivAt_mul` (Module 1's Leibniz) with
    `f = g = fun x => fromTauRat x`, both having derivative `TauReal.one`
    by `IsDerivAt_id`. The bound parameter `M = 2` is chosen to cover
    the worst-case dyadic shift at depth `N = 0` (where `dyadicStep 0 = 1`,
    giving `|a + 1| ≤ 3/2 ≤ 2`).

    The resulting derivative `((TauReal.one.mul (fromTauRat a)).add
    ((fromTauRat a).mul TauReal.one))` is the unsimplified Leibniz form;
    consumers who need the cleaner `fromTauRat (a.add a)` form can apply
    a simplification congruence (deferred to a later wave). -/
theorem TauReal.IsDerivAt_sq (a : TauRat) (ha : 2 * |a.toRat| ≤ 1) :
    TauReal.IsDerivAt
      (fun x : TauRat => TauReal.fromTauRat (TauRat.mul x x))
      a
      ((TauReal.one.mul (TauReal.fromTauRat a)).add
        ((TauReal.fromTauRat a).mul TauReal.one)) := by
  -- The function `fun x => fromTauRat (x · x)` equals
  -- `fun x => (fromTauRat x).mul (fromTauRat x)` definitionally, so we
  -- can directly apply Leibniz to f = g = fromTauRat.
  have h_id : TauReal.IsDerivAt (fun x => TauReal.fromTauRat x) a TauReal.one :=
    TauReal.IsDerivAt_id a
  -- Bounds with M = 2:
  --   |a.toRat| ≤ 1/2 ≤ 2.
  --   |(a + dyadicStep N).toRat| ≤ |a.toRat| + 1 ≤ 3/2 ≤ 2.
  --   |TauReal.one.approx n .toRat| = 1 ≤ 2.
  have h_a_abs : |a.toRat| ≤ (1 : Rat)/2 := by linarith
  have h_a_le_M : |a.toRat| ≤ (2 : Rat) := by linarith
  -- Bound: |(fromTauRat a).approx n|.abs.toRat ≤ 2
  have h_bound_fa : ∀ n, ((TauReal.fromTauRat a).approx n).abs.toRat ≤ (2 : Nat) := by
    intro n
    rw [fromTauRat_approx_abs_toRat]
    have : (((2 : Nat) : Rat) : Rat) = 2 := by norm_num
    show |a.toRat| ≤ ((2 : Nat) : Rat)
    have : ((2 : Nat) : Rat) = 2 := by norm_num
    linarith
  -- Bound: |TauReal.one.approx n|.abs.toRat ≤ 2
  have h_bound_one : ∀ n, (TauReal.one.approx n).abs.toRat ≤ (2 : Nat) := by
    intro n
    show (TauRat.one.abs).toRat ≤ ((2 : Nat) : Rat)
    rw [TauRat.toRat_abs, toRat_one]
    have : ((2 : Nat) : Rat) = 2 := by norm_num
    rw [this]; norm_num
  -- Bound: |(fun x => fromTauRat x) (a + dyad).approx n|.abs.toRat ≤ 2
  have h_bound_g_at_steps :
      ∀ N n, (((fun x : TauRat => TauReal.fromTauRat x)
                (a.add (TauRat.dyadicStep N))).approx n).abs.toRat ≤ (2 : Nat) := by
    intro N n
    show ((TauReal.fromTauRat (a.add (TauRat.dyadicStep N))).approx n).abs.toRat
        ≤ ((2 : Nat) : Rat)
    rw [fromTauRat_approx_abs_toRat]
    have h_shift := dyadicStep_shift_abs_le a N
    have : ((2 : Nat) : Rat) = 2 := by norm_num
    rw [this]
    linarith
  -- Apply Leibniz with M = 2 and the bounds above.
  exact TauReal.IsDerivAt_mul (f := fun x => TauReal.fromTauRat x)
                              (g := fun x => TauReal.fromTauRat x)
                              (a := a) (L_f := TauReal.one) (L_g := TauReal.one)
    2 (by norm_num : 1 ≤ 2)
    h_bound_fa h_bound_fa h_bound_g_at_steps
    h_bound_one h_bound_one
    h_id h_id

-- ============================================================
-- PART 3: THE CUBIC RULE
-- ============================================================

/-- Helper for the cubic rule: bound on `|q²|` for `|q.toRat| ≤ 3/2`. -/
private theorem sq_abs_bound_of_le_threehalves
    (q : TauRat) (h : |q.toRat| ≤ (3 : Rat)/2) :
    |(q.mul q).toRat| ≤ (9 : Rat)/4 := by
  rw [toRat_mul]
  rw [abs_mul]
  have h_nn : (0 : Rat) ≤ |q.toRat| := _root_.abs_nonneg _
  have h_le : (3 : Rat)/2 ≥ 0 := by norm_num
  calc |q.toRat| * |q.toRat|
      ≤ ((3 : Rat)/2) * |q.toRat| := by
        apply mul_le_mul_of_nonneg_right h h_nn
    _ ≤ ((3 : Rat)/2) * ((3 : Rat)/2) := by
        apply mul_le_mul_of_nonneg_left h h_le
    _ = (9 : Rat)/4 := by norm_num

/-- **[I.T-IsDerivAt-Cube]** Cubic rule for the TauReal derivative:

    `IsDerivAt (fun x => fromTauRat (x · (x · x))) a (Leibniz-form derivative)`

    on the disk `2·|a.toRat| ≤ 1`. The derivative's `.toRat` evaluates to `3a²`.

    Proof strategy: apply `IsDerivAt_mul` (Leibniz) with `f = fun x => fromTauRat x`
    (identity, derivative `TauReal.one`) and `g = fun x => fromTauRat (x · x)`
    (square, derivative from `IsDerivAt_sq`). Bound parameter `M = 4` accommodates
    the worst-case `|(a + dyadicStep 0)²| ≤ 9/4 ≤ 4`.

    Wave 2 deliverable — demonstrates the Leibniz-iteration pattern for higher
    monomial degrees. -/
theorem TauReal.IsDerivAt_cube (a : TauRat) (ha : 2 * |a.toRat| ≤ 1) :
    TauReal.IsDerivAt
      (fun x : TauRat => TauReal.fromTauRat (TauRat.mul x (TauRat.mul x x)))
      a
      ((TauReal.one.mul (TauReal.fromTauRat (TauRat.mul a a))).add
        ((TauReal.fromTauRat a).mul
          ((TauReal.one.mul (TauReal.fromTauRat a)).add
            ((TauReal.fromTauRat a).mul TauReal.one)))) := by
  have h_id : TauReal.IsDerivAt (fun x => TauReal.fromTauRat x) a TauReal.one :=
    TauReal.IsDerivAt_id a
  have h_sq : TauReal.IsDerivAt (fun x => TauReal.fromTauRat (TauRat.mul x x)) a
      ((TauReal.one.mul (TauReal.fromTauRat a)).add
        ((TauReal.fromTauRat a).mul TauReal.one)) := TauReal.IsDerivAt_sq a ha
  -- Bounds with M = 4:
  --   |a.toRat| ≤ 1/2 ≤ 4
  --   |(a + dyadicStep N).toRat| ≤ 3/2 ≤ 4
  --   |a².toRat| ≤ 1/4 ≤ 4
  --   |(a + dyad)².toRat| ≤ 9/4 ≤ 4
  --   |L_f|.abs.toRat = |TauReal.one.approx n|.abs.toRat = 1 ≤ 4
  --   |L_g|.abs.toRat = 2·|a.toRat| ≤ 1 ≤ 4
  have h_a_abs : |a.toRat| ≤ (1 : Rat)/2 := by linarith
  -- Bound: |(fromTauRat a).approx n|.abs.toRat ≤ 4
  have h_bound_fa : ∀ n, ((TauReal.fromTauRat a).approx n).abs.toRat ≤ (4 : Nat) := by
    intro n
    rw [fromTauRat_approx_abs_toRat]
    show |a.toRat| ≤ ((4 : Nat) : Rat)
    have : ((4 : Nat) : Rat) = 4 := by norm_num
    linarith
  -- Bound: |(fromTauRat (a · a)).approx n|.abs.toRat ≤ 4
  have h_bound_ga : ∀ n, ((TauReal.fromTauRat (TauRat.mul a a)).approx n).abs.toRat
                            ≤ (4 : Nat) := by
    intro n
    rw [fromTauRat_approx_abs_toRat]
    show |(a.mul a).toRat| ≤ ((4 : Nat) : Rat)
    rw [toRat_mul, abs_mul]
    have : ((4 : Nat) : Rat) = 4 := by norm_num
    rw [this]
    have h_nn : (0 : Rat) ≤ |a.toRat| := _root_.abs_nonneg _
    calc |a.toRat| * |a.toRat|
        ≤ ((1 : Rat)/2) * |a.toRat| := by
          apply mul_le_mul_of_nonneg_right h_a_abs h_nn
      _ ≤ ((1 : Rat)/2) * ((1 : Rat)/2) := by
          apply mul_le_mul_of_nonneg_left h_a_abs (by norm_num : (0 : Rat) ≤ (1 : Rat)/2)
      _ ≤ 4 := by norm_num
  -- Bound: |(fun x => fromTauRat (x · x)) (a + dyad).approx n|.abs.toRat ≤ 4
  have h_bound_g_at_steps :
      ∀ N n, (((fun x : TauRat => TauReal.fromTauRat (TauRat.mul x x))
                (a.add (TauRat.dyadicStep N))).approx n).abs.toRat ≤ (4 : Nat) := by
    intro N n
    show ((TauReal.fromTauRat ((a.add (TauRat.dyadicStep N)).mul
            (a.add (TauRat.dyadicStep N)))).approx n).abs.toRat ≤ ((4 : Nat) : Rat)
    rw [fromTauRat_approx_abs_toRat]
    have h_shift := dyadicStep_shift_abs_le a N
    have h_shift_le_threehalves : |(a.add (TauRat.dyadicStep N)).toRat| ≤ (3 : Rat)/2 := by
      linarith
    have h_sq_bound := sq_abs_bound_of_le_threehalves _ h_shift_le_threehalves
    have : ((4 : Nat) : Rat) = 4 := by norm_num
    rw [this]
    linarith
  -- Bound: |TauReal.one.approx n|.abs.toRat ≤ 4
  have h_bound_Lf : ∀ n, (TauReal.one.approx n).abs.toRat ≤ (4 : Nat) := by
    intro n
    show (TauRat.one.abs).toRat ≤ ((4 : Nat) : Rat)
    rw [TauRat.toRat_abs, toRat_one]
    have : ((4 : Nat) : Rat) = 4 := by norm_num
    rw [this]; norm_num
  -- Bound: |L_g|.abs.toRat ≤ 4 where L_g is the square rule's derivative.
  have h_bound_Lg : ∀ n, (((TauReal.one.mul (TauReal.fromTauRat a)).add
                            ((TauReal.fromTauRat a).mul TauReal.one)).approx n).abs.toRat
                            ≤ (4 : Nat) := by
    intro n
    show (TauRat.add (TauRat.mul TauRat.one a) (TauRat.mul a TauRat.one)).abs.toRat
            ≤ ((4 : Nat) : Rat)
    rw [TauRat.toRat_abs, toRat_add, toRat_mul, toRat_mul, toRat_one]
    have : ((4 : Nat) : Rat) = 4 := by norm_num
    rw [this]
    have h_eq : 1 * a.toRat + a.toRat * 1 = 2 * a.toRat := by ring
    rw [h_eq]
    have : |2 * a.toRat| = 2 * |a.toRat| := by
      rw [abs_mul]
      have h_two_nn : (0 : Rat) ≤ 2 := by norm_num
      rw [abs_of_nonneg h_two_nn]
    rw [this]
    linarith
  -- Apply Leibniz: f = identity, g = square, M = 4
  exact TauReal.IsDerivAt_mul
    (f := fun x => TauReal.fromTauRat x)
    (g := fun x => TauReal.fromTauRat (TauRat.mul x x))
    (a := a)
    (L_f := TauReal.one)
    (L_g := (TauReal.one.mul (TauReal.fromTauRat a)).add
              ((TauReal.fromTauRat a).mul TauReal.one))
    4 (by norm_num : 1 ≤ 4)
    h_bound_fa h_bound_ga h_bound_g_at_steps
    h_bound_Lf h_bound_Lg
    h_id h_sq

-- ============================================================
-- PART 4: IsDerivAt CONGRUENCE AT .toRat LEVEL
-- ============================================================

/-! ## Wave 3 — `IsDerivAt` `.toRat`-congruence lemma

  The `IsDerivAt` predicate's only access to `f`, `L` is through
  `.approx N` followed by `.abs.toRat` comparisons against `ofNatRecip k`.
  Since `TauRat.lt` is defined as Rat-level `<`, IsDerivAt is **invariant**
  under replacement of `f`, `L` by `g`, `L'` whose `.approx N` values are
  `.toRat`-equal at every depth `N`.

  This congruence lemma is the foundation for:
  - Simplifying Leibniz-form derivatives (e.g., to `fromTauRat (a.add a)`).
  - Building the general power rule via Nat-induction.
  - Bridging between TauRat-equivalent but structurally-different
    function representations.
-/

/-- **[I.T-IsDerivAt-Congr-toRat]** Congruence: `IsDerivAt` is invariant
    under `.toRat`-equality of function values and derivative at every
    approximation depth.

    If `f x` and `g x` are pointwise `.approx N .toRat`-equal at every
    `x` and `N`, and `L`, `L'` are `.approx N .toRat`-equal at every
    `N`, then `IsDerivAt f a L → IsDerivAt g a L'`.

    The proof transfers the modulus `μ` from `hf` and verifies that
    the scaled-difference-minus-derivative expression has identical
    `.toRat` value at every depth `N` (via toRat-distribution over add,
    mul, negate), so the strict-less-than bound carries over. -/
theorem TauReal.IsDerivAt_of_approx_toRat_eq
    {f g : TauRat → TauReal} {a : TauRat} {L L' : TauReal}
    (h_func : ∀ x N, ((f x).approx N).toRat = ((g x).approx N).toRat)
    (h_deriv : ∀ N, (L.approx N).toRat = (L'.approx N).toRat)
    (hf : TauReal.IsDerivAt f a L) : TauReal.IsDerivAt g a L' := by
  obtain ⟨μ, hμ⟩ := hf
  refine ⟨μ, fun k N hN => ?_⟩
  have h_f := hμ k N hN
  unfold TauRat.lt at h_f ⊢
  rw [TauRat.toRat_abs] at h_f ⊢
  -- Show: ((scaledDiff_f - L).approx N).toRat = ((scaledDiff_g - L').approx N).toRat
  -- Both sides unfold via toRat_add, toRat_mul, toRat_negate to the same Rat expression
  -- (modulo h_func and h_deriv substitutions).
  have h_eq :
      (((((f (a.add (TauRat.dyadicStep N))).sub (f a)).mul
            (TauReal.fromTauRat (TauRat.twoPowN N))).sub L).approx N).toRat
      = (((((g (a.add (TauRat.dyadicStep N))).sub (g a)).mul
            (TauReal.fromTauRat (TauRat.twoPowN N))).sub L').approx N).toRat := by
    -- Unfold both sides to flat Rat expressions
    show (TauRat.add
            (TauRat.mul
              (TauRat.add ((f (a.add (TauRat.dyadicStep N))).approx N)
                          (TauRat.negate ((f a).approx N)))
              ((TauReal.fromTauRat (TauRat.twoPowN N)).approx N))
            (TauRat.negate (L.approx N))).toRat
        = (TauRat.add
            (TauRat.mul
              (TauRat.add ((g (a.add (TauRat.dyadicStep N))).approx N)
                          (TauRat.negate ((g a).approx N)))
              ((TauReal.fromTauRat (TauRat.twoPowN N)).approx N))
            (TauRat.negate (L'.approx N))).toRat
    simp only [toRat_add, toRat_mul, toRat_negate]
    -- LHS .toRat = ((f(a+dyad).approx N).toRat - (f a).approx N .toRat) * (twoPowN N).toRat
    --             - (L.approx N).toRat
    -- RHS .toRat = same with g, L' substituted.
    -- By h_func: (f x).approx N .toRat = (g x).approx N .toRat for any x.
    -- By h_deriv: L.approx N .toRat = L'.approx N .toRat.
    rw [h_func (a.add (TauRat.dyadicStep N)) N]
    rw [h_func a N]
    rw [h_deriv N]
  rw [h_eq] at h_f
  exact h_f

-- ============================================================
-- PART 4b: TauRat POWER + BASIC LEMMAS (Wave 4 infrastructure)
-- ============================================================

/-! ## Wave 4 — general power rule via Nat-induction

  Ships `TauRat.pow_nat` (recursive) + bound lemmas + the general
  power rule:

      IsDerivAt (fun x => fromTauRat (x.pow_nat (k+1))) a (powDerivAcc a k)

  where `powDerivAcc a k` is the recursively-built TauReal whose `.toRat`
  evaluates to `(k+1) · a.toRat^k`.

  Proof by induction on `k`:
  - **Base k=0**: bridge from `IsDerivAt_id` to `IsDerivAt (pow_nat 1)`
    via the Wave 3 congruence lemma (since `pow_nat x 1 = x.mul one`
    is `.toRat`-equal to `x`).
  - **Step k → k+1**: apply `IsDerivAt_mul` (Leibniz) with `f = id` and
    `g = pow_nat (k+1)`, bound `M = 2^(k+2)` (covers `(3/2)^(k+2)` and
    `k+2`). The Leibniz output is structurally `powDerivAcc a (k+1)`.

  This unlocks differentiation of arbitrary polynomial expressions
  (sums, scalar multiples) at TauRat-input, which Module 3 uses for the
  arctan partial-sum differentiation.
-/

/-- `TauRat.pow_nat q k`: the k-th power of `q` as a TauRat. Recursive. -/
def TauRat.pow_nat (q : TauRat) : Nat → TauRat
  | 0     => TauRat.one
  | n + 1 => q.mul (q.pow_nat n)

/-- `q^0 = 1`. -/
theorem TauRat.pow_nat_zero (q : TauRat) : q.pow_nat 0 = TauRat.one := rfl

/-- `q^(k+1) = q · q^k`. -/
theorem TauRat.pow_nat_succ (q : TauRat) (k : Nat) :
    q.pow_nat (k+1) = q.mul (q.pow_nat k) := rfl

/-- `(q^k).toRat = q.toRat^k`. -/
theorem TauRat.pow_nat_toRat (q : TauRat) (k : Nat) :
    (q.pow_nat k).toRat = q.toRat ^ k := by
  induction k with
  | zero =>
    show TauRat.one.toRat = q.toRat ^ 0
    rw [toRat_one, pow_zero]
  | succ k ih =>
    show (q.mul (q.pow_nat k)).toRat = q.toRat ^ (k+1)
    rw [toRat_mul, ih, pow_succ]
    ring

/-- Bound: `|q^k|.toRat ≤ M^k` when `|q.toRat| ≤ M`. -/
theorem TauRat.pow_nat_abs_toRat_le (q : TauRat) (M : Rat) (k : Nat)
    (hq : |q.toRat| ≤ M) :
    |(q.pow_nat k).toRat| ≤ M^k := by
  rw [TauRat.pow_nat_toRat, abs_pow]
  exact pow_le_pow_left₀ (_root_.abs_nonneg _) hq k

-- ============================================================
-- PART 5: CLEAN-FORM DERIVATIVES VIA CONGRUENCE
-- ============================================================

/-- **[I.T-IsDerivAt-Sq-Clean]** Clean-form square rule: the derivative
    expressed as `fromTauRat (a.add a)` instead of the messy Leibniz
    output `((TauReal.one.mul (fromTauRat a)).add ((fromTauRat a).mul
    TauReal.one))`.

    Both forms have `.toRat = 2·a.toRat` at every depth, so they are
    `.toRat`-equivalent and IsDerivAt transfers via the congruence lemma.

    Downstream consumers should prefer this form when the cleaner
    expression matters (e.g., in algebraic manipulation). -/
theorem TauReal.IsDerivAt_sq_clean (a : TauRat) (ha : 2 * |a.toRat| ≤ 1) :
    TauReal.IsDerivAt
      (fun x : TauRat => TauReal.fromTauRat (TauRat.mul x x))
      a
      (TauReal.fromTauRat (a.add a)) := by
  apply TauReal.IsDerivAt_of_approx_toRat_eq
    (f := fun x : TauRat => TauReal.fromTauRat (TauRat.mul x x))
    (L := (TauReal.one.mul (TauReal.fromTauRat a)).add
            ((TauReal.fromTauRat a).mul TauReal.one))
    (h_func := fun _ _ => rfl)
  · intro N
    show (TauRat.add (TauRat.mul TauRat.one a) (TauRat.mul a TauRat.one)).toRat
        = (a.add a).toRat
    simp only [toRat_add, toRat_mul, toRat_one]
    ring
  · exact TauReal.IsDerivAt_sq a ha

-- ============================================================
-- PART 6: powDerivAcc + GENERAL POWER RULE BY INDUCTION
-- ============================================================

/-- `powDerivAcc a k`: the Leibniz-form derivative of `x^(k+1)` evaluated
    at `x = a`. Recursive — at level `k+1`, it's the Leibniz output of
    applying the product rule to `x · x^(k+1)` (using the previous
    accumulator at level `k`).

    Mathematically, `(powDerivAcc a k).toRat = (k+1) · a.toRat^k`. -/
def TauReal.powDerivAcc (a : TauRat) : Nat → TauReal
  | 0     => TauReal.one
  | k + 1 => (TauReal.one.mul (TauReal.fromTauRat (a.pow_nat (k+1)))).add
              ((TauReal.fromTauRat a).mul (TauReal.powDerivAcc a k))

/-- `(powDerivAcc a k).approx N .toRat = (k+1) · a.toRat^k`. -/
theorem TauReal.powDerivAcc_approx_toRat (a : TauRat) (k : Nat) (N : Nat) :
    ((TauReal.powDerivAcc a k).approx N).toRat = ((k+1 : Nat) : Rat) * a.toRat^k := by
  induction k with
  | zero =>
    show (TauRat.one).toRat = ((0+1 : Nat) : Rat) * a.toRat^0
    rw [toRat_one]
    norm_num
  | succ k ih =>
    show (TauRat.add
            (TauRat.mul TauRat.one (a.pow_nat (k+1)))
            (TauRat.mul a ((TauReal.powDerivAcc a k).approx N))).toRat
        = ((k+1+1 : Nat) : Rat) * a.toRat^(k+1)
    rw [toRat_add, toRat_mul, toRat_mul, toRat_one]
    rw [TauRat.pow_nat_toRat, ih]
    have h_cast : ((k+1+1 : Nat) : Rat) = ((k+1 : Nat) : Rat) + 1 := by push_cast; ring
    rw [h_cast]
    rw [pow_succ]
    ring

/-- Bound: `|powDerivAcc a k .approx N|.toRat ≤ (k+1)` when `2·|a.toRat| ≤ 1`. -/
theorem TauReal.powDerivAcc_abs_approx_toRat_le
    (a : TauRat) (k : Nat) (N : Nat) (ha : 2 * |a.toRat| ≤ 1) :
    |((TauReal.powDerivAcc a k).approx N).toRat| ≤ ((k+1 : Nat) : Rat) := by
  rw [TauReal.powDerivAcc_approx_toRat]
  rw [abs_mul, abs_pow]
  have h_a_le_one : |a.toRat| ≤ 1 := by linarith
  have h_a_nn : (0 : Rat) ≤ |a.toRat| := _root_.abs_nonneg _
  have h_pow_le_one : |a.toRat|^k ≤ 1 := by
    have : |a.toRat|^k ≤ (1 : Rat)^k := pow_le_pow_left₀ h_a_nn h_a_le_one k
    simpa using this
  have h_cast_nn : (0 : Rat) ≤ ((k+1 : Nat) : Rat) := by exact_mod_cast Nat.zero_le _
  have h_abs_cast : |((k+1 : Nat) : Rat)| = ((k+1 : Nat) : Rat) := abs_of_nonneg h_cast_nn
  rw [h_abs_cast]
  calc ((k+1 : Nat) : Rat) * |a.toRat|^k
      ≤ ((k+1 : Nat) : Rat) * 1 := by
        apply mul_le_mul_of_nonneg_left h_pow_le_one h_cast_nn
    _ = ((k+1 : Nat) : Rat) := by ring

/-- Helper: `k + 1 ≤ 2^(k+1)`. -/
private theorem succ_le_two_pow_succ (k : Nat) : k + 1 ≤ 2^(k+1) := by
  induction k with
  | zero => norm_num
  | succ k ih =>
    have h_pow_pos : 1 ≤ 2^(k+1) := Nat.one_le_pow _ _ (by norm_num)
    calc k + 1 + 1
        ≤ 2^(k+1) + 2^(k+1) := by omega
      _ = 2^(k+2) := by ring

/-- Helper: `(3/2 : Rat)^k ≤ 2^k` for any `k`. -/
private theorem pow_three_half_le_two_pow (k : Nat) : ((3 : Rat)/2)^k ≤ (2 : Rat)^k := by
  apply pow_le_pow_left₀ (by norm_num : (0 : Rat) ≤ 3/2) (by norm_num : (3 : Rat)/2 ≤ 2)

/-- **[I.T-IsDerivAt-Pow-Zero]** Power rule base case: `IsDerivAt x^1`.

    `pow_nat x 1 = x.mul TauRat.one` differs from `x` structurally but
    is `.toRat`-equal. The congruence lemma `IsDerivAt_of_approx_toRat_eq`
    bridges from `IsDerivAt_id`. -/
theorem TauReal.IsDerivAt_pow_nat_zero (a : TauRat) :
    TauReal.IsDerivAt (fun x : TauRat => TauReal.fromTauRat (x.pow_nat 1)) a
                      (TauReal.powDerivAcc a 0) := by
  apply TauReal.IsDerivAt_of_approx_toRat_eq
    (f := fun x : TauRat => TauReal.fromTauRat x)
    (L := TauReal.one)
  · intro x N
    show x.toRat = (x.mul TauRat.one).toRat
    rw [toRat_mul, toRat_one]; ring
  · intro N; rfl
  · exact TauReal.IsDerivAt_id a

/-- **[I.T-IsDerivAt-Pow-Step]** Power rule inductive step: from
    `IsDerivAt x^(k+1)` derive `IsDerivAt x^(k+2)`.

    Applies `IsDerivAt_mul` (Leibniz) with `f = identity`, `g = pow_nat (k+1)`,
    bound parameter `M = 2^(k+1)`. The Leibniz output is structurally
    `powDerivAcc a (k+1)` by definition. -/
theorem TauReal.IsDerivAt_pow_nat_succ_step
    (a : TauRat) (k : Nat) (ha : 2 * |a.toRat| ≤ 1)
    (IH : TauReal.IsDerivAt (fun x : TauRat => TauReal.fromTauRat (x.pow_nat (k+1))) a
                            (TauReal.powDerivAcc a k)) :
    TauReal.IsDerivAt (fun x : TauRat => TauReal.fromTauRat (x.pow_nat (k+2))) a
                      (TauReal.powDerivAcc a (k+1)) := by
  have h_id : TauReal.IsDerivAt (fun x : TauRat => TauReal.fromTauRat x) a TauReal.one :=
    TauReal.IsDerivAt_id a
  -- Choose M = 2^(k+1)
  set M : Nat := 2^(k+1) with hM_def
  have hM_pos : 1 ≤ M := by
    simp only [hM_def]
    exact Nat.one_le_pow _ _ (by norm_num)
  have h_a_abs_half : |a.toRat| ≤ (1 : Rat)/2 := by linarith
  have h_a_abs_le_one : |a.toRat| ≤ 1 := by linarith
  -- M as Rat ≥ 1
  have hM_rat_pos : (1 : Rat) ≤ (M : Rat) := by exact_mod_cast hM_pos
  -- M as Rat ≥ k+1
  have hM_ge_succ : ((k+1 : Nat) : Rat) ≤ (M : Rat) := by
    have : k + 1 ≤ M := by simp only [hM_def]; exact succ_le_two_pow_succ k
    exact_mod_cast this
  -- M as Rat = 2^(k+1)
  have hM_rat : ((M : Nat) : Rat) = (2 : Rat)^(k+1) := by
    simp only [hM_def]; push_cast; ring
  -- Bound: |a.toRat| ≤ M
  have h_bound_fa : ∀ n, ((TauReal.fromTauRat a).approx n).abs.toRat ≤ (M : Nat) := by
    intro n
    rw [fromTauRat_approx_abs_toRat]
    show |a.toRat| ≤ ((M : Nat) : Rat)
    linarith
  -- Bound: |a.pow_nat (k+1)|.toRat ≤ 1 ≤ M
  have h_bound_ga : ∀ n, ((TauReal.fromTauRat (a.pow_nat (k+1))).approx n).abs.toRat
                            ≤ (M : Nat) := by
    intro n
    rw [fromTauRat_approx_abs_toRat]
    show |(a.pow_nat (k+1)).toRat| ≤ ((M : Nat) : Rat)
    have h_a_bound := TauRat.pow_nat_abs_toRat_le a 1 (k+1) h_a_abs_le_one
    calc |(a.pow_nat (k+1)).toRat|
        ≤ (1 : Rat)^(k+1) := h_a_bound
      _ = 1 := one_pow _
      _ ≤ (M : Rat) := hM_rat_pos
  -- Bound: |(a + dyad N).pow_nat (k+1)|.toRat ≤ (3/2)^(k+1) ≤ 2^(k+1) = M
  have h_bound_g_at_steps :
      ∀ N n, (((fun x : TauRat => TauReal.fromTauRat (x.pow_nat (k+1)))
                (a.add (TauRat.dyadicStep N))).approx n).abs.toRat ≤ (M : Nat) := by
    intro N n
    show ((TauReal.fromTauRat ((a.add (TauRat.dyadicStep N)).pow_nat (k+1))).approx n).abs.toRat
        ≤ ((M : Nat) : Rat)
    rw [fromTauRat_approx_abs_toRat]
    have h_shift := dyadicStep_shift_abs_le a N
    have h_shift_le_threehalves :
        |(a.add (TauRat.dyadicStep N)).toRat| ≤ (3 : Rat)/2 := by linarith
    have h_pow_bound := TauRat.pow_nat_abs_toRat_le
                          (a.add (TauRat.dyadicStep N)) (3/2) (k+1) h_shift_le_threehalves
    have h_three_half_le_two : ((3 : Rat)/2)^(k+1) ≤ (2 : Rat)^(k+1) :=
      pow_three_half_le_two_pow (k+1)
    rw [hM_rat]
    linarith
  -- Bound: |TauReal.one.approx n|.abs.toRat = 1 ≤ M
  have h_bound_Lf : ∀ n, (TauReal.one.approx n).abs.toRat ≤ (M : Nat) := by
    intro n
    show TauRat.one.abs.toRat ≤ ((M : Nat) : Rat)
    rw [TauRat.toRat_abs, toRat_one]
    have h_abs : |(1 : Rat)| = 1 := by norm_num
    rw [h_abs]
    exact hM_rat_pos
  -- Bound: |powDerivAcc a k|.toRat ≤ k+1 ≤ M
  have h_bound_Lg : ∀ n, ((TauReal.powDerivAcc a k).approx n).abs.toRat ≤ (M : Nat) := by
    intro n
    rw [TauRat.toRat_abs]
    have h_bd := TauReal.powDerivAcc_abs_approx_toRat_le a k n ha
    show |((TauReal.powDerivAcc a k).approx n).toRat| ≤ ((M : Nat) : Rat)
    linarith
  -- Apply Leibniz: f = identity, g = pow_nat (k+1)
  -- Function becomes fun x => fromTauRat (x.pow_nat (k+2)) by definitional equality
  -- (pow_nat (k+2) = x.mul (pow_nat (k+1))).
  -- Derivative becomes powDerivAcc a (k+1) by definition.
  exact TauReal.IsDerivAt_mul
    (f := fun x : TauRat => TauReal.fromTauRat x)
    (g := fun x : TauRat => TauReal.fromTauRat (x.pow_nat (k+1)))
    (a := a) (L_f := TauReal.one) (L_g := TauReal.powDerivAcc a k)
    M hM_pos
    h_bound_fa h_bound_ga h_bound_g_at_steps
    h_bound_Lf h_bound_Lg
    h_id IH

/-- **[I.T-IsDerivAt-Pow]** General power rule for the TauReal derivative:

    `IsDerivAt (fun x => fromTauRat (x.pow_nat (k+1))) a (powDerivAcc a k)`

    on the disk `2·|a.toRat| ≤ 1`, for every natural number `k`.

    Proof: induction on `k`, using the base case `IsDerivAt_pow_nat_zero`
    (bridged from `IsDerivAt_id` via the `.toRat`-congruence) and the
    inductive step `IsDerivAt_pow_nat_succ_step` (Leibniz with growing M). -/
theorem TauReal.IsDerivAt_pow_nat (a : TauRat) (k : Nat) (ha : 2 * |a.toRat| ≤ 1) :
    TauReal.IsDerivAt
      (fun x : TauRat => TauReal.fromTauRat (x.pow_nat (k+1))) a
      (TauReal.powDerivAcc a k) := by
  induction k with
  | zero => exact TauReal.IsDerivAt_pow_nat_zero a
  | succ k IH => exact TauReal.IsDerivAt_pow_nat_succ_step a k ha IH

end Tau.Boundary
