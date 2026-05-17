import TauLib.BookI.Boundary.TauRealInv
import TauLib.BookI.Boundary.TauRealAnalyticalHelpers
import Mathlib.Tactic.Ring
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity

/-!
# TauLib.BookI.Boundary.TauRealDerivative

The **TauReal derivative** predicate `IsDerivAt`, defined via the
dyadic-step difference quotient.

## Wave Γ₈ Phase 2.6.B.2.β.4.9 — Module 1

For a function `f : TauRat → TauReal`, the derivative at point `a : TauRat`
is the limit (as the step `h_N = 1/2^N` tends to zero) of the **scaled
difference quotient**

    (f(a + h_N) − f(a)) · 2^N

at TauReal-equivalence level. The "limit" is encoded constructively via
an explicit modulus `μ : Nat → Nat` such that for every tolerance `k`
and every step exponent `N ≥ μ k`, the difference quotient is within
`1/(k+1)` of the claimed derivative `L : TauReal` at depth `N`.

### Why dyadic steps `h_N = 1/2^N`?

* Matches the existing Cauchy infrastructure (`Rat.four_div_two_pow_lt_recip`
  workhorse from TauRealAnalyticalHelpers.lean).
* Provides natural sub-division for the discrete Gronwall lemma's dyadic
  grid argument (TauRealGronwall.lean).
* Native to `TauRat.ofNatRecip`: `ofNatRecip (2^N - 1) = 1/2^N` for `N ≥ 0`.

This module ships the **core definitions** (IsDerivAt, dyadic step
helpers). Linearity (sum/scalar), product (Leibniz), chain rules, and
the constant rule are queued for follow-up after the basic definition
infrastructure stabilises in downstream usage.
-/

set_option autoImplicit false

namespace Tau.Boundary

open Tau.Denotation

-- ============================================================
-- PART 1: HELPERS — TauRat constructions for dyadic steps
-- ============================================================

/-- The dyadic step `h_N = 1/2^N` as a TauRat.

    Using `TauRat.ofNatRecip (2^N - 1)`: since `ofNatRecip k = 1/(k+1)`,
    we get `1/(2^N - 1 + 1) = 1/2^N`. For `N = 0` this gives `1`, for
    `N ≥ 1` it gives the standard dyadic step. -/
def TauRat.dyadicStep (N : Nat) : TauRat :=
  TauRat.ofNatRecip (2^N - 1)

/-- `2^N` embedded as a TauRat with denominator 1. -/
def TauRat.twoPowN (N : Nat) : TauRat :=
  ⟨TauInt.fromNat (2^N), 1, Nat.one_pos⟩

/-- `dyadicStep N .toRat = 1 / 2^N`. -/
theorem TauRat.dyadicStep_toRat (N : Nat) :
    (TauRat.dyadicStep N).toRat = 1 / (2 : Rat)^N := by
  unfold TauRat.dyadicStep
  rw [TauRat.ofNatRecip_toRat]
  have h_pos : 1 ≤ 2^N := Nat.one_le_pow N 2 (by norm_num)
  have h_nat : (2^N - 1 + 1 : Nat) = 2^N := by omega
  have h_cast : (((2^N - 1 : Nat) : Rat) + 1) = (2 : Rat)^N := by
    have h_left : ((2^N - 1 + 1 : Nat) : Rat) = ((2^N : Nat) : Rat) := by
      exact_mod_cast h_nat
    have h_split : ((2^N - 1 + 1 : Nat) : Rat) = ((2^N - 1 : Nat) : Rat) + 1 := by
      push_cast; ring
    have h_pow : ((2^N : Nat) : Rat) = (2 : Rat)^N := by push_cast; ring
    linarith
  rw [h_cast]

/-- `twoPowN N .toRat = 2^N`. -/
theorem TauRat.twoPowN_toRat (N : Nat) :
    (TauRat.twoPowN N).toRat = (2 : Rat)^N := by
  unfold TauRat.twoPowN TauRat.toRat TauInt.toInt TauInt.fromNat
  push_cast
  ring

/-- `dyadicStep N · twoPowN N = 1` at Rat level (multiplicative inverses). -/
theorem TauRat.dyadicStep_mul_twoPowN_toRat (N : Nat) :
    (TauRat.dyadicStep N).toRat * (TauRat.twoPowN N).toRat = 1 := by
  rw [TauRat.dyadicStep_toRat, TauRat.twoPowN_toRat]
  have h_pos : (0 : Rat) < (2 : Rat)^N := by positivity
  field_simp

-- ============================================================
-- PART 2: IsDerivAt DEFINITION
-- ============================================================

/-- **[I.D-IsDerivAt]** `IsDerivAt f a L`: f has derivative L at TauRat point a.

    Constructively: there exists `μ : Nat → Nat` such that for every
    tolerance level `k` and step exponent `N ≥ μ k`, the scaled difference
    quotient

        (f(a + 1/2^N) − f(a)) · 2^N

    is within `1/(k+1)` of `L` at depth-N TauRat approximation level.

    The scaled-difference form (multiplying by `2^N` rather than dividing
    by `h_N`) avoids the need to invoke `TauReal.inv` and matches the
    discrete Gronwall lemma's natural step structure. -/
def TauReal.IsDerivAt (f : TauRat → TauReal) (a : TauRat) (L : TauReal) : Prop :=
  ∃ μ : Nat → Nat, ∀ k N : Nat, μ k ≤ N →
    TauRat.lt
      (((((f (a.add (TauRat.dyadicStep N))).sub (f a)).mul
            (TauReal.fromTauRat (TauRat.twoPowN N))).sub L).approx N).abs
      (TauRat.ofNatRecip k)

-- ============================================================
-- PART 3: CONSTANT RULE
-- ============================================================

/-- **[I.T-IsDerivAt-Const]** The constant function `fun _ => c` has
    derivative `TauReal.zero` at every point.

    Proof: `(c - c) · 2^N = 0` at TauReal level, so the scaled
    difference is zero in every approximation. Modulus is `fun _ => 0`. -/
theorem TauReal.IsDerivAt_const (c : TauReal) (a : TauRat) :
    TauReal.IsDerivAt (fun _ => c) a TauReal.zero := by
  refine ⟨fun _ => 0, fun k N _ => ?_⟩
  unfold TauRat.lt
  rw [TauRat.toRat_abs, TauRat.ofNatRecip_toRat]
  -- Compute the inner .toRat = 0 via step-by-step unfolding
  -- The expression at depth N: ((c - c) · 2^N - 0).approx N
  -- = TauRat.add ((c-c).mul ...).approx N (TauRat.negate TauRat.zero)
  -- = TauRat.add (TauRat.mul ((c-c).approx N) (...)) (...)
  -- = TauRat.mul (TauRat.add (c.approx N) (TauRat.negate (c.approx N))) ... etc.
  -- All toRat values cancel to 0.
  have h_zero : ((((((fun _ : TauRat => c) (a.add (TauRat.dyadicStep N))).sub
                  ((fun _ : TauRat => c) a)).mul
                (TauReal.fromTauRat (TauRat.twoPowN N))).sub
                TauReal.zero).approx N).toRat = 0 := by
    -- Beta-reduces (fun _ => c) applications
    show (((((c).sub c).mul
              (TauReal.fromTauRat (TauRat.twoPowN N))).sub
            TauReal.zero).approx N).toRat = 0
    -- Expand (.sub TauReal.zero).approx N
    show (TauRat.add
            (((c.sub c).mul (TauReal.fromTauRat (TauRat.twoPowN N))).approx N)
            ((TauReal.zero.negate).approx N)).toRat = 0
    rw [toRat_add]
    -- (TauReal.zero.negate).approx N .toRat = 0
    have h_neg_zero : ((TauReal.zero.negate).approx N).toRat = 0 := by
      show (TauRat.negate (TauReal.zero.approx N)).toRat = 0
      show (TauRat.negate TauRat.zero).toRat = 0
      rw [toRat_negate, toRat_zero]
      ring
    rw [h_neg_zero]
    -- ((c.sub c).mul ...).approx N .toRat = 0 · ... = 0
    have h_mul_zero :
        (((c.sub c).mul (TauReal.fromTauRat (TauRat.twoPowN N))).approx N).toRat = 0 := by
      show (TauRat.mul ((c.sub c).approx N)
              ((TauReal.fromTauRat (TauRat.twoPowN N)).approx N)).toRat = 0
      rw [toRat_mul]
      -- (c.sub c).approx N .toRat = 0 via add+negate cancellation
      have h_diff : ((c.sub c).approx N).toRat = 0 := by
        show ((c.add c.negate).approx N).toRat = 0
        show (TauRat.add (c.approx N) ((c.negate).approx N)).toRat = 0
        show (TauRat.add (c.approx N) (TauRat.negate (c.approx N))).toRat = 0
        rw [toRat_add, toRat_negate]
        ring
      rw [h_diff]
      ring
    rw [h_mul_zero]
    ring
  rw [h_zero, abs_zero]
  -- Goal: 0 < 1/((k:Rat)+1)
  have h_k : (0 : Rat) ≤ (k : Rat) := by exact_mod_cast Nat.zero_le k
  have h_pos : (0 : Rat) < (k : Rat) + 1 := by linarith
  exact div_pos (by norm_num : (0 : Rat) < 1) h_pos

-- ============================================================
-- PART 4: IDENTITY RULE
-- ============================================================

/-- **[I.T-IsDerivAt-Id]** The identity function `fromTauRat` has derivative
    `TauReal.one` at every point.

    The scaled difference quotient is exactly
        ((a₀ + 1/2^N) - a₀) · 2^N = (1/2^N) · 2^N = 1
    at every depth (Rat-exact), so it equals `TauReal.one` exactly up to
    equivalence. Modulus is `fun _ => 0`. -/
theorem TauReal.IsDerivAt_id (a₀ : TauRat) :
    TauReal.IsDerivAt (fun a => TauReal.fromTauRat a) a₀ TauReal.one := by
  refine ⟨fun _ => 0, fun k N _ => ?_⟩
  unfold TauRat.lt
  rw [TauRat.toRat_abs, TauRat.ofNatRecip_toRat]
  -- Compute the inner toRat = 0:
  -- scaledDiff = (fromTauRat (a₀ + h_N) - fromTauRat a₀) · fromTauRat (2^N)
  -- At depth N, .toRat = ((a₀.toRat + h_N.toRat) - a₀.toRat) · 2^N.toRat = h_N.toRat · 2^N.toRat = 1
  -- (scaledDiff.sub TauReal.one).approx N .toRat = 1 - 1 = 0
  have h_inner :
      ((((((fun a => TauReal.fromTauRat a) (a₀.add (TauRat.dyadicStep N))).sub
            ((fun a => TauReal.fromTauRat a) a₀)).mul
          (TauReal.fromTauRat (TauRat.twoPowN N))).sub
          TauReal.one).approx N).toRat = 0 := by
    -- Beta-reduce: (fun a => fromTauRat a) x = fromTauRat x
    show ((((((TauReal.fromTauRat (a₀.add (TauRat.dyadicStep N))).sub
              (TauReal.fromTauRat a₀)).mul
            (TauReal.fromTauRat (TauRat.twoPowN N))).sub
            TauReal.one).approx N).toRat = 0)
    -- Outer .sub structure: ((X.sub Y).approx N).toRat
    show (TauRat.add
            ((((TauReal.fromTauRat (a₀.add (TauRat.dyadicStep N))).sub
                (TauReal.fromTauRat a₀)).mul
              (TauReal.fromTauRat (TauRat.twoPowN N))).approx N)
            (TauReal.one.negate.approx N)).toRat = 0
    rw [toRat_add]
    -- TauReal.one.negate.approx N .toRat = -1
    have h_neg_one : (TauReal.one.negate.approx N).toRat = -1 := by
      show (TauRat.negate TauRat.one).toRat = -1
      rw [toRat_negate, toRat_one]
    rw [h_neg_one]
    -- The scaledDiff at depth N .toRat = 1
    have h_scaled :
        (((((TauReal.fromTauRat (a₀.add (TauRat.dyadicStep N))).sub
              (TauReal.fromTauRat a₀)).mul
            (TauReal.fromTauRat (TauRat.twoPowN N))).approx N)).toRat = 1 := by
      show (TauRat.mul
              ((((TauReal.fromTauRat (a₀.add (TauRat.dyadicStep N))).sub
                  (TauReal.fromTauRat a₀)).approx N))
              ((TauReal.fromTauRat (TauRat.twoPowN N)).approx N)).toRat = 1
      rw [toRat_mul]
      -- (fromTauRat x).approx N = x (constant sequence)
      -- so ((fromTauRat A).sub (fromTauRat B)).approx N = TauRat.add A (negate B)
      have h_diff :
          (((TauReal.fromTauRat (a₀.add (TauRat.dyadicStep N))).sub
              (TauReal.fromTauRat a₀)).approx N).toRat = (TauRat.dyadicStep N).toRat := by
        show (TauRat.add (a₀.add (TauRat.dyadicStep N)) (TauRat.negate a₀)).toRat
            = (TauRat.dyadicStep N).toRat
        rw [toRat_add, toRat_add, toRat_negate]
        ring
      have h_two :
          ((TauReal.fromTauRat (TauRat.twoPowN N)).approx N).toRat
            = (TauRat.twoPowN N).toRat := rfl
      rw [h_diff, h_two]
      exact TauRat.dyadicStep_mul_twoPowN_toRat N
    rw [h_scaled]
    ring
  rw [h_inner, abs_zero]
  have h_k : (0 : Rat) ≤ (k : Rat) := by exact_mod_cast Nat.zero_le k
  have h_pos : (0 : Rat) < (k : Rat) + 1 := by linarith
  exact div_pos (by norm_num : (0 : Rat) < 1) h_pos

-- ============================================================
-- PART 5: SUM RULE
-- ============================================================

/-- **Helper**: scaled-difference at depth N split into f-part + g-part (Rat level).

    The sum-rule's key algebraic identity, stated at the Rat-arithmetic
    level (after all TauReal operations and `.approx N` and `.toRat` have
    been unfolded). -/
private theorem scaledDiff_add_split
    (Fh Ga Fa Gh : TauRat) (Lf Lg : TauRat) (t : TauRat) :
    (TauRat.add
        (TauRat.mul
          (TauRat.add
            (TauRat.add Fh Gh)
            (TauRat.negate (TauRat.add Fa Ga)))
          t)
        (TauRat.negate (TauRat.add Lf Lg))).toRat
    = (TauRat.add
          (TauRat.mul (TauRat.add Fh (TauRat.negate Fa)) t)
          (TauRat.negate Lf)).toRat
      + (TauRat.add
          (TauRat.mul (TauRat.add Gh (TauRat.negate Ga)) t)
          (TauRat.negate Lg)).toRat := by
  simp only [toRat_add, toRat_mul, toRat_negate]
  ring

/-- **[I.T-IsDerivAt-Add]** Sum rule for the TauReal derivative:

        IsDerivAt f a L_f, IsDerivAt g a L_g  ⟹  IsDerivAt (f + g) a (L_f + L_g)

    Modulus: max(μ_f(2k+1), μ_g(2k+1)) using the standard "halve the
    tolerance" pattern from `TauReal.equiv_trans`. -/
theorem TauReal.IsDerivAt_add
    {f g : TauRat → TauReal} {a : TauRat} {L_f L_g : TauReal}
    (hf : TauReal.IsDerivAt f a L_f) (hg : TauReal.IsDerivAt g a L_g) :
    TauReal.IsDerivAt (fun x => (f x).add (g x)) a (L_f.add L_g) := by
  obtain ⟨μ_f, hμ_f⟩ := hf
  obtain ⟨μ_g, hμ_g⟩ := hg
  refine ⟨fun k => max (μ_f (2*k+1)) (μ_g (2*k+1)), fun k N hN => ?_⟩
  have hN_f : μ_f (2*k+1) ≤ N := le_of_max_le_left hN
  have hN_g : μ_g (2*k+1) ≤ N := le_of_max_le_right hN
  have h_f := hμ_f (2*k+1) N hN_f
  have h_g := hμ_g (2*k+1) N hN_g
  unfold TauRat.lt at h_f h_g ⊢
  rw [TauRat.toRat_abs, TauRat.ofNatRecip_toRat] at h_f h_g ⊢
  -- Define short names for the depth-N values
  set Fh : TauRat := (f (a.add (TauRat.dyadicStep N))).approx N with hFh
  set Ga : TauRat := (g a).approx N with hGa
  set Fa : TauRat := (f a).approx N with hFa
  set Gh : TauRat := (g (a.add (TauRat.dyadicStep N))).approx N with hGh
  set Lf : TauRat := L_f.approx N with hLf
  set Lg : TauRat := L_g.approx N with hLg
  set t : TauRat := (TauReal.fromTauRat (TauRat.twoPowN N)).approx N with ht
  -- Algebraic split of the sum's toRat
  have h_split := scaledDiff_add_split Fh Ga Fa Gh Lf Lg t
  -- The .approx N of TauReal-level expressions matches the TauRat-level form
  have h_LHS_eq :
      (((((fun x => (f x).add (g x)) (a.add (TauRat.dyadicStep N))).sub
            ((fun x => (f x).add (g x)) a)).mul
          (TauReal.fromTauRat (TauRat.twoPowN N))).sub
          (L_f.add L_g)).approx N
      = TauRat.add
          (TauRat.mul
            (TauRat.add (TauRat.add Fh Gh) (TauRat.negate (TauRat.add Fa Ga))) t)
          (TauRat.negate (TauRat.add Lf Lg)) := rfl
  have h_RHS_f_eq :
      ((((f (a.add (TauRat.dyadicStep N))).sub (f a)).mul
          (TauReal.fromTauRat (TauRat.twoPowN N))).sub L_f).approx N
      = TauRat.add (TauRat.mul (TauRat.add Fh (TauRat.negate Fa)) t)
                    (TauRat.negate Lf) := rfl
  have h_RHS_g_eq :
      ((((g (a.add (TauRat.dyadicStep N))).sub (g a)).mul
          (TauReal.fromTauRat (TauRat.twoPowN N))).sub L_g).approx N
      = TauRat.add (TauRat.mul (TauRat.add Gh (TauRat.negate Ga)) t)
                    (TauRat.negate Lg) := rfl
  rw [h_LHS_eq]
  rw [h_RHS_f_eq] at h_f
  rw [h_RHS_g_eq] at h_g
  -- h_split: LHS.toRat = f-part.toRat + g-part.toRat
  rw [h_split]
  -- Triangle inequality + tolerance arithmetic
  have h_tri : |(TauRat.add (TauRat.mul (TauRat.add Fh (TauRat.negate Fa)) t)
                              (TauRat.negate Lf)).toRat
                + (TauRat.add (TauRat.mul (TauRat.add Gh (TauRat.negate Ga)) t)
                              (TauRat.negate Lg)).toRat|
              ≤ |(TauRat.add (TauRat.mul (TauRat.add Fh (TauRat.negate Fa)) t)
                              (TauRat.negate Lf)).toRat|
                + |(TauRat.add (TauRat.mul (TauRat.add Gh (TauRat.negate Ga)) t)
                              (TauRat.negate Lg)).toRat| := abs_add_le _ _
  have h_eq : (1 : Rat) / (((2*k+1 : Nat) : Rat) + 1) + 1 / (((2*k+1 : Nat) : Rat) + 1)
              = 1 / ((k : Rat) + 1) := by
    push_cast; field_simp; ring
  linarith

-- ============================================================
-- PART 6: NEGATION RULE
-- ============================================================

/-- **Helper**: the negated scaled-difference at depth N (Rat level).

    Algebraic identity: the scaled-difference of `(-f)` at depth N is
    the negation of `f`'s scaled-difference, both at the .toRat level. -/
private theorem scaledDiff_neg_split
    (Fh Fa Lf : TauRat) (t : TauRat) :
    (TauRat.add
        (TauRat.mul
          (TauRat.add (TauRat.negate Fh) (TauRat.negate (TauRat.negate Fa)))
          t)
        (TauRat.negate (TauRat.negate Lf))).toRat
    = -((TauRat.add
            (TauRat.mul (TauRat.add Fh (TauRat.negate Fa)) t)
            (TauRat.negate Lf)).toRat) := by
  simp only [toRat_add, toRat_mul, toRat_negate]
  ring

/-- **[I.T-IsDerivAt-Neg]** Negation rule for the TauReal derivative:

        IsDerivAt f a L_f  ⟹  IsDerivAt (-f) a (-L_f). -/
theorem TauReal.IsDerivAt_neg
    {f : TauRat → TauReal} {a : TauRat} {L_f : TauReal}
    (hf : TauReal.IsDerivAt f a L_f) :
    TauReal.IsDerivAt (fun x => (f x).negate) a L_f.negate := by
  obtain ⟨μ, hμ⟩ := hf
  refine ⟨μ, fun k N hN => ?_⟩
  have h_f := hμ k N hN
  unfold TauRat.lt at h_f ⊢
  rw [TauRat.toRat_abs, TauRat.ofNatRecip_toRat] at h_f ⊢
  -- Set up names for depth-N values
  set Fh : TauRat := (f (a.add (TauRat.dyadicStep N))).approx N with hFh
  set Fa : TauRat := (f a).approx N with hFa
  set Lf : TauRat := L_f.approx N with hLf
  set t : TauRat := (TauReal.fromTauRat (TauRat.twoPowN N)).approx N with ht
  -- LHS .approx N unfolds to a TauRat expression via rfl
  have h_lhs_eq :
      (((((fun x => (f x).negate) (a.add (TauRat.dyadicStep N))).sub
            ((fun x => (f x).negate) a)).mul
          (TauReal.fromTauRat (TauRat.twoPowN N))).sub
          L_f.negate).approx N
      = TauRat.add
          (TauRat.mul
            (TauRat.add (TauRat.negate Fh) (TauRat.negate (TauRat.negate Fa)))
            t)
          (TauRat.negate (TauRat.negate Lf)) := rfl
  have h_f_eq :
      ((((f (a.add (TauRat.dyadicStep N))).sub (f a)).mul
          (TauReal.fromTauRat (TauRat.twoPowN N))).sub L_f).approx N
      = TauRat.add (TauRat.mul (TauRat.add Fh (TauRat.negate Fa)) t)
                    (TauRat.negate Lf) := rfl
  rw [h_lhs_eq]
  rw [h_f_eq] at h_f
  rw [scaledDiff_neg_split, abs_neg]
  exact h_f

-- ============================================================
-- PART 7: DIFFERENCE RULE
-- ============================================================

/-- **[I.T-IsDerivAt-Sub]** Difference rule for the TauReal derivative:

        IsDerivAt f a L_f, IsDerivAt g a L_g  ⟹
          IsDerivAt (fun x => (f x).sub (g x)) a (L_f.sub L_g).

    Derived from `IsDerivAt_add` + `IsDerivAt_neg` (via TauReal.sub def). -/
theorem TauReal.IsDerivAt_sub
    {f g : TauRat → TauReal} {a : TauRat} {L_f L_g : TauReal}
    (hf : TauReal.IsDerivAt f a L_f) (hg : TauReal.IsDerivAt g a L_g) :
    TauReal.IsDerivAt (fun x => (f x).sub (g x)) a (L_f.sub L_g) := by
  -- (f x).sub (g x) = (f x).add ((g x).negate)
  -- L_f.sub L_g = L_f.add L_g.negate
  -- Apply add rule with hg replaced by IsDerivAt_neg hg
  have h_neg_g := TauReal.IsDerivAt_neg hg
  have h_add := TauReal.IsDerivAt_add hf h_neg_g
  -- h_add: IsDerivAt (fun x => (f x).add ((g x).negate)) a (L_f.add L_g.negate)
  -- TauReal.sub is defined as add ∘ negate, so this is definitionally what we want.
  exact h_add

-- ============================================================
-- PART 8: CONSTANT SCALAR RULE  (with bound)
-- ============================================================

/-- **Helper**: constant-scalar scaled-difference at depth N (Rat level).

    Algebraic identity: the scaled-difference of `c · f` at depth N is
    `c · (scaled-difference of f)`, at the .toRat level. -/
private theorem scaledDiff_constMul_split
    (c Fh Fa Lf t : TauRat) :
    (TauRat.add
        (TauRat.mul
          (TauRat.add (TauRat.mul c Fh) (TauRat.negate (TauRat.mul c Fa)))
          t)
        (TauRat.negate (TauRat.mul c Lf))).toRat
    = c.toRat * ((TauRat.add
                    (TauRat.mul (TauRat.add Fh (TauRat.negate Fa)) t)
                    (TauRat.negate Lf)).toRat) := by
  simp only [toRat_add, toRat_mul, toRat_negate]
  ring

/-- **[I.T-IsDerivAt-ConstScale]** Constant-scalar rule for the TauReal derivative:

        IsDerivAt f a L_f, (c is bounded)  ⟹
          IsDerivAt (fun x => c · f x) a (c · L_f).

    Modulus: μ_f(M·k + M − 1) where M is a Nat upper bound on |c|.
    Justification: M · (1/(Mk+M)) = 1/(k+1). -/
theorem TauReal.IsDerivAt_const_mul
    {f : TauRat → TauReal} {a : TauRat} {L_f : TauReal}
    (c : TauReal) (M : Nat) (hM : 1 ≤ M)
    (h_bound : ∀ n, (c.approx n).abs.toRat ≤ M)
    (hf : TauReal.IsDerivAt f a L_f) :
    TauReal.IsDerivAt (fun x => c.mul (f x)) a (c.mul L_f) := by
  obtain ⟨μ, hμ⟩ := hf
  refine ⟨fun k => μ (M*k + M - 1), fun k N hN => ?_⟩
  have h_f := hμ (M*k + M - 1) N hN
  unfold TauRat.lt at h_f ⊢
  rw [TauRat.toRat_abs, TauRat.ofNatRecip_toRat] at h_f ⊢
  -- Set up names
  set Fh : TauRat := (f (a.add (TauRat.dyadicStep N))).approx N with hFh
  set Fa : TauRat := (f a).approx N with hFa
  set Lf : TauRat := L_f.approx N with hLf
  set cN : TauRat := c.approx N with hcN
  set t : TauRat := (TauReal.fromTauRat (TauRat.twoPowN N)).approx N with ht
  -- LHS .approx N: definitionally TauRat-level expression
  have h_lhs_eq :
      (((((fun x => c.mul (f x)) (a.add (TauRat.dyadicStep N))).sub
            ((fun x => c.mul (f x)) a)).mul
          (TauReal.fromTauRat (TauRat.twoPowN N))).sub
          (c.mul L_f)).approx N
      = TauRat.add
          (TauRat.mul
            (TauRat.add (TauRat.mul cN Fh) (TauRat.negate (TauRat.mul cN Fa)))
            t)
          (TauRat.negate (TauRat.mul cN Lf)) := rfl
  have h_f_eq :
      ((((f (a.add (TauRat.dyadicStep N))).sub (f a)).mul
          (TauReal.fromTauRat (TauRat.twoPowN N))).sub L_f).approx N
      = TauRat.add (TauRat.mul (TauRat.add Fh (TauRat.negate Fa)) t)
                    (TauRat.negate Lf) := rfl
  rw [h_lhs_eq]
  rw [h_f_eq] at h_f
  rw [scaledDiff_constMul_split]
  rw [abs_mul]
  -- Now: |cN.toRat| · |inner.toRat| < 1/((k:Rat)+1)
  -- Bounds: |cN.toRat| ≤ M (from h_bound at depth N), |inner.toRat| < 1/((Mk+M-1:Nat)+1) = 1/(Mk+M)
  -- M · 1/(Mk+M) = 1/(k+1). ✓
  have h_c_bound : |TauRat.toRat cN| ≤ (M : Rat) := by
    have h := h_bound N
    rw [TauRat.toRat_abs] at h
    exact h
  have h_inner_nn : (0 : Rat) ≤
      |(((Fh.add Fa.negate).mul t).add Lf.negate).toRat| := by
    apply _root_.abs_nonneg
  -- The cast for the inner tolerance
  have h_cast : (((M * k + M - 1 : Nat) : Rat) + 1) = (M : Rat) * ((k : Rat) + 1) := by
    have hM_pos : 1 ≤ M * k + M := by
      have : M ≥ 1 := hM
      omega
    have hN_pos : 0 < M * k + M := by omega
    have h_nat : (M * k + M - 1 + 1 : Nat) = M * k + M := by omega
    push_cast
    have : ((M * k + M - 1 : Nat) : Rat) + 1 = ((M * k + M : Nat) : Rat) := by
      have h_cast_eq : (((M * k + M - 1 + 1) : Nat) : Rat) = ((M * k + M : Nat) : Rat) := by
        exact_mod_cast h_nat
      have h_split : (((M * k + M - 1 + 1) : Nat) : Rat) = ((M * k + M - 1 : Nat) : Rat) + 1 := by
        push_cast; ring
      linarith
    rw [this]
    push_cast
    ring
  rw [h_cast] at h_f
  -- Goal: |cN.toRat| · |inner| < 1/(k+1). h_f: |inner| < 1/(M(k+1)).
  -- |cN.toRat| ≤ M, so |cN.toRat| · |inner| ≤ M · |inner| < M · 1/(M(k+1)) = 1/(k+1).
  have hM_pos : (0 : Rat) < (M : Rat) := by exact_mod_cast (Nat.lt_of_lt_of_le Nat.zero_lt_one hM)
  have h_k1_pos : (0 : Rat) < (k : Rat) + 1 := by
    have : (0 : Rat) ≤ (k : Rat) := by exact_mod_cast Nat.zero_le k
    linarith
  have h_Mk1_pos : (0 : Rat) < (M : Rat) * ((k : Rat) + 1) := mul_pos hM_pos h_k1_pos
  calc |cN.toRat| * |((TauRat.add
                        (TauRat.mul (TauRat.add Fh (TauRat.negate Fa)) t)
                        (TauRat.negate Lf)).toRat)|
      ≤ (M : Rat) * |((TauRat.add
                        (TauRat.mul (TauRat.add Fh (TauRat.negate Fa)) t)
                        (TauRat.negate Lf)).toRat)| := by
        exact mul_le_mul_of_nonneg_right h_c_bound h_inner_nn
    _ < (M : Rat) * (1 / ((M : Rat) * ((k : Rat) + 1))) := by
        exact mul_lt_mul_of_pos_left h_f hM_pos
    _ = 1 / ((k : Rat) + 1) := by
        field_simp

end Tau.Boundary
