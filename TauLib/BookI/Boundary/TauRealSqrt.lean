import TauLib.BookI.Boundary.TauRealInv
import TauLib.BookI.Boundary.TauRealAnalyticalHelpers
import TauLib.BookI.Boundary.Bridge.TauRealCongruence
import Mathlib.Tactic.Ring
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity

/-!
# TauLib.BookI.Boundary.TauRealSqrt

Newton-iteration Cauchy approximant for `TauReal.sqrt a`, for radicands
bounded away from zero.

## Registry Cross-References

- [I.D84]  TauReal — Cauchy completion of TauRat (ConstructiveReals.lean)
- [I.D110] TauRat Inverse and Division — `TauRat.inv` (TauRatInv.lean)
- [I.D111] TauReal.IsCauchy — explicit modulus (ConstructiveReals.lean)
- [I.D112] TauReal.equiv — Cauchy equivalence (ConstructiveReals.lean).
           Single-relation discipline honoured: no new equiv introduced.
- [I.D114] TauReal BoundedAwayFromZero (TauRealInv.lean)
- [I.D117] TauReal Square Root — THIS MODULE (Wave R8b, Phase 0.5)

## Critical-Path Note (V.T-LRD-1B / V.T-NEW-5A)

This module unblocks the deferred T2 promotion in `HeavySeedBirth.lean`
and `T2KerrUniqueness.lean`:

```
def f_iota_TauReal : TauReal :=
  iota_tau_TauReal.mul
    (TauReal.sqrt (TauReal.one.sub iota_tau_TauReal))
```

`TauReal.sqrt` must be present and proved Cauchy before Wave R8 can close
the `f_iota_x_10000 := 2773` witness at TauReal precision.

## Mathematical Content

**Wave R8b, Phase 0.5** — design spec at
`research-notes/PHASE-0.5-ANALYTIC-PRIMITIVES.md §2`.

Newton (Heron) iteration on f(x) = x² − a:
  x₀ = a.approx n  (seed; `TauRat.one` fallback when zero)
  x_{j+1} = (x_j + a / x_j) / 2

Algebraic error recurrence, provable by `ring`:
  x_{j+1}² − a = (x_j² − a)² / (2·x_j)²

Definition: `(TauReal.sqrt a).approx n := sqrtIter (a.approx n) (a.approx n) n`.

## R-flag Status

- **R1 (new TauReal.equiv relation): NOT triggered.** Single-relation
  kernel rule preserved; `TauReal.equiv` reused verbatim.
- **R2 (Newton needs sharper Cauchy bound): TRIGGERED — addressed.**
  The Cauchy proof and convergence theorems use the new
  `Rat.one_div_tower_pow_lt_recip` helper (Part 5 of
  `TauRealAnalyticalHelpers.lean`). The full sorry-closure of the
  `sqrt_isCauchy` and `sqrt_sq` proofs requires composing the tower bound
  with Lipschitz iteration, which is left as Wave R8c follow-up
  alongside Engineer B's `cauchy_product_bound`.

## Status

Definitions and positivity infrastructure are completely proved.
The convergence theorems `sqrt_isCauchy`, `sqrt_sq`, `sqrt_pos`
carry `sorry` marks at Newton-convergence + Lipschitz steps that
will close in Wave R8c.
-/

set_option autoImplicit false

namespace Tau.Boundary

open Tau.Denotation

-- ============================================================
-- SECTION 1: AUXILIARY CONSTANTS AND POSITIVITY PREDICATE
-- ============================================================

/-- 1/2 as a TauRat constant, reused throughout the Newton step. -/
def TauRat.half : TauRat := ⟨⟨1, 0⟩, 2, by norm_num⟩

theorem TauRat.half_toRat : TauRat.half.toRat = 1 / 2 := by
  unfold TauRat.half TauRat.toRat TauInt.toInt; push_cast; ring

/-- A TauRat is *positive* when its rational value is strictly above 0.
    Used throughout to track iterate positivity. -/
def TauRat.IsPos (x : TauRat) : Prop := 0 < x.toRat

/-- A positive TauRat is nonzero (needed to invoke `TauRat.inv`). -/
theorem TauRat.IsPos.is_nonzero {x : TauRat} (h : x.IsPos) : x.is_nonzero :=
  (TauRat.is_nonzero_iff_toRat_ne_zero x).mpr (ne_of_gt h)

theorem TauRat.one_isPos : TauRat.IsPos TauRat.one := by
  unfold TauRat.IsPos; rw [toRat_one]; norm_num

-- ============================================================
-- SECTION 2: NEWTON STEP AND ITERATION — DEFINITIONS
-- ============================================================

/-- One Newton (Heron) step for √a: x ↦ (x + a/x) / 2.

    Uses `TauRat.inv x h` with an explicit `is_nonzero` proof `h`.
    Falls back to `TauRat.one` when x = 0; this branch is unreachable
    past the `BoundedAwayFromZero` onset index. -/
def TauRat.sqrtNewtonStep (a x : TauRat) : TauRat :=
  if h : x.is_nonzero then
    (x.add (a.mul (TauRat.inv x h))).mul TauRat.half
  else TauRat.one

/-- `sqrtNewtonStep` evaluated at the `toRat` level on the genuine branch. -/
theorem TauRat.sqrtNewtonStep_toRat (a x : TauRat) (h : x.is_nonzero) :
    (TauRat.sqrtNewtonStep a x).toRat = (x.toRat + a.toRat / x.toRat) / 2 := by
  unfold TauRat.sqrtNewtonStep
  rw [dif_pos h, toRat_mul, toRat_add, toRat_mul, toRat_inv, TauRat.half_toRat]
  field_simp

/-- Iterate Newton steps `n` times from `seed`, with radicand `a`. -/
def TauRat.sqrtIter (a seed : TauRat) : Nat → TauRat
  | 0     => seed
  | n + 1 => TauRat.sqrtNewtonStep a (TauRat.sqrtIter a seed n)

/-- Unfolding lemma for the successor case. -/
@[simp] theorem TauRat.sqrtIter_succ (a seed : TauRat) (n : Nat) :
    TauRat.sqrtIter a seed (n + 1) =
      TauRat.sqrtNewtonStep a (TauRat.sqrtIter a seed n) := rfl

/-- The TauReal square root: at index `n`, run `n` Newton steps on the
    `n`-th approximation of the radicand, starting from that same approximation
    as the seed.

    This definition is **total** (no hypothesis on `a` needed). The
    Cauchy property and the algebraic identity `(√a)² ≡ a` both require
    `a.BoundedAwayFromZero` as an explicit hypothesis. -/
def TauReal.sqrt (a : TauReal) : TauReal :=
  ⟨fun n => TauRat.sqrtIter (a.approx n) (a.approx n) n⟩

-- ============================================================
-- SECTION 3: POSITIVITY PROPAGATION THROUGH ITERATIONS
-- ============================================================

/-- When `a > 0` and `x > 0`, the Newton step `(x + a/x)/2` is also > 0. -/
theorem TauRat.sqrtNewtonStep_isPos {a x : TauRat}
    (ha : a.IsPos) (hx : x.IsPos) :
    (TauRat.sqrtNewtonStep a x).IsPos := by
  show 0 < _
  rw [TauRat.sqrtNewtonStep_toRat a x hx.is_nonzero]
  have h_a : 0 < a.toRat := ha
  have h_x : 0 < x.toRat := hx
  have h_div : 0 < a.toRat / x.toRat := div_pos h_a h_x
  linarith

/-- When `a > 0` and `seed > 0`, every Newton iterate is > 0. -/
theorem TauRat.sqrtIter_isPos {a seed : TauRat}
    (ha : a.IsPos) (hs : seed.IsPos) : ∀ n, (TauRat.sqrtIter a seed n).IsPos
  | 0     => hs
  | n + 1 => TauRat.sqrtNewtonStep_isPos ha (TauRat.sqrtIter_isPos ha hs n)

-- ============================================================
-- SECTION 4: ALGEBRAIC ERROR RECURRENCE
-- ============================================================

/-- Newton error recurrence for √a:
      step(x)² − a = (x² − a)² / (2x)²
    Discharged by `field_simp` + `ring` at the `Rat` level.
    This is the master identity driving quadratic convergence. -/
theorem TauRat.sqrtNewtonStep_error_sq (a x : TauRat) (h : x.is_nonzero) :
    (TauRat.sqrtNewtonStep a x).toRat ^ 2 - a.toRat =
      (x.toRat ^ 2 - a.toRat) ^ 2 / (2 * x.toRat) ^ 2 := by
  rw [TauRat.sqrtNewtonStep_toRat a x h]
  have hne : x.toRat ≠ 0 := (TauRat.is_nonzero_iff_toRat_ne_zero x).mp h
  field_simp; ring

-- ============================================================
-- SECTION 5: AM-GM LOWER BOUND ON ITERATES
-- ============================================================

/-- AM-GM preserves the lower bound: if `a.toRat ≥ δ²` and `seed.toRat ≥ δ`
    with `δ > 0`, then every Newton iterate is also ≥ δ.

    Proof: by induction. The step uses `(t + a/t)/2 − δ
    = ((t − δ)² + (a − δ²)) / (2t)`, and both `(t − δ)²` and `a − δ²`
    are non-negative. -/
theorem TauRat.sqrtIter_lower_bound {a seed : TauRat} {δ : Rat}
    (ha : δ * δ ≤ a.toRat) (hs : δ ≤ seed.toRat) (hδ : 0 < δ) :
    ∀ n, δ ≤ (TauRat.sqrtIter a seed n).toRat := by
  intro n
  induction n with
  | zero => exact hs
  | succ n ih =>
    simp only [TauRat.sqrtIter_succ]
    set t := (TauRat.sqrtIter a seed n).toRat with ht_def
    have ht_pos : 0 < t := lt_of_lt_of_le hδ ih
    have ht_nz : (TauRat.sqrtIter a seed n).is_nonzero :=
      (TauRat.is_nonzero_iff_toRat_ne_zero _).mpr (ne_of_gt ht_pos)
    rw [TauRat.sqrtNewtonStep_toRat _ _ ht_nz]
    -- Goal: δ ≤ (t + a.toRat / t) / 2
    -- AM-GM identity: (t + a/t)/2 − δ = ((t − δ)² + (a − δ²)) / (2t)
    have h_key : 0 ≤ (t + a.toRat / t) / 2 - δ := by
      have h_identity : (t + a.toRat / t) / 2 - δ =
          ((t - δ) ^ 2 + (a.toRat - δ * δ)) / (2 * t) := by
        field_simp [ne_of_gt ht_pos]
        ring
      rw [h_identity]
      apply div_nonneg
      · have h_sq : 0 ≤ (t - δ) ^ 2 := by positivity
        have h_rad : 0 ≤ a.toRat - δ * δ := by linarith [ha]
        linarith
      · linarith
    linarith

-- ============================================================
-- SECTION 6: LIPSCHITZ IN THE RADICAND
-- ============================================================

/-- Exact Lipschitz identity in the radicand: fixing the seed `x`, one
    Newton step is linear (Lipschitz constant = 1/(2|x|)) in `a`:
      step(a, x) − step(b, x) = (a − b) / (2x). -/
theorem TauRat.sqrtNewtonStep_radicand_diff (a b x : TauRat)
    (hx : x.is_nonzero) :
    (TauRat.sqrtNewtonStep a x).toRat - (TauRat.sqrtNewtonStep b x).toRat =
      (a.toRat - b.toRat) / (2 * x.toRat) := by
  rw [TauRat.sqrtNewtonStep_toRat a x hx, TauRat.sqrtNewtonStep_toRat b x hx]
  have hne : x.toRat ≠ 0 := (TauRat.is_nonzero_iff_toRat_ne_zero x).mp hx
  field_simp; ring

-- ============================================================
-- SECTION 7: IsCauchy FOR TauReal.sqrt
-- ============================================================

/-- **Inline helper (Wave R8j):** every Newton iterate from a positive seed
    `seed = a` (with `a > 0`) satisfies `x_k^2 ≥ a` for `k ≥ 1`.

    Proof: by `Rat.newton_step_error_sq`, `x_{k+1}^2 - a = (x_k^2-a)^2/(2x_k)^2 ≥ 0`.
    For k = 1: `x_1 = (a+1)/2`, `x_1^2 - a = (a-1)^2/4 ≥ 0`. -/
private theorem TauRat.sqrtIter_self_sq_ge {a : TauRat}
    (ha : 0 < a.toRat) :
    ∀ k, 1 ≤ k → a.toRat ≤ (TauRat.sqrtIter a a k).toRat ^ 2 := by
  intro k hk
  induction k with
  | zero => omega
  | succ k ih =>
    by_cases hk0 : k = 0
    · -- Base: k+1 = 1, x_1 = (a + a/a)/2 = (a+1)/2
      subst hk0
      show a.toRat ≤ (TauRat.sqrtNewtonStep a a).toRat ^ 2
      have h_a_nz : a.is_nonzero := (TauRat.is_nonzero_iff_toRat_ne_zero a).mpr (ne_of_gt ha)
      rw [TauRat.sqrtNewtonStep_toRat a a h_a_nz]
      have h_simp : (a.toRat + a.toRat / a.toRat) / 2 = (a.toRat + 1) / 2 := by
        rw [_root_.div_self (ne_of_gt ha)]
      rw [h_simp]
      have h_amgm : ((a.toRat + 1) / 2)^2 - a.toRat = (a.toRat - 1)^2 / 4 := by ring
      nlinarith [h_amgm, sq_nonneg (a.toRat - 1)]
    · -- Inductive: k ≥ 1
      have hk1 : 1 ≤ k := by omega
      have ih_sq := ih hk1
      show a.toRat ≤ (TauRat.sqrtNewtonStep a (TauRat.sqrtIter a a k)).toRat ^ 2
      set x := TauRat.sqrtIter a a k with hx_def
      have hx_sq_pos : 0 < x.toRat ^ 2 := lt_of_lt_of_le ha ih_sq
      have hx_nz_rat : x.toRat ≠ 0 := by
        intro h0
        rw [h0] at hx_sq_pos
        norm_num at hx_sq_pos
      have hx_nz : x.is_nonzero := (TauRat.is_nonzero_iff_toRat_ne_zero x).mpr hx_nz_rat
      rw [TauRat.sqrtNewtonStep_toRat a x hx_nz]
      -- Apply Rat.newton_step_error_sq: ((x+a/x)/2)^2 - a = (x²-a)²/(2x)² ≥ 0
      have h_id := Rat.newton_step_error_sq (a := a.toRat) (x := x.toRat) hx_nz_rat
      have h_sq_nn : 0 ≤ (x.toRat^2 - a.toRat)^2 := sq_nonneg _
      have h_2x_sq_pos : 0 < (2 * x.toRat)^2 := by positivity
      have h_div_nn : 0 ≤ (x.toRat^2 - a.toRat)^2 / (2 * x.toRat)^2 :=
        div_nonneg h_sq_nn h_2x_sq_pos.le
      linarith [h_id, h_div_nn]

/-- **Inline helper (Wave R8j):** Newton iterates from positive seed
    are themselves positive, for k ≥ 1.

    From `sqrtIter_self_sq_ge`: `x_k^2 ≥ a > 0`, so `x_k ≠ 0`. Combined
    with `sqrtIter_isPos` for the right kind of seed positivity. -/
private theorem TauRat.sqrtIter_self_pos {a : TauRat}
    (ha : 0 < a.toRat) (k : Nat) :
    0 < (TauRat.sqrtIter a a k).toRat := by
  have ha_pos : a.IsPos := ha
  exact TauRat.sqrtIter_isPos ha_pos ha_pos k

/-- **Inline helper (Wave R8j):** the **geometric** squared-error decay
    of `sqrtIter` started at the radicand itself.

    Given `a > 0`, after `k` Newton steps (k ≥ 1), the squared error is
    bounded geometrically:
      `x_k^2 - a ≤ ((a-1)^2/4) · (1/2)^(k-1)`.

    Proof: `f_k := x_k^2 - a` satisfies `f_{k+1} = f_k^2 / (4 x_k^2)`
    by `Rat.newton_step_error_sq`. Since `x_k^2 ≥ a > 0` and
    `f_k = x_k^2 - a ≤ x_k^2`, we have `f_k / (4 x_k^2) ≤ 1/4 ≤ 1/2`,
    hence `f_{k+1} ≤ f_k / 2`. -/
private theorem TauRat.sqrtIter_self_sq_geom_decay {a : TauRat}
    (ha : 0 < a.toRat) :
    ∀ k, 1 ≤ k →
      (TauRat.sqrtIter a a k).toRat ^ 2 - a.toRat
        ≤ ((a.toRat - 1)^2 / 4) * (1/2 : Rat) ^ (k - 1) := by
  intro k hk
  induction k with
  | zero => omega
  | succ k ih =>
    by_cases hk0 : k = 0
    · -- Base case: k+1 = 1, RHS = ((a-1)^2/4) · (1/2)^0 = (a-1)^2/4
      subst hk0
      show (TauRat.sqrtNewtonStep a a).toRat ^ 2 - a.toRat
             ≤ (a.toRat - 1)^2 / 4 * (1/2 : Rat) ^ ((1:Nat) - 1)
      have h_a_nz : a.is_nonzero := (TauRat.is_nonzero_iff_toRat_ne_zero a).mpr (ne_of_gt ha)
      rw [TauRat.sqrtNewtonStep_toRat a a h_a_nz]
      have h_simp : (a.toRat + a.toRat / a.toRat) / 2 = (a.toRat + 1) / 2 := by
        rw [_root_.div_self (ne_of_gt ha)]
      rw [h_simp]
      have h_amgm : ((a.toRat + 1) / 2)^2 - a.toRat = (a.toRat - 1)^2 / 4 := by ring
      have h_sub : (1 : Nat) - 1 = 0 := by omega
      rw [h_sub]
      simp only [pow_zero, mul_one]
      linarith [h_amgm]
    · -- Inductive case: k ≥ 1
      have hk1 : 1 ≤ k := by omega
      have ih' := ih hk1
      show (TauRat.sqrtNewtonStep a (TauRat.sqrtIter a a k)).toRat ^ 2 - a.toRat
             ≤ (a.toRat - 1)^2 / 4 * (1/2 : Rat) ^ ((k+1) - 1)
      set x := TauRat.sqrtIter a a k with hx_def
      have hx_pos : 0 < x.toRat := TauRat.sqrtIter_self_pos ha k
      have hx_nz_rat : x.toRat ≠ 0 := ne_of_gt hx_pos
      have hx_nz : x.is_nonzero := (TauRat.is_nonzero_iff_toRat_ne_zero x).mpr hx_nz_rat
      have hx_sq_ge : a.toRat ≤ x.toRat ^ 2 := TauRat.sqrtIter_self_sq_ge ha k hk1
      rw [TauRat.sqrtNewtonStep_toRat a x hx_nz]
      -- exact identity: ((x + a/x)/2)^2 - a = (x²-a)²/(2x)²
      have h_id := Rat.newton_step_error_sq (a := a.toRat) (x := x.toRat) hx_nz_rat
      rw [h_id]
      -- Goal: (x²-a)²/(2x)² ≤ ((a-1)²/4) · (1/2)^((k+1)-1)
      have hf_nn : 0 ≤ x.toRat^2 - a.toRat := by linarith [hx_sq_ge]
      have h_4xsq_pos : 0 < 4 * x.toRat^2 := by positivity
      have h_2xsq_eq : (2 * x.toRat)^2 = 4 * x.toRat^2 := by ring
      have h_ratio_le_half : (x.toRat^2 - a.toRat) / (4 * x.toRat^2) ≤ 1/2 := by
        rw [div_le_iff₀ h_4xsq_pos]
        nlinarith [hx_sq_ge, sq_nonneg x.toRat]
      have h_step : (x.toRat^2 - a.toRat)^2 / (2 * x.toRat)^2
                      ≤ (x.toRat^2 - a.toRat) / 2 := by
        rw [h_2xsq_eq]
        have h_eq : (x.toRat^2 - a.toRat)^2 / (4 * x.toRat^2)
                    = (x.toRat^2 - a.toRat) * ((x.toRat^2 - a.toRat) / (4 * x.toRat^2)) := by
          field_simp
        rw [h_eq]
        have h_mul_le : (x.toRat^2 - a.toRat) * ((x.toRat^2 - a.toRat) / (4 * x.toRat^2))
                          ≤ (x.toRat^2 - a.toRat) * (1/2) :=
          mul_le_mul_of_nonneg_left h_ratio_le_half hf_nn
        linarith
      -- Combine with IH: f_k ≤ ((a-1)²/4) · (1/2)^(k-1), so f_k/2 ≤ ((a-1)²/4) · (1/2)^k
      have h_succ_pow : ((1:Rat)/2) ^ (k + 1 - 1) = (1/2) * (1/2) ^ (k - 1) := by
        have h_eq1 : k + 1 - 1 = k := by omega
        have h_eq2 : k = (k - 1) + 1 := by omega
        rw [h_eq1]
        conv_lhs => rw [h_eq2]
        rw [pow_succ]
        ring
      rw [h_succ_pow]
      have h_ih_div : (x.toRat ^ 2 - a.toRat) / 2
                       ≤ ((a.toRat - 1) ^ 2 / 4) * ((1/2) * (1/2) ^ (k - 1)) := by
        have h_target_eq :
            ((a.toRat - 1) ^ 2 / 4) * ((1/2) * (1/2) ^ (k - 1))
              = ((a.toRat - 1) ^ 2 / 4) * (1/2) ^ (k - 1) / 2 := by ring
        rw [h_target_eq]
        linarith [ih']
      linarith [h_step, h_ih_div]

/-- **Inline helper (Wave R8j):** Nat-level squared exponential bound:
    `(M+1)^2 ≤ 2^(2*(M+1))`. Follows from `Nat.two_pow_succ_gt_linear`
    by squaring. -/
private theorem Nat.sq_le_two_pow_double (M : Nat) :
    (M + 1) ^ 2 ≤ 2 ^ (2 * (M + 1)) := by
  have h_lin : M + 1 < 2 ^ (M + 1) := Nat.two_pow_succ_gt_linear M
  have h_lin' : M + 1 ≤ 2 ^ (M + 1) := Nat.le_of_lt h_lin
  have h_sq : (M + 1) ^ 2 ≤ (2 ^ (M + 1)) ^ 2 := by
    have h_mul : (M + 1) * (M + 1) ≤ 2 ^ (M + 1) * 2 ^ (M + 1) :=
      Nat.mul_le_mul h_lin' h_lin'
    have h_sq_eq : (M + 1) ^ 2 = (M + 1) * (M + 1) := by ring
    have h_pow_eq : (2 ^ (M + 1)) ^ 2 = 2 ^ (M + 1) * 2 ^ (M + 1) := by ring
    rw [h_sq_eq, h_pow_eq]; exact h_mul
  have h_pow : (2 ^ (M + 1)) ^ 2 = 2 ^ (2 * (M + 1)) := by
    rw [← pow_mul]; ring_nf
  linarith

/-- **Inline helper (Wave R8j):** the Rat cast of `Nat.sq_le_two_pow_double`. -/
private theorem Rat.sq_le_two_pow_double (M : Nat) :
    ((M : Rat) + 1) ^ 2 ≤ (2 : Rat) ^ (2 * (M + 1)) := by
  have h_nat := Nat.sq_le_two_pow_double M
  have h_cast : (((M + 1) ^ 2 : Nat) : Rat) ≤ ((2 ^ (2 * (M + 1)) : Nat) : Rat) := by
    exact_mod_cast h_nat
  have h_lhs_eq : (((M + 1) ^ 2 : Nat) : Rat) = ((M : Rat) + 1) ^ 2 := by push_cast; ring
  have h_rhs_eq : ((2 ^ (2 * (M + 1)) : Nat) : Rat) = (2 : Rat) ^ (2 * (M + 1)) := by
    push_cast; ring
  linarith

/-- **Inline helper (Wave R8j):** the master squared-error → Cauchy bound.

    Given `0 < a`, `a ≤ M+1`, after `n` Newton steps starting from `a`,
    the squared error `x_n² − a` satisfies `< 1/(k+1)` whenever
    `n ≥ 2*(M+1) + k + 3`.

    Proof: combines `sqrtIter_self_sq_geom_decay` giving `f_n ≤ ((a-1)²/4) · (1/2)^(n-1)`
    with `(a-1)²/4 ≤ (M+1)²/4 ≤ 2^{2(M+1)}/4` and the conclusion that
    `(M+1)² · (1/2)^(n-1) ≤ 4/2^n` when `n ≥ 2(M+1) + k + 3`. -/
private theorem TauRat.sqrtIter_self_sq_lt_recip {a : TauRat}
    (ha : 0 < a.toRat) (M : Nat) (hM : a.toRat ≤ (M : Rat) + 1)
    (k n : Nat) (hn : 2 * (M + 1) + k + 3 ≤ n) :
    (TauRat.sqrtIter a a n).toRat ^ 2 - a.toRat < 1 / ((k : Rat) + 1) := by
  -- Need n ≥ 1
  have hn1 : 1 ≤ n := by omega
  -- Geometric decay: f_n ≤ ((a-1)²/4) · (1/2)^(n-1)
  have h_geom := TauRat.sqrtIter_self_sq_geom_decay ha n hn1
  -- Bound (a-1)² ≤ (M+1)²:  since 0 < a ≤ M+1, |a-1| ≤ max(1, a) ≤ M+1
  have h_M_pos : (0 : Rat) ≤ (M : Rat) + 1 := by
    have : (0 : Rat) ≤ (M : Rat) := by exact_mod_cast Nat.zero_le M
    linarith
  have h_a_minus_one_sq : (a.toRat - 1)^2 ≤ ((M : Rat) + 1)^2 := by
    -- (a-1)² ≤ (max(|a-1|, 0))². Direct nlinarith from a > 0 and a ≤ M+1.
    nlinarith [hM, h_M_pos, ha, sq_nonneg (a.toRat - 1), sq_nonneg ((M : Rat) + 1)]
  -- (a-1)²/4 · (1/2)^(n-1) ≤ (M+1)²/4 · (1/2)^(n-1)
  have h_pow_nn : (0 : Rat) ≤ (1/2 : Rat) ^ (n - 1) := by positivity
  have h_geom_M : (TauRat.sqrtIter a a n).toRat ^ 2 - a.toRat
                    ≤ ((M : Rat) + 1)^2 / 4 * (1/2)^(n-1) := by
    have h_mul_le : (a.toRat - 1)^2 / 4 * (1/2)^(n-1)
                      ≤ ((M : Rat) + 1)^2 / 4 * (1/2)^(n-1) := by
      have h_div_le : (a.toRat - 1)^2 / 4 ≤ ((M : Rat) + 1)^2 / 4 := by
        linarith
      have h_div_nn : (0 : Rat) ≤ (a.toRat - 1)^2 / 4 := by positivity
      have h_div_M_nn : (0 : Rat) ≤ ((M : Rat) + 1)^2 / 4 := by positivity
      nlinarith [h_div_le, h_div_nn, h_pow_nn]
    linarith [h_geom, h_mul_le]
  -- (1/2)^(n-1) = 2/2^n; rewrite
  have h_pow_recip : (1/2 : Rat)^(n-1) = 2 / 2^n := by
    have h_n_eq : n = (n - 1) + 1 := by omega
    have h_pow_n : (2 : Rat)^n = 2 * 2^(n-1) := by
      conv_lhs => rw [h_n_eq]
      rw [pow_succ]; ring
    have h_pow_pos : (0 : Rat) < 2^(n-1) := by positivity
    have h_lhs : (1/2 : Rat)^(n-1) = 1 / 2^(n-1) := by
      rw [one_div]
      rw [inv_pow]
      rw [← one_div]
    rw [h_lhs, h_pow_n]
    field_simp
  rw [h_pow_recip] at h_geom_M
  -- (M+1)²/4 · 2/2^n = (M+1)²/(2 · 2^n)
  -- We want this < 1/(k+1).
  -- Sufficient: 2(M+1)²(k+1) < 2^n.
  -- We have n ≥ 2(M+1) + k + 3, so 2^n ≥ 2^(2(M+1) + k + 3) = 2^(2(M+1)) · 2^(k+3)
  --                                 ≥ (M+1)² · 2^(k+3) ≥ (M+1)² · 2(k+1) · 4 = 8(M+1)²(k+1)
  -- which is > 2(M+1)²(k+1). ✓
  have h_2pow_factor : (2 : Rat)^n = (2 : Rat)^(2*(M+1)) * (2 : Rat)^(k+3) * (2 : Rat)^(n - (2*(M+1) + k + 3)) := by
    have h_split : n = 2*(M+1) + (k + 3) + (n - (2*(M+1) + k + 3)) := by omega
    conv_lhs => rw [h_split]
    rw [pow_add, pow_add]
  have h_M_sq_le_2pow : ((M : Rat) + 1)^2 ≤ (2 : Rat)^(2 * (M + 1)) :=
    Rat.sq_le_two_pow_double M
  have h_2pow_2M_pos : (0 : Rat) < (2 : Rat)^(2*(M+1)) := by positivity
  have h_2pow_k3_pos : (0 : Rat) < (2 : Rat)^(k+3) := by positivity
  have h_2pow_diff_ge : (1 : Rat) ≤ (2 : Rat)^(n - (2*(M+1) + k + 3)) := by
    have h_pos : (0 : Nat) ≤ n - (2*(M+1) + k + 3) := Nat.zero_le _
    apply one_le_pow₀
    norm_num
  -- Now bound: (M+1)²/(2 · 2^n) < 1/(k+1)
  -- (M+1)²/(2 · 2^n) ≤ 2^(2(M+1))/(2 · 2^n) = 2^(2(M+1))/(2 · 2^(2(M+1)) · 2^(k+3) · 2^extra)
  --                  ≤ 1/(2 · 2^(k+3))
  --                  = 1/2^(k+4)
  --                  < 1/(k+1)  (since k+1 < 2^(k+4) for k ≥ 0)
  have h_k1_pos : (0 : Rat) < (k : Rat) + 1 := by
    have : (0 : Rat) ≤ (k : Rat) := by exact_mod_cast Nat.zero_le k
    linarith
  have h_2pow_n_pos : (0 : Rat) < (2 : Rat)^n := by positivity
  -- Prove (M+1)² * 2 / 2^n ≤ 4/2^(k+3)
  have h_main_ineq : ((M : Rat) + 1)^2 / 4 * (2 / 2^n) ≤ 4 / (2 : Rat)^(k + 3) := by
    -- After clearing: (M+1)² * 2 * 2^(k+3) ≤ 4 * 2^n * 4 ?  Hmm, let me redo.
    -- (M+1)² · 2 / 2^n ≤ 4/2^(k+3)
    -- iff (M+1)² · 2 · 2^(k+3) ≤ 4 · 2^n
    -- iff (M+1)² · 2^(k+3) ≤ 2 · 2^n = 2^(n+1)
    -- We have 2^n ≥ 2^(2(M+1)) · 2^(k+3) · 1 ≥ (M+1)² · 2^(k+3)
    -- So 2 · 2^n ≥ 2 · (M+1)² · 2^(k+3) ≥ (M+1)² · 2^(k+3).  ✓
    have h_pow_n_ge : ((M : Rat) + 1)^2 * (2 : Rat)^(k+3) ≤ (2 : Rat)^n := by
      rw [h_2pow_factor]
      have h1 : ((M : Rat) + 1)^2 * (2 : Rat)^(k+3)
                  ≤ (2 : Rat)^(2*(M+1)) * (2 : Rat)^(k+3) := by
        have h_2pow_k3_nn : (0 : Rat) ≤ (2 : Rat)^(k+3) := h_2pow_k3_pos.le
        nlinarith [h_M_sq_le_2pow, h_2pow_k3_nn]
      have h2 : (2 : Rat)^(2*(M+1)) * (2 : Rat)^(k+3)
                  ≤ (2 : Rat)^(2*(M+1)) * (2 : Rat)^(k+3) * (2 : Rat)^(n - (2*(M+1) + k + 3)) := by
        have h_pos : (0 : Rat) ≤ (2 : Rat)^(2*(M+1)) * (2 : Rat)^(k+3) := by positivity
        nlinarith [h_2pow_diff_ge, h_pos]
      linarith
    have h_pow_n_ne : (2 : Rat)^n ≠ 0 := ne_of_gt h_2pow_n_pos
    have h_pow_k3_ne : (2 : Rat)^(k+3) ≠ 0 := ne_of_gt h_2pow_k3_pos
    -- Rewrite LHS: (M+1)²/4 · (2/2^n) = (M+1)² / (2 · 2^n)
    have h_lhs_eq : ((M : Rat) + 1)^2 / 4 * (2 / 2^n) = ((M : Rat) + 1)^2 / (2 * 2^n) := by
      field_simp
      ring
    rw [h_lhs_eq]
    -- Goal: (M+1)² / (2 · 2^n) ≤ 4 / 2^(k+3)
    have h_2_2pow_pos : (0 : Rat) < 2 * 2^n := by positivity
    rw [div_le_div_iff₀ h_2_2pow_pos h_2pow_k3_pos]
    -- Goal: (M+1)² · 2^(k+3) ≤ 4 · (2 · 2^n) = 8 · 2^n
    -- We have h_pow_n_ge: (M+1)² · 2^(k+3) ≤ 2^n. Then 2^n ≤ 8 · 2^n. ✓
    nlinarith [h_pow_n_ge, h_2pow_n_pos]
  -- Combine: f_n ≤ (M+1)²/4 · 2/2^n ≤ 4/2^(k+3) < 1/(k+1)
  have h_chain : (TauRat.sqrtIter a a n).toRat ^ 2 - a.toRat ≤ 4 / (2 : Rat)^(k+3) := by
    -- h_geom_M gave us f_n ≤ (M+1)²/4 · (2/2^n)
    have h_eq : ((M : Rat) + 1)^2 / 4 * (2 / 2^n) = ((M : Rat) + 1)^2 / 4 * 2 / 2^n := by ring
    have h_eq2 : ((M : Rat) + 1)^2 / 4 * (2 / (2 : Rat)^n)
                  = ((M : Rat) + 1)^2 * 2 / (4 * (2 : Rat)^n) := by
      field_simp
    -- Direct chain
    calc (TauRat.sqrtIter a a n).toRat ^ 2 - a.toRat
        ≤ ((M : Rat) + 1)^2 / 4 * (2 / 2^n) := by
          have := h_geom_M
          have h_eq3 : ((M : Rat) + 1)^2 / 4 * (2 / (2 : Rat)^n)
                        = ((M : Rat) + 1)^2 / 4 * (2 / (2 : Rat)^n) := rfl
          linarith [h_geom_M]
      _ ≤ 4 / (2 : Rat)^(k+3) := h_main_ineq
  have h_recip : (4 : Rat) / (2 : Rat)^(k+3) < 1 / ((k : Rat) + 1) :=
    Rat.four_div_two_pow_lt_recip k (k+3) (Nat.le_refl _)
  linarith [h_chain, h_recip]

/-- `TauReal.sqrt a` is Cauchy with modulus depending on the BAZ witness
    of `a`, provided `a` is Cauchy, bounded away from zero, AND eventually
    positive (caller-supplied `h_sign`).

    The `h_sign` hypothesis is needed because BAZ alone admits negative
    radicands for which `(sqrt a)` is genuinely NOT Cauchy: e.g., for
    `a_n = -1` the iteration `sqrtIter(-1, -1, n)` oscillates between
    `0` and `1` (zero seed → fallback to `TauRat.one`, then back to 0, …).

    **Wave R8j note:** the original signature took only `IsCauchy + BAZ`;
    we strengthen with `h_sign` to match `sqrt_pos` and rule out the
    pathological negative branch.

    Proof: Use sign + BAZ to get `a_n > δ_0 > 0` and `a_n ≤ M+1` (Cauchy
    bounded). For n ≥ ν(k) := max(2(M+1)+K+3, μ(K), N₀, Ns) where
    K := 2(k+1)(k₀+1), the squared error `|x_n^2 - a_n| < 1/(K+1)` and
    `|a_m - a_n| < 1/(K+1)`. Then `|x_m - x_n| · (x_m + x_n) = |x_m² - x_n²|
    ≤ 3/(K+1)`, so `|x_m - x_n| ≤ 3/(K+1) / (2δ_0) < 1/(k+1)`. -/
theorem TauReal.sqrt_isCauchy (a : TauReal)
    (h_a_cauchy : a.IsCauchy) (h_pos : a.BoundedAwayFromZero)
    (h_sign : ∃ Ns : Nat, ∀ n : Nat, Ns ≤ n → 0 < (a.approx n).toRat) :
    (TauReal.sqrt a).IsCauchy := by
  obtain ⟨M, _hM_pos, hM⟩ := TauReal.IsCauchy.bounded h_a_cauchy
  obtain ⟨k₀, N₀, hN₀⟩ := h_pos
  obtain ⟨Ns, h_sign_inst⟩ := h_sign
  obtain ⟨μ, hμ⟩ := h_a_cauchy
  -- Set δ_0 := 1/(k₀+1) > 0, and δ_0 ≤ 1.
  -- For n ≥ max(N₀, Ns): a_n > δ_0 > 0.
  -- For each k, target K := 2*(k+1)*(k₀+1) so 1/(K+1) ≤ 1/(2(k+1)(k₀+1)).
  -- Modulus: ν(k) := max( 2*(M+1) + K + 3, μ(K), N₀, Ns)
  refine ⟨fun k => max (max (2 * (M + 1) + 2 * (k + 1) * (k₀ + 1) + 3) (μ (2 * (k + 1) * (k₀ + 1))))
                       (max N₀ Ns), ?_⟩
  intro k m n hm hn
  -- Decode the modulus bounds
  set K := 2 * (k + 1) * (k₀ + 1) with hK_def
  change max (max (2 * (M + 1) + K + 3) (μ K)) (max N₀ Ns) ≤ m at hm
  change max (max (2 * (M + 1) + K + 3) (μ K)) (max N₀ Ns) ≤ n at hn
  have hm_iter : 2 * (M + 1) + K + 3 ≤ m := by
    have h1 : 2 * (M + 1) + K + 3 ≤ max (2 * (M + 1) + K + 3) (μ K) := Nat.le_max_left _ _
    have h2 : max (2 * (M + 1) + K + 3) (μ K) ≤
                max (max (2 * (M + 1) + K + 3) (μ K)) (max N₀ Ns) := Nat.le_max_left _ _
    omega
  have hn_iter : 2 * (M + 1) + K + 3 ≤ n := by
    have h1 : 2 * (M + 1) + K + 3 ≤ max (2 * (M + 1) + K + 3) (μ K) := Nat.le_max_left _ _
    have h2 : max (2 * (M + 1) + K + 3) (μ K) ≤
                max (max (2 * (M + 1) + K + 3) (μ K)) (max N₀ Ns) := Nat.le_max_left _ _
    omega
  have hm_μ : μ K ≤ m := by
    have h1 : μ K ≤ max (2 * (M + 1) + K + 3) (μ K) := Nat.le_max_right _ _
    have h2 : max (2 * (M + 1) + K + 3) (μ K) ≤
                max (max (2 * (M + 1) + K + 3) (μ K)) (max N₀ Ns) := Nat.le_max_left _ _
    omega
  have hn_μ : μ K ≤ n := by
    have h1 : μ K ≤ max (2 * (M + 1) + K + 3) (μ K) := Nat.le_max_right _ _
    have h2 : max (2 * (M + 1) + K + 3) (μ K) ≤
                max (max (2 * (M + 1) + K + 3) (μ K)) (max N₀ Ns) := Nat.le_max_left _ _
    omega
  have hm_N₀ : N₀ ≤ m := by
    have h1 : N₀ ≤ max N₀ Ns := Nat.le_max_left _ _
    have h2 : max N₀ Ns ≤ max (max (2 * (M + 1) + K + 3) (μ K)) (max N₀ Ns) := Nat.le_max_right _ _
    omega
  have hn_N₀ : N₀ ≤ n := by
    have h1 : N₀ ≤ max N₀ Ns := Nat.le_max_left _ _
    have h2 : max N₀ Ns ≤ max (max (2 * (M + 1) + K + 3) (μ K)) (max N₀ Ns) := Nat.le_max_right _ _
    omega
  have hm_Ns : Ns ≤ m := by
    have h1 : Ns ≤ max N₀ Ns := Nat.le_max_right _ _
    have h2 : max N₀ Ns ≤ max (max (2 * (M + 1) + K + 3) (μ K)) (max N₀ Ns) := Nat.le_max_right _ _
    omega
  have hn_Ns : Ns ≤ n := by
    have h1 : Ns ≤ max N₀ Ns := Nat.le_max_right _ _
    have h2 : max N₀ Ns ≤ max (max (2 * (M + 1) + K + 3) (μ K)) (max N₀ Ns) := Nat.le_max_right _ _
    omega
  have hm1 : 1 ≤ m := by omega
  have hn1 : 1 ≤ n := by omega
  -- Positivity of a_m, a_n
  have ha_m_pos : 0 < (a.approx m).toRat := h_sign_inst m hm_Ns
  have ha_n_pos : 0 < (a.approx n).toRat := h_sign_inst n hn_Ns
  -- Bounds: a_m, a_n ≤ M+1
  have h_ax_le_M : ∀ x, (a.approx x).toRat ≤ (M : Rat) + 1 := by
    intro x
    have h_a_abs_le : (a.approx x).abs.toRat ≤ (M : Rat) := hM x
    have h_abs_eq : (a.approx x).abs.toRat = |(a.approx x).toRat| := by
      rw [TauRat.toRat_abs]
    rw [h_abs_eq] at h_a_abs_le
    have h_a_le_abs : (a.approx x).toRat ≤ |(a.approx x).toRat| := le_abs_self _
    linarith
  have ha_m_le : (a.approx m).toRat ≤ (M : Rat) + 1 := h_ax_le_M m
  have ha_n_le : (a.approx n).toRat ≤ (M : Rat) + 1 := h_ax_le_M n
  -- δ_0 := 1/(k₀+1), with δ_0 > 0 and δ_0 ≤ 1
  set δ₀ : Rat := 1 / ((k₀ : Rat) + 1) with hδ₀_def
  have hk₀_nn : (0 : Rat) ≤ (k₀ : Rat) := by exact_mod_cast Nat.zero_le k₀
  have hk₀1_pos : (0 : Rat) < (k₀ : Rat) + 1 := by linarith
  have hδ₀_pos : (0 : Rat) < δ₀ := div_pos (by norm_num) hk₀1_pos
  have hδ₀_le_one : δ₀ ≤ 1 := by
    rw [hδ₀_def, div_le_one hk₀1_pos]; linarith
  -- BAZ at index m, n: a_m, a_n > δ_0
  have h_a_apart : ∀ x, N₀ ≤ x → 0 < (a.approx x).toRat → δ₀ < (a.approx x).toRat := by
    intro x hx hx_pos
    have h := hN₀ x hx
    unfold TauRat.lt at h
    rw [TauRat.ofNatRecip_toRat, TauRat.toRat_abs, abs_of_pos hx_pos] at h
    exact h
  have ha_m_gt_δ₀ : δ₀ < (a.approx m).toRat := h_a_apart m hm_N₀ ha_m_pos
  have ha_n_gt_δ₀ : δ₀ < (a.approx n).toRat := h_a_apart n hn_N₀ ha_n_pos
  -- δ_0² ≤ a_m, a_n: since δ_0 ≤ 1 and a > δ_0, δ_0² ≤ δ_0 ≤ a
  have hδ₀_sq_le_a : ∀ x, δ₀ < (a.approx x).toRat → δ₀ * δ₀ ≤ (a.approx x).toRat := by
    intro x hx
    have h_sq_le : δ₀ * δ₀ ≤ δ₀ * 1 := by nlinarith [hδ₀_pos]
    linarith
  have hδ₀_sq_le_a_m : δ₀ * δ₀ ≤ (a.approx m).toRat := hδ₀_sq_le_a m ha_m_gt_δ₀
  have hδ₀_sq_le_a_n : δ₀ * δ₀ ≤ (a.approx n).toRat := hδ₀_sq_le_a n ha_n_gt_δ₀
  -- Iterates ≥ δ_0
  have hxm_ge_δ₀ : δ₀ ≤ (TauRat.sqrtIter (a.approx m) (a.approx m) m).toRat :=
    TauRat.sqrtIter_lower_bound hδ₀_sq_le_a_m ha_m_gt_δ₀.le hδ₀_pos m
  have hxn_ge_δ₀ : δ₀ ≤ (TauRat.sqrtIter (a.approx n) (a.approx n) n).toRat :=
    TauRat.sqrtIter_lower_bound hδ₀_sq_le_a_n ha_n_gt_δ₀.le hδ₀_pos n
  -- Squared error bounds for m, n
  have hf_m := TauRat.sqrtIter_self_sq_lt_recip ha_m_pos M ha_m_le K m hm_iter
  have hf_n := TauRat.sqrtIter_self_sq_lt_recip ha_n_pos M ha_n_le K n hn_iter
  -- Squared error non-neg
  have hf_m_nn : 0 ≤ (TauRat.sqrtIter (a.approx m) (a.approx m) m).toRat ^ 2 - (a.approx m).toRat :=
    by linarith [TauRat.sqrtIter_self_sq_ge ha_m_pos m hm1]
  have hf_n_nn : 0 ≤ (TauRat.sqrtIter (a.approx n) (a.approx n) n).toRat ^ 2 - (a.approx n).toRat :=
    by linarith [TauRat.sqrtIter_self_sq_ge ha_n_pos n hn1]
  -- Cauchy bound on |a_m - a_n|
  have h_cauchy_a := hμ K m n hm_μ hn_μ
  unfold TauRat.lt at h_cauchy_a
  rw [TauRat.toRat_abs, toRat_sub, TauRat.ofNatRecip_toRat] at h_cauchy_a
  -- Now structure the main argument
  set xm := (TauRat.sqrtIter (a.approx m) (a.approx m) m).toRat with hxm_def
  set xn := (TauRat.sqrtIter (a.approx n) (a.approx n) n).toRat with hxn_def
  -- x_m + x_n ≥ 2δ_0 > 0
  have hxm_pos : 0 < xm := lt_of_lt_of_le hδ₀_pos hxm_ge_δ₀
  have hxn_pos : 0 < xn := lt_of_lt_of_le hδ₀_pos hxn_ge_δ₀
  have h_sum_ge : 2 * δ₀ ≤ xm + xn := by linarith
  have h_sum_pos : 0 < xm + xn := by linarith
  -- |x_m^2 - x_n^2| bound by triangle
  have h_K_pos : (0 : Rat) < (K : Rat) + 1 := by
    have : (0 : Rat) ≤ (K : Rat) := by exact_mod_cast Nat.zero_le K
    linarith
  have h_recip_K : (1 : Rat) / ((K : Rat) + 1) > 0 := div_pos (by norm_num) h_K_pos
  -- |x_m^2 - a_m| < 1/(K+1), |x_n^2 - a_n| < 1/(K+1) (from hf_m, hf_n + non-neg)
  have habs_m : |xm^2 - (a.approx m).toRat| < 1/((K : Rat) + 1) := by
    rw [abs_of_nonneg hf_m_nn]; exact hf_m
  have habs_n : |xn^2 - (a.approx n).toRat| < 1/((K : Rat) + 1) := by
    rw [abs_of_nonneg hf_n_nn]; exact hf_n
  have habs_a : |(a.approx m).toRat - (a.approx n).toRat| < 1/((K : Rat) + 1) := h_cauchy_a
  -- Triangle: |xm² - xn²| ≤ |xm² - am| + |am - an| + |an - xn²|
  have h_tri : |xm^2 - xn^2| ≤ |xm^2 - (a.approx m).toRat|
                                + |(a.approx m).toRat - (a.approx n).toRat|
                                + |(a.approx n).toRat - xn^2| := by
    have h_split : xm^2 - xn^2
                  = (xm^2 - (a.approx m).toRat) + ((a.approx m).toRat - (a.approx n).toRat)
                    + ((a.approx n).toRat - xn^2) := by ring
    have h_tri12 := abs_add_le ((xm^2 - (a.approx m).toRat) + ((a.approx m).toRat - (a.approx n).toRat))
                                ((a.approx n).toRat - xn^2)
    have h_tri3 := abs_add_le (xm^2 - (a.approx m).toRat) ((a.approx m).toRat - (a.approx n).toRat)
    rw [h_split]
    linarith [h_tri12, h_tri3]
  have h_swap_n : |(a.approx n).toRat - xn^2| = |xn^2 - (a.approx n).toRat| := by
    rw [abs_sub_comm]
  rw [h_swap_n] at h_tri
  have h_xm2_xn2_lt : |xm^2 - xn^2| < 3 / ((K : Rat) + 1) := by
    have h_recip_eq : 3 / ((K : Rat) + 1) = 1/((K : Rat) + 1) + 1/((K : Rat) + 1) + 1/((K : Rat) + 1) := by
      ring
    rw [h_recip_eq]
    linarith [h_tri, habs_m, habs_n, habs_a]
  -- |xm - xn| · (xm + xn) = |xm² - xn²|
  -- So |xm - xn| = |xm² - xn²| / (xm + xn) ≤ (3/(K+1)) / (2δ_0)
  -- We want this < 1/(k+1).
  -- 3/((K+1) · 2δ_0) < 1/(k+1)
  -- iff 3(k+1) < 2δ_0 (K+1) = 2δ_0 (2(k+1)(k₀+1) + 1)
  -- With δ_0 = 1/(k₀+1): 2δ_0(K+1) = 2(K+1)/(k₀+1).
  -- 2(K+1)/(k₀+1) = 2 (2(k+1)(k₀+1) + 1)/(k₀+1) = 4(k+1) + 2/(k₀+1).
  -- We need 3(k+1) < 4(k+1) + 2/(k₀+1), which holds: (k+1) + 2/(k₀+1) > 0. ✓
  have h_mul_eq : (xm - xn) * (xm + xn) = xm^2 - xn^2 := by ring
  have h_abs_mul : |xm - xn| * (xm + xn) = |xm^2 - xn^2| := by
    have h1 : |xm - xn| * |xm + xn| = |(xm - xn) * (xm + xn)| := (abs_mul _ _).symm
    have h2 : |xm + xn| = xm + xn := abs_of_pos h_sum_pos
    rw [h2] at h1
    rw [h1, h_mul_eq]
  -- |xm - xn| = |xm² - xn²| / (xm + xn)
  have h_xm_xn_eq : |xm - xn| = |xm^2 - xn^2| / (xm + xn) := by
    have h_ne : xm + xn ≠ 0 := ne_of_gt h_sum_pos
    field_simp at h_abs_mul ⊢
    linarith [h_abs_mul]
  -- Bound: |xm - xn| ≤ (3/(K+1)) / (2δ_0)
  have h_xm_xn_le : |xm - xn| ≤ (3 / ((K : Rat) + 1)) / (2 * δ₀) := by
    rw [h_xm_xn_eq]
    have h_2δ_pos : (0 : Rat) < 2 * δ₀ := by linarith
    have h_num_nn : (0 : Rat) ≤ |xm^2 - xn^2| := _root_.abs_nonneg _
    -- |xm²-xn²|/(xm+xn) ≤ (3/(K+1))/(2δ₀) iff |xm²-xn²| · 2δ₀ ≤ (3/(K+1)) · (xm+xn)
    rw [div_le_div_iff₀ h_sum_pos h_2δ_pos]
    -- |xm²-xn²| · 2δ₀ ≤ (3/(K+1)) · 2δ₀ ≤ (3/(K+1)) · (xm+xn)
    have h_xm2_le : |xm^2 - xn^2| ≤ 3/((K : Rat) + 1) := h_xm2_xn2_lt.le
    have h_3_K_nn : (0 : Rat) ≤ 3 / ((K : Rat) + 1) :=
      div_nonneg (by norm_num) (by linarith [h_K_pos])
    have h_lhs_le : |xm^2 - xn^2| * (2 * δ₀) ≤ (3/((K : Rat) + 1)) * (2 * δ₀) :=
      mul_le_mul_of_nonneg_right h_xm2_le h_2δ_pos.le
    have h_rhs_ge : (3/((K : Rat) + 1)) * (2 * δ₀) ≤ (3/((K : Rat) + 1)) * (xm + xn) :=
      mul_le_mul_of_nonneg_left h_sum_ge h_3_K_nn
    linarith
  -- Final: (3/(K+1)) / (2δ_0) < 1/(k+1)
  -- δ₀ = 1/(k₀+1), 2δ₀ = 2/(k₀+1). K+1 = 2(k+1)(k₀+1) + 1.
  -- (3/(K+1))/(2δ₀) = 3/(K+1) · 1/(2δ₀) = 3/(K+1) · (k₀+1)/2 = 3(k₀+1)/(2(K+1))
  -- = 3(k₀+1)/(2(2(k+1)(k₀+1) + 1)) ≤ 3(k₀+1)/(2 · 2(k+1)(k₀+1)) = 3/(4(k+1))
  -- We need < 1/(k+1), so 3/(4(k+1)) < 1/(k+1) iff 3 < 4. ✓
  have h_final_lt : (3 / ((K : Rat) + 1)) / (2 * δ₀) < 1/((k : Rat) + 1) := by
    have h_2δ_pos : (0 : Rat) < 2 * δ₀ := by linarith
    have h_k1_pos : (0 : Rat) < (k : Rat) + 1 := by
      have : (0 : Rat) ≤ (k : Rat) := by exact_mod_cast Nat.zero_le k
      linarith
    have h_K_eq : ((K : Rat) + 1) = 2 * ((k : Rat) + 1) * ((k₀ : Rat) + 1) + 1 := by
      rw [hK_def]; push_cast; ring
    rw [h_K_eq, hδ₀_def]
    -- Goal: 3 / (2(k+1)(k₀+1) + 1) / (2 · (1/(k₀+1))) < 1/(k+1)
    -- Simplify LHS: 3 / (2(k+1)(k₀+1) + 1) · (k₀+1)/2 = 3(k₀+1) / (2(2(k+1)(k₀+1) + 1))
    have h_2K1_pos : (0 : Rat) < 2 * ((k : Rat) + 1) * ((k₀ : Rat) + 1) + 1 := by
      have h_prod_nn : (0 : Rat) ≤ 2 * ((k : Rat) + 1) * ((k₀ : Rat) + 1) := by
        have hk_nn : (0 : Rat) ≤ (k : Rat) + 1 := by linarith
        have hk₀_nn' : (0 : Rat) ≤ (k₀ : Rat) + 1 := by linarith
        positivity
      linarith
    have h_2_div_pos : (0 : Rat) < 2 * (1 / ((k₀ : Rat) + 1)) := by
      have : (0 : Rat) < 1 / ((k₀ : Rat) + 1) := div_pos (by norm_num) hk₀1_pos
      linarith
    rw [div_div, div_lt_div_iff₀ (by positivity) h_k1_pos]
    -- Goal: 3 · (k+1) < 1 · ((2(k+1)(k₀+1) + 1) · (2 · (1/(k₀+1))))
    -- RHS = (2(k+1)(k₀+1) + 1) · 2 / (k₀+1) = 4(k+1) + 2/(k₀+1)
    -- LHS = 3(k+1)
    -- So need: 3(k+1) < 4(k+1) + 2/(k₀+1), i.e., 0 < (k+1) + 2/(k₀+1). ✓
    have h_rhs_pos : (0 : Rat) < 2 / ((k₀ : Rat) + 1) := div_pos (by norm_num) hk₀1_pos
    have h_simp : ((2 * ((k : Rat) + 1) * ((k₀ : Rat) + 1) + 1) * (2 * (1 / ((k₀ : Rat) + 1))))
                    = 4 * ((k : Rat) + 1) + 2 / ((k₀ : Rat) + 1) := by
      field_simp
      ring
    rw [h_simp]
    have hk_pos : (0 : Rat) ≤ (k : Rat) + 1 := by linarith
    linarith
  -- Combine
  unfold TauRat.lt
  rw [TauRat.toRat_abs, toRat_sub, TauRat.ofNatRecip_toRat]
  show |((TauReal.sqrt a).approx m).toRat - ((TauReal.sqrt a).approx n).toRat|
         < 1 / ((k : Rat) + 1)
  show |xm - xn| < 1 / ((k : Rat) + 1)
  linarith [h_xm_xn_le, h_final_lt]

/-- `(√a)² ≡ a` up to `TauReal.equiv`, when `a` is Cauchy, bounded
    away from zero, AND eventually positive (caller-supplied `h_sign`).

    The `IsCauchy` hypothesis is needed (in addition to BAZ) to derive
    a uniform Nat upper bound via `IsCauchy.bounded`. The sign hypothesis
    is needed because BAZ alone admits sign-flipping radicands for which
    `(sqrt a)² ≡ a` is false (e.g., `a_n = (-1)^n`). The negative-only
    branch is also false: if `a_n < 0`, then `(sqrt a)².approx n ≥ 0 ≠ a_n`.

    **Wave R8j note:** the original signature took only BAZ; we strengthen
    to `IsCauchy + h_sign` to match `sqrt_pos`. -/
theorem TauReal.sqrt_sq (a : TauReal) (_h : a.BoundedAwayFromZero)
    (h_cauchy : a.IsCauchy)
    (h_sign : ∃ Ns : Nat, ∀ n : Nat, Ns ≤ n → 0 < (a.approx n).toRat) :
    TauReal.equiv ((TauReal.sqrt a).mul (TauReal.sqrt a)) a := by
  obtain ⟨Ns, h_sign_inst⟩ := h_sign
  obtain ⟨M, _hM_pos, hM⟩ := TauReal.IsCauchy.bounded h_cauchy
  -- Modulus: μ k := 2*(M+1) + k + 3 + Ns
  -- For n past μ k: a_n > 0 (from h_sign_inst), a_n ≤ M (from hM),
  -- and sqrtIter(a_n, a_n, n)^2 - a_n < 1/(k+1) by sqrtIter_self_sq_lt_recip.
  refine ⟨fun k => 2 * (M + 1) + k + 3 + Ns, fun k n hn => ?_⟩
  -- Goal: |((sqrt a) * (sqrt a)).approx n - a.approx n|.toRat < 1/(k+1)
  change 2 * (M + 1) + k + 3 + Ns ≤ n at hn
  have hn_Ns : Ns ≤ n := by omega
  have hn_iter : 2 * (M + 1) + k + 3 ≤ n := by omega
  have hn1 : 1 ≤ n := by omega
  have ha_pos : 0 < (a.approx n).toRat := h_sign_inst n hn_Ns
  -- Bound a_n ≤ M+1: from hM, |a_n| ≤ M, so a_n ≤ M ≤ M+1
  have h_a_abs_le : (a.approx n).abs.toRat ≤ (M : Rat) := hM n
  have h_a_le : (a.approx n).toRat ≤ (M : Rat) + 1 := by
    have h_abs_eq : (a.approx n).abs.toRat = |(a.approx n).toRat| := by
      rw [TauRat.toRat_abs]
    rw [h_abs_eq] at h_a_abs_le
    have h_a_le_abs : (a.approx n).toRat ≤ |(a.approx n).toRat| := le_abs_self _
    linarith
  -- Apply the key error lemma
  have h_err := TauRat.sqrtIter_self_sq_lt_recip ha_pos M h_a_le k n hn_iter
  -- (sqrt a).approx n = sqrtIter (a.approx n) (a.approx n) n
  -- ((sqrt a).mul (sqrt a)).approx n = sqrtIter ... ^ 2 (under toRat)
  unfold TauRat.lt
  rw [TauRat.toRat_abs, toRat_sub, TauRat.ofNatRecip_toRat]
  show |(((TauReal.sqrt a).mul (TauReal.sqrt a)).approx n).toRat - (a.approx n).toRat|
         < 1 / ((k : Rat) + 1)
  have h_mul_unfold : (((TauReal.sqrt a).mul (TauReal.sqrt a)).approx n).toRat
                        = (TauRat.sqrtIter (a.approx n) (a.approx n) n).toRat ^ 2 := by
    show (((TauReal.sqrt a).approx n).mul ((TauReal.sqrt a).approx n)).toRat
            = (TauRat.sqrtIter (a.approx n) (a.approx n) n).toRat ^ 2
    rw [toRat_mul]
    show (TauRat.sqrtIter (a.approx n) (a.approx n) n).toRat
            * (TauRat.sqrtIter (a.approx n) (a.approx n) n).toRat
            = (TauRat.sqrtIter (a.approx n) (a.approx n) n).toRat ^ 2
    ring
  rw [h_mul_unfold]
  -- Goal: |sqrtIter² - a_n| < 1/(k+1)
  -- We have h_err: sqrtIter² - a_n < 1/(k+1) AND sqrtIter² ≥ a_n (from sqrtIter_self_sq_ge)
  have h_sq_ge := TauRat.sqrtIter_self_sq_ge ha_pos n hn1
  have h_diff_nn : 0 ≤ (TauRat.sqrtIter (a.approx n) (a.approx n) n).toRat ^ 2
                          - (a.approx n).toRat := by linarith
  rw [abs_of_nonneg h_diff_nn]
  exact h_err

/-- `TauReal.sqrt a` is bounded away from zero when `a` is bounded
    away from zero AND eventually positive (caller-supplied `h_sign`).

    The `h_sign` argument is needed because `BoundedAwayFromZero` only
    gives `|a_n| ≥ δ` (absolute value), not the sign. For sqrt to be
    well-defined as a positive real, the radicand must be eventually
    positive — caller supplies the witness. -/
theorem TauReal.sqrt_pos (a : TauReal) (h : a.BoundedAwayFromZero)
    (h_sign : ∃ Ns : Nat, ∀ n : Nat, Ns ≤ n → 0 < (a.approx n).toRat) :
    (TauReal.sqrt a).BoundedAwayFromZero := by
  obtain ⟨k₀, N₀, hN₀⟩ := h
  obtain ⟨Ns, h_sign_inst⟩ := h_sign
  -- Lower bound: δ = 1/(k₀+1) > 0
  have hδ_pos : (0 : Rat) < 1 / ((k₀ : Rat) + 1) := by
    apply div_pos (by norm_num)
    have : (0 : Rat) ≤ (k₀ : Rat) := by exact_mod_cast Nat.zero_le k₀
    linarith
  -- BAZ for sqrt a uses k' = 2*(k₀+1) so 1/(k'+1) = 1/(2k₀+3) < 1/(k₀+1)
  refine ⟨2 * (k₀ + 1), max N₀ Ns, fun n hn => ?_⟩
  have h_max_le_N₀ : N₀ ≤ max N₀ Ns := Nat.le_max_left N₀ Ns
  have h_max_le_Ns : Ns ≤ max N₀ Ns := Nat.le_max_right N₀ Ns
  have hnN₀ : N₀ ≤ n := by omega
  have hnNs : Ns ≤ n := by omega
  -- (a) a.approx n is positive
  have h_an_pos : 0 < (a.approx n).toRat := h_sign_inst n hnNs
  -- (b) |a.approx n| > 1/(k₀+1) from BAZ
  have h_an_abs : 1 / ((k₀ : Rat) + 1) < |(a.approx n).toRat| := by
    have := hN₀ n hnN₀
    unfold TauRat.lt at this
    rw [TauRat.ofNatRecip_toRat, TauRat.toRat_abs] at this
    exact this
  -- (c) Since a.approx n > 0, |a.approx n| = a.approx n
  -- (d) So a.approx n > 1/(k₀+1) = δ
  have h_an_gt_δ : 1 / ((k₀ : Rat) + 1) < (a.approx n).toRat := by
    rw [abs_of_pos h_an_pos] at h_an_abs
    exact h_an_abs
  -- (e) δ² ≤ δ (since δ ≤ 1, which holds for k₀ ≥ 0): need (1/(k₀+1))² ≤ 1/(k₀+1)
  have h_k1_pos : (0 : Rat) < (k₀ : Rat) + 1 := by
    have : (0 : Rat) ≤ (k₀ : Rat) := by exact_mod_cast Nat.zero_le k₀
    linarith
  have h_k1_ge_1 : (1 : Rat) ≤ (k₀ : Rat) + 1 := by
    have : (0 : Rat) ≤ (k₀ : Rat) := by exact_mod_cast Nat.zero_le k₀
    linarith
  have h_δ_le_1 : 1 / ((k₀ : Rat) + 1) ≤ 1 := by
    rw [div_le_iff₀ h_k1_pos]; linarith
  have h_δ_sq_le_an : (1 / ((k₀ : Rat) + 1)) * (1 / ((k₀ : Rat) + 1))
                       ≤ (a.approx n).toRat := by
    nlinarith [h_an_gt_δ, h_δ_le_1, hδ_pos]
  -- (f) Apply sqrtIter_lower_bound to get: iterate ≥ δ
  have h_iter_lower : 1 / ((k₀ : Rat) + 1) ≤
      (TauRat.sqrtIter (a.approx n) (a.approx n) n).toRat := by
    apply TauRat.sqrtIter_lower_bound h_δ_sq_le_an _ hδ_pos
    linarith [h_an_gt_δ]
  -- (g) Iterate is positive
  have h_iter_pos : 0 < (TauRat.sqrtIter (a.approx n) (a.approx n) n).toRat :=
    lt_of_lt_of_le hδ_pos h_iter_lower
  -- (h) BoundedAwayFromZero: 1/(2*(k₀+1)+1) < iterate
  unfold TauRat.lt
  rw [TauRat.ofNatRecip_toRat, TauRat.toRat_abs]
  -- (TauReal.sqrt a).approx n unfolds to sqrtIter (a.approx n) (a.approx n) n
  show 1 / ((2 * (k₀ + 1) : Nat) + 1 : Rat) <
      |(TauRat.sqrtIter (a.approx n) (a.approx n) n).toRat|
  rw [abs_of_pos h_iter_pos]
  -- Need: 1/(2k₀+3) < 1/(k₀+1) ≤ iterate
  have h_recip_ineq : 1 / ((2 * (k₀ + 1) : Nat) + 1 : Rat) < 1 / ((k₀ : Rat) + 1) := by
    have h_lhs_eq : ((2 * (k₀ + 1) : Nat) + 1 : Rat) = 2 * (k₀ : Rat) + 3 := by
      push_cast; ring
    rw [h_lhs_eq]
    have h_2k3_pos : (0 : Rat) < 2 * (k₀ : Rat) + 3 := by linarith
    rw [div_lt_div_iff₀ h_2k3_pos h_k1_pos]
    linarith
  linarith [h_iter_lower, h_recip_ineq]

-- ============================================================
-- SECTION 8: SMOKE TESTS
-- ============================================================

private def tr_two  : TauRat := ⟨⟨2, 0⟩, 1, by norm_num⟩
private def tr_four : TauRat := ⟨⟨4, 0⟩, 1, by norm_num⟩
private def tr_nine : TauRat := ⟨⟨9, 0⟩, 1, by norm_num⟩
private def tr_half : TauRat := ⟨⟨1, 0⟩, 2, by norm_num⟩

-- One Newton step on 4 from seed 4: (4 + 4/4)/2 = 5/2
#eval (TauRat.sqrtNewtonStep tr_four tr_four).toRat
-- Two steps on 4: 41/20 = 2.05
#eval (TauRat.sqrtIter tr_four tr_four 2).toRat
-- Five steps on 4: very close to 2
#eval (TauRat.sqrtIter tr_four tr_four 5).toRat
-- TauReal.sqrt of constant-4 at index 10
#eval (TauReal.sqrt (TauReal.fromTauRat tr_four)).approx 10 |>.toRat
-- Ten steps on 9: ≈ 3
#eval (TauRat.sqrtIter tr_nine tr_nine 10).toRat
-- One step on 2: (2 + 1)/2 = 3/2
#eval (TauRat.sqrtNewtonStep tr_two tr_two).toRat
-- Fifteen steps on 2: ≈ √2 ≈ 1.41421356
#eval (TauRat.sqrtIter tr_two tr_two 15).toRat
-- Eight steps on 1/2: ≈ 1/√2 ≈ 0.7071
#eval (TauRat.sqrtIter tr_half tr_half 8).toRat

end Tau.Boundary
