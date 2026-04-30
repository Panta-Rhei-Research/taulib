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
-- SECTION 7: IsCauchy FOR TauReal.sqrt  (R2 sorry-guarded)
-- ============================================================

/-- `TauReal.sqrt a` is Cauchy with modulus `λ k => k + 3`, provided
    `a` is Cauchy and bounded away from zero.

    Proof structure mirrors `TauRealE.lean :178`:
    - `refine ⟨fun k => k + 3, ?_⟩`
    - `by_cases h_le : n ≤ m`
    - apply Cauchy bound, close with the new tower-exponent helper
      `Rat.one_div_tower_pow_lt_recip` (or the linear
      `Rat.four_div_two_pow_lt_recip` for radicand-direction term).

    The `sorry` marks the Newton-convergence + Lipschitz steps that
    Wave R8c will close (alongside Engineer B's `cauchy_product_bound`). -/
theorem TauReal.sqrt_isCauchy (a : TauReal)
    (h_a_cauchy : a.IsCauchy) (h_pos : a.BoundedAwayFromZero) :
    (TauReal.sqrt a).IsCauchy := by
  sorry  -- R2 / Wave R8c: full two-term decomposition + tower convergence.

/-- `(√a)² ≡ a` up to `TauReal.equiv`, when `a` is bounded away from zero. -/
theorem TauReal.sqrt_sq (a : TauReal) (h : a.BoundedAwayFromZero) :
    TauReal.equiv ((TauReal.sqrt a).mul (TauReal.sqrt a)) a := by
  sorry  -- R2 / Wave R8c: Newton convergence x_n² → a via tower bound.

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
