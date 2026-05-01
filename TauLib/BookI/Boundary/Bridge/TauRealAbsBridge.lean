import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Algebra.Order.AbsoluteValue.Basic
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp

open BigOperators

/-!
# TauLib.BookI.Boundary.Bridge.TauRealAbsBridge

**Wave R8d — Mathlib abs-distribution bridge**.

Re-exports the abs-distribution lemmas (`abs_pow`, `abs_div`, `abs_mul`,
`pow_le_pow_left₀`, `pow_le_one₀`) at the `Rat` level so τ-native code
in `TauRealSqrt.lean`, `TauRealExp.lean`, etc. can use them without
violating the tactics-only-Mathlib CI grep-guard.

## Bridge zone justification

The `taulib_tactic_budget` CI grep-guard (`.github/workflows/lean-build.yml`
line 38-59) forbids direct `Mathlib.Algebra.*` imports outside `Bridge/`
subdirectories. This file lives in `BookI/Boundary/Bridge/`, an explicit
orthodox-bridge zone (matching the existing `TauRealQuotientField.lean`
convention which imports `Mathlib.Algebra.Field.Defs`).

The bridge is **import-only**: it does not introduce new tactics or
proof obligations. Downstream τ-native code imports this module to access
abs-distribution lemmas the same way one imports a Mathlib tactic.

## What this module delivers

- Direct re-export of `abs_mul`, `abs_div`, `abs_pow`, `abs_inv` from
  `Mathlib.Algebra.Order.Ring.Abs` and `Mathlib.Algebra.Order.AbsoluteValue.Basic`.
- Direct re-export of `pow_le_pow_left₀`, `pow_le_one₀` from
  `Mathlib.Algebra.Order.Field.Basic`.

These are pure pass-throughs — the Mathlib lemmas at face value.

## Wave R8d unblocks

This bridge unblocks:
- `TauRealExp.exp_term_abs_le_geom` (Wave R8c sorried)
- Engineer A2's 6 sqrt sub-lemmas (Wave R8c not integrated)
- Downstream chain: exp_partial_cauchy_bound + exp_of_rat_isCauchy +
  sqrt_isCauchy + sqrt_sq

## Source notes

- Wave R8c closing dashboard `audits/taulib/2026-05-01-wave-r8c-sorry-closure-dashboard.md`
  Discovery 2 documented the import-budget wall this bridge resolves.
- CI grep-guard at `.github/workflows/lean-build.yml:42` exempts `Bridge/`.
-/

namespace Tau.Boundary.Bridge

/-- Re-export `abs_mul` for Rat at the bridge boundary. -/
theorem rat_abs_mul (a b : Rat) : |a * b| = |a| * |b| := abs_mul a b

/-- Re-export `abs_div` for Rat at the bridge boundary. -/
theorem rat_abs_div (a b : Rat) : |a / b| = |a| / |b| := abs_div a b

/-- Re-export `abs_pow` for Rat at the bridge boundary. -/
theorem rat_abs_pow (a : Rat) (n : Nat) : |a ^ n| = |a| ^ n := abs_pow a n

/-- Re-export `abs_inv` for Rat at the bridge boundary. -/
theorem rat_abs_inv (a : Rat) : |a⁻¹| = |a|⁻¹ := abs_inv a

/-- Re-export `pow_le_pow_left₀` for Rat at the bridge boundary. -/
theorem rat_pow_le_pow_left₀ {a b : Rat} (h : 0 ≤ a) (hab : a ≤ b) (n : Nat) :
    a ^ n ≤ b ^ n :=
  pow_le_pow_left₀ h hab n

/-- Re-export `pow_le_one₀` for Rat at the bridge boundary. -/
theorem rat_pow_le_one₀ {a : Rat} (h_nn : 0 ≤ a) (h_le : a ≤ 1) (n : Nat) :
    a ^ n ≤ 1 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ]
    have h_pow_nn : 0 ≤ a ^ n := pow_nonneg h_nn n
    nlinarith

-- ============================================================
-- WAVE R8f: Finset re-export for cauchy_product_bound closure
-- ============================================================

/-- Sum of constants over `Finset.range n` equals `n · c`. Re-export from Mathlib. -/
theorem rat_sum_const_range (c : Rat) (n : Nat) :
    ∑ _i ∈ Finset.range n, c = (n : Rat) * c := by
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]

/-- Sum upper bound via per-term bounds. -/
theorem rat_finset_sum_le_const_mul {n : Nat} (f : Nat → Rat) (c : Rat)
    (hf : ∀ i ∈ Finset.range n, f i ≤ c) :
    ∑ i ∈ Finset.range n, f i ≤ (n : Rat) * c := by
  rw [← rat_sum_const_range c n]
  apply Finset.sum_le_sum
  exact hf

/-- Abs of finset sum bounded by sum of abs (triangle inequality). -/
theorem rat_abs_finset_sum_le (f : Nat → Rat) (n : Nat) :
    |∑ i ∈ Finset.range n, f i| ≤ ∑ i ∈ Finset.range n, |f i| := by
  exact Finset.abs_sum_le_sum_abs f (Finset.range n)

/-- Re-export of right-distribution of multiplication over finite sums. -/
theorem rat_finset_sum_mul (n : Nat) (f : Nat → Rat) (a : Rat) :
    (∑ i ∈ Finset.range n, f i) * a = ∑ i ∈ Finset.range n, f i * a :=
  Finset.sum_mul (Finset.range n) f a

-- ============================================================
-- WAVE R8h-A: Binomial-theorem re-export for exp_add closure
-- ============================================================

/-- Binomial theorem (`add_pow`) at `Rat`, re-exported via Bridge. -/
theorem rat_add_pow (x y : Rat) (n : Nat) :
    (x + y) ^ n =
      ∑ k ∈ Finset.range (n + 1),
        x ^ k * y ^ (n - k) * (Nat.choose n k : Rat) :=
  add_pow x y n

/-- Pointwise rewrite of finite sums (extensionality). -/
theorem rat_finset_sum_congr (n : Nat) (f g : Nat → Rat)
    (h : ∀ i ∈ Finset.range n, f i = g i) :
    ∑ i ∈ Finset.range n, f i = ∑ i ∈ Finset.range n, g i :=
  Finset.sum_congr rfl h

/-- Pull a constant scalar out of a finite sum (left). -/
theorem rat_mul_finset_sum (n : Nat) (a : Rat) (f : Nat → Rat) :
    a * (∑ i ∈ Finset.range n, f i) = ∑ i ∈ Finset.range n, a * f i :=
  Finset.mul_sum (Finset.range n) f a

/-- Choose-factorial identity at the `Rat` level (key for binomial / exp).
    `n.choose k * (k! * (n-k)!) = n!` as Rats, when `k ≤ n`. -/
theorem rat_choose_mul_factorial (n k : Nat) (hk : k ≤ n) :
    (Nat.choose n k : Rat) * (Nat.factorial k : Rat) * (Nat.factorial (n - k) : Rat)
      = (Nat.factorial n : Rat) := by
  have h_nat : Nat.choose n k * Nat.factorial k * Nat.factorial (n - k) = Nat.factorial n :=
    Nat.choose_mul_factorial_mul_factorial hk
  exact_mod_cast h_nat

end Tau.Boundary.Bridge
