import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Algebra.Order.AbsoluteValue.Basic
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp

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

end Tau.Boundary.Bridge
