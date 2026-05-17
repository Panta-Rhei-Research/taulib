import TauLib.BookI.Boundary.TauRealGronwallHelpers
import Mathlib.Tactic.Ring
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity

/-!
# TauLib.BookI.Boundary.TauRealGronwall

The **discrete Gronwall inequality** at Rat level, with a Nat-indexed
sequence-form variant suitable for τ-stack analytical capstones.

## Wave Γ₈ Phase 2.6.B.2.β.4.9 — Approach (ii) PoC

This module is the **proof-of-concept** first deliverable of Wave Γ₈
Phase β.4.9 (the analytical capstone discharge approach choosing
"foundational TauReal derivative theory + discrete Gronwall").

### Statement (basic form)

If a non-negative Rat sequence `u : Nat → Rat` satisfies:
1. `u 0 ≤ ε₀` (small initial value)
2. `u (n+1) ≤ (1+M) · u n + δ` (linear recurrence with non-negative
   constants `M, δ`)

then for every `N`:
```
u N ≤ (1+M)^N · ε₀ + N · (1+M)^N · δ
```

This is the **weak form** of discrete Gronwall: tight only up to the
`N · (1+M)^N` factor on the additive error. Sufficient for the
τ-stack tangent-identity discharge because both `ε₀` and `δ` are
chosen to converge to 0 with separate moduli.

### Strategic role

The lemma here is the discrete Gronwall inequality at Rat level. The
TauReal-level lift (a sequence of TauReal-equivalences converging to
TauReal.zero) follows in subsequent modules via the standard
"Cauchy-modulus + linarith" pattern.

For the eventual tangent-identity application:
- `u n` will represent `|h(a_n)|.toRat` at depth-n dyadic discretization
- `M = h·C` where `C = max |M(a)|` (bounded by 1 in our case)
- `δ = ε(N)` is the per-step finite-difference truncation error
- `ε₀ = |h(0)|.toRat` (≈ 0 by `cisTauReal(0) ≈ TauComplex.one`)
- Conclusion: `|h(a)|.toRat → 0` as discretization refines
-/

set_option autoImplicit false

namespace Tau.Boundary

-- ============================================================
-- PART 1: DISCRETE GRONWALL INEQUALITY (Rat level, sequence form)
-- ============================================================

/-- **Discrete Gronwall inequality (weak form, Rat level)**.

    For a non-negative Rat sequence `u : Nat → Rat` with:
    * Initial bound `u 0 ≤ ε₀`
    * Recurrence `u (n+1) ≤ (1+M) · u n + δ`
    * Non-negative `M, δ, ε₀`

    The conclusion:
    ```
    u N ≤ (1+M)^N · ε₀ + N · (1+M)^N · δ
    ```

    Proved by induction on `N`, using `Rat.gronwall_inductive_step` from
    `TauRealGronwallHelpers.lean`. -/
theorem Rat.discrete_gronwall_weak
    (u : Nat → Rat) (M δ ε₀ : Rat)
    (hM : 0 ≤ M) (hδ : 0 ≤ δ) (hε₀ : 0 ≤ ε₀)
    (h_nn : ∀ n, 0 ≤ u n)
    (h_0 : u 0 ≤ ε₀)
    (h_step : ∀ n, u (n+1) ≤ (1+M) * u n + δ) :
    ∀ N, u N ≤ (1+M)^N * ε₀ + (N : Rat) * (1+M)^N * δ := by
  intro N
  induction N with
  | zero =>
    simp only [pow_zero, one_mul, Nat.cast_zero, zero_mul, add_zero]
    exact le_trans (h_0) (by linarith)
  | succ n ih =>
    -- IH: u n ≤ (1+M)^n · ε₀ + n · (1+M)^n · δ
    -- Step: u (n+1) ≤ (1+M) · u n + δ
    -- Goal: u (n+1) ≤ (1+M)^(n+1) · ε₀ + (n+1) · (1+M)^(n+1) · δ
    exact Rat.gronwall_inductive_step M δ hM hδ
      (u n) (u (n+1)) ε₀ n
      hε₀ (h_nn n) ih (h_step n)

-- ============================================================
-- PART 2: GRONWALL WITH ZERO INITIAL VALUE (key corollary)
-- ============================================================

/-- **Discrete Gronwall with zero initial**: if `u 0 = 0` exactly, then
    `u N ≤ N · (1+M)^N · δ`. -/
theorem Rat.discrete_gronwall_zero_init
    (u : Nat → Rat) (M δ : Rat)
    (hM : 0 ≤ M) (hδ : 0 ≤ δ)
    (h_nn : ∀ n, 0 ≤ u n)
    (h_0 : u 0 = 0)
    (h_step : ∀ n, u (n+1) ≤ (1+M) * u n + δ) :
    ∀ N, u N ≤ (N : Rat) * (1+M)^N * δ := by
  intro N
  have h_init : u 0 ≤ 0 := by rw [h_0]
  have h_gronwall := Rat.discrete_gronwall_weak u M δ 0 hM hδ (le_refl 0)
    h_nn h_init h_step N
  simpa using h_gronwall

-- ============================================================
-- PART 3: SMOKE TEST — trivial witness
-- ============================================================

/-- Smoke test: the all-zero sequence trivially satisfies Gronwall's
    hypotheses, and the conclusion gives `0 ≤ 0`. -/
example (M δ : Rat) (hM : 0 ≤ M) (hδ : 0 ≤ δ) (N : Nat) :
    (fun _ : Nat => (0 : Rat)) N ≤ (N : Rat) * (1+M)^N * δ := by
  have h := Rat.discrete_gronwall_zero_init
    (fun _ => (0 : Rat)) M δ hM hδ
    (fun _ => le_refl 0) rfl (fun _ => by simp; exact hδ)
  exact h N

-- ============================================================
-- PART 4: BOUNDED-RHS COROLLARY (uniform decay)
-- ============================================================

/-- **Uniform decay form**: for a sequence satisfying Gronwall with both
    `ε₀` and `δ` bounded by the same small quantity `η`, the bound becomes
    `u N ≤ (1 + N) · (1+M)^N · η`.

    Useful for the eventual TauReal-level "as discretization refines, the
    error goes to 0" argument: pick `η = max(ε₀, δ)` going to 0. -/
theorem Rat.discrete_gronwall_uniform
    (u : Nat → Rat) (M η : Rat)
    (hM : 0 ≤ M) (hη : 0 ≤ η)
    (h_nn : ∀ n, 0 ≤ u n)
    (h_0 : u 0 ≤ η)
    (h_step : ∀ n, u (n+1) ≤ (1+M) * u n + η) :
    ∀ N, u N ≤ (1 + (N : Rat)) * (1+M)^N * η := by
  intro N
  have h_gronwall := Rat.discrete_gronwall_weak u M η η hM hη hη
    h_nn h_0 h_step N
  -- (1+M)^N · η + N · (1+M)^N · η = (1+N) · (1+M)^N · η
  have h_combine : (1+M)^N * η + (N : Rat) * (1+M)^N * η
                = (1 + (N : Rat)) * (1+M)^N * η := by ring
  linarith [h_gronwall, h_combine]

-- ============================================================
-- PART 5: ABSOLUTE VALUE VARIANT
-- ============================================================

/-- **Discrete Gronwall on absolute values**: a common formulation in
    analytical proofs. Given a Rat-valued sequence `v` (not necessarily
    non-negative), if the absolute values satisfy the recurrence, then
    the absolute-value Gronwall bound holds.

    This is essentially `Rat.discrete_gronwall_weak` applied to `|v n|`. -/
theorem Rat.discrete_gronwall_abs
    (v : Nat → Rat) (M δ ε₀ : Rat)
    (hM : 0 ≤ M) (hδ : 0 ≤ δ) (hε₀ : 0 ≤ ε₀)
    (h_0 : |v 0| ≤ ε₀)
    (h_step : ∀ n, |v (n+1)| ≤ (1+M) * |v n| + δ) :
    ∀ N, |v N| ≤ (1+M)^N * ε₀ + (N : Rat) * (1+M)^N * δ := by
  apply Rat.discrete_gronwall_weak (fun n => |v n|) M δ ε₀ hM hδ hε₀
  · intro n; exact abs_nonneg _
  · exact h_0
  · exact h_step

end Tau.Boundary
