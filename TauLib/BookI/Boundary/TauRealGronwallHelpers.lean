import TauLib.BookI.Boundary.TauRealAnalyticalHelpers
import Mathlib.Tactic.Ring
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity

/-!
# TauLib.BookI.Boundary.TauRealGronwallHelpers

Named lemmas for the discrete Gronwall inequality (Wave Γ₈ Phase 2.6.B.2.β.4.9).

## Rationale

The discrete Gronwall lemma at TauReal level uses three key Rat-level
inequalities that don't close cleanly via `linarith` / `positivity`:

1. **Geometric / Bernoulli-style growth**: `(1 + M)^N` bounds for non-negative M
2. **Telescoping induction**: the recurrence `u_{n+1} ≤ (1+M)·u_n + δ`
   unfolds to `u_N ≤ (1+M)^N · u_0 + δ · ((1+M)^N - 1)/M` (or weaker form for M=0).
3. **Uniform absolute bound**: `(1+M)^N ≤ (1+M)^N` (monotone), with explicit
   numeric upper bound when `M ≤ M_max`.

These helpers parallel `TauRealAnalyticalHelpers.lean`'s pattern: prove once,
reuse in the main Gronwall proof + downstream applications.
-/

set_option autoImplicit false

namespace Tau.Boundary

-- ============================================================
-- PART 1: BERNOULLI INEQUALITY (Rat)
-- ============================================================

/-- **Bernoulli's inequality at Rat level**: `1 + N·M ≤ (1+M)^N` for `M ≥ 0`.

    Proof by induction on N. Base `N = 0`: `1 ≤ 1`. Step: assume `1 + N·M ≤ (1+M)^N`,
    multiply both sides by `(1+M)` (which is `≥ 1 ≥ 0`), use IH + algebra. -/
theorem Rat.bernoulli_inequality (M : Rat) (hM : 0 ≤ M) (N : Nat) :
    1 + (N : Rat) * M ≤ (1 + M) ^ N := by
  induction N with
  | zero => simp
  | succ n ih =>
    have h_pos : (0 : Rat) ≤ 1 + M := by linarith
    have h_mul : (1 + (n : Rat) * M) * (1 + M) ≤ (1 + M) ^ n * (1 + M) := by
      have h_pow_nn : (0 : Rat) ≤ (1 + M) ^ n := pow_nonneg h_pos n
      exact mul_le_mul_of_nonneg_right ih h_pos
    have h_lhs : (1 + (n : Rat) * M) * (1 + M)
                = 1 + (n+1 : Nat) * M + (n : Rat) * M * M := by
      push_cast; ring
    have h_rhs : (1 + M) ^ n * (1 + M) = (1 + M) ^ (n+1) := by ring
    have h_extra : (0 : Rat) ≤ (n : Rat) * M * M := by
      have h_n_nn : (0 : Rat) ≤ (n : Rat) := by exact_mod_cast Nat.zero_le n
      have h_nM_nn : (0 : Rat) ≤ (n : Rat) * M := mul_nonneg h_n_nn hM
      exact mul_nonneg h_nM_nn hM
    -- 1 + (n+1) M ≤ 1 + (n+1) M + n M² = (1 + n M)(1+M) ≤ (1+M)^n (1+M) = (1+M)^(n+1)
    have h_chain : 1 + ((n+1 : Nat) : Rat) * M
                ≤ (1 + (n : Rat) * M) * (1 + M) := by
      rw [h_lhs]; linarith
    linarith [h_mul, h_rhs]

-- ============================================================
-- PART 2: POSITIVITY OF (1+M)^N FOR NON-NEGATIVE M
-- ============================================================

/-- `(1 + M)^N ≥ 1` for `M ≥ 0` — corollary of Bernoulli or direct positivity. -/
theorem Rat.one_le_one_plus_pow (M : Rat) (hM : 0 ≤ M) (N : Nat) :
    1 ≤ (1 + M) ^ N := by
  have h_bern := Rat.bernoulli_inequality M hM N
  have h_n_nn : (0 : Rat) ≤ (N : Rat) := by exact_mod_cast Nat.zero_le N
  have h_nM_nn : (0 : Rat) ≤ (N : Rat) * M := mul_nonneg h_n_nn hM
  linarith

/-- `(1 + M)^N > 0` for `M ≥ 0` (positivity). -/
theorem Rat.one_plus_pow_pos (M : Rat) (hM : 0 ≤ M) (N : Nat) :
    (0 : Rat) < (1 + M) ^ N := by
  have h := Rat.one_le_one_plus_pow M hM N
  linarith

-- ============================================================
-- PART 3: TELESCOPING INDUCTIVE STEP
-- ============================================================

/-- **Discrete Gronwall step bound**: given `0 ≤ M`, `0 ≤ δ`,
    `0 ≤ u_n`, and the bound `u_n ≤ (1+M)^n · u_0 + n · (1+M)^n · δ`,
    plus the recurrence `u_{n+1} ≤ (1+M) · u_n + δ`, conclude
    `u_{n+1} ≤ (1+M)^{n+1} · u_0 + (n+1) · (1+M)^{n+1} · δ`.

    This is the inductive step of the basic discrete Gronwall inequality
    (weaker than the tight form but easier to manipulate). -/
theorem Rat.gronwall_inductive_step
    (M δ : Rat) (hM : 0 ≤ M) (hδ : 0 ≤ δ)
    (u_n u_succ_n u_0 : Rat) (n : Nat)
    (hu_0_nn : 0 ≤ u_0) (hu_n_nn : 0 ≤ u_n)
    (h_ih : u_n ≤ (1 + M) ^ n * u_0 + (n : Rat) * (1 + M) ^ n * δ)
    (h_step : u_succ_n ≤ (1 + M) * u_n + δ) :
    u_succ_n ≤ (1 + M) ^ (n+1) * u_0 + ((n+1 : Nat) : Rat) * (1 + M) ^ (n+1) * δ := by
  have h_pos : (0 : Rat) ≤ 1 + M := by linarith
  have h_pow_pos : (0 : Rat) ≤ (1 + M) ^ n := pow_nonneg h_pos n
  -- (1+M) · u_n ≤ (1+M) · ((1+M)^n · u_0 + n·(1+M)^n·δ)
  have h_scaled : (1 + M) * u_n
                ≤ (1 + M) * ((1 + M) ^ n * u_0 + (n : Rat) * (1 + M) ^ n * δ) := by
    exact mul_le_mul_of_nonneg_left h_ih h_pos
  -- Algebraic: (1+M) · ((1+M)^n · u_0 + n·(1+M)^n·δ) = (1+M)^(n+1)·u_0 + n·(1+M)^(n+1)·δ
  have h_alg : (1 + M) * ((1 + M) ^ n * u_0 + (n : Rat) * (1 + M) ^ n * δ)
            = (1 + M) ^ (n+1) * u_0 + (n : Rat) * (1 + M) ^ (n+1) * δ := by
    ring
  -- Combine: u_{n+1} ≤ (1+M) · u_n + δ ≤ (1+M)^(n+1)·u_0 + n·(1+M)^(n+1)·δ + δ
  -- Want: ≤ (1+M)^(n+1)·u_0 + (n+1)·(1+M)^(n+1)·δ
  -- i.e., need: n·(1+M)^(n+1)·δ + δ ≤ (n+1)·(1+M)^(n+1)·δ
  -- i.e., δ ≤ (1+M)^(n+1)·δ. True since (1+M)^(n+1) ≥ 1 and δ ≥ 0.
  have h_pow_succ_ge_one : 1 ≤ (1 + M) ^ (n+1) :=
    Rat.one_le_one_plus_pow M hM (n+1)
  have h_delta_bound : δ ≤ (1 + M) ^ (n+1) * δ := by
    nlinarith [h_pow_succ_ge_one, hδ]
  have h_cast : ((n+1 : Nat) : Rat) = (n : Rat) + 1 := by push_cast; ring
  rw [h_cast]
  nlinarith [h_step, h_scaled, h_alg, h_delta_bound]

-- ============================================================
-- PART 4: UNIFORM BOUND FOR (1 + 1/(N+1))^N
-- ============================================================

/-- For step size `h = 1/(N+1)` and unit decay constant `M`, the term `(1 + h·M)^N`
    is loosely bounded by `(1+M)^N` (since `h ≤ 1` for `N ≥ 0`).

    This is a coarse but easy bound used in the Gronwall lift to TauReal. -/
theorem Rat.one_plus_scaled_pow_le_one_plus_pow
    (M : Rat) (hM : 0 ≤ M) (N : Nat) (h : Rat) (h_nn : 0 ≤ h) (h_le : h ≤ 1) :
    (1 + h * M) ^ N ≤ (1 + M) ^ N := by
  have h_base_pos : (0 : Rat) ≤ 1 + h * M := by
    have h_hM_nn : 0 ≤ h * M := mul_nonneg h_nn hM
    linarith
  have h_base_le : 1 + h * M ≤ 1 + M := by
    have h_hM_le : h * M ≤ 1 * M := by
      exact mul_le_mul_of_nonneg_right h_le hM
    linarith
  exact pow_le_pow_left₀ h_base_pos h_base_le N

end Tau.Boundary
