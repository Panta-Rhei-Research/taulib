import TauLib.BookI.Boundary.TauRealIotaTau
import TauLib.BookI.Boundary.TauRealAnalyticalHelpers
import TauLib.BookI.Boundary.TauRealSum
import TauLib.BookI.Boundary.TauRealExp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity

/-!
# TauLib.BookI.Boundary.TauRealSin

**Wave Γ₇ Phase 3A — τ-native sin(x) at TauRat arguments.**

The sin Taylor series

$$ \sin(x) \;=\; \sum_{n=0}^\infty \frac{(-1)^n \, x^{2n+1}}{(2n+1)!}
   \;=\; x - \frac{x^3}{3!} + \frac{x^5}{5!} - \frac{x^7}{7!} + \cdots $$

paired into the all-positive form to avoid alternating-series
machinery (the tactics-only Mathlib budget can't comfortably
support it).

## Paired form

Pair `k` aggregates the `n = 2k` and `n = 2k + 1` Taylor terms:

$$ \mathrm{sin\_pair}_k(x) \;=\; \frac{x^{4k+1}}{(4k+1)!} - \frac{x^{4k+3}}{(4k+3)!} $$

For `0 ≤ x ≤ 1`, this is non-negative: `1/(4k+1)! ≥ x²/(4k+3)!`
since `(4k+3)! = (4k+1)! · (4k+3)(4k+2) ≥ 6 · (4k+1)!`, and
`x² ≤ 1`.

## Wave Γ₇ Phase plan

* **Phase 3A** (this commit): paired-term construction, partial-sum,
  toRat bridges, per-term magnitude bound `≤ 2/(4k+1)!`.
* **Phase 3B**: companion `TauRealCos.lean` with parallel structure.
* **Phase 3C (M3 breakthrough)**: sin/cos addition formula via
  exp-addition + i-structure decomposition.
* **Phase 3D-3F**: arctan inverse, addition formula, Machin chain
  proof of `pi_machin.equiv pi_leibniz`.

## Construction pattern

Following the `TauRealExp` template:

```
def sin_pair_term x k =
  let first  := (pow x (4k+1)) / (4k+1)!   -- via structural num/den
  let second := (pow x (4k+3)) / (4k+3)!   -- via structural num/den
  first.sub second                          -- via TauRat.sub
```

This uses `TauRat.pow` (from `TauRealExp`), per-piece factorial
division (mirroring `exp_term`), and `TauRat.sub` to combine.

## Registry Cross-References

* [I.D-Exp-Term] `TauRat.exp_term` (the template, `TauRealExp.lean`)
* [I.D-Arctan-Reciprocal-Pair-Term] `TauRat.arctan_reciprocal_pair_term`
  (Wave Γ₇ Phase 1A — parallel structure)
* Wave Γ₇ Phase 3 strategy doc
  `atlas/planning/wave-gamma-7-phase-3-strategy.md`
* `cauchy-bound-template-pattern` atlas insight (2026-05-14)

## Build state

* `sorry` count: 0
* `axiom` count: 0
* Imports: TauLib (TauRealIotaTau, TauRealAnalyticalHelpers,
  TauRealSum, TauRealExp for TauRat.pow) + Mathlib tactics-only.

## Phase 3A deliverables (this commit)

* `TauRat.sin_pair_term_first`, `TauRat.sin_pair_term_second` —
  the two sub-fractions making up the paired sin term.
* `TauRat.sin_pair_term x k` — `first - second` via TauRat.sub.
* `sin_pair_term_rat x k` — natural Rat formula.
* `TauRat.sin_pair_term_toRat` — bridge.
* `TauRat.sin_partial x n` — partial sum via TauRat.sum.
* `sin_partial_rat x n` — Rat companion.
* `TauRat.sin_partial_toRat` — partial-sum bridge.
* `sin_pair_term_rat_abs_bound` — per-term magnitude bound
  `|sin_pair_term_rat x k| ≤ 2/(4k+1)!` for `|x| ≤ 1`.
-/

set_option autoImplicit false

namespace Tau.Boundary

open Tau.Denotation

-- ============================================================
-- PART 1: SIN PAIRED TERM CONSTRUCTION (TauRat level)
-- ============================================================

/-- The first sub-fraction of the k-th sin paired term:
    `x^(4k+1) / (4k+1)!`. Built by taking the TauRat power and
    multiplying its denominator by `(4k+1)!`. -/
def TauRat.sin_pair_term_first (x : TauRat) (k : Nat) : TauRat :=
  { num    := (TauRat.pow x (4*k+1)).num
    den    := (TauRat.pow x (4*k+1)).den * Nat.factorial (4*k+1)
    den_pos := Nat.mul_pos (TauRat.pow x (4*k+1)).den_pos
                            (Nat.factorial_pos (4*k+1)) }

/-- The second sub-fraction of the k-th sin paired term:
    `x^(4k+3) / (4k+3)!`. -/
def TauRat.sin_pair_term_second (x : TauRat) (k : Nat) : TauRat :=
  { num    := (TauRat.pow x (4*k+3)).num
    den    := (TauRat.pow x (4*k+3)).den * Nat.factorial (4*k+3)
    den_pos := Nat.mul_pos (TauRat.pow x (4*k+3)).den_pos
                            (Nat.factorial_pos (4*k+3)) }

/-- The k-th sin paired term as a TauRat:
    `pair_k(x) = x^(4k+1)/(4k+1)! − x^(4k+3)/(4k+3)!`.

    Uses TauRat.sub on the two sub-fractions, so signed inputs
    handle correctly via the Int-level subtraction. -/
def TauRat.sin_pair_term (x : TauRat) (k : Nat) : TauRat :=
  (TauRat.sin_pair_term_first x k).sub (TauRat.sin_pair_term_second x k)

-- ============================================================
-- PART 2: TOR-LEVEL BRIDGE
-- ============================================================

/-- The k-th sin paired term at the Rat level (the natural
    arithmetic form). -/
def sin_pair_term_rat (x : Rat) (k : Nat) : Rat :=
  x^(4*k+1) / (Nat.factorial (4*k+1) : Rat) -
  x^(4*k+3) / (Nat.factorial (4*k+3) : Rat)

/-- Helper: `(sin_pair_term_first x k).toRat = pow(x, 4k+1).toRat / (4k+1)!`. -/
private theorem sin_pair_term_first_toRat (x : TauRat) (k : Nat) :
    (TauRat.sin_pair_term_first x k).toRat
      = (TauRat.pow x (4*k+1)).toRat / (Nat.factorial (4*k+1) : Rat) := by
  unfold TauRat.sin_pair_term_first TauRat.toRat TauInt.toInt
  have h_fac : (0 : Rat) < (Nat.factorial (4*k+1) : Rat) := by
    have := Nat.factorial_pos (4*k+1); exact_mod_cast this
  push_cast
  field_simp

/-- Helper: `(sin_pair_term_second x k).toRat = pow(x, 4k+3).toRat / (4k+3)!`. -/
private theorem sin_pair_term_second_toRat (x : TauRat) (k : Nat) :
    (TauRat.sin_pair_term_second x k).toRat
      = (TauRat.pow x (4*k+3)).toRat / (Nat.factorial (4*k+3) : Rat) := by
  unfold TauRat.sin_pair_term_second TauRat.toRat TauInt.toInt
  have h_fac : (0 : Rat) < (Nat.factorial (4*k+3) : Rat) := by
    have := Nat.factorial_pos (4*k+3); exact_mod_cast this
  push_cast
  field_simp

/-- **Bridge theorem**: the TauRat construction and the Rat formula
    agree under `.toRat`. -/
theorem TauRat.sin_pair_term_toRat (x : TauRat) (k : Nat) :
    (TauRat.sin_pair_term x k).toRat = sin_pair_term_rat x.toRat k := by
  unfold TauRat.sin_pair_term sin_pair_term_rat
  rw [toRat_sub, sin_pair_term_first_toRat, sin_pair_term_second_toRat,
      TauRat.pow_toRat, TauRat.pow_toRat]

-- ============================================================
-- PART 3: SIN PARTIAL SUM
-- ============================================================

/-- Partial sum of the sin paired series:
    `sin_partial x n = Σ_{k=0}^{n-1} pair_k(x)`. -/
def TauRat.sin_partial (x : TauRat) (n : Nat) : TauRat :=
  TauRat.sum (TauRat.sin_pair_term x) n

@[simp] theorem TauRat.sin_partial_zero (x : TauRat) :
    TauRat.sin_partial x 0 = TauRat.zero := rfl

@[simp] theorem TauRat.sin_partial_succ (x : TauRat) (n : Nat) :
    TauRat.sin_partial x (n + 1) =
      (TauRat.sin_partial x n).add (TauRat.sin_pair_term x n) := rfl

/-- Rat-level companion partial sum. -/
def sin_partial_rat (x : Rat) : Nat → Rat
  | 0 => 0
  | n + 1 => sin_partial_rat x n + sin_pair_term_rat x n

@[simp] theorem sin_partial_rat_zero (x : Rat) : sin_partial_rat x 0 = 0 := rfl

@[simp] theorem sin_partial_rat_succ (x : Rat) (n : Nat) :
    sin_partial_rat x (n + 1) = sin_partial_rat x n + sin_pair_term_rat x n := rfl

/-- **Partial-sum bridge theorem**. -/
theorem TauRat.sin_partial_toRat (x : TauRat) (n : Nat) :
    (TauRat.sin_partial x n).toRat = sin_partial_rat x.toRat n := by
  induction n with
  | zero =>
    simp [TauRat.sin_partial_zero, sin_partial_rat_zero, toRat_zero]
  | succ n ih =>
    rw [TauRat.sin_partial_succ, toRat_add, ih, TauRat.sin_pair_term_toRat,
        sin_partial_rat_succ]

-- ============================================================
-- PART 4: PER-TERM MAGNITUDE BOUND
-- ============================================================

/-- Helper: `(4k+1)! ≤ (4k+3)!` (factorial monotonicity at integers
    differing by ≤ 2). -/
private theorem factorial_4k1_le_4k3 (k : Nat) :
    Nat.factorial (4*k+1) ≤ Nat.factorial (4*k+3) := by
  apply Nat.factorial_le
  omega

/-- **Per-term magnitude bound (Wave Γ₇ Phase 3A — Cauchy seed)**:
    each sin paired term is bounded in absolute value by
    `2 / (4k+1)!` for `|x| ≤ 1`.

    Proof: triangle inequality on the difference, then bound each
    sub-fraction by `1/(4k+1)!`:

    * `|x^(4k+1)/(4k+1)!| ≤ 1/(4k+1)!` (since `|x|^(4k+1) ≤ 1`).
    * `|x^(4k+3)/(4k+3)!| ≤ 1/(4k+3)! ≤ 1/(4k+1)!`.
    * Sum: `≤ 2/(4k+1)!`. -/
theorem sin_pair_term_rat_abs_bound (x : Rat) (hx : |x| ≤ 1) (k : Nat) :
    |sin_pair_term_rat x k| ≤ 2 / (Nat.factorial (4*k+1) : Rat) := by
  unfold sin_pair_term_rat
  -- Positivity of factorial denominators.
  have h_fac_4k1_pos : (0 : Rat) < (Nat.factorial (4*k+1) : Rat) := by
    have := Nat.factorial_pos (4*k+1); exact_mod_cast this
  have h_fac_4k3_pos : (0 : Rat) < (Nat.factorial (4*k+3) : Rat) := by
    have := Nat.factorial_pos (4*k+3); exact_mod_cast this
  have h_fac_le : (Nat.factorial (4*k+1) : Rat) ≤ (Nat.factorial (4*k+3) : Rat) := by
    have := factorial_4k1_le_4k3 k; exact_mod_cast this
  -- Bound each sub-fraction.
  have h_x_pow_4k1 : |x^(4*k+1)| ≤ 1 := by
    rw [abs_pow]
    exact pow_le_one₀ (abs_nonneg _) hx
  have h_x_pow_4k3 : |x^(4*k+3)| ≤ 1 := by
    rw [abs_pow]
    exact pow_le_one₀ (abs_nonneg _) hx
  -- |first| ≤ 1/(4k+1)!
  have h_first_abs : |x^(4*k+1) / (Nat.factorial (4*k+1) : Rat)|
                      ≤ 1 / (Nat.factorial (4*k+1) : Rat) := by
    rw [abs_div, abs_of_pos h_fac_4k1_pos]
    rw [div_le_div_iff₀ h_fac_4k1_pos h_fac_4k1_pos]
    nlinarith
  -- |second| ≤ 1/(4k+3)! ≤ 1/(4k+1)!
  have h_second_abs : |x^(4*k+3) / (Nat.factorial (4*k+3) : Rat)|
                      ≤ 1 / (Nat.factorial (4*k+1) : Rat) := by
    rw [abs_div, abs_of_pos h_fac_4k3_pos]
    rw [div_le_div_iff₀ h_fac_4k3_pos h_fac_4k1_pos]
    nlinarith
  -- Combine via triangle inequality on the difference.
  have h_tri : |x^(4*k+1) / (Nat.factorial (4*k+1) : Rat) -
                x^(4*k+3) / (Nat.factorial (4*k+3) : Rat)|
                ≤ |x^(4*k+1) / (Nat.factorial (4*k+1) : Rat)| +
                  |x^(4*k+3) / (Nat.factorial (4*k+3) : Rat)| := by
    have := abs_sub (x^(4*k+1) / (Nat.factorial (4*k+1) : Rat))
                    (x^(4*k+3) / (Nat.factorial (4*k+3) : Rat))
    linarith
  -- Final: triangle ≤ 1/(4k+1)! + 1/(4k+1)! = 2/(4k+1)!
  have h_sum : 1 / (Nat.factorial (4*k+1) : Rat) +
               1 / (Nat.factorial (4*k+1) : Rat)
               = 2 / (Nat.factorial (4*k+1) : Rat) := by ring
  linarith

-- ============================================================
-- PART 5: FACTORIAL GROWTH + GEOMETRIC PER-TERM BOUND
-- ============================================================

/-- **Factorial growth bound**: `2^k ≤ (4k+1)!` for all `k ≥ 0`.

    Proof by induction:
    * `k = 0`: `2^0 = 1 = 1!` ✓.
    * `k → k+1`: `(4(k+1)+1)! = (4k+5)·(4k+4)·(4k+3)·(4k+2)·(4k+1)!`.
      By IH `(4k+1)! ≥ 2^k`, and the four-factor product is `≥ 5·4·3·2 = 120 ≥ 2`.
      So `(4k+5)! ≥ 2·2^k = 2^(k+1)`. ✓

    Load-bearing for the sin Cauchy bound: lets us chain
    `2/(4k+1)! ≤ 2/2^k` to fit the existing Cauchy-bound template. -/
theorem Nat.factorial_4k1_ge_two_pow_k (k : Nat) :
    2^k ≤ (4*k+1).factorial := by
  induction k with
  | zero => simp [Nat.factorial]
  | succ k ih =>
    -- Unfold (4(k+1)+1)! = (4k+5)!
    have h_index : 4*(k+1)+1 = 4*k+5 := by ring
    rw [h_index]
    -- Chain of factorial_succ applications to unfold (4k+5)! down to (4k+1)!
    have e0 : (4*k+5).factorial = (4*k+5) * (4*k+4).factorial := by
      rw [show (4*k+5 : Nat) = (4*k+4) + 1 from by omega]
      exact Nat.factorial_succ _
    have e1 : (4*k+4).factorial = (4*k+4) * (4*k+3).factorial := by
      rw [show (4*k+4 : Nat) = (4*k+3) + 1 from by omega]
      exact Nat.factorial_succ _
    have e2 : (4*k+3).factorial = (4*k+3) * (4*k+2).factorial := by
      rw [show (4*k+3 : Nat) = (4*k+2) + 1 from by omega]
      exact Nat.factorial_succ _
    have e3 : (4*k+2).factorial = (4*k+2) * (4*k+1).factorial := by
      rw [show (4*k+2 : Nat) = (4*k+1) + 1 from by omega]
      exact Nat.factorial_succ _
    -- Combined: (4k+5)! = (4k+5)(4k+4)(4k+3)(4k+2)·(4k+1)!
    have h_unfold : (4*k+5).factorial =
        ((4*k+5) * (4*k+4) * (4*k+3) * (4*k+2)) * (4*k+1).factorial := by
      rw [e0, e1, e2, e3]; ring
    rw [h_unfold]
    -- The four-factor product is ≥ 2 (since the (4k+2) factor is ≥ 2).
    have h_factor_ge_two : 2 ≤ (4*k+5) * (4*k+4) * (4*k+3) * (4*k+2) := by
      have h_2 : 2 ≤ 4*k+2 := by omega
      have h_pos : 1 ≤ (4*k+5) * (4*k+4) * (4*k+3) := by
        have : 0 < (4*k+5) * (4*k+4) * (4*k+3) := by positivity
        omega
      calc 2 = 1 * 2 := by ring
        _ ≤ ((4*k+5) * (4*k+4) * (4*k+3)) * (4*k+2) :=
            Nat.mul_le_mul h_pos h_2
    -- Combine: 2^(k+1) = 2·2^k ≤ 2·(4k+1)! ≤ ((4k+5)(4k+4)(4k+3)(4k+2))·(4k+1)!.
    have h_pow_succ : 2^(k+1) = 2 * 2^k := by ring
    calc 2^(k+1)
        = 2 * 2^k := h_pow_succ
      _ ≤ 2 * (4*k+1).factorial := Nat.mul_le_mul_left 2 ih
      _ ≤ ((4*k+5) * (4*k+4) * (4*k+3) * (4*k+2)) * (4*k+1).factorial :=
          Nat.mul_le_mul_right _ h_factor_ge_two

/-- **Geometric per-term bound (Wave Γ₇ Phase 3A — Cauchy seed, geometric form)**:
    each sin paired term is bounded by `2/2^k` for `|x| ≤ 1`.

    Combines `sin_pair_term_rat_abs_bound` (≤ 2/(4k+1)!) with the
    factorial growth `(4k+1)! ≥ 2^k` to fit the Cauchy-bound template. -/
theorem sin_pair_term_rat_abs_bound_geom (x : Rat) (hx : |x| ≤ 1) (k : Nat) :
    |sin_pair_term_rat x k| ≤ 2 / (2 : Rat)^k := by
  have h_factorial := sin_pair_term_rat_abs_bound x hx k
  have h_fac_ge : (2 : Rat)^k ≤ (Nat.factorial (4*k+1) : Rat) := by
    have := Nat.factorial_4k1_ge_two_pow_k k
    have h_cast : ((2^k : Nat) : Rat) = (2 : Rat)^k := by push_cast; ring
    have h_cast_le : ((2^k : Nat) : Rat) ≤ ((Nat.factorial (4*k+1) : Nat) : Rat) :=
      by exact_mod_cast this
    rw [h_cast] at h_cast_le
    exact h_cast_le
  have h_2k_pos : (0 : Rat) < (2 : Rat)^k := by positivity
  have h_fac_pos : (0 : Rat) < (Nat.factorial (4*k+1) : Rat) := by
    have := Nat.factorial_pos (4*k+1); exact_mod_cast this
  have h_bound : (2 : Rat) / (Nat.factorial (4*k+1) : Rat) ≤ 2 / (2 : Rat)^k := by
    rw [div_le_div_iff₀ h_fac_pos h_2k_pos]
    nlinarith
  linarith

-- ============================================================
-- PART 6: CAUCHY TAIL BOUND
-- ============================================================

/-- **Cauchy tail bound — exact form**: for `n ≤ m`, `|x| ≤ 1`,
    `|sin_partial_rat x m − sin_partial_rat x n| ≤ 4/2^n − 4/2^m`.

    The exact form (with the `−4/2^m` correction) is load-bearing for
    the induction; the loose form `≤ 4/2^n` doesn't close the inductive
    step because `IH + 2/2^m > 4/2^n` when `IH = 4/2^n`. The exact form
    leaves room via the algebraic identity
    `(4/2^n − 4/2^m) + 2/2^m = 4/2^n − 2/2^m = 4/2^n − 4/2^(m+1)`. -/
theorem sin_partial_rat_cauchy_bound_exact (x : Rat) (hx : |x| ≤ 1)
    (m n : Nat) (hnm : n ≤ m) :
    |sin_partial_rat x m - sin_partial_rat x n|
      ≤ 4 / (2 : Rat)^n - 4 / (2 : Rat)^m := by
  induction m, hnm using Nat.le_induction with
  | base => simp
  | succ m hnm ih =>
    rw [sin_partial_rat_succ]
    have h_diff : sin_partial_rat x m + sin_pair_term_rat x m - sin_partial_rat x n
                    = (sin_partial_rat x m - sin_partial_rat x n) + sin_pair_term_rat x m := by ring
    rw [h_diff]
    have h_tri : |(sin_partial_rat x m - sin_partial_rat x n) + sin_pair_term_rat x m|
                  ≤ |sin_partial_rat x m - sin_partial_rat x n|
                    + |sin_pair_term_rat x m| := abs_add_le _ _
    have h_term := sin_pair_term_rat_abs_bound_geom x hx m
    -- Algebraic identity: (4/2^n − 4/2^m) + 2/2^m = 4/2^n − 4/2^(m+1)
    have h_2_m_pos : (0 : Rat) < (2 : Rat)^m := by positivity
    have h_pow_succ : (2 : Rat)^(m+1) = 2 * (2 : Rat)^m := by
      rw [pow_succ]; ring
    have h_algebra :
        4 / (2 : Rat)^n - 4 / (2 : Rat)^m + 2 / (2 : Rat)^m
          = 4 / (2 : Rat)^n - 4 / (2 : Rat)^(m+1) := by
      rw [h_pow_succ]
      have h_2_n_pos : (0 : Rat) < (2 : Rat)^n := by positivity
      field_simp
      ring
    linarith

/-- **Cauchy tail bound — loose form**: `|sin_partial_rat x m − sin_partial_rat x n| ≤ 4/2^n`. -/
theorem sin_partial_rat_cauchy_bound (x : Rat) (hx : |x| ≤ 1)
    (m n : Nat) (hnm : n ≤ m) :
    |sin_partial_rat x m - sin_partial_rat x n| ≤ 4 / (2 : Rat)^n := by
  have h_exact := sin_partial_rat_cauchy_bound_exact x hx m n hnm
  have h_subtract_nn : (0 : Rat) ≤ 4 / (2 : Rat)^m := by
    apply div_nonneg (by norm_num : (0 : Rat) ≤ 4)
    positivity
  linarith

-- ============================================================
-- PART 7: TauReal.sin_of_rat + IsCauchy
-- ============================================================

/-- **[I.D-Sin-of-Rat]** The τ-native sin at a fixed TauRat argument.

    The n-th approximation is the partial sum `sin_partial x n`.
    Cauchy under `|x.toRat| ≤ 1` (Wave Γ₇ Phase 3A — the trig
    extension of the Cauchy-bound template).

    Mirrors `TauReal.exp_of_rat`, `TauReal.geom_of_rat`,
    `TauReal.arctan_reciprocal` architecturally. -/
def TauReal.sin_of_rat (x : TauRat) : TauReal :=
  ⟨TauRat.sin_partial x⟩

@[simp] theorem TauReal.sin_of_rat_approx (x : TauRat) (n : Nat) :
    (TauReal.sin_of_rat x).approx n = TauRat.sin_partial x n := rfl

/-- **[I.T-Sin-of-Rat-IsCauchy]** `TauReal.sin_of_rat x` is Cauchy
    under `|x.toRat| ≤ 1` with explicit modulus `λ k => k + 3`.

    Same modulus as exp/geom — the Cauchy-bound template's fourth
    canonical instantiation. -/
theorem TauReal.sin_of_rat_isCauchy (x : TauRat) (hx : |x.toRat| ≤ 1) :
    (TauReal.sin_of_rat x).IsCauchy := by
  refine ⟨fun k => k + 3, ?_⟩
  intro k m n hm hn
  change k + 3 ≤ m at hm
  change k + 3 ≤ n at hn
  unfold TauRat.lt
  rw [TauRat.toRat_abs, toRat_sub, TauRat.ofNatRecip_toRat]
  show |(TauRat.sin_partial x m).toRat - (TauRat.sin_partial x n).toRat|
         < 1 / ((k : Rat) + 1)
  rw [TauRat.sin_partial_toRat, TauRat.sin_partial_toRat]
  by_cases h_le : n ≤ m
  · have h_bound := sin_partial_rat_cauchy_bound x.toRat hx m n h_le
    have h_four_lt := Rat.four_div_two_pow_lt_recip k n hn
    linarith
  · push_neg at h_le
    have h_m_le_n : m ≤ n := Nat.le_of_lt h_le
    have h_swap_abs :
        |sin_partial_rat x.toRat m - sin_partial_rat x.toRat n|
          = |sin_partial_rat x.toRat n - sin_partial_rat x.toRat m| := by
      rw [show sin_partial_rat x.toRat m - sin_partial_rat x.toRat n
            = -(sin_partial_rat x.toRat n - sin_partial_rat x.toRat m) from by ring, abs_neg]
    rw [h_swap_abs]
    have h_bound := sin_partial_rat_cauchy_bound x.toRat hx n m h_m_le_n
    have h_four_lt := Rat.four_div_two_pow_lt_recip k m hm
    linarith

-- ============================================================
-- PART 9: 🎯 sin is ODD — parity identity (Phase 2.6.B.2.β.4.5)
-- ============================================================

/-! ## Phase 2.6.B.2.β.4.5 — sin parity (odd function)

  `sin_pair_term_rat x k = x^(4k+1)/(4k+1)! − x^(4k+3)/(4k+3)!`

  Both `4k+1` and `4k+3` are odd, so `(−x)^odd = −x^odd`, giving
  `sin_pair_term_rat (−x) k = −sin_pair_term_rat x k`. Summing:
  `sin_partial_rat (−x) n = −sin_partial_rat x n`. -/

/-- **[I.T-SinPairTerm-Odd]** `sin_pair_term_rat (−x) k = −sin_pair_term_rat x k`. -/
theorem sin_pair_term_rat_neg (x : Rat) (k : Nat) :
    sin_pair_term_rat (-x) k = -(sin_pair_term_rat x k) := by
  unfold sin_pair_term_rat
  have h_odd1 : Odd (4*k+1) := ⟨2*k, by ring⟩
  have h_odd2 : Odd (4*k+3) := ⟨2*k+1, by ring⟩
  rw [Odd.neg_pow h_odd1, Odd.neg_pow h_odd2]
  ring

/-- **[I.T-SinPartial-Odd]** `sin_partial_rat (−x) n = −sin_partial_rat x n`. -/
theorem sin_partial_rat_neg (x : Rat) (n : Nat) :
    sin_partial_rat (-x) n = -(sin_partial_rat x n) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [sin_partial_rat_succ, ih, sin_pair_term_rat_neg,
        sin_partial_rat_succ]
    ring

/-- **🎯 [I.T-SinOfRat-Odd]** `sin_of_rat (negate q) ≈ negate (sin_of_rat q)` at TauReal. -/
theorem TauReal.sin_of_rat_negate (q : TauRat) :
    TauReal.equiv
      (TauReal.sin_of_rat (TauRat.negate q))
      (TauReal.negate (TauReal.sin_of_rat q)) := by
  apply TauReal.equiv_of_pointwise
  intro n
  rw [equiv_iff_toRat_eq]
  change ((TauRat.sin_partial (TauRat.negate q) n).toRat
        = (TauRat.negate (TauRat.sin_partial q n)).toRat)
  simp only [TauRat.sin_partial_toRat, toRat_negate, sin_partial_rat_neg]

end Tau.Boundary
