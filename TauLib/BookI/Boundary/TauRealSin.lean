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

end Tau.Boundary
