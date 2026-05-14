import TauLib.BookI.Boundary.TauRealIotaTau
import TauLib.BookI.Boundary.TauRealAnalyticalHelpers
import TauLib.BookI.Boundary.TauRealSum
import TauLib.BookI.Boundary.TauRealExp
import TauLib.BookI.Boundary.TauRealPi
import Mathlib.Tactic.Ring
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity

/-!
# TauLib.BookI.Boundary.TauRealArctan

**Wave Γ₇ Phase 1 — τ-native arctan at rational reciprocal arguments.**

The arctan Taylor series

$$ \arctan(x) \;=\; \sum_{n=0}^\infty \frac{(-1)^n \, x^{2n+1}}{2n+1}
   \;=\; x - \frac{x^3}{3} + \frac{x^5}{5} - \cdots $$

specialised to `x = 1/q` (positive rational reciprocal) and paired
into the all-positive form to avoid alternating-series machinery
(the tactics-only Mathlib budget can't comfortably support it).

## Paired form

Pair `k` aggregates the `n = 2k` and `n = 2k + 1` Taylor terms:

$$ \mathrm{pair}_k(x) \;=\; \frac{x^{4k+1}}{4k+1} - \frac{x^{4k+3}}{4k+3} $$

Common-denominator form:

$$ \mathrm{pair}_k(x) \;=\; \frac{x^{4k+1} \cdot \left[(4k+3) - x^2 (4k+1)\right]}{(4k+1)(4k+3)} $$

For `x = 1/q` (positive rational with `q ≥ 1`):

$$ \mathrm{pair}_k(1/q) \;=\; \frac{q^2 (4k+3) - (4k+1)}{q^{4k+3} \cdot (4k+1)(4k+3)} $$

The numerator `q²(4k+3) − (4k+1)` is always positive for `q ≥ 1`
(equals `2` when `q = 1`, equals `96k + 74` when `q = 5`, etc.),
keeping the paired representation in the positive cone.

## Structural relation to existing TauLib π

For `q = 1`: `pair_k(1) = 2/((4k+1)(4k+3))`, so

$$ \pi = 4 \arctan(1) = \sum_{k=0}^\infty \frac{8}{(4k+1)(4k+3)}
       = \sum_{k=0}^\infty 4 \cdot \mathrm{pair}_k(1) $$

This recovers the existing `pi_pair_term k = 8/((4k+1)(4k+3))`
from `TauRealPi.lean` as `4 · arctan_reciprocal_pair_term 1 k`. The
structural connection: **TauLib's `TauReal.pi` is `4 · arctan(1)`**.

## Wave Γ₇ Phase plan

* **Phase 1A** (this commit): paired-term, partial-sum, toRat bridge,
  per-term magnitude bound for `arctan(1/q)` with `q ≥ 1`.
* **Phase 1B**: Cauchy tail bound + IsCauchy at modulus `λ k => k + 2`.
  Mirrors `TauRealGeometric` and `TauRealBBP` template.
* **Phase 2**: Structural connection `4 · arctan_reciprocal 1 ≈ TauReal.pi`.
* **Phase 3**: arctan addition formula
  `arctan(a) + arctan(b) = arctan((a+b)/(1-ab))` for ab < 1.
* **Phase 4**: Machin's formula
  `π = 16 · arctan(1/5) − 4 · arctan(1/239)`.
* **Phase 5**: `pi_machin.equiv pi_leibniz` — the structural payoff.

## Registry Cross-References

* [I.D-Pi-BBP] `TauReal.pi_bbp` (Wave Γ₆)
* [I.T-Pi-Cauchy] `TauReal.pi.IsCauchy` (Wave 4)
* [I.D-Pi-Pair-Term] `TauRat.pi_pair_term` (Wave 4)
* Wave Γ₇ atlas red-team verdict
  `2026-05-14-accelerated-pi-feasibility-redteam/verdict.md`
* `cauchy-bound-template-pattern` atlas insight (2026-05-14)

## Build state

* `sorry` count: 0
* `axiom` count: 0
* Imports: TauLib (TauRealIotaTau, TauRealAnalyticalHelpers, TauRealSum,
  TauRealExp for `TauRat.pow`, TauRealPi for the existing π) +
  Mathlib tactics-only.

## Phase 1A deliverables (this commit)

* `TauRat.arctan_reciprocal_pair_term q k` — the k-th paired arctan
  term at argument `1/q`, as a TauRat.
* `arctan_reciprocal_pair_term_rat q k` — natural Rat formula.
* `TauRat.arctan_reciprocal_pair_term_toRat` — bridge theorem.
* `TauRat.arctan_reciprocal_partial q n` — partial sum.
* `arctan_reciprocal_partial_rat q n` — Rat companion.
* `TauRat.arctan_reciprocal_partial_toRat` — partial-sum bridge.
* `arctan_reciprocal_pair_term_rat_abs_bound` — per-term magnitude
  bound `≤ 2/q^(4k+1)` (the seed for the Cauchy-bound template).
* `pi_pair_term_eq_four_times_arctan_one` — the structural identity
  `pi_pair_term k = 4 · arctan_reciprocal_pair_term 1 k`.
-/

set_option autoImplicit false

namespace Tau.Boundary

open Tau.Denotation

-- ============================================================
-- PART 1: arctan(1/q) PAIRED TERM CONSTRUCTION (TauRat level)
-- ============================================================

/-- The denominator of the k-th arctan(1/q) paired term:
    `q^(4k+3) · (4k+1) · (4k+3)`. -/
def arctan_reciprocal_denom (q k : Nat) : Nat :=
  q ^ (4 * k + 3) * (4 * k + 1) * (4 * k + 3)

theorem arctan_reciprocal_denom_pos (q k : Nat) (hq : 1 ≤ q) :
    0 < arctan_reciprocal_denom q k := by
  unfold arctan_reciprocal_denom
  have h_q : 0 < q := hq
  positivity

/-- The k-th arctan(1/q) paired term as a TauRat.
    Uses TauInt's pos/neg slots directly (`pos = q²(4k+3)`,
    `neg = 4k+1`) so that the Int-level `pos − neg` subtraction
    avoids the Nat-subtraction casting issues. -/
def TauRat.arctan_reciprocal_pair_term (q k : Nat) (hq : 1 ≤ q) : TauRat :=
  ⟨⟨q ^ 2 * (4 * k + 3), 4 * k + 1⟩,
   arctan_reciprocal_denom q k,
   arctan_reciprocal_denom_pos q k hq⟩

-- ============================================================
-- PART 2: TOR-LEVEL BRIDGE
-- ============================================================

/-- The k-th arctan(1/q) paired term at the Rat level (the natural
    arithmetic form). -/
def arctan_reciprocal_pair_term_rat (q k : Nat) : Rat :=
  (1 / ((q : Rat)^(4*k+1))) * (1 / ((4*k+1 : Nat) : Rat))
  - (1 / ((q : Rat)^(4*k+3))) * (1 / ((4*k+3 : Nat) : Rat))

/-- **Bridge theorem**: the TauRat construction and the natural
    Rat formula agree under `.toRat`. -/
theorem TauRat.arctan_reciprocal_pair_term_toRat (q k : Nat) (hq : 1 ≤ q) :
    (TauRat.arctan_reciprocal_pair_term q k hq).toRat
      = arctan_reciprocal_pair_term_rat q k := by
  unfold TauRat.arctan_reciprocal_pair_term arctan_reciprocal_pair_term_rat
  unfold TauRat.toRat TauInt.toInt arctan_reciprocal_denom
  -- Positivity of all denominators.
  have h_q_pos : (0 : Rat) < (q : Rat) := by
    have : (0 : Nat) < q := hq
    exact_mod_cast this
  have h_q_4k1_pos : (0 : Rat) < (q : Rat)^(4*k+1) := by positivity
  have h_q_4k3_pos : (0 : Rat) < (q : Rat)^(4*k+3) := by positivity
  have h_4k1_pos : (0 : Rat) < ((4*k+1 : Nat) : Rat) := by
    have : (0 : Nat) < 4 * k + 1 := by omega
    exact_mod_cast this
  have h_4k3_pos : (0 : Rat) < ((4*k+3 : Nat) : Rat) := by
    have : (0 : Nat) < 4 * k + 3 := by omega
    exact_mod_cast this
  -- q^(4k+3) = q^(4k+1) · q² (for ring to clean up).
  have h_pow_split : ((q : Rat))^(4*k+3) = ((q : Rat))^(4*k+1) * ((q : Rat))^2 := by
    rw [show 4*k+3 = (4*k+1) + 2 from by ring, pow_add]
  push_cast
  field_simp
  ring

-- ============================================================
-- PART 3: arctan(1/q) PARTIAL SUM
-- ============================================================

/-- Partial sum of the arctan(1/q) paired series:
    `arctan_reciprocal_partial q n = Σ_{k=0}^{n-1} pair_k(1/q)`. -/
def TauRat.arctan_reciprocal_partial (q : Nat) (hq : 1 ≤ q) (n : Nat) : TauRat :=
  TauRat.sum (fun k => TauRat.arctan_reciprocal_pair_term q k hq) n

@[simp] theorem TauRat.arctan_reciprocal_partial_zero (q : Nat) (hq : 1 ≤ q) :
    TauRat.arctan_reciprocal_partial q hq 0 = TauRat.zero := rfl

@[simp] theorem TauRat.arctan_reciprocal_partial_succ
    (q : Nat) (hq : 1 ≤ q) (n : Nat) :
    TauRat.arctan_reciprocal_partial q hq (n + 1) =
      (TauRat.arctan_reciprocal_partial q hq n).add
        (TauRat.arctan_reciprocal_pair_term q n hq) := rfl

/-- Rat-level companion partial sum. -/
def arctan_reciprocal_partial_rat (q : Nat) : Nat → Rat
  | 0 => 0
  | n + 1 => arctan_reciprocal_partial_rat q n + arctan_reciprocal_pair_term_rat q n

@[simp] theorem arctan_reciprocal_partial_rat_zero (q : Nat) :
    arctan_reciprocal_partial_rat q 0 = 0 := rfl

@[simp] theorem arctan_reciprocal_partial_rat_succ (q : Nat) (n : Nat) :
    arctan_reciprocal_partial_rat q (n + 1) =
      arctan_reciprocal_partial_rat q n + arctan_reciprocal_pair_term_rat q n := rfl

/-- **Partial-sum bridge theorem**: the TauRat partial sum and the
    Rat companion agree under `.toRat`. -/
theorem TauRat.arctan_reciprocal_partial_toRat (q : Nat) (hq : 1 ≤ q) (n : Nat) :
    (TauRat.arctan_reciprocal_partial q hq n).toRat
      = arctan_reciprocal_partial_rat q n := by
  induction n with
  | zero =>
    simp [TauRat.arctan_reciprocal_partial_zero, arctan_reciprocal_partial_rat_zero,
          toRat_zero]
  | succ n ih =>
    rw [TauRat.arctan_reciprocal_partial_succ, toRat_add, ih,
        TauRat.arctan_reciprocal_pair_term_toRat, arctan_reciprocal_partial_rat_succ]

-- ============================================================
-- PART 4: STRUCTURAL CONNECTION TO EXISTING TauLib π
-- ============================================================

/-- **The structural identity** (Wave Γ₇ Phase 1A — key bridge):
    the existing `pi_pair_term k = 8/((4k+1)(4k+3))` equals
    `4 · arctan_reciprocal_pair_term 1 k` at the Rat level.

    This is the τ-canon-internal articulation that
    **TauLib's `TauReal.pi` is precisely `4 · arctan(1)`** — the
    classical Leibniz identity, made τ-native. -/
theorem pi_pair_term_eq_four_times_arctan_one (k : Nat) :
    (TauRat.pi_pair_term k).toRat
      = 4 * arctan_reciprocal_pair_term_rat 1 k := by
  rw [TauRat.pi_pair_term_toRat]
  unfold arctan_reciprocal_pair_term_rat
  -- For q = 1: 1^(4k+r) = 1, so 1/1^(4k+1) = 1, 1/1^(4k+3) = 1.
  have h_pow_one : ∀ m : Nat, ((1 : Nat) : Rat)^m = 1 := by
    intro m; simp
  simp only [Nat.cast_one, one_pow]
  -- Goal: 8 / ((4k+1)(4k+3)) = 4 · (1/(4k+1) - 1/(4k+3))
  have h_4k1_pos : (0 : Rat) < ((4*k+1 : Nat) : Rat) := by
    have : (0 : Nat) < 4 * k + 1 := by omega
    exact_mod_cast this
  have h_4k3_pos : (0 : Rat) < ((4*k+3 : Nat) : Rat) := by
    have : (0 : Nat) < 4 * k + 3 := by omega
    exact_mod_cast this
  push_cast
  field_simp
  ring

-- ============================================================
-- PART 5: PER-TERM MAGNITUDE BOUND
-- ============================================================

/-- **Per-term magnitude bound (Wave Γ₇ Phase 1A — Cauchy seed)**:
    each arctan(1/q) paired term is bounded in absolute value by
    `2 / q^(4k+1)`.

    Proof: bound the bracket
    `b = 1/((4k+1) · q^(4k+1)) − 1/((4k+3) · q^(4k+3))`
    by `0 ≤ b ≤ 1/q^(4k+1)`, then add `2` slack. The two sub-terms
    are both positive (so `b` lies in `[0, first term]`), and the
    first term is bounded by `1/q^(4k+1)` (since `4k + 1 ≥ 1`).

    Combined with the `1/q^(4k+1)` factor, we get `|b| ≤ 1/q^(4k+1)`,
    and we use `2/q^(4k+1)` as a slightly-loose-but-cleaner bound
    that fits the Cauchy-bound template. -/
theorem arctan_reciprocal_pair_term_rat_abs_bound (q k : Nat) (hq : 1 ≤ q) :
    |arctan_reciprocal_pair_term_rat q k| ≤ 2 / ((q : Rat)^(4*k+1)) := by
  unfold arctan_reciprocal_pair_term_rat
  have h_q_pos : (0 : Rat) < (q : Rat) := by
    have : (0 : Nat) < q := hq
    exact_mod_cast this
  have h_q_4k1_pos : (0 : Rat) < (q : Rat)^(4*k+1) := by positivity
  have h_q_4k3_pos : (0 : Rat) < (q : Rat)^(4*k+3) := by positivity
  have h_4k1_pos : (0 : Rat) < ((4*k+1 : Nat) : Rat) := by
    have : (0 : Nat) < 4 * k + 1 := by omega
    exact_mod_cast this
  have h_4k3_pos : (0 : Rat) < ((4*k+3 : Nat) : Rat) := by
    have : (0 : Nat) < 4 * k + 3 := by omega
    exact_mod_cast this
  -- Each sub-fraction is positive.
  have h_term_1_pos :
      0 < 1 / (q : Rat)^(4*k+1) * (1 / ((4*k+1 : Nat) : Rat)) := by
    apply mul_pos
    · exact div_pos (by norm_num) h_q_4k1_pos
    · exact div_pos (by norm_num) h_4k1_pos
  have h_term_3_pos :
      0 < 1 / (q : Rat)^(4*k+3) * (1 / ((4*k+3 : Nat) : Rat)) := by
    apply mul_pos
    · exact div_pos (by norm_num) h_q_4k3_pos
    · exact div_pos (by norm_num) h_4k3_pos
  -- Upper bound on first term: 1/(q^(4k+1) · (4k+1)) ≤ 1/q^(4k+1)
  have h_term_1_upper :
      1 / (q : Rat)^(4*k+1) * (1 / ((4*k+1 : Nat) : Rat))
        ≤ 1 / (q : Rat)^(4*k+1) := by
    have h_4k1_ge_1 : (1 : Rat) ≤ ((4*k+1 : Nat) : Rat) := by
      have : (1 : Nat) ≤ 4 * k + 1 := by omega
      exact_mod_cast this
    have h_div_le_1 : 1 / ((4*k+1 : Nat) : Rat) ≤ 1 := by
      rw [div_le_iff₀ h_4k1_pos]; linarith
    have h_q_inv_nn : 0 ≤ 1 / (q : Rat)^(4*k+1) :=
      div_nonneg (by norm_num) h_q_4k1_pos.le
    nlinarith
  -- Lower bound on b: b ≥ 0. Cross-multiplication approach.
  -- Want: 1/(q^(4k+1)·(4k+1)) ≥ 1/(q^(4k+3)·(4k+3))
  -- ⟺ q^(4k+3)·(4k+3) ≥ q^(4k+1)·(4k+1)
  -- ⟺ q^(4k+1)·q²·(4k+3) ≥ q^(4k+1)·(4k+1)
  -- ⟺ q²·(4k+3) ≥ 4k+1  [dividing by q^(4k+1) > 0]
  -- True since q ≥ 1 gives q² ≥ 1, so q²·(4k+3) ≥ 4k+3 > 4k+1.
  have h_b_lower :
      0 ≤ 1 / (q : Rat)^(4*k+1) * (1 / ((4*k+1 : Nat) : Rat))
          - 1 / (q : Rat)^(4*k+3) * (1 / ((4*k+3 : Nat) : Rat)) := by
    have h_q_sq_ge_one : (1 : Rat) ≤ (q : Rat)^2 := by
      have h_q_ge_one : (1 : Rat) ≤ (q : Rat) := by
        have : (1 : Nat) ≤ q := hq
        exact_mod_cast this
      nlinarith
    have h_pow_succ : (q : Rat)^(4*k+3) = (q : Rat)^(4*k+1) * (q : Rat)^2 := by
      rw [show 4*k+3 = (4*k+1) + 2 from by ring, pow_add]
    -- Simplify both sides to common form.
    have h_lhs_eq :
        1 / (q : Rat)^(4*k+1) * (1 / ((4*k+1 : Nat) : Rat))
          = 1 / ((q : Rat)^(4*k+1) * ((4*k+1 : Nat) : Rat)) := by
      field_simp
    have h_rhs_eq :
        1 / (q : Rat)^(4*k+3) * (1 / ((4*k+3 : Nat) : Rat))
          = 1 / ((q : Rat)^(4*k+3) * ((4*k+3 : Nat) : Rat)) := by
      field_simp
    rw [h_lhs_eq, h_rhs_eq]
    -- Now: 1/((q^(4k+1))(4k+1)) - 1/((q^(4k+3))(4k+3)) ≥ 0.
    have h_denom_lhs_pos :
        (0 : Rat) < (q : Rat)^(4*k+1) * ((4*k+1 : Nat) : Rat) := mul_pos h_q_4k1_pos h_4k1_pos
    have h_denom_rhs_pos :
        (0 : Rat) < (q : Rat)^(4*k+3) * ((4*k+3 : Nat) : Rat) := mul_pos h_q_4k3_pos h_4k3_pos
    rw [sub_nonneg, div_le_div_iff₀ h_denom_rhs_pos h_denom_lhs_pos]
    -- Goal: 1 · (q^(4k+1)·(4k+1)) ≤ 1 · (q^(4k+3)·(4k+3))
    -- ⟺ q^(4k+1)·(4k+1) ≤ q^(4k+3)·(4k+3)
    rw [h_pow_succ]
    -- Goal becomes: 1 · (q^(4k+1)·(4k+1)) ≤ 1 · (q^(4k+1)·q²·(4k+3))
    -- Intermediate fact: (4k+1) ≤ q²·(4k+3).
    have h_intermediate : ((4*k+1 : Nat) : Rat) ≤ (q : Rat)^2 * ((4*k+3 : Nat) : Rat) := by
      have h_4k1_le_4k3 : ((4*k+1 : Nat) : Rat) ≤ ((4*k+3 : Nat) : Rat) := by
        have : (4*k+1 : Nat) ≤ 4*k+3 := by omega
        exact_mod_cast this
      have h_4k3_nn : (0 : Rat) ≤ ((4*k+3 : Nat) : Rat) := h_4k3_pos.le
      calc ((4*k+1 : Nat) : Rat)
          ≤ ((4*k+3 : Nat) : Rat) := h_4k1_le_4k3
        _ = 1 * ((4*k+3 : Nat) : Rat) := by ring
        _ ≤ (q : Rat)^2 * ((4*k+3 : Nat) : Rat) :=
            mul_le_mul_of_nonneg_right h_q_sq_ge_one h_4k3_nn
    -- Multiply the intermediate by q^(4k+1) ≥ 0.
    have h_q_pow_nn : (0 : Rat) ≤ (q : Rat)^(4*k+1) := h_q_4k1_pos.le
    have h_mul : (q : Rat)^(4*k+1) * ((4*k+1 : Nat) : Rat)
                  ≤ (q : Rat)^(4*k+1) * ((q : Rat)^2 * ((4*k+3 : Nat) : Rat)) :=
      mul_le_mul_of_nonneg_left h_intermediate h_q_pow_nn
    linarith
  -- |b| ≤ first term (since 0 ≤ b ≤ first term).
  have h_b_abs :
      |1 / (q : Rat)^(4*k+1) * (1 / ((4*k+1 : Nat) : Rat))
        - 1 / (q : Rat)^(4*k+3) * (1 / ((4*k+3 : Nat) : Rat))|
        ≤ 1 / (q : Rat)^(4*k+1) := by
    rw [abs_of_nonneg h_b_lower]
    linarith [h_term_3_pos]
  -- Final bound: |b| ≤ 1/q^(4k+1) ≤ 2/q^(4k+1).
  have h_one_le_two_over_q : 1 / (q : Rat)^(4*k+1) ≤ 2 / (q : Rat)^(4*k+1) := by
    have h_inv_pos : 0 < 1 / (q : Rat)^(4*k+1) := div_pos (by norm_num) h_q_4k1_pos
    rw [div_le_div_iff₀ h_q_4k1_pos h_q_4k1_pos]
    nlinarith
  linarith

-- ============================================================
-- PART 6: NUMERICAL CHECKPOINT (Wave Γ₇ Strategy G)
-- ============================================================

/-! ## Wave Γ₇ Numerical Certificate

Per the Wave Γ₇ Phase 3 strategic plan
(`atlas/planning/wave-gamma-7-phase-3-strategy.md`), we land a
numerical certificate as defensive evidence **before** attempting
the M3 breakthrough (the tan-addition formula via i-structure
decomposition).

The certificate: Machin's formula applied at finite partial-sum
depth K=3 lies within `1/15` of the Leibniz partial sum at depth
M=10. This validates that:

1. The arctan(1/q) infrastructure (Phase 1A) is correctly
   capturing the Machin chain values.
2. The Machin formula `π = 16·arctan(1/5) − 4·arctan(1/239)`
   evaluates numerically to the same value as Leibniz π
   (verified at modest precision via `native_decide`).
3. The pi_machin and pi_leibniz approximation sequences are
   getting closer with K, M (~0.05 at K=3,M=10 vs full π
   agreement at K, M → ∞).

This is **not a proof of `pi_machin.equiv pi_leibniz`** — that
remains the Phase 3F target. It's empirical evidence at finite
precision that the chain numerically does what it should.
-/

/-- Machin's formula partial sum at the Rat level:
    `16 · arctan_partial(1/5, K) − 4 · arctan_partial(1/239, K)`.

    Converges to `π = 16·arctan(1/5) − 4·arctan(1/239)` exponentially.
    Reference convergence: K=42 gives 50-digit precision; K=3 already
    gives ~3 digits of π. -/
def pi_machin_partial_rat (K : Nat) : Rat :=
  16 * arctan_reciprocal_partial_rat 5 K - 4 * arctan_reciprocal_partial_rat 239 K

/-- **Numerical certificate (Wave Γ₇ Strategy G — intermediate checkpoint)**:
    at K=3, M=10, the Machin and Leibniz partial sums agree within `1/15`.

    Empirically (verified by `native_decide` at the bytecode level):
    * `pi_machin_partial_rat 3 ≈ 3.1416 - δ` for small δ
    * `(pi_partial 10).toRat ≈ 3.0916` (Leibniz error ~0.05)
    * Difference ≈ `0.0500`, comfortably within `1/15 ≈ 0.0667`.

    This is a finite-precision evidence checkpoint, not a proof of
    Cauchy equivalence. It precedes (and motivates) the Phase 3C M3
    breakthrough that would establish the full
    `pi_machin.equiv pi_leibniz`. -/
theorem pi_machin_close_to_pi_leibniz_K3M10 :
    |pi_machin_partial_rat 3 - (TauRat.pi_partial 10).toRat| < 1 / 15 := by
  native_decide

/-- **Tighter numerical certificate** at K=5, M=50: agreement within
    `1/80`. The K=5 Machin partial already has 8+ digits of π; the
    M=50 Leibniz partial is at error ~0.01. -/
theorem pi_machin_close_to_pi_leibniz_K5M50 :
    |pi_machin_partial_rat 5 - (TauRat.pi_partial 50).toRat| < 1 / 80 := by
  native_decide

end Tau.Boundary
