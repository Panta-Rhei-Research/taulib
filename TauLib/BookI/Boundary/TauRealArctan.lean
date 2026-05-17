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

-- ============================================================
-- PART 7: GEOMETRIC PER-TERM BOUND (q ≥ 2)
-- ============================================================

/-- **Geometric per-term bound** for `q ≥ 2`: each arctan(1/q) paired term
    is bounded by `2/2^k` in absolute value.

    Derived from `arctan_reciprocal_pair_term_rat_abs_bound (|.| ≤ 2/q^(4k+1))`
    plus `q^(4k+1) ≥ 2^k` for `q ≥ 2`, since `4k+1 ≥ k` for all k. -/
theorem arctan_reciprocal_pair_term_rat_abs_bound_geom
    (q k : Nat) (hq : 2 ≤ q) :
    |arctan_reciprocal_pair_term_rat q k| ≤ 2 / (2 : Rat)^k := by
  have hq1 : 1 ≤ q := by omega
  have h_orig := arctan_reciprocal_pair_term_rat_abs_bound q k hq1
  -- |pair_k| ≤ 2/q^(4k+1) ≤ 2/2^k
  have h_q_ge_2 : (2 : Rat) ≤ (q : Rat) := by exact_mod_cast hq
  have h_q_pow_ge : (2 : Rat)^(4*k+1) ≤ (q : Rat)^(4*k+1) :=
    pow_le_pow_left₀ (by norm_num : (0 : Rat) ≤ 2) h_q_ge_2 _
  have h_2_pow_4k1_ge_k : (2 : Rat)^k ≤ (2 : Rat)^(4*k+1) := by
    apply pow_le_pow_right₀ (by norm_num : (1 : Rat) ≤ 2)
    omega
  have h_q_pow_pos : (0 : Rat) < (q : Rat)^(4*k+1) := by
    apply pow_pos
    have : (0 : Nat) < q := by omega
    exact_mod_cast this
  have h_2_pow_k_pos : (0 : Rat) < (2 : Rat)^k := by positivity
  have h_2_div_q_pow_le : (2 : Rat) / (q : Rat)^(4*k+1) ≤ 2 / (2 : Rat)^k := by
    rw [div_le_div_iff₀ h_q_pow_pos h_2_pow_k_pos]
    have h_chain : (2 : Rat)^k ≤ (q : Rat)^(4*k+1) :=
      le_trans h_2_pow_4k1_ge_k h_q_pow_ge
    nlinarith
  linarith

-- ============================================================
-- PART 8: CAUCHY TAIL BOUND (q ≥ 2)
-- ============================================================

/-- **Exact Cauchy tail bound** for arctan(1/q) with `q ≥ 2`:
    `|partial m − partial n| ≤ 4/2^n − 4/2^m` for `n ≤ m`.

    Proof: telescoping inductive bound using the geometric per-term bound.
    Mirrors `cos_partial_rat_cauchy_bound_exact` template. -/
theorem arctan_reciprocal_partial_rat_cauchy_bound_exact
    (q : Nat) (hq : 2 ≤ q) (m n : Nat) (hnm : n ≤ m) :
    |arctan_reciprocal_partial_rat q m - arctan_reciprocal_partial_rat q n|
      ≤ 4 / (2 : Rat)^n - 4 / (2 : Rat)^m := by
  induction m, hnm using Nat.le_induction with
  | base => simp
  | succ m hnm ih =>
    rw [arctan_reciprocal_partial_rat_succ]
    have h_diff : arctan_reciprocal_partial_rat q m + arctan_reciprocal_pair_term_rat q m
                  - arctan_reciprocal_partial_rat q n
                  = (arctan_reciprocal_partial_rat q m - arctan_reciprocal_partial_rat q n)
                    + arctan_reciprocal_pair_term_rat q m := by ring
    rw [h_diff]
    have h_tri : |(arctan_reciprocal_partial_rat q m - arctan_reciprocal_partial_rat q n)
                  + arctan_reciprocal_pair_term_rat q m|
                  ≤ |arctan_reciprocal_partial_rat q m - arctan_reciprocal_partial_rat q n|
                    + |arctan_reciprocal_pair_term_rat q m| := abs_add_le _ _
    have h_term := arctan_reciprocal_pair_term_rat_abs_bound_geom q m hq
    have h_2_m_pos : (0 : Rat) < (2 : Rat)^m := by positivity
    have h_pow_succ : (2 : Rat)^(m+1) = 2 * (2 : Rat)^m := by rw [pow_succ]; ring
    have h_algebra :
        4 / (2 : Rat)^n - 4 / (2 : Rat)^m + 2 / (2 : Rat)^m
          = 4 / (2 : Rat)^n - 4 / (2 : Rat)^(m+1) := by
      rw [h_pow_succ]
      have h_2_n_pos : (0 : Rat) < (2 : Rat)^n := by positivity
      field_simp; ring
    linarith

/-- **Loose Cauchy tail bound** for arctan(1/q): `≤ 4/2^n` (drops the
    subtractive 4/2^m term). Matches the standard Cauchy-bound template. -/
theorem arctan_reciprocal_partial_rat_cauchy_bound
    (q : Nat) (hq : 2 ≤ q) (m n : Nat) (hnm : n ≤ m) :
    |arctan_reciprocal_partial_rat q m - arctan_reciprocal_partial_rat q n|
      ≤ 4 / (2 : Rat)^n := by
  have h_exact := arctan_reciprocal_partial_rat_cauchy_bound_exact q hq m n hnm
  have h_subtract_nn : (0 : Rat) ≤ 4 / (2 : Rat)^m := by
    apply div_nonneg (by norm_num : (0 : Rat) ≤ 4)
    positivity
  linarith

-- ============================================================
-- PART 9: TauReal.arctan_reciprocal AND IsCauchy
-- ============================================================

/-- **[I.D-Arctan-Reciprocal]** `TauReal.arctan_reciprocal q hq` — the
    τ-native arctan(1/q) as a TauReal, for `q ≥ 2`. -/
def TauReal.arctan_reciprocal (q : Nat) (hq : 2 ≤ q) : TauReal :=
  ⟨TauRat.arctan_reciprocal_partial q (by omega : 1 ≤ q)⟩

@[simp] theorem TauReal.arctan_reciprocal_approx (q : Nat) (hq : 2 ≤ q) (n : Nat) :
    (TauReal.arctan_reciprocal q hq).approx n =
      TauRat.arctan_reciprocal_partial q (by omega : 1 ≤ q) n := rfl

/-- **[I.T-Arctan-Reciprocal-IsCauchy]** `TauReal.arctan_reciprocal q hq` is
    Cauchy with explicit modulus `λ k => k + 3`, mirroring the cos/sin/π
    Cauchy template. -/
theorem TauReal.arctan_reciprocal_isCauchy (q : Nat) (hq : 2 ≤ q) :
    (TauReal.arctan_reciprocal q hq).IsCauchy := by
  refine ⟨fun k => k + 3, ?_⟩
  intro k m n hm hn
  change k + 3 ≤ m at hm
  change k + 3 ≤ n at hn
  unfold TauRat.lt
  rw [TauRat.toRat_abs, toRat_sub, TauRat.ofNatRecip_toRat]
  show |((TauRat.arctan_reciprocal_partial q (by omega : 1 ≤ q) m).toRat
          - (TauRat.arctan_reciprocal_partial q (by omega : 1 ≤ q) n).toRat)|
         < 1 / ((k : Rat) + 1)
  rw [TauRat.arctan_reciprocal_partial_toRat, TauRat.arctan_reciprocal_partial_toRat]
  by_cases h_le : n ≤ m
  · have h_bound := arctan_reciprocal_partial_rat_cauchy_bound q hq m n h_le
    have h_four_lt := Rat.four_div_two_pow_lt_recip k n hn
    linarith
  · push_neg at h_le
    have h_m_le_n : m ≤ n := Nat.le_of_lt h_le
    have h_swap_abs :
        |arctan_reciprocal_partial_rat q m - arctan_reciprocal_partial_rat q n|
          = |arctan_reciprocal_partial_rat q n - arctan_reciprocal_partial_rat q m| := by
      rw [show arctan_reciprocal_partial_rat q m - arctan_reciprocal_partial_rat q n
            = -(arctan_reciprocal_partial_rat q n - arctan_reciprocal_partial_rat q m) from by ring,
          abs_neg]
    rw [h_swap_abs]
    have h_bound := arctan_reciprocal_partial_rat_cauchy_bound q hq n m h_m_le_n
    have h_four_lt := Rat.four_div_two_pow_lt_recip k m hm
    linarith

-- ============================================================
-- PART 10: TauReal.pi_machin AND IsCauchy
-- ============================================================

/-- **Constants are Cauchy**: `(TauReal.fromTauRat q).IsCauchy` for any `q`.
    The approximation sequence is constant at `q`, so all differences are 0. -/
theorem TauReal.IsCauchy_fromTauRat (q : TauRat) :
    (TauReal.fromTauRat q).IsCauchy := by
  refine ⟨fun _ => 0, fun k _ _ _ _ => ?_⟩
  unfold TauRat.lt
  rw [TauRat.toRat_abs, toRat_sub, TauRat.ofNatRecip_toRat]
  show |q.toRat - q.toRat| < 1 / ((k : Rat) + 1)
  rw [sub_self, abs_zero]
  have h_pos : (0 : Rat) < (k : Rat) + 1 := by
    have : (0 : Rat) ≤ (k : Rat) := by exact_mod_cast Nat.zero_le k
    linarith
  positivity

/-- **Nat embeddings are Cauchy**: `(TauReal.fromNat n).IsCauchy`. -/
theorem TauReal.IsCauchy_fromNat (n : Nat) : (TauReal.fromNat n).IsCauchy :=
  TauReal.IsCauchy_fromTauRat _

/-- **[I.D-Pi-Machin]** Machin's formula at TauReal level:
    `pi_machin = 16 · arctan(1/5) − 4 · arctan(1/239)`.

    The classical identity `π/4 = 4·arctan(1/5) − arctan(1/239)` rearranges
    to `π = 16·arctan(1/5) − 4·arctan(1/239)`, the form we encode. -/
def TauReal.pi_machin : TauReal :=
  ((TauReal.fromNat 16).mul (TauReal.arctan_reciprocal 5 (by norm_num))).sub
    ((TauReal.fromNat 4).mul (TauReal.arctan_reciprocal 239 (by norm_num)))

/-- **[I.T-Pi-Machin-IsCauchy]** `TauReal.pi_machin.IsCauchy` — derived
    compositionally from each `arctan_reciprocal` being Cauchy plus the
    standard TauReal arithmetic lift lemmas (`IsCauchy_add`, `IsCauchy_mul`,
    `IsCauchy_negate`, `IsCauchy_fromNat`). -/
theorem TauReal.pi_machin_isCauchy : TauReal.pi_machin.IsCauchy := by
  show (((TauReal.fromNat 16).mul (TauReal.arctan_reciprocal 5 (by norm_num))).sub
        ((TauReal.fromNat 4).mul (TauReal.arctan_reciprocal 239 (by norm_num)))).IsCauchy
  unfold TauReal.sub
  apply TauReal.IsCauchy_add
  · -- (fromNat 16).mul (arctan_reciprocal 5) IsCauchy
    apply TauReal.IsCauchy_mul
    · exact TauReal.IsCauchy_fromNat 16
    · exact TauReal.arctan_reciprocal_isCauchy 5 (by norm_num)
  · -- ((fromNat 4).mul (arctan_reciprocal 239)).negate IsCauchy
    apply TauReal.IsCauchy_negate
    apply TauReal.IsCauchy_mul
    · exact TauReal.IsCauchy_fromNat 4
    · exact TauReal.arctan_reciprocal_isCauchy 239 (by norm_num)

-- ============================================================
-- PART 11: GENERALIZED arctan_of_rat (for general |x.toRat| ≤ 1/2)
-- ============================================================

/-! ## Phase 2.6.A — Generalized arctan_of_rat

The `arctan_reciprocal q hq` infrastructure handles `arctan(1/q)` for
`q ≥ 2 : Nat`. For Machin's identity, intermediate values arise via the
arctan addition formula:

  arctan(1/5) + arctan(1/5) = arctan(5/12)   (5/12 ≈ 0.417 < 1/2)
  arctan(5/12) + arctan(5/12) = arctan(120/119)   (> 1, queued for later)

This part generalizes to `TauReal.arctan_of_rat (x : TauRat) (hx : |x.toRat| · 2 ≤ 1) :
TauReal`, handling any rational argument with `|x| ≤ 1/2`. -/

/-- Helper: divide a TauRat by a positive Nat. Constructs `q/n` by
    multiplying the denominator. -/
def TauRat.div_pos_nat (q : TauRat) (n : Nat) (hn : 0 < n) : TauRat :=
  ⟨q.num, q.den * n, Nat.mul_pos q.den_pos hn⟩

theorem TauRat.div_pos_nat_toRat (q : TauRat) (n : Nat) (hn : 0 < n) :
    (TauRat.div_pos_nat q n hn).toRat = q.toRat / (n : Rat) := by
  unfold TauRat.div_pos_nat TauRat.toRat
  have h_q_den_pos : (0 : Rat) < (q.den : Rat) := by exact_mod_cast q.den_pos
  have h_n_pos : (0 : Rat) < (n : Rat) := by exact_mod_cast hn
  push_cast
  field_simp

/-- **General arctan paired term** at TauRat level (signed):
    `pair_term x k = x^(4k+1)/(4k+1) - x^(4k+3)/(4k+3)`. -/
def TauRat.arctan_pair_term (x : TauRat) (k : Nat) : TauRat :=
  (TauRat.div_pos_nat (TauRat.pow x (4*k+1)) (4*k+1) (by omega)).sub
    (TauRat.div_pos_nat (TauRat.pow x (4*k+3)) (4*k+3) (by omega))

/-- Rat-level companion. -/
def arctan_pair_term_rat (x : Rat) (k : Nat) : Rat :=
  x^(4*k+1)/(4*k+1) - x^(4*k+3)/(4*k+3)

/-- Bridge: TauRat construction = Rat companion under `.toRat`. -/
theorem TauRat.arctan_pair_term_toRat (x : TauRat) (k : Nat) :
    (TauRat.arctan_pair_term x k).toRat = arctan_pair_term_rat x.toRat k := by
  unfold TauRat.arctan_pair_term arctan_pair_term_rat
  rw [toRat_sub, TauRat.div_pos_nat_toRat, TauRat.div_pos_nat_toRat,
      TauRat.pow_toRat, TauRat.pow_toRat]
  push_cast
  ring

/-- **General arctan partial sum** at TauRat level. -/
def TauRat.arctan_partial (x : TauRat) (n : Nat) : TauRat :=
  TauRat.sum (fun k => TauRat.arctan_pair_term x k) n

@[simp] theorem TauRat.arctan_partial_zero (x : TauRat) :
    TauRat.arctan_partial x 0 = TauRat.zero := rfl

@[simp] theorem TauRat.arctan_partial_succ (x : TauRat) (n : Nat) :
    TauRat.arctan_partial x (n + 1) =
      (TauRat.arctan_partial x n).add (TauRat.arctan_pair_term x n) := rfl

/-- Rat-level companion partial sum. -/
def arctan_partial_rat (x : Rat) : Nat → Rat
  | 0 => 0
  | n + 1 => arctan_partial_rat x n + arctan_pair_term_rat x n

@[simp] theorem arctan_partial_rat_zero (x : Rat) : arctan_partial_rat x 0 = 0 := rfl

@[simp] theorem arctan_partial_rat_succ (x : Rat) (n : Nat) :
    arctan_partial_rat x (n + 1) = arctan_partial_rat x n + arctan_pair_term_rat x n := rfl

/-- Bridge for partial sums. -/
theorem TauRat.arctan_partial_toRat (x : TauRat) (n : Nat) :
    (TauRat.arctan_partial x n).toRat = arctan_partial_rat x.toRat n := by
  induction n with
  | zero =>
    simp [TauRat.arctan_partial_zero, arctan_partial_rat_zero, toRat_zero]
  | succ n ih =>
    rw [TauRat.arctan_partial_succ, toRat_add, ih, TauRat.arctan_pair_term_toRat,
        arctan_partial_rat_succ]

-- ============================================================
-- PART 12: PER-TERM BOUND for general arctan (|x| ≤ 1/2)
-- ============================================================

/-- **Geometric per-term bound**: for `|x| ≤ 1/2`,
    `|arctan_pair_term_rat x k| ≤ 2/2^k`.

    Proof: `|x^(4k+1)/(4k+1)| ≤ |x|^(4k+1) ≤ (1/2)^(4k+1) ≤ (1/2)^k`,
    and similarly for the second sub-term. Triangle inequality: sum ≤ 2/2^k. -/
theorem arctan_pair_term_rat_abs_bound_geom (x : Rat) (hx : 2 * |x| ≤ 1) (k : Nat) :
    |arctan_pair_term_rat x k| ≤ 2 / (2 : Rat)^k := by
  unfold arctan_pair_term_rat
  -- |x^(4k+1)/(4k+1)| ≤ |x|^(4k+1) and similarly for second term
  have h_abs_x_le_half : |x| ≤ 1/2 := by linarith
  have h_abs_x_nn : (0 : Rat) ≤ |x| := abs_nonneg _
  have h_4k1_pos : (0 : Rat) < ((4*k+1 : Nat) : Rat) := by
    have : 0 < 4*k+1 := by omega
    exact_mod_cast this
  have h_4k3_pos : (0 : Rat) < ((4*k+3 : Nat) : Rat) := by
    have : 0 < 4*k+3 := by omega
    exact_mod_cast this
  have h_4k1_ge_1 : (1 : Rat) ≤ ((4*k+1 : Nat) : Rat) := by
    have : 1 ≤ 4*k+1 := by omega
    exact_mod_cast this
  have h_4k3_ge_1 : (1 : Rat) ≤ ((4*k+3 : Nat) : Rat) := by
    have : 1 ≤ 4*k+3 := by omega
    exact_mod_cast this
  have h_2_pow_k_pos : (0 : Rat) < (2 : Rat)^k := by positivity
  -- |x^(4k+1)| ≤ (1/2)^(4k+1) ≤ 1/2^(k+1) ≤ 1/2^k
  have h_x_pow_le : |x|^(4*k+1) ≤ (1 : Rat) / (2 : Rat)^(k+1) := by
    calc |x|^(4*k+1)
        ≤ (1/2 : Rat)^(4*k+1) := pow_le_pow_left₀ h_abs_x_nn h_abs_x_le_half _
      _ = 1 / (2 : Rat)^(4*k+1) := by rw [div_pow, one_pow]
      _ ≤ 1 / (2 : Rat)^(k+1) := by
          apply one_div_le_one_div_of_le
          · positivity
          · apply pow_le_pow_right₀ (by norm_num : (1 : Rat) ≤ 2); omega
  have h_x_pow_3_le : |x|^(4*k+3) ≤ (1 : Rat) / (2 : Rat)^(k+1) := by
    calc |x|^(4*k+3)
        ≤ (1/2 : Rat)^(4*k+3) := pow_le_pow_left₀ h_abs_x_nn h_abs_x_le_half _
      _ = 1 / (2 : Rat)^(4*k+3) := by rw [div_pow, one_pow]
      _ ≤ 1 / (2 : Rat)^(k+1) := by
          apply one_div_le_one_div_of_le
          · positivity
          · apply pow_le_pow_right₀ (by norm_num : (1 : Rat) ≤ 2); omega
  -- |x^(4k+1)/(4k+1)| ≤ |x|^(4k+1) (since (4k+1) ≥ 1)
  have h_first_abs : |x^(4*k+1) / ((4*k+1 : Nat) : Rat)|
                      ≤ 1 / (2 : Rat)^(k+1) := by
    rw [abs_div]
    rw [show |((4*k+1 : Nat) : Rat)| = ((4*k+1 : Nat) : Rat) from abs_of_pos h_4k1_pos]
    calc |x^(4*k+1)| / ((4*k+1 : Nat) : Rat)
        ≤ |x^(4*k+1)| / 1 := by
          apply div_le_div_of_nonneg_left (abs_nonneg _) (by norm_num : (0:Rat) < 1) h_4k1_ge_1
      _ = |x^(4*k+1)| := by ring
      _ = |x|^(4*k+1) := abs_pow x (4*k+1)
      _ ≤ 1 / (2 : Rat)^(k+1) := h_x_pow_le
  have h_second_abs : |x^(4*k+3) / ((4*k+3 : Nat) : Rat)|
                       ≤ 1 / (2 : Rat)^(k+1) := by
    rw [abs_div]
    rw [show |((4*k+3 : Nat) : Rat)| = ((4*k+3 : Nat) : Rat) from abs_of_pos h_4k3_pos]
    calc |x^(4*k+3)| / ((4*k+3 : Nat) : Rat)
        ≤ |x^(4*k+3)| / 1 := by
          apply div_le_div_of_nonneg_left (abs_nonneg _) (by norm_num : (0:Rat) < 1) h_4k3_ge_1
      _ = |x^(4*k+3)| := by ring
      _ = |x|^(4*k+3) := abs_pow x (4*k+3)
      _ ≤ 1 / (2 : Rat)^(k+1) := h_x_pow_3_le
  -- Triangle: |sum| ≤ |first| + |second| ≤ 2/2^(k+1) = 1/2^k ≤ 2/2^k
  have h_tri : |x^(4*k+1) / ((4*k+1 : Nat) : Rat) - x^(4*k+3) / ((4*k+3 : Nat) : Rat)|
              ≤ |x^(4*k+1) / ((4*k+1 : Nat) : Rat)| + |x^(4*k+3) / ((4*k+3 : Nat) : Rat)| := by
    have := abs_sub (x^(4*k+1) / ((4*k+1 : Nat) : Rat)) (x^(4*k+3) / ((4*k+3 : Nat) : Rat))
    exact this
  have h_sum_le : (1 : Rat) / (2 : Rat)^(k+1) + 1 / (2 : Rat)^(k+1) = 1 / (2 : Rat)^k := by
    have h_pow_succ : (2 : Rat)^(k+1) = 2 * (2 : Rat)^k := by rw [pow_succ]; ring
    rw [h_pow_succ]
    field_simp
    ring
  have h_one_le_two : (1 : Rat) / (2 : Rat)^k ≤ 2 / (2 : Rat)^k := by
    rw [div_le_div_iff₀ h_2_pow_k_pos h_2_pow_k_pos]
    nlinarith
  have h_step : |x^(4*k+1) / ((4*k+1 : Nat) : Rat) - x^(4*k+3) / ((4*k+3 : Nat) : Rat)|
              ≤ 1 / (2 : Rat)^(k+1) + 1 / (2 : Rat)^(k+1) := by linarith
  push_cast at h_step
  linarith

-- ============================================================
-- PART 13: CAUCHY TAIL BOUND for general arctan (|x| ≤ 1/2)
-- ============================================================

/-- **Cauchy tail bound for general arctan**: for `|x| ≤ 1/2`,
    `|arctan_partial_rat x m − arctan_partial_rat x n| ≤ 4/2^n − 4/2^m`
    for `n ≤ m`. Telescoping inductive proof. -/
theorem arctan_partial_rat_cauchy_bound_exact
    (x : Rat) (hx : 2 * |x| ≤ 1) (m n : Nat) (hnm : n ≤ m) :
    |arctan_partial_rat x m - arctan_partial_rat x n|
      ≤ 4 / (2 : Rat)^n - 4 / (2 : Rat)^m := by
  induction m, hnm using Nat.le_induction with
  | base => simp
  | succ m hnm ih =>
    rw [arctan_partial_rat_succ]
    have h_diff : arctan_partial_rat x m + arctan_pair_term_rat x m - arctan_partial_rat x n
                  = (arctan_partial_rat x m - arctan_partial_rat x n)
                    + arctan_pair_term_rat x m := by ring
    rw [h_diff]
    have h_tri : |(arctan_partial_rat x m - arctan_partial_rat x n) + arctan_pair_term_rat x m|
                  ≤ |arctan_partial_rat x m - arctan_partial_rat x n|
                    + |arctan_pair_term_rat x m| := abs_add_le _ _
    have h_term := arctan_pair_term_rat_abs_bound_geom x hx m
    have h_2_m_pos : (0 : Rat) < (2 : Rat)^m := by positivity
    have h_pow_succ : (2 : Rat)^(m+1) = 2 * (2 : Rat)^m := by rw [pow_succ]; ring
    have h_algebra :
        4 / (2 : Rat)^n - 4 / (2 : Rat)^m + 2 / (2 : Rat)^m
          = 4 / (2 : Rat)^n - 4 / (2 : Rat)^(m+1) := by
      rw [h_pow_succ]
      have h_2_n_pos : (0 : Rat) < (2 : Rat)^n := by positivity
      field_simp; ring
    linarith

/-- **Loose Cauchy tail bound** for general arctan: drop the subtractive term. -/
theorem arctan_partial_rat_cauchy_bound
    (x : Rat) (hx : 2 * |x| ≤ 1) (m n : Nat) (hnm : n ≤ m) :
    |arctan_partial_rat x m - arctan_partial_rat x n| ≤ 4 / (2 : Rat)^n := by
  have h_exact := arctan_partial_rat_cauchy_bound_exact x hx m n hnm
  have h_subtract_nn : (0 : Rat) ≤ 4 / (2 : Rat)^m := by
    apply div_nonneg (by norm_num : (0 : Rat) ≤ 4)
    positivity
  linarith

-- ============================================================
-- PART 14: TauReal.arctan_of_rat AND IsCauchy
-- ============================================================

/-- **[I.D-Arctan-General]** General τ-native `arctan(x)` as a TauReal, for
    any `x : TauRat` with `|x.toRat| ≤ 1/2`. -/
def TauReal.arctan_of_rat (x : TauRat) (_ : 2 * |x.toRat| ≤ 1) : TauReal :=
  ⟨TauRat.arctan_partial x⟩

@[simp] theorem TauReal.arctan_of_rat_approx (x : TauRat) (hx : 2 * |x.toRat| ≤ 1) (n : Nat) :
    (TauReal.arctan_of_rat x hx).approx n = TauRat.arctan_partial x n := rfl

/-- **[I.T-Arctan-General-IsCauchy]** General `arctan_of_rat` is Cauchy with
    modulus `λ k => k + 3` for `|x.toRat| ≤ 1/2`. -/
theorem TauReal.arctan_of_rat_isCauchy (x : TauRat) (hx : 2 * |x.toRat| ≤ 1) :
    (TauReal.arctan_of_rat x hx).IsCauchy := by
  refine ⟨fun k => k + 3, ?_⟩
  intro k m n hm hn
  change k + 3 ≤ m at hm
  change k + 3 ≤ n at hn
  unfold TauRat.lt
  rw [TauRat.toRat_abs, toRat_sub, TauRat.ofNatRecip_toRat]
  show |((TauRat.arctan_partial x m).toRat - (TauRat.arctan_partial x n).toRat)|
         < 1 / ((k : Rat) + 1)
  rw [TauRat.arctan_partial_toRat, TauRat.arctan_partial_toRat]
  by_cases h_le : n ≤ m
  · have h_bound := arctan_partial_rat_cauchy_bound x.toRat hx m n h_le
    have h_four_lt := Rat.four_div_two_pow_lt_recip k n hn
    linarith
  · push_neg at h_le
    have h_m_le_n : m ≤ n := Nat.le_of_lt h_le
    have h_swap_abs :
        |arctan_partial_rat x.toRat m - arctan_partial_rat x.toRat n|
          = |arctan_partial_rat x.toRat n - arctan_partial_rat x.toRat m| := by
      rw [show arctan_partial_rat x.toRat m - arctan_partial_rat x.toRat n
            = -(arctan_partial_rat x.toRat n - arctan_partial_rat x.toRat m) from by ring,
          abs_neg]
    rw [h_swap_abs]
    have h_bound := arctan_partial_rat_cauchy_bound x.toRat hx n m h_m_le_n
    have h_four_lt := Rat.four_div_two_pow_lt_recip k m hm
    linarith

-- ============================================================
-- PART 15: Phase 2.6.B.2.β.4 starter — arctan_of_rat bounded ≤ 1
-- ============================================================

/-! ## Phase 2.6.B.2.β.4 starter — arctan_of_rat boundedness for |a| ≤ 1/2

For `|a.toRat| ≤ 1/2`, every approximation of `arctan_of_rat a` is bounded
in absolute value by 1. This unlocks applying `cisTauReal_add` (β.3 full)
to arctan-image angles, the structural prerequisite for arctan addition.

**Proof skeleton**:
1. **Tighter per-term bound**: `|arctan_pair_term_rat a k| ≤ (5/4)·|a|^(4k+1)` for `|a| ≤ 1/2`.
   Via triangle on the two sub-fractions + `1+|a|² ≤ 5/4`.
2. **Geometric sum**: by induction, `(1-|a|⁴)·|arctan_partial a n| ≤ (5/4)·|a|·(1-|a|^(4n))`.
3. **Conclude**: `|arctan_partial a n| ≤ (5/4)·|a|/(1-|a|⁴) ≤ 2/3 < 1` for `|a| ≤ 1/2`. -/

/-- **Tighter per-term bound** for `|a| ≤ 1/2`:
    `|arctan_pair_term_rat a k| ≤ (5/4) · |a|^(4k+1)`.

    Derived via triangle: `|p₁ - p₂| ≤ |a|^(4k+1)/(4k+1) + |a|^(4k+3)/(4k+3)`,
    then bounding by `|a|^(4k+1) · (1 + |a|²) ≤ (5/4)·|a|^(4k+1)`. -/
theorem arctan_pair_term_rat_abs_bound_tight (a : Rat) (ha : 2 * |a| ≤ 1) (k : Nat) :
    |arctan_pair_term_rat a k| ≤ (5/4) * |a|^(4*k+1) := by
  unfold arctan_pair_term_rat
  -- Setup: |a| ≤ 1/2, hence |a|² ≤ 1/4, hence 1 + |a|² ≤ 5/4
  have h_abs_a_le_half : |a| ≤ 1/2 := by linarith
  have h_abs_a_nn : (0 : Rat) ≤ |a| := abs_nonneg _
  have h_abs_a_sq : |a|^2 ≤ 1/4 := by
    have : |a|^2 ≤ (1/2)^2 := by
      apply pow_le_pow_left₀ h_abs_a_nn h_abs_a_le_half
    have : (1/2 : Rat)^2 = 1/4 := by norm_num
    linarith [pow_le_pow_left₀ h_abs_a_nn h_abs_a_le_half 2]
  have h_one_plus_sq : 1 + |a|^2 ≤ 5/4 := by linarith
  -- Denominators positive
  have h_4k1_pos : (0 : Rat) < ((4*k+1 : Nat) : Rat) := by
    have : (0 : Nat) < 4*k+1 := by omega
    exact_mod_cast this
  have h_4k3_pos : (0 : Rat) < ((4*k+3 : Nat) : Rat) := by
    have : (0 : Nat) < 4*k+3 := by omega
    exact_mod_cast this
  have h_4k1_ge_1 : (1 : Rat) ≤ ((4*k+1 : Nat) : Rat) := by
    have : 1 ≤ 4*k+1 := by omega
    exact_mod_cast this
  have h_4k3_ge_1 : (1 : Rat) ≤ ((4*k+3 : Nat) : Rat) := by
    have : 1 ≤ 4*k+3 := by omega
    exact_mod_cast this
  -- |pair_k| ≤ |a|^(4k+1)/(4k+1) + |a|^(4k+3)/(4k+3) (triangle)
  have h_tri :
      |a^(4*k+1) / ((4*k+1 : Nat) : Rat) - a^(4*k+3) / ((4*k+3 : Nat) : Rat)|
        ≤ |a|^(4*k+1) / ((4*k+1 : Nat) : Rat) + |a|^(4*k+3) / ((4*k+3 : Nat) : Rat) := by
    calc |a^(4*k+1) / ((4*k+1 : Nat) : Rat) - a^(4*k+3) / ((4*k+3 : Nat) : Rat)|
        ≤ |a^(4*k+1) / ((4*k+1 : Nat) : Rat)| + |a^(4*k+3) / ((4*k+3 : Nat) : Rat)| := abs_sub _ _
      _ = |a^(4*k+1)| / ((4*k+1 : Nat) : Rat) + |a^(4*k+3)| / ((4*k+3 : Nat) : Rat) := by
          rw [abs_div, abs_div]
          rw [abs_of_pos h_4k1_pos, abs_of_pos h_4k3_pos]
      _ = |a|^(4*k+1) / ((4*k+1 : Nat) : Rat) + |a|^(4*k+3) / ((4*k+3 : Nat) : Rat) := by
          rw [abs_pow, abs_pow]
  -- Each term: |a|^N / N' ≤ |a|^N (since N' ≥ 1)
  have h_first : |a|^(4*k+1) / ((4*k+1 : Nat) : Rat) ≤ |a|^(4*k+1) := by
    have h_pow_nn : (0 : Rat) ≤ |a|^(4*k+1) := by positivity
    calc |a|^(4*k+1) / ((4*k+1 : Nat) : Rat)
        ≤ |a|^(4*k+1) / 1 :=
          div_le_div_of_nonneg_left h_pow_nn (by norm_num : (0 : Rat) < 1) h_4k1_ge_1
      _ = |a|^(4*k+1) := by ring
  have h_second : |a|^(4*k+3) / ((4*k+3 : Nat) : Rat) ≤ |a|^(4*k+3) := by
    have h_pow_nn : (0 : Rat) ≤ |a|^(4*k+3) := by positivity
    calc |a|^(4*k+3) / ((4*k+3 : Nat) : Rat)
        ≤ |a|^(4*k+3) / 1 :=
          div_le_div_of_nonneg_left h_pow_nn (by norm_num : (0 : Rat) < 1) h_4k3_ge_1
      _ = |a|^(4*k+3) := by ring
  -- |a|^(4k+3) = |a|^(4k+1) · |a|²
  have h_pow_split : |a|^(4*k+3) = |a|^(4*k+1) * |a|^2 := by
    rw [show 4*k+3 = (4*k+1) + 2 from by ring, pow_add]
  -- Combine: |pair_k| ≤ |a|^(4k+1) + |a|^(4k+1)·|a|² = |a|^(4k+1)·(1+|a|²) ≤ (5/4)·|a|^(4k+1)
  have h_pow_4k1_nn : (0 : Rat) ≤ |a|^(4*k+1) := by positivity
  have h_combined :
      |a^(4*k+1) / ((4*k+1 : Nat) : Rat) - a^(4*k+3) / ((4*k+3 : Nat) : Rat)|
        ≤ (5/4) * |a|^(4*k+1) := by
    calc |a^(4*k+1) / ((4*k+1 : Nat) : Rat) - a^(4*k+3) / ((4*k+3 : Nat) : Rat)|
        ≤ |a|^(4*k+1) / ((4*k+1 : Nat) : Rat) + |a|^(4*k+3) / ((4*k+3 : Nat) : Rat) := h_tri
      _ ≤ |a|^(4*k+1) + |a|^(4*k+3) := by linarith
      _ = |a|^(4*k+1) + |a|^(4*k+1) * |a|^2 := by rw [h_pow_split]
      _ = |a|^(4*k+1) * (1 + |a|^2) := by ring
      _ ≤ |a|^(4*k+1) * (5/4) := by nlinarith
      _ = (5/4) * |a|^(4*k+1) := by ring
  -- Push the cast form to match the goal
  push_cast at h_combined
  exact h_combined

/-- **Step 2 — inductive bound via telescoping**:
    `(1 - |a|⁴) · |arctan_partial_rat a n| ≤ (5/4) · |a| · (1 - |a|^(4n))`
    for `|a| ≤ 1/2`, all n. -/
theorem arctan_partial_rat_abs_tight_bound (a : Rat) (ha : 2 * |a| ≤ 1) (n : Nat) :
    (1 - |a|^4) * |arctan_partial_rat a n| ≤ (5/4) * |a| * (1 - |a|^(4*n)) := by
  have h_abs_a_le_half : |a| ≤ 1/2 := by linarith
  have h_abs_a_nn : (0 : Rat) ≤ |a| := abs_nonneg _
  have h_pow4_le : |a|^4 ≤ (1/2 : Rat)^4 := pow_le_pow_left₀ h_abs_a_nn h_abs_a_le_half 4
  have h_pow4_lt_one : |a|^4 < 1 := by
    have : (1/2 : Rat)^4 = 1/16 := by norm_num
    linarith
  have h_one_minus_pow_pos : (0 : Rat) ≤ 1 - |a|^4 := by linarith
  induction n with
  | zero =>
    show (1 - |a|^4) * |arctan_partial_rat a 0| ≤ (5/4) * |a| * (1 - |a|^(4*0))
    rw [arctan_partial_rat_zero, abs_zero, mul_zero]
    simp
  | succ n IH =>
    rw [arctan_partial_rat_succ]
    have h_tri : |arctan_partial_rat a n + arctan_pair_term_rat a n|
                ≤ |arctan_partial_rat a n| + |arctan_pair_term_rat a n| := abs_add_le _ _
    have h_term : |arctan_pair_term_rat a n| ≤ (5/4) * |a|^(4*n+1) :=
      arctan_pair_term_rat_abs_bound_tight a ha n
    -- (1 - |a|⁴) · |partial(n+1)| ≤ (1 - |a|⁴) · (|partial n| + |pair n|)
    have h_step1 :
        (1 - |a|^4) * |arctan_partial_rat a n + arctan_pair_term_rat a n|
          ≤ (1 - |a|^4) * (|arctan_partial_rat a n| + |arctan_pair_term_rat a n|) := by
      exact mul_le_mul_of_nonneg_left h_tri h_one_minus_pow_pos
    -- (1 - |a|⁴) · (|partial n| + |pair n|) = (1-|a|⁴)·|partial n| + (1-|a|⁴)·|pair n|
    -- ≤ (5/4)·|a|·(1-|a|^(4n)) + (1-|a|⁴)·(5/4)·|a|^(4n+1)
    have h_pair_pow_nn : (0 : Rat) ≤ |a|^(4*n+1) := by positivity
    have h_step2 :
        (1 - |a|^4) * (|arctan_partial_rat a n| + |arctan_pair_term_rat a n|)
          ≤ (5/4) * |a| * (1 - |a|^(4*n)) + (1 - |a|^4) * ((5/4) * |a|^(4*n+1)) := by
      have h_pair_bound : (1 - |a|^4) * |arctan_pair_term_rat a n|
                        ≤ (1 - |a|^4) * ((5/4) * |a|^(4*n+1)) := by
        exact mul_le_mul_of_nonneg_left h_term h_one_minus_pow_pos
      nlinarith [IH, h_pair_bound]
    -- (5/4)·|a|·(1-|a|^(4n)) + (1-|a|⁴)·(5/4)·|a|^(4n+1) = (5/4)·|a|·(1-|a|^(4(n+1)))
    have h_step3 :
        (5/4) * |a| * (1 - |a|^(4*n)) + (1 - |a|^4) * ((5/4) * |a|^(4*n+1))
          = (5/4) * |a| * (1 - |a|^(4*(n+1))) := by
      have h_pow_4n1 : |a|^(4*n+1) = |a| * |a|^(4*n) := by
        rw [show 4*n+1 = 1 + 4*n from by ring, pow_add, pow_one]
      have h_pow_4np : |a|^(4*(n+1)) = |a|^4 * |a|^(4*n) := by
        rw [show 4*(n+1) = 4 + 4*n from by ring, pow_add]
      rw [h_pow_4n1, h_pow_4np]
      ring
    linarith

/-- **Step 3 — unscaled bound**: `|arctan_partial_rat a n| ≤ 1` for `|a| ≤ 1/2`.

    Derived from Step 2 by:
    1. `(1 - |a|^(4n)) ≤ 1` (since `|a|^(4n) ≥ 0`)
    2. `(1 - |a|⁴) ≥ 15/16 > 0` for `|a| ≤ 1/2`
    3. Combine: `|partial| ≤ (5/4)·|a| / (15/16) = (4/3)·|a| ≤ 2/3 < 1`. -/
theorem arctan_partial_rat_abs_le_one (a : Rat) (ha : 2 * |a| ≤ 1) (n : Nat) :
    |arctan_partial_rat a n| ≤ 1 := by
  have h_abs_a_le_half : |a| ≤ 1/2 := by linarith
  have h_abs_a_nn : (0 : Rat) ≤ |a| := abs_nonneg _
  have h_pow4_le : |a|^4 ≤ 1/16 := by
    have h1 : |a|^4 ≤ (1/2 : Rat)^4 := pow_le_pow_left₀ h_abs_a_nn h_abs_a_le_half 4
    have h2 : (1/2 : Rat)^4 = 1/16 := by norm_num
    linarith
  have h_one_minus_pow_pos : (0 : Rat) < 1 - |a|^4 := by linarith
  have h_pow_4n_nn : (0 : Rat) ≤ |a|^(4*n) := by positivity
  have h_one_minus_le : 1 - |a|^(4*n) ≤ 1 := by linarith
  have h_step2 := arctan_partial_rat_abs_tight_bound a ha n
  -- (1-|a|⁴)·|partial| ≤ (5/4)·|a|
  have h_unscaled : (1 - |a|^4) * |arctan_partial_rat a n| ≤ (5/4) * |a| := by
    have h_5a_nn : (0 : Rat) ≤ (5/4) * |a| := by positivity
    calc (1 - |a|^4) * |arctan_partial_rat a n|
        ≤ (5/4) * |a| * (1 - |a|^(4*n)) := h_step2
      _ ≤ (5/4) * |a| * 1 := mul_le_mul_of_nonneg_left h_one_minus_le h_5a_nn
      _ = (5/4) * |a| := by ring
  -- |partial| ≤ (5/4)·|a|/(1-|a|⁴) ≤ 2/3 < 1
  have h_partial_le_div : |arctan_partial_rat a n| ≤ (5/4) * |a| / (1 - |a|^4) := by
    rw [le_div_iff₀ h_one_minus_pow_pos]
    linarith
  have h_one_minus_ge : (1 : Rat) - |a|^4 ≥ 15/16 := by linarith
  have h_div_bound : (5/4) * |a| / (1 - |a|^4) ≤ 2/3 := by
    rw [div_le_iff₀ h_one_minus_pow_pos]
    nlinarith
  linarith

/-- **🎯 Step 4 (headline)**: every approximation of `TauReal.arctan_of_rat a hx`
    is bounded by 1 in absolute value, for `|a.toRat| ≤ 1/2`.

    This is the key prerequisite for applying `cisTauReal_add` (β.3 full) to
    `arctan_of_rat a + arctan_of_rat b` — both arctan-image angles satisfy
    the BoundedBy 1 hypothesis. -/
theorem TauReal.arctan_of_rat_approx_abs_toRat_le_one (a : TauRat)
    (hx : 2 * |a.toRat| ≤ 1) (n : Nat) :
    ((TauReal.arctan_of_rat a hx).approx n).abs.toRat ≤ 1 := by
  rw [TauReal.arctan_of_rat_approx, TauRat.toRat_abs, TauRat.arctan_partial_toRat]
  exact arctan_partial_rat_abs_le_one a.toRat hx n

end Tau.Boundary
