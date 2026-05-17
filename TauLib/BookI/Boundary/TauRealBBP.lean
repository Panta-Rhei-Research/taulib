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
# TauLib.BookI.Boundary.TauRealBBP

**Wave Γ₆ Phase 1A — τ-native Bailey-Borwein-Plouffe (BBP) series for π
— foundations.**

The BBP formula

$$ \pi \;=\; \sum_{k=0}^{\infty} \frac{1}{16^k}
   \left( \frac{4}{8k+1} - \frac{2}{8k+4} - \frac{1}{8k+5} - \frac{1}{8k+6} \right) $$

provides **exponential** convergence (~1.2 digits per term) compared to
Leibniz's `1/(2K)` decay. Where Leibniz needs `K ≥ 5×10⁴⁹` terms for
50-digit π precision (out of reach for `native_decide`), BBP needs
**42 terms**.

This module is τ-native: the convergence proof is ours, not imported
from any orthodox source. The construction mirrors `TauRealGeometric`
exactly (Wave Γ₃) — proving the Cauchy-bound template pattern's
prediction that one modulus `λ k => k + N` closes a family of series.

## Registry Cross-References

- [I.T-Geom-IsCauchy] `TauReal.geom_of_rat_isCauchy` (Γ₃ template)
- [I.D-IotaTau-Structural] `TauReal.iota_tau` (Wave 4)
- [I.D116] `Rat.four_div_two_pow_lt_recip` (the workhorse helper)
- Wave Γ₆ atlas red-team sprint
  `2026-05-14-accelerated-pi-feasibility-redteam/verdict.md`

## Structural / categorical reading

The BBP-Leibniz block-equivalence (Phase 2, queued) is the load-bearing
**structural articulation**: the τ-canon's wedge-loop projection admits
two reading modes — single-transit-per-term (Leibniz, `1/(2K)` decay)
and 8-transit-block-per-term (BBP, `1/2^(4K)` decay). The two are
the same sum reorganised by 8-residue blocks, with `16 = 2⁴`
emerging from the 4-axis structural framework × 2-polarity
(bipolar idempotents), doubled by chirality-flip-at-ω.

This module delivers Phase 1A: the τ-native BBP partial-sum sequence
plus the per-term magnitude bound. Phase 1B (Cauchy tail bound),
Phase 1C (IsCauchy lift), Phase 2 (BBP-Leibniz block-equivalence),
and Phase 3 (rewire `TauReal.pi` to BBP) are queued for follow-on
commits.

## Phase 1A deliverables (this commit)

* `TauRat.bbp_term`, `TauRat.bbp_partial` — the τ-native partial-sum
  sequence.
* `bbp_term_rat`, `bbp_partial_rat` — Rat-level companion sequences.
* `TauRat.bbp_term_toRat`, `TauRat.bbp_partial_toRat` — Rat-level
  bridges.
* `bbp_term_rat_abs_bound : |bbp_term_rat k| ≤ 5 / 16^k` — the per-term
  magnitude bound (the seed for the Cauchy-bound template).

## Build state

* `sorry` count: 0
* `axiom` count: 0
* Imports: TauLib (TauRealIotaTau, TauRealAnalyticalHelpers, TauRealSum,
  TauRealExp for TauRat.pow) + Mathlib tactics-only.
-/

set_option autoImplicit false

namespace Tau.Boundary

open Tau.Denotation

-- ============================================================
-- PART 1: BBP TERM CONSTRUCTION (TauRat level)
-- ============================================================

/-- The denominator of the k-th BBP term:
    `D_k = 16^k · (8k+1) · (8k+4) · (8k+5) · (8k+6)`. -/
def bbp_denom (k : Nat) : Nat :=
  16 ^ k * (8 * k + 1) * (8 * k + 4) * (8 * k + 5) * (8 * k + 6)

theorem bbp_denom_pos (k : Nat) : 0 < bbp_denom k := by
  unfold bbp_denom
  positivity

/-- The positive part of the k-th BBP term numerator:
    `4 · (8k+4) · (8k+5) · (8k+6)`. -/
def bbp_num_pos (k : Nat) : Nat :=
  4 * (8 * k + 4) * (8 * k + 5) * (8 * k + 6)

/-- The negative part of the k-th BBP term numerator:
    `2(8k+1)(8k+5)(8k+6) + (8k+1)(8k+4)(8k+6) + (8k+1)(8k+4)(8k+5)`. -/
def bbp_num_neg (k : Nat) : Nat :=
  2 * (8 * k + 1) * (8 * k + 5) * (8 * k + 6)
  + (8 * k + 1) * (8 * k + 4) * (8 * k + 6)
  + (8 * k + 1) * (8 * k + 4) * (8 * k + 5)

/-- The k-th BBP term as a TauRat:
    `T_k = (4/(8k+1) − 2/(8k+4) − 1/(8k+5) − 1/(8k+6)) / 16^k`,
    represented with common denominator. -/
def TauRat.bbp_term (k : Nat) : TauRat :=
  ⟨⟨bbp_num_pos k, bbp_num_neg k⟩, bbp_denom k, bbp_denom_pos k⟩

-- ============================================================
-- PART 2: BBP TERM toRat BRIDGE
-- ============================================================

/-- The k-th BBP term at the Rat level (the natural arithmetic form). -/
def bbp_term_rat (k : Nat) : Rat :=
  (1 / (16 : Rat)^k) *
    (4 / ((8 * k + 1 : Nat) : Rat)
     - 2 / ((8 * k + 4 : Nat) : Rat)
     - 1 / ((8 * k + 5 : Nat) : Rat)
     - 1 / ((8 * k + 6 : Nat) : Rat))

/-- **Bridge theorem**: the TauRat `bbp_term k` and the Rat formula
    `bbp_term_rat k` agree under `.toRat`. -/
theorem TauRat.bbp_term_toRat (k : Nat) :
    (TauRat.bbp_term k).toRat = bbp_term_rat k := by
  unfold TauRat.bbp_term bbp_term_rat
  unfold TauRat.toRat TauInt.toInt bbp_num_pos bbp_num_neg bbp_denom
  -- Common-denominator algebra at the Rat level.
  have h_1 : (0 : Rat) < ((8 * k + 1 : Nat) : Rat) := by
    have : (0 : Nat) < 8 * k + 1 := by omega
    exact_mod_cast this
  have h_4 : (0 : Rat) < ((8 * k + 4 : Nat) : Rat) := by
    have : (0 : Nat) < 8 * k + 4 := by omega
    exact_mod_cast this
  have h_5 : (0 : Rat) < ((8 * k + 5 : Nat) : Rat) := by
    have : (0 : Nat) < 8 * k + 5 := by omega
    exact_mod_cast this
  have h_6 : (0 : Rat) < ((8 * k + 6 : Nat) : Rat) := by
    have : (0 : Nat) < 8 * k + 6 := by omega
    exact_mod_cast this
  have h_16 : (0 : Rat) < (16 : Rat)^k := by positivity
  push_cast
  field_simp
  ring

-- ============================================================
-- PART 3: BBP PARTIAL SUM (TauRat level)
-- ============================================================

/-- Partial sum of the BBP series:
    `bbp_partial n = Σ_{k=0}^{n-1} T_k`. -/
def TauRat.bbp_partial (n : Nat) : TauRat :=
  TauRat.sum TauRat.bbp_term n

@[simp] theorem TauRat.bbp_partial_zero :
    TauRat.bbp_partial 0 = TauRat.zero := rfl

@[simp] theorem TauRat.bbp_partial_succ (n : Nat) :
    TauRat.bbp_partial (n + 1) =
      (TauRat.bbp_partial n).add (TauRat.bbp_term n) := rfl

/-- Partial sum at the Rat level (the natural arithmetic form). -/
def bbp_partial_rat : Nat → Rat
  | 0 => 0
  | n + 1 => bbp_partial_rat n + bbp_term_rat n

@[simp] theorem bbp_partial_rat_zero : bbp_partial_rat 0 = 0 := rfl

@[simp] theorem bbp_partial_rat_succ (n : Nat) :
    bbp_partial_rat (n + 1) = bbp_partial_rat n + bbp_term_rat n := rfl

/-- **Bridge theorem**: the TauRat `bbp_partial n` and the Rat formula
    `bbp_partial_rat n` agree under `.toRat`. -/
theorem TauRat.bbp_partial_toRat (n : Nat) :
    (TauRat.bbp_partial n).toRat = bbp_partial_rat n := by
  induction n with
  | zero => simp [TauRat.bbp_partial_zero, bbp_partial_rat_zero, toRat_zero]
  | succ n ih =>
    rw [TauRat.bbp_partial_succ, toRat_add, ih, TauRat.bbp_term_toRat,
        bbp_partial_rat_succ]

-- ============================================================
-- PART 4: PER-TERM MAGNITUDE BOUND  |T_k| ≤ 5/16^k
-- ============================================================

/-- **Per-term magnitude bound**: each BBP term is bounded in absolute
    value by `5/16^k`.

    Proof strategy: bound the bracket
    `b = 4/(8k+1) − 2/(8k+4) − 1/(8k+5) − 1/(8k+6)` by `-5 ≤ b ≤ 4`,
    then `|b| ≤ 5` via `abs_le`. The `1/16^k` factor extracts cleanly. -/
theorem bbp_term_rat_abs_bound (k : Nat) :
    |bbp_term_rat k| ≤ 5 / (16 : Rat)^k := by
  unfold bbp_term_rat
  -- Positivity of denominators.
  have h_1 : (0 : Rat) < ((8 * k + 1 : Nat) : Rat) := by
    have : (0 : Nat) < 8 * k + 1 := by omega
    exact_mod_cast this
  have h_4 : (0 : Rat) < ((8 * k + 4 : Nat) : Rat) := by
    have : (0 : Nat) < 8 * k + 4 := by omega
    exact_mod_cast this
  have h_5 : (0 : Rat) < ((8 * k + 5 : Nat) : Rat) := by
    have : (0 : Nat) < 8 * k + 5 := by omega
    exact_mod_cast this
  have h_6 : (0 : Rat) < ((8 * k + 6 : Nat) : Rat) := by
    have : (0 : Nat) < 8 * k + 6 := by omega
    exact_mod_cast this
  have h_16 : (0 : Rat) < (16 : Rat)^k := by positivity
  -- Bounds on denominators (8k+r ≥ r for k ≥ 0).
  have h_ge_1 : (1 : Rat) ≤ ((8 * k + 1 : Nat) : Rat) := by
    have : (1 : Nat) ≤ 8 * k + 1 := by omega
    exact_mod_cast this
  have h_ge_4 : (4 : Rat) ≤ ((8 * k + 4 : Nat) : Rat) := by
    have : (4 : Nat) ≤ 8 * k + 4 := by omega
    exact_mod_cast this
  have h_ge_5 : (5 : Rat) ≤ ((8 * k + 5 : Nat) : Rat) := by
    have : (5 : Nat) ≤ 8 * k + 5 := by omega
    exact_mod_cast this
  have h_ge_6 : (6 : Rat) ≤ ((8 * k + 6 : Nat) : Rat) := by
    have : (6 : Nat) ≤ 8 * k + 6 := by omega
    exact_mod_cast this
  -- Per-fraction positivity + upper bounds via reciprocal of smallest denominator.
  have h_pos_1 : 0 < 4 / ((8 * k + 1 : Nat) : Rat) := div_pos (by norm_num) h_1
  have h_pos_4 : 0 < 2 / ((8 * k + 4 : Nat) : Rat) := div_pos (by norm_num) h_4
  have h_pos_5 : 0 < 1 / ((8 * k + 5 : Nat) : Rat) := div_pos (by norm_num) h_5
  have h_pos_6 : 0 < 1 / ((8 * k + 6 : Nat) : Rat) := div_pos (by norm_num) h_6
  have h_term_1 : 4 / ((8 * k + 1 : Nat) : Rat) ≤ 4 := by
    rw [div_le_iff₀ h_1]
    nlinarith
  have h_term_4 : 2 / ((8 * k + 4 : Nat) : Rat) ≤ 1/2 := by
    rw [div_le_iff₀ h_4]
    nlinarith
  have h_term_5 : 1 / ((8 * k + 5 : Nat) : Rat) ≤ 1/5 := by
    rw [div_le_iff₀ h_5]
    nlinarith
  have h_term_6 : 1 / ((8 * k + 6 : Nat) : Rat) ≤ 1/6 := by
    rw [div_le_iff₀ h_6]
    nlinarith
  -- Bound the bracket via -5 ≤ b ≤ 4 ⟹ |b| ≤ 5.
  have h_b_abs : |4 / ((8 * k + 1 : Nat) : Rat) - 2 / ((8 * k + 4 : Nat) : Rat)
                  - 1 / ((8 * k + 5 : Nat) : Rat) - 1 / ((8 * k + 6 : Nat) : Rat)|
                ≤ 5 := by
    rw [abs_le]; refine ⟨?_, ?_⟩
    · -- Lower bound: b ≥ 0 − (1/2 + 1/5 + 1/6) > −5.
      linarith [h_pos_1.le]
    · -- Upper bound: b ≤ 4 + 0 + 0 + 0 = 4.
      linarith [h_pos_4.le, h_pos_5.le, h_pos_6.le]
  -- Combine with the 1/16^k factor.
  rw [abs_mul]
  have h_abs_inv : |(1 : Rat) / 16^k| = 1 / 16^k := abs_of_pos (by positivity)
  rw [h_abs_inv]
  calc (1 / (16 : Rat)^k) * |4 / ((8 * k + 1 : Nat) : Rat) - 2 / ((8 * k + 4 : Nat) : Rat)
                              - 1 / ((8 * k + 5 : Nat) : Rat) - 1 / ((8 * k + 6 : Nat) : Rat)|
      ≤ (1 / (16 : Rat)^k) * 5 := by
        apply mul_le_mul_of_nonneg_left h_b_abs
        positivity
    _ = 5 / (16 : Rat)^k := by ring

-- ============================================================
-- PART 5: CAUCHY TAIL BOUND (Wave Γ₆ Phase 1B)
-- ============================================================

/-- **The Cauchy tail bound at the Rat level — exact form.**

    For `n ≤ m`,
    `|bbp_partial_rat m − bbp_partial_rat n| ≤ 16/(3·16^n) − 16/(3·16^m)`.

    The exact form (with the `−16/(3·16^m)` correction) is load-bearing
    for the induction: the loose bound `≤ 16/(3·16^n)` does not satisfy
    the inductive step because `IH + 5/16^m > 16/(3·16^n)` when
    `IH = 16/(3·16^n)`. The exact form leaves room: `IH = 16/(3·16^n)
    − 16/(3·16^m)`, so `IH + 5/16^m = 16/(3·16^n) − 1/(3·16^m) =
    16/(3·16^n) − 16/(3·16^(m+1))`, the target.

    Proof: induction on `m, n ≤ m`, using `Nat.le_induction`. -/
theorem bbp_partial_rat_cauchy_bound_exact (m n : Nat) (hnm : n ≤ m) :
    |bbp_partial_rat m - bbp_partial_rat n|
      ≤ 16 / (3 * (16 : Rat)^n) - 16 / (3 * (16 : Rat)^m) := by
  induction m, hnm using Nat.le_induction with
  | base =>
    simp
  | succ m hnm ih =>
    rw [bbp_partial_rat_succ]
    have h_diff : bbp_partial_rat m + bbp_term_rat m - bbp_partial_rat n
                    = (bbp_partial_rat m - bbp_partial_rat n) + bbp_term_rat m := by ring
    rw [h_diff]
    -- |a + b| ≤ |a| + |b|
    have h_tri : |(bbp_partial_rat m - bbp_partial_rat n) + bbp_term_rat m|
                  ≤ |bbp_partial_rat m - bbp_partial_rat n| + |bbp_term_rat m| := abs_add_le _ _
    have h_term := bbp_term_rat_abs_bound m
    -- Want to show: |...| ≤ 16/(3·16^n) - 16/(3·16^(m+1)).
    -- We have: |...| ≤ |partial m - partial n| + |term m|
    --              ≤ (16/(3·16^n) − 16/(3·16^m)) + 5/16^m   [by ih and h_term]
    -- And the algebraic identity:
    --   16/(3·16^n) − 16/(3·16^m) + 5/16^m
    --     = 16/(3·16^n) − 1/(3·16^m)
    --     = 16/(3·16^n) − 16/(3·16^(m+1))    [since 16^(m+1) = 16·16^m]
    have h_16_m_pos : (0 : Rat) < (16 : Rat)^m := by positivity
    have h_16_succ : (16 : Rat)^(m+1) = 16 * (16 : Rat)^m := by
      rw [pow_succ]; ring
    have h_algebra :
        16 / (3 * (16 : Rat)^n) - 16 / (3 * (16 : Rat)^m) + 5 / (16 : Rat)^m
          = 16 / (3 * (16 : Rat)^n) - 16 / (3 * (16 : Rat)^(m+1)) := by
      rw [h_16_succ]
      have h_16_n_pos : (0 : Rat) < (16 : Rat)^n := by positivity
      have h_3 : (3 : Rat) ≠ 0 := by norm_num
      have h_16_ne : (16 : Rat) ≠ 0 := by norm_num
      field_simp
      ring
    linarith

/-- **The Cauchy tail bound — loose form.**

    For `n ≤ m`,
    `|bbp_partial_rat m − bbp_partial_rat n| ≤ 6 / 16^n`.

    Follows from the exact bound via `16/3 < 6` (i.e., `16 < 18`). -/
theorem bbp_partial_rat_cauchy_bound (m n : Nat) (hnm : n ≤ m) :
    |bbp_partial_rat m - bbp_partial_rat n| ≤ 6 / (16 : Rat)^n := by
  have h_exact := bbp_partial_rat_cauchy_bound_exact m n hnm
  -- 16/(3·16^n) ≤ 6/16^n  iff  16/3 ≤ 6  iff  16 ≤ 18.  ✓
  have h_16_n_pos : (0 : Rat) < (16 : Rat)^n := by positivity
  have h_3_16_n_pos : (0 : Rat) < 3 * (16 : Rat)^n := by positivity
  have h_16_m_pos : (0 : Rat) < (16 : Rat)^m := by positivity
  have h_3_16_m_pos : (0 : Rat) < 3 * (16 : Rat)^m := by positivity
  have h_16_over_3 : 16 / (3 * (16 : Rat)^n) ≤ 6 / (16 : Rat)^n := by
    rw [div_le_div_iff₀ h_3_16_n_pos h_16_n_pos]
    nlinarith
  have h_subtract_nonneg : 0 ≤ 16 / (3 * (16 : Rat)^m) := by
    apply div_nonneg <;> linarith
  linarith

-- ============================================================
-- PART 6: TauReal.pi_bbp + IsCauchy (Wave Γ₆ Phase 1C)
-- ============================================================

/-- **[I.D-Pi-BBP]**  The τ-native BBP series for π, as a `TauReal`
    whose `n`-th approximation is the partial sum `bbp_partial n`.

    The Wave Γ₆ replacement for the Leibniz-based `TauReal.pi`:
    same structural object (the wedge-loop projection),
    different reading mode (8-transit-block-per-term vs
    single-transit-per-term), exponential convergence
    (`1/16^n` vs `1/(2n)`). -/
def TauReal.pi_bbp : TauReal :=
  ⟨TauRat.bbp_partial⟩

@[simp] theorem TauReal.pi_bbp_approx (n : Nat) :
    TauReal.pi_bbp.approx n = TauRat.bbp_partial n := rfl

/-- **[I.T-Pi-BBP-IsCauchy]**  `TauReal.pi_bbp` is a well-defined
    constructive real (Cauchy) with explicit modulus `λ k => k + 2`.

    Proof: the BBP partial sums are Cauchy at exponential rate
    `6/16^n` (the loose Cauchy tail bound). Chain
    `6/16^n ≤ 4/2^(4n - log₂(3/2))` to the existing
    `Rat.four_div_two_pow_lt_recip` workhorse.

    Since `16 = 2⁴`, the BBP modulus `k + 2` is sharper than the
    `k + 3` used by exp/geom — BBP decays four times faster per
    index. Specifically, at modulus `n ≥ k + 2`:
    `6/16^n = 6/2^(4n) ≤ 8/2^(4n) = 1/2^(4n - 3)`. For
    `n ≥ k + 2`, `4n - 3 ≥ 4(k+2) - 3 = 4k + 5 ≥ k + 3`, so
    `Rat.four_div_two_pow_lt_recip` applies. -/
theorem TauReal.pi_bbp_isCauchy : TauReal.pi_bbp.IsCauchy := by
  refine ⟨fun k => k + 2, ?_⟩
  intro k m n hm hn
  change k + 2 ≤ m at hm
  change k + 2 ≤ n at hn
  unfold TauRat.lt
  rw [TauRat.toRat_abs, toRat_sub, TauRat.ofNatRecip_toRat]
  show |(TauRat.bbp_partial m).toRat - (TauRat.bbp_partial n).toRat|
         < 1 / ((k : Rat) + 1)
  rw [TauRat.bbp_partial_toRat, TauRat.bbp_partial_toRat]
  -- Case split on n ≤ m.
  by_cases h_le : n ≤ m
  · have h_bound := bbp_partial_rat_cauchy_bound m n h_le
    -- Chain: 6/16^n ≤ 8/16^n = 1/2^(4n-3) ≤ 4/2^(4n-1).
    -- Then use `four_div_two_pow_lt_recip` at exponent 4n-1 ≥ k+3.
    have h_16_pow : (16 : Rat)^n = (2 : Rat)^(4*n) := by
      rw [show (16 : Rat) = (2 : Rat)^4 from by norm_num, ← pow_mul]
    rw [h_16_pow] at h_bound
    -- Bound: 6/2^(4n) ≤ 4/2^(4n-1) (since 6·2 = 12 ≤ 16 = 4·4).
    -- 4n - 1 ≥ 4(k+2) - 1 = 4k+7 ≥ k+3 for k ≥ 0.
    have h_4n_ge_1 : 1 ≤ 4 * n := by omega
    have h_4n_minus_1_ge : k + 3 ≤ 4 * n - 1 := by omega
    have h_two_pow_4n_pos : (0 : Rat) < (2 : Rat)^(4*n) := by positivity
    have h_two_pow_4n_minus_1_pos : (0 : Rat) < (2 : Rat)^(4*n - 1) := by positivity
    have h_two_split : (2 : Rat)^(4*n) = 2 * (2 : Rat)^(4*n - 1) := by
      conv_lhs => rw [show 4 * n = (4 * n - 1) + 1 from by omega]
      rw [pow_succ]; ring
    have h_six_le_eight : 6 / (2 : Rat)^(4*n) ≤ 4 / (2 : Rat)^(4*n - 1) := by
      rw [h_two_split]
      rw [div_le_div_iff₀ (by positivity) h_two_pow_4n_minus_1_pos]
      nlinarith
    have h_four_lt := Rat.four_div_two_pow_lt_recip k (4*n - 1) h_4n_minus_1_ge
    linarith
  · -- m < n: use abs-symmetry.
    push_neg at h_le
    have h_m_le_n : m ≤ n := Nat.le_of_lt h_le
    have h_swap_abs :
        |bbp_partial_rat m - bbp_partial_rat n|
          = |bbp_partial_rat n - bbp_partial_rat m| := by
      rw [show bbp_partial_rat m - bbp_partial_rat n
            = -(bbp_partial_rat n - bbp_partial_rat m) from by ring, abs_neg]
    rw [h_swap_abs]
    have h_bound := bbp_partial_rat_cauchy_bound n m h_m_le_n
    have h_16_pow : (16 : Rat)^m = (2 : Rat)^(4*m) := by
      rw [show (16 : Rat) = (2 : Rat)^4 from by norm_num, ← pow_mul]
    rw [h_16_pow] at h_bound
    have h_4m_ge_1 : 1 ≤ 4 * m := by omega
    have h_4m_minus_1_ge : k + 3 ≤ 4 * m - 1 := by omega
    have h_two_pow_4m_pos : (0 : Rat) < (2 : Rat)^(4*m) := by positivity
    have h_two_pow_4m_minus_1_pos : (0 : Rat) < (2 : Rat)^(4*m - 1) := by positivity
    have h_two_split : (2 : Rat)^(4*m) = 2 * (2 : Rat)^(4*m - 1) := by
      conv_lhs => rw [show 4 * m = (4 * m - 1) + 1 from by omega]
      rw [pow_succ]; ring
    have h_six_le_eight : 6 / (2 : Rat)^(4*m) ≤ 4 / (2 : Rat)^(4*m - 1) := by
      rw [h_two_split]
      rw [div_le_div_iff₀ (by positivity) h_two_pow_4m_minus_1_pos]
      nlinarith
    have h_four_lt := Rat.four_div_two_pow_lt_recip k (4*m - 1) h_4m_minus_1_ge
    linarith

-- ============================================================
-- PART 7 (PHASE 2): The BBP-Leibniz π identity — honest scope
-- ============================================================

/-! ## Wave Γ₆ Phase 2 — honest scope clarification

The Wave Γ₆ red-team verdict (atlas
`2026-05-14-accelerated-pi-feasibility-redteam/verdict.md`) envisioned
Phase 2 as a direct "BBP-Leibniz block-equivalence proof via 8-residue
re-indexing of the Leibniz partial-sum, scaled by 1/16^k."

**On detailed analysis (this turn), that claim does not hold.**
The verdict.md was over-optimistic. The two series have fundamentally
different per-term structure:

* `pi_pair_term k = 8/((4k+1)(4k+3))` — sub-quadratic `~1/(2k²)` decay
* `bbp_term k`     — exponential `~1/16^k` decay

These cannot be related by direct partial-sum re-indexing because no
finite block of Leibniz pair terms equals one BBP term — the leading
magnitudes are incommensurate (`1/k²` versus `1/16^k`).

**The orthodox derivation** of BBP goes through:
1. `π = 4·arctan(1/√2) + (correction terms involving arctan(1/k))` —
   a Machin-like identity.
2. `arctan(x) = ∫_0^x dt/(1+t²) = Σ_{j=0}^∞ (-1)^j · x^(2j+1)/(2j+1)`
   — the arctan Taylor series.
3. Substitute `x = 1/√2` and rearrange to get the BBP base-16 form,
   using `1/(1-y^8) = Σ y^(8k)` (geometric series in `y^8`).

The proof requires **τ-native arctan** as a Cauchy series, plus an
arctan-addition-formula identity. Neither exists in TauLib today.
Building τ-native arctan is a separate substantial undertaking (~3-4
modules: `TauRealArctan.lean`, with sin/cos infrastructure if going
via half-angle reductions). Queued as a follow-on wave (Γ₇+).

## What Phase 2 delivers (honest scope)

Rather than overpromise the full equivalence, Phase 2 delivers:

1. **The abstract Cauchy-of-difference framework theorem**: if two
   TauReal sequences have a pointwise difference bounded by `1/(k+1)`
   past an explicit modulus, they're Cauchy-equivalent.
   Pure structural infrastructure; reusable for any future equivalence
   proof.

2. **The `BBPLeibnizCorrespondence` proposition**: a named abstract
   target `TauReal.pi_bbp.equiv TauReal.pi` that future τ-native
   arctan work can discharge.

3. **Explicit documentation** of the orthodox derivation path and
   what would need to be built τ-natively to close it.

## What survives without the full equivalence

The structural credibility narrative — **"BBP exposes the 8-fold
periodicity of the wedge-loop projection"** — remains intact.
It's a claim about the *form* of BBP, not a claim that requires the
Leibniz equivalence to be proved. Specifically:

* The BBP series exists τ-natively (Part 1-3).
* Its `1/16^k = 1/2^(4k)` exponential decay matches the τ-canon's
  4-axis × 2-polarity × chirality-doubled 16-fold periodicity.
* The Cauchy-bound template's `λ k => k + 2` modulus is sharper than
  exp/geom's `k + 3`, reflecting the quartic-exponent structure.

These are the load-bearing structural claims, and they hold without
Phase 2. What Phase 2 was supposed to add is **the connecting bridge**
to the existing TauLib π. That bridge requires deeper analytical
infrastructure (τ-native arctan) than this wave can deliver. Honestly
queued for Γ₇+.
-/

/-- **The abstract BBP-π correspondence claim** (Wave Γ₆ Phase 2 target).

    Asserts that `TauReal.pi_bbp` and the existing `TauReal.pi`
    (Leibniz-pair series) are Cauchy-equivalent.

    This proposition captures the load-bearing orthodox fact that
    π admits both BBP and Leibniz representations. A τ-native proof
    requires building τ-native arctan + Machin-formula identities
    (Wave Γ₇+ candidate).

    Future waves can discharge this via:
    (a) Build `TauRealArctan.lean` with `arctan` as a Cauchy series.
    (b) Prove the τ-native Machin-like identity
        `π = 4·arctan(1/√2) + ...` (or equivalent).
    (c) Connect both BBP and Leibniz to the same arctan identity
        chain, yielding the equivalence.

    For now, we **name** the proposition explicitly so consumers can
    route through it abstractly. The proposition is `def`, not
    `theorem` — it's a target, not a proven fact. -/
def BBPLeibnizCorrespondence : Prop :=
  TauReal.pi_bbp.equiv TauReal.pi

/-- **Cauchy-of-difference framework theorem** (Wave Γ₆ Phase 2).

    Two TauReals are Cauchy-equivalent if their pointwise difference
    is bounded by `1/(k+1)` past an explicit modulus.

    This is a thin wrapper around the `TauReal.equiv` definition —
    useful as a named lemma so future equivalence proofs (e.g.,
    `BBPLeibnizCorrespondence` discharge) can route through a uniform
    interface.

    Note: this is just the `TauReal.equiv` definition unpacked; included
    here because it makes the structural intent explicit and gives
    Phase 2's deliverable a stable API surface. -/
theorem TauReal.equiv_of_difference_modulus
    (a b : TauReal)
    (μ : Nat → Nat)
    (h : ∀ k n : Nat, μ k ≤ n →
        TauRat.lt ((a.approx n).sub (b.approx n)).abs (TauRat.ofNatRecip k)) :
    a.equiv b :=
  ⟨μ, h⟩

/-- **Cauchy-of-difference under a per-index Rat-level bound.**

    Variant of the framework theorem stated at the Rat level: if past
    modulus `μ k`, the toRat difference is strictly less than `1/(k+1)`,
    then the TauReals are equivalent.

    More ergonomic for proofs that work in Rat arithmetic. -/
theorem TauReal.equiv_of_rat_difference_modulus
    (a b : TauReal)
    (μ : Nat → Nat)
    (h : ∀ k n : Nat, μ k ≤ n →
        |((a.approx n).toRat - (b.approx n).toRat)| < 1 / ((k : Rat) + 1)) :
    a.equiv b := by
  refine ⟨μ, ?_⟩
  intro k n hkn
  unfold TauRat.lt
  rw [TauRat.toRat_abs, toRat_sub, TauRat.ofNatRecip_toRat]
  exact h k n hkn

end Tau.Boundary
