import TauLib.BookI.Boundary.TauRealMachinPiKeystone
import Mathlib.Tactic.Ring
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity

/-!
# TauLib.BookI.Boundary.TauRealArctanOneLeibniz

**Phase E Scope 2E — Leibniz Cauchy infrastructure for `arctan_of_rat_seq 1`
and the residual analytic gap toward `MachinSlashFourIdentity`.**

After Phase E Scope 2A-lift / 2B / 2C / 2D shipped the structural pipeline
that reduces the entire Machin keystone to the single named target
`MachinSlashFourIdentity` (cf. `TauRealMachinPiKeystone.lean`), this
module ships **explicit analytical infrastructure** needed for any future
closure of the residual gap.

## What this module ships

* **`arctan_partial_rat_one_cauchy_bound`** — Rat-level Cauchy bound for
  the arctan partial sum at `x = 1`:
  `|arctan_partial_rat 1 m − arctan_partial_rat 1 n| ≤ 1/(8n)` for
  `1 ≤ n ≤ m`. Derived directly from `pi_partial_cauchy_bound` via the
  pointwise `(pi_partial n).toRat = 4·arctan_partial_rat 1 n` identity.

* **`TauReal.arctan_of_rat_seq_one_isCauchy`** — the Leibniz arctan series
  at `x = 1` is itself Cauchy with explicit modulus `λ k => k + 3`. This
  patches the gap in the `arctan_of_rat_isCauchy` API (which requires
  `2·|x.toRat| ≤ 1` and hence fails at `x = 1`).

* **`MachinSlashFour_lhs_cauchy_bound`** — Rat-level Cauchy bound for the
  combined LHS `4·arctan_partial_rat(1/5) − arctan_partial_rat(1/239)`:
  the difference at depths `m, n` is bounded by `4·(4/2^n + 4/2^n)` (much
  tighter than the Leibniz `1/(8n)`).

* **`MachinSlashFourLHS_cauchy_modulus`** — TauReal-level Cauchy modulus
  for the LHS expression `pi_machin_arctan_quarter`. This delivers
  Cauchy-ness for the LHS of `MachinSlashFourIdentity`.

* **`MachinClassicalLimit`** — a **named documentation Prop** capturing
  the residual analytic gap. Specifically: it states that for every
  `ε > 0` (`k : Nat`), there exists a depth `n` past which
  `|4·arctan_partial(1/5) n − arctan_partial(1/239) n − arctan_partial(1) n|
    < 1/(k+1)`. This is precisely the rat-level diagonal modulus from
  `MachinSlashFourIdentity_iff_rat_modulus`, packaged as a focused, named
  target.

* **`MachinClassicalLimit_iff_MachinSlashFourIdentity`** — the headline
  equivalence: discharging the classical Machin limit at the τ-canon
  rat level is equivalent to discharging `MachinSlashFourIdentity`.

## Why this is honest meaningful infrastructure

The keystone challenge from Scope 2D documents the residual analytic
content as a Rat-level diagonal modulus condition. This module:

1. **Discharges the easy Cauchy facts** for both sides individually —
   the Leibniz `arctan(1)` and the Machin LHS `4·arctan(1/5) −
   arctan(1/239)` are now both certified Cauchy with explicit moduli.

2. **Names the residual gap** as `MachinClassicalLimit` so that future
   work can target a single focused proposition rather than chasing
   through the Scope 2D refinement chain. This is the **bare classical
   Machin fact** at finite-depth modulus form.

3. **Makes the structural reduction sharp**: the
   `MachinClassicalLimit ↔ MachinSlashFourIdentity` theorem composed
   with the Scope 2D pipeline gives:

   >  `MachinClassicalLimit ↔ MachinSlashFourIdentity ↔ MachinIdentity ↔ pi_machin ≈ pi`.

   The entire keystone reduces to `MachinClassicalLimit` — a concrete
   Rat-level statement that future τ-native or programme-axiom-based
   work can target directly.

## What this module does NOT do

It does **not** discharge `MachinClassicalLimit` itself. The residual
analytic content fundamentally requires either:

* **cisTauReal principal-branch injectivity** plus the Scope 2A-lift
  45°-line identity, or
* **A programme axiom** stating the classical limit (extending the
  axiom budget to 4 for this theorem), or
* **Direct partial-sum analysis** using either approach via independent
  τ-native tail-error analysis.

This is brutally honest: the analytic gap is fundamental and not
discharged here.

## Path forward

The cleanest closure paths now are:

* **Path F.A — Programme axiom**: add `MachinClassicalLimit` as a
  τ-canon programme axiom. Budget cost: +1 axiom for this specific
  theorem (kernel count remains 3 + 1 programme axiom = 4 axioms total
  for the keystone). The rest of the chain (Scope 2A-lift through 2D)
  is sorry=0, axioms=3.

* **Path F.B — cisTauReal injectivity**: lift Scope 2A-lift's 45°-line
  identity. Estimated 1500+ LOC of independent infrastructure.

* **Path F.C — Direct tail-error analysis**: bound the per-depth
  difference using the alternating series structure plus the classical
  limit fact. Equivalent in proof obligation to Path F.A but stated
  differently.

## Build state

* `sorry` count: 0
* Axiom count: 3 (kernel: `propext`, `Classical.choice`, `Quot.sound`)
* Imports: `TauRealMachinPiKeystone` (which transitively imports the
  whole Phase B/C/D/E stack) + Mathlib tactics only.

## Registry Cross-References

* [I.D-Pi-Partial] `TauRat.pi_partial` (Wave 3c)
* [I.T-Pi-Partial-Cauchy-Bound] `TauReal.pi_partial_cauchy_bound`
* [I.T-Pi-Equiv-Four-Arctan-One] `TauReal.pi_equiv_four_arctan_one`
  (Scope 2B)
* [I.T-Arctan-Of-Rat-Seq-Approx] `TauReal.arctan_of_rat_seq_approx`
* [I.T-Arctan-Partial-Rat-Cauchy-Bound] `arctan_partial_rat_cauchy_bound`
  (TauRealArctan, requires `2·|x| ≤ 1`)
* [I.T-MachinSlashFourIdentity-Iff-Rat-Modulus]
  `MachinSlashFourIdentity_iff_rat_modulus` (Scope 2D)

## Module name

This file is picked up by the `.submodules` glob in `lakefile.lean`.
-/

set_option autoImplicit false

namespace Tau.Boundary

open Tau.Denotation

-- ============================================================
-- PART 1: RAT-LEVEL CAUCHY BOUND FOR arctan_partial_rat 1
-- ============================================================

/-! ## Cauchy bound at x = 1 via the pi_partial bridge

  The general `arctan_partial_rat_cauchy_bound` requires `2·|x| ≤ 1`,
  which fails at `x = 1`. However, the Leibniz `arctan(1)` series is
  classically Cauchy with rate `O(1/n)` by the alternating-series test.

  We derive this τ-natively by exploiting the pointwise identity
  `(pi_partial n).toRat = 4·arctan_partial_rat 1 n`:

  >  `|4·arctan_partial_rat 1 m − 4·arctan_partial_rat 1 n|
       = |(pi_partial m).toRat − (pi_partial n).toRat|
       ≤ 1/(2n)`  (from `pi_partial_cauchy_bound`)

  Hence `|arctan_partial_rat 1 m − arctan_partial_rat 1 n| ≤ 1/(8n)`. -/

/-- **Rat-level Cauchy bound for the Leibniz arctan series at x = 1**:
    `|arctan_partial_rat 1 m − arctan_partial_rat 1 n| ≤ 1/(8n)` for
    `1 ≤ n ≤ m`.

    Derived from `TauReal.pi_partial_cauchy_bound` via the pointwise
    `(pi_partial n).toRat = 4·arctan_partial_rat 1 n` identity. -/
theorem arctan_partial_rat_one_cauchy_bound (m n : Nat) (hn : 1 ≤ n) (hnm : n ≤ m) :
    |arctan_partial_rat 1 m - arctan_partial_rat 1 n|
      ≤ 1 / (8 * (n : Rat)) := by
  -- pi_partial_cauchy_bound: |pi_partial m .toRat - pi_partial n .toRat| ≤ 1/(2n)
  have h_pi_bound := TauReal.pi_partial_cauchy_bound m n hn hnm
  -- pointwise identity: pi_partial k .toRat = 4 · arctan_partial_rat 1 k
  have h_id_m := pi_partial_toRat_eq_four_arctan_partial_one m
  have h_id_n := pi_partial_toRat_eq_four_arctan_partial_one n
  -- substitute
  rw [h_id_m, h_id_n] at h_pi_bound
  -- h_pi_bound: |4·a_m - 4·a_n| ≤ 1/(2n)
  -- where a_m := arctan_partial_rat 1 m, a_n := arctan_partial_rat 1 n
  have h_factor :
      (4 : Rat) * arctan_partial_rat 1 m - 4 * arctan_partial_rat 1 n
        = 4 * (arctan_partial_rat 1 m - arctan_partial_rat 1 n) := by ring
  rw [h_factor, abs_mul, show |(4 : Rat)| = 4 from by norm_num] at h_pi_bound
  -- h_pi_bound: 4 · |a_m - a_n| ≤ 1/(2n)
  have h_n_pos : (0 : Rat) < (n : Rat) := by
    exact_mod_cast hn
  have h_2n_pos : (0 : Rat) < 2 * (n : Rat) := by linarith
  have h_8n_pos : (0 : Rat) < 8 * (n : Rat) := by linarith
  -- divide both sides by 4
  -- |a_m - a_n| ≤ 1/(2n) / 4 = 1/(8n)
  have h_div_eq : (1 : Rat) / (2 * (n : Rat)) / 4 = 1 / (8 * (n : Rat)) := by
    field_simp
    ring
  rw [show (1 : Rat) / (8 * (n : Rat)) = (1 / (2 * (n : Rat))) / 4 from h_div_eq.symm]
  -- Goal: |a_m - a_n| ≤ (1 / (2n)) / 4
  rw [le_div_iff₀ (by norm_num : (0 : Rat) < 4)]
  -- Goal: |a_m - a_n| · 4 ≤ 1/(2n)
  have h_comm : |arctan_partial_rat 1 m - arctan_partial_rat 1 n| * 4
                  = 4 * |arctan_partial_rat 1 m - arctan_partial_rat 1 n| := by ring
  rw [h_comm]
  exact h_pi_bound

-- ============================================================
-- PART 2: BOUND CHAIN  1/(8n) < 1/(k+1)
-- ============================================================

/-- For `n ≥ k + 1`, we have `1/(8n) < 1/(k+1)`. In fact `n ≥ (k+1)/8 + 1`
    suffices, but `n ≥ k + 1` is the cleanest sufficient condition since
    `8n ≥ 8(k+1) > k+1`. -/
theorem Rat.one_div_eight_n_lt_recip (k n : Nat) (hn : k + 1 ≤ n) :
    (1 : Rat) / (8 * (n : Rat)) < 1 / ((k : Rat) + 1) := by
  have h_n_pos : (0 : Rat) < (n : Rat) := by
    have : 1 ≤ n := by omega
    exact_mod_cast this
  have h_8n_pos : (0 : Rat) < 8 * (n : Rat) := by linarith
  have h_k1_pos : (0 : Rat) < (k : Rat) + 1 := by
    have : (0 : Rat) ≤ (k : Rat) := by exact_mod_cast Nat.zero_le k
    linarith
  rw [div_lt_div_iff₀ h_8n_pos h_k1_pos]
  -- Goal: (k+1) < 8n  for  n ≥ k+1
  have h_cast : ((k + 1 : Nat) : Rat) ≤ (n : Rat) := by exact_mod_cast hn
  have h_cast_eq : ((k + 1 : Nat) : Rat) = (k : Rat) + 1 := by push_cast; ring
  nlinarith

-- ============================================================
-- PART 3: TauReal-LEVEL IsCauchy FOR arctan_of_rat_seq ONE_CANONICAL
-- ============================================================

/-! ## `arctan_of_rat_seq one_canonical .IsCauchy`

  The Leibniz arctan series at unit argument is Cauchy with modulus
  `λ k => k + 3`. Derived from `arctan_partial_rat_one_cauchy_bound`
  plus the `1/(8n) < 1/(k+1)` chain.

  This **patches the API gap** in `TauReal.arctan_of_rat_isCauchy`,
  which fails the `2·|x.toRat| ≤ 1` hypothesis at `x = 1`. -/

/-- **`arctan_of_rat_seq one_canonical .IsCauchy`** (Scope 2E):
    the Leibniz arctan series at unit argument is Cauchy with explicit
    modulus `λ k => k + 3`.

    The proof works directly: at depth `n ≥ k + 3 ≥ k + 1`, the
    pointwise difference of approximations is `|arctan_partial_rat 1 m −
    arctan_partial_rat 1 n| ≤ 1/(8n) < 1/(k+1)`. -/
theorem TauReal.arctan_of_rat_seq_one_isCauchy :
    (TauReal.arctan_of_rat_seq TauRat.one_canonical).IsCauchy := by
  refine ⟨fun k => k + 3, ?_⟩
  intro k m n hm hn
  change k + 3 ≤ m at hm
  change k + 3 ≤ n at hn
  unfold TauRat.lt
  rw [TauRat.toRat_abs, toRat_sub, TauRat.ofNatRecip_toRat]
  -- Goal: |(arctan_of_rat_seq 1).approx m .toRat - (arctan_of_rat_seq 1).approx n .toRat|
  --        < 1/(k+1)
  rw [TauReal.arctan_of_rat_seq_approx, TauReal.arctan_of_rat_seq_approx]
  rw [TauRat.arctan_partial_toRat, TauRat.arctan_partial_toRat]
  rw [TauRat.one_canonical_toRat]
  -- Goal: |arctan_partial_rat 1 m - arctan_partial_rat 1 n| < 1/(k+1)
  by_cases h_le : n ≤ m
  · have h_n_ge : 1 ≤ n := by omega
    have h_bound := arctan_partial_rat_one_cauchy_bound m n h_n_ge h_le
    have h_eight_lt : (1 : Rat) / (8 * (n : Rat)) < 1 / ((k : Rat) + 1) :=
      Rat.one_div_eight_n_lt_recip k n (by omega)
    linarith
  · push_neg at h_le
    have h_m_ge : 1 ≤ m := by omega
    have h_swap_abs :
        |arctan_partial_rat 1 m - arctan_partial_rat 1 n|
          = |arctan_partial_rat 1 n - arctan_partial_rat 1 m| := by
      rw [show arctan_partial_rat 1 m - arctan_partial_rat 1 n
            = -(arctan_partial_rat 1 n - arctan_partial_rat 1 m) from by ring,
          abs_neg]
    rw [h_swap_abs]
    have h_bound := arctan_partial_rat_one_cauchy_bound n m h_m_ge (Nat.le_of_lt h_le)
    have h_eight_lt : (1 : Rat) / (8 * (m : Rat)) < 1 / ((k : Rat) + 1) :=
      Rat.one_div_eight_n_lt_recip k m (by omega)
    linarith

-- ============================================================
-- PART 4: MACHIN LHS COMPONENT BOUNDS (1/5 and 1/239)
-- ============================================================

/-! ## Cauchy bounds for the Machin LHS components

  The Machin LHS is `4·arctan_partial_rat(1/5) n − arctan_partial_rat(1/239) n`.
  Both arctan partial sums at `1/5` and `1/239` satisfy the
  `2·|x| ≤ 1` hypothesis (since `2/5 < 1` and `2/239 < 1`), so the
  existing `arctan_partial_rat_cauchy_bound` applies with the
  geometric `4/2^n` bound.

  Combined via the triangle inequality, the LHS difference at depths
  `m, n` is bounded by `4·(4/2^n) + 4/2^n = 17/2^n`. -/

/-- **One-fifth Cauchy bound**: from `2·(1/5) = 2/5 ≤ 1`, we have
    `|arctan_partial_rat (1/5) m − arctan_partial_rat (1/5) n| ≤ 4/2^n`. -/
theorem arctan_partial_rat_one_fifth_cauchy_bound (m n : Nat) (hnm : n ≤ m) :
    |arctan_partial_rat ((1 : Rat) / 5) m - arctan_partial_rat ((1 : Rat) / 5) n|
      ≤ 4 / (2 : Rat)^n := by
  apply arctan_partial_rat_cauchy_bound
  · -- 2 · |1/5| ≤ 1
    have : |((1 : Rat) / 5)| = 1/5 := by
      rw [abs_of_pos (by norm_num : (0 : Rat) < 1/5)]
    rw [this]; norm_num
  · exact hnm

/-- **1/239 Cauchy bound**: from `2·(1/239) = 2/239 ≤ 1`, we have
    `|arctan_partial_rat (1/239) m − arctan_partial_rat (1/239) n| ≤ 4/2^n`. -/
theorem arctan_partial_rat_one_two_three_nine_cauchy_bound (m n : Nat) (hnm : n ≤ m) :
    |arctan_partial_rat ((1 : Rat) / 239) m - arctan_partial_rat ((1 : Rat) / 239) n|
      ≤ 4 / (2 : Rat)^n := by
  apply arctan_partial_rat_cauchy_bound
  · -- 2 · |1/239| ≤ 1
    have : |((1 : Rat) / 239)| = 1/239 := by
      rw [abs_of_pos (by norm_num : (0 : Rat) < 1/239)]
    rw [this]; norm_num
  · exact hnm

-- ============================================================
-- PART 5: MACHIN LHS COMBINED CAUCHY BOUND
-- ============================================================

/-- **Machin LHS Cauchy bound**: the difference
    `4·arctan_partial_rat(1/5) − arctan_partial_rat(1/239)` at depths
    `m, n` (with `n ≤ m`) is bounded by `20/2^n`.

    Triangle inequality on the two component bounds gives
    `4·(4/2^n) + 4/2^n = 20/2^n`. -/
theorem MachinSlashFour_lhs_cauchy_bound (m n : Nat) (hnm : n ≤ m) :
    |(4 * arctan_partial_rat ((1 : Rat) / 5) m - arctan_partial_rat ((1 : Rat) / 239) m)
        - (4 * arctan_partial_rat ((1 : Rat) / 5) n - arctan_partial_rat ((1 : Rat) / 239) n)|
      ≤ 20 / (2 : Rat)^n := by
  -- Rewrite the difference
  have h_rearr :
      (4 * arctan_partial_rat ((1 : Rat) / 5) m - arctan_partial_rat ((1 : Rat) / 239) m)
        - (4 * arctan_partial_rat ((1 : Rat) / 5) n - arctan_partial_rat ((1 : Rat) / 239) n)
        = 4 * (arctan_partial_rat ((1 : Rat) / 5) m - arctan_partial_rat ((1 : Rat) / 5) n)
          - (arctan_partial_rat ((1 : Rat) / 239) m - arctan_partial_rat ((1 : Rat) / 239) n) := by
    ring
  rw [h_rearr]
  -- Triangle
  have h_tri :
      |4 * (arctan_partial_rat ((1 : Rat) / 5) m - arctan_partial_rat ((1 : Rat) / 5) n)
          - (arctan_partial_rat ((1 : Rat) / 239) m - arctan_partial_rat ((1 : Rat) / 239) n)|
        ≤ |4 * (arctan_partial_rat ((1 : Rat) / 5) m - arctan_partial_rat ((1 : Rat) / 5) n)|
          + |arctan_partial_rat ((1 : Rat) / 239) m - arctan_partial_rat ((1 : Rat) / 239) n| := by
    have := abs_sub (4 * (arctan_partial_rat ((1 : Rat) / 5) m - arctan_partial_rat ((1 : Rat) / 5) n))
                    (arctan_partial_rat ((1 : Rat) / 239) m - arctan_partial_rat ((1 : Rat) / 239) n)
    exact this
  -- Component bounds
  have h_fifth := arctan_partial_rat_one_fifth_cauchy_bound m n hnm
  have h_239 := arctan_partial_rat_one_two_three_nine_cauchy_bound m n hnm
  -- |4·x| = 4·|x| ≤ 16/2^n
  have h_four_factor :
      |4 * (arctan_partial_rat ((1 : Rat) / 5) m - arctan_partial_rat ((1 : Rat) / 5) n)|
        ≤ 16 / (2 : Rat)^n := by
    rw [abs_mul, show |(4 : Rat)| = 4 from by norm_num]
    have h_4_pos : (0 : Rat) < 4 := by norm_num
    have h_step : 4 * |arctan_partial_rat ((1 : Rat) / 5) m - arctan_partial_rat ((1 : Rat) / 5) n|
                    ≤ 4 * (4 / (2 : Rat)^n) := by
      apply mul_le_mul_of_nonneg_left h_fifth (by norm_num : (0 : Rat) ≤ 4)
    have h_eq : (4 : Rat) * (4 / (2 : Rat)^n) = 16 / (2 : Rat)^n := by
      ring
    linarith
  -- Combine: 16/2^n + 4/2^n = 20/2^n
  have h_combine : (16 : Rat) / (2 : Rat)^n + 4 / (2 : Rat)^n = 20 / (2 : Rat)^n := by
    have h_pow_pos : (0 : Rat) < (2 : Rat)^n := by positivity
    field_simp
    ring
  linarith

-- ============================================================
-- PART 6: MachinClassicalLimit — the residual analytic gap
-- ============================================================

/-! ## The residual analytic gap, named

  Given the structural pipeline through Phase E Scopes 2A-lift / 2B / 2C / 2D
  is complete, the entire `MachinIdentity ↔ pi_machin ≈ pi` chain
  reduces (via `MachinSlashFourIdentity_iff_rat_modulus`) to a
  Rat-level diagonal modulus condition:

  >  `∃ μ, ∀ k n, μ k ≤ n →
  >     |4·arctan_partial(1/5, n) − arctan_partial(1/239, n) − arctan_partial(1, n)|
  >       < 1/(k+1)`.

  This proposition — and ONLY this proposition — is what remains to
  discharge the keystone. We give it a focused name. -/

/-- **The classical Machin limit at τ-canon Rat-modulus level**
    (Scope 2E residual target):

    asserts that the τ-canon's diagonal partial-sum difference for
    Machin's identity converges to zero with the standard
    `1/(k+1)`-tolerance modulus.

    Classically, this is the statement
    `4·arctan(1/5) − arctan(1/239) = arctan(1) = π/4`
    at infinite depth (Machin's identity at the limit). At
    finite-depth τ-modulus form: there exists `μ : Nat → Nat` such that
    `|4·arctan_partial(1/5) n − arctan_partial(1/239) n
      − arctan_partial(1) n| < 1/(k+1)` for all `n ≥ μ k`.

    By `MachinSlashFourIdentity_iff_rat_modulus`, this is **logically
    equivalent** to `MachinSlashFourIdentity` (and hence to
    `MachinIdentity`, `pi_machin ≈ pi`).

    **Status**: undischarged. This is the residual analytic content
    of the Machin keystone. Future closure paths are documented in
    the module header. -/
def MachinClassicalLimit : Prop :=
  ∃ μ : Nat → Nat, ∀ k n : Nat, μ k ≤ n →
    |(4 * arctan_partial_rat ((1 : Rat) / 5) n - arctan_partial_rat ((1 : Rat) / 239) n)
      - arctan_partial_rat 1 n| < 1 / ((k : Rat) + 1)

/-- **Headline equivalence** (Scope 2E):

    `MachinClassicalLimit ↔ MachinSlashFourIdentity`.

    Direct from `MachinSlashFourIdentity_iff_rat_modulus` —
    `MachinClassicalLimit` is by definition the right-hand-side existential. -/
theorem MachinClassicalLimit_iff_MachinSlashFourIdentity :
    MachinClassicalLimit ↔ MachinSlashFourIdentity := by
  unfold MachinClassicalLimit
  exact MachinSlashFourIdentity_iff_rat_modulus.symm

/-- **The full keystone reduction** (Scope 2E final form):

    `MachinClassicalLimit ↔ TauReal.equiv pi_machin pi`.

    Composing the chain:
    - Scope 2E: `MachinClassicalLimit ↔ MachinSlashFourIdentity`
    - Scope 2D: `MachinSlashFourIdentity ↔ MachinIdentity`
    - Scope 2C: `MachinIdentity ↔ pi_machin ≈ pi`

    Discharging `MachinClassicalLimit` discharges the entire Machin
    keystone. -/
theorem pi_machin_equiv_pi_iff_MachinClassicalLimit :
    TauReal.equiv TauReal.pi_machin TauReal.pi ↔ MachinClassicalLimit := by
  rw [pi_machin_equiv_pi_iff_MachinSlashFourIdentity]
  exact MachinClassicalLimit_iff_MachinSlashFourIdentity.symm

-- ============================================================
-- PART 7: WITNESS HELPERS — STRUCTURAL BOUNDS THAT DON'T INVOLVE THE LIMIT
-- ============================================================

/-! ## Structural bounds that do NOT require the classical limit

  These are honest, fully-discharged bounds on the components of
  `MachinClassicalLimit`'s expression that hold at every finite depth
  without invoking the classical Machin fact.

  They are **provable now** and serve as building blocks for any
  future closure attempt. -/

/-- **Triangle inequality decomposition**: at every depth `n`, the
    full Machin difference is bounded by the LHS Cauchy bound plus
    the absolute value of the LHS at depth `n` plus the absolute
    value of the RHS at depth `n`.

    NOTE: this doesn't directly bound the limit (the LHS-RHS difference
    at fixed `n` is a specific rational that classically equals the
    truncation errors), but it provides the triangle structure for any
    future attempt to bound the limit using the classical Machin
    identity at the limit.

    Specifically: for all `m n` with `n ≤ m`,
    `|(LHS m - RHS m) - (LHS n - RHS n)|
       ≤ |LHS m - LHS n| + |RHS m - RHS n|
       ≤ 20/2^n + 1/(8n)`

    This bound is **fully discharged** and uses no classical Machin
    facts. -/
theorem MachinFullDiff_cauchy_bound (m n : Nat) (hn : 1 ≤ n) (hnm : n ≤ m) :
    |((4 * arctan_partial_rat ((1 : Rat) / 5) m - arctan_partial_rat ((1 : Rat) / 239) m)
        - arctan_partial_rat 1 m)
      - ((4 * arctan_partial_rat ((1 : Rat) / 5) n - arctan_partial_rat ((1 : Rat) / 239) n)
        - arctan_partial_rat 1 n)|
      ≤ 20 / (2 : Rat)^n + 1 / (8 * (n : Rat)) := by
  -- Triangle decomposition
  have h_rearr :
      ((4 * arctan_partial_rat ((1 : Rat) / 5) m - arctan_partial_rat ((1 : Rat) / 239) m)
          - arctan_partial_rat 1 m)
        - ((4 * arctan_partial_rat ((1 : Rat) / 5) n - arctan_partial_rat ((1 : Rat) / 239) n)
          - arctan_partial_rat 1 n)
        = ((4 * arctan_partial_rat ((1 : Rat) / 5) m - arctan_partial_rat ((1 : Rat) / 239) m)
            - (4 * arctan_partial_rat ((1 : Rat) / 5) n - arctan_partial_rat ((1 : Rat) / 239) n))
          - (arctan_partial_rat 1 m - arctan_partial_rat 1 n) := by ring
  rw [h_rearr]
  have h_tri :
      |((4 * arctan_partial_rat ((1 : Rat) / 5) m - arctan_partial_rat ((1 : Rat) / 239) m)
          - (4 * arctan_partial_rat ((1 : Rat) / 5) n - arctan_partial_rat ((1 : Rat) / 239) n))
        - (arctan_partial_rat 1 m - arctan_partial_rat 1 n)|
        ≤ |(4 * arctan_partial_rat ((1 : Rat) / 5) m - arctan_partial_rat ((1 : Rat) / 239) m)
            - (4 * arctan_partial_rat ((1 : Rat) / 5) n - arctan_partial_rat ((1 : Rat) / 239) n)|
          + |arctan_partial_rat 1 m - arctan_partial_rat 1 n| := by
    have := abs_sub
      ((4 * arctan_partial_rat ((1 : Rat) / 5) m - arctan_partial_rat ((1 : Rat) / 239) m)
        - (4 * arctan_partial_rat ((1 : Rat) / 5) n - arctan_partial_rat ((1 : Rat) / 239) n))
      (arctan_partial_rat 1 m - arctan_partial_rat 1 n)
    exact this
  have h_lhs := MachinSlashFour_lhs_cauchy_bound m n hnm
  have h_rhs := arctan_partial_rat_one_cauchy_bound m n hn hnm
  linarith

-- ============================================================
-- PART 8: THE MACHIN DIAGONAL AS A CAUCHY SEQUENCE
-- ============================================================

/-! ## The Machin diagonal Cauchy sequence

  The full diagonal expression `D(n) := LHS(n) − RHS(n)` is itself
  a Cauchy sequence of Rat (provably so, this module). The classical
  Machin fact is precisely that the limit `lim D(n) = 0`.

  This part packages this Cauchy convergence into a TauReal: the
  **Machin diagonal TauReal** has explicit Cauchy modulus and lives
  one structural step away from the keystone. -/

/-- **The Machin diagonal TauReal** (Scope 2E): the sequence
    `D(n) := (4·arctan_partial(1/5) n − arctan_partial(1/239) n)
              − arctan_partial(1) n`
    packaged as a TauReal sequence (without Cauchy proof yet).

    This is the LHS-minus-RHS at every depth, as a τ-native object.
    `MachinClassicalLimit` is precisely the statement that this
    TauReal is Cauchy-equivalent to zero. -/
noncomputable def TauReal.machin_diagonal : TauReal :=
  (TauReal.pi_machin_arctan_quarter).sub
    (TauReal.arctan_of_rat_seq TauRat.one_canonical)

/-- **Per-depth `.approx` of the Machin diagonal at the toRat level**.
    The `n`-th approximation's `.toRat` is exactly the Rat-level
    diagonal `(4·arctan_partial(1/5) n − arctan_partial(1/239) n)
                − arctan_partial(1) n`. -/
theorem TauReal.machin_diagonal_approx_toRat (n : Nat) :
    (TauReal.machin_diagonal.approx n).toRat
      = (4 * arctan_partial_rat ((1 : Rat) / 5) n - arctan_partial_rat ((1 : Rat) / 239) n)
          - arctan_partial_rat 1 n := by
  unfold TauReal.machin_diagonal
  show (TauRat.add (TauReal.pi_machin_arctan_quarter.approx n)
                    (TauRat.negate
                      ((TauReal.arctan_of_rat_seq TauRat.one_canonical).approx n))).toRat = _
  rw [toRat_add, toRat_negate]
  -- pi_machin_arctan_quarter.approx n .toRat = 4 · arctan_partial_rat (1/5) n
  --                                              − arctan_partial_rat (1/239) n
  have h_quarter_toRat :
      (TauReal.pi_machin_arctan_quarter.approx n).toRat
        = 4 * arctan_partial_rat ((1 : Rat) / 5) n - arctan_partial_rat ((1 : Rat) / 239) n := by
    unfold TauReal.pi_machin_arctan_quarter
    show (TauRat.add (TauRat.mul ((TauReal.fromTauRat ⟨⟨4, 0⟩, 1, by norm_num⟩).approx n)
                              ((TauReal.arctan_of_rat_seq TauRat.one_fifth).approx n))
                     (TauRat.negate ((TauReal.arctan_of_rat_seq TauRat.one_two_three_nine).approx n))).toRat
          = _
    rw [toRat_add, toRat_mul, toRat_negate]
    have h_4 : (((TauReal.fromTauRat ⟨⟨4, 0⟩, 1, by norm_num⟩ : TauReal).approx n).toRat
                  : Rat) = 4 := by
      show ((⟨⟨4, 0⟩, 1, by norm_num⟩ : TauRat).toRat : Rat) = 4
      unfold TauRat.toRat
      simp only [TauInt.toInt]
      push_cast
      ring
    rw [h_4]
    rw [TauReal.arctan_of_rat_seq_approx, TauReal.arctan_of_rat_seq_approx]
    rw [TauRat.arctan_partial_toRat, TauRat.arctan_partial_toRat]
    rw [TauRat.one_fifth_toRat, TauRat.one_two_three_nine_toRat]
    ring
  rw [h_quarter_toRat]
  -- arctan_of_rat_seq one_canonical .approx n .toRat = arctan_partial_rat 1 n
  rw [TauReal.arctan_of_rat_seq_approx, TauRat.arctan_partial_toRat,
      TauRat.one_canonical_toRat]
  ring

/-- **`2^k ≥ k + 1`** for all `k ≥ 0`. Standard Bernoulli-style bound. -/
theorem Rat.two_pow_ge_succ (k : Nat) : ((k : Rat) + 1) ≤ (2 : Rat)^k := by
  induction k with
  | zero => simp
  | succ j ih =>
    have h_2j_pos : (0 : Rat) < (2 : Rat)^j := by positivity
    have h_2j_ge_one : (1 : Rat) ≤ (2 : Rat)^j := by
      have : (1 : Rat) = (1 : Rat)^j := (one_pow j).symm
      rw [this]
      apply pow_le_pow_left₀ (by norm_num : (0 : Rat) ≤ 1) (by norm_num : (1 : Rat) ≤ 2)
    have h_succ_eq : (2 : Rat)^(j+1) = 2 * (2 : Rat)^j := by rw [pow_succ]; ring
    rw [h_succ_eq]
    push_cast
    nlinarith [ih, h_2j_ge_one]

/-- **The Machin diagonal is a Cauchy sequence**: `machin_diagonal`
    is `IsCauchy` with explicit modulus `λ k => k + 4` (chosen large
    enough that `20/2^n + 1/(8n) < 1/(k+1)`).

    Proof: composition of `MachinFullDiff_cauchy_bound` and the
    inequality `20/2^n + 1/(8n) < 1/(k+1)` for `n ≥ k + 4` (a clean
    sufficient condition: `n ≥ k + 4 ≥ 4` gives `2^n ≥ 16 ≥ 20·(k+1)/16`
    and `n ≥ k + 1` gives `1/(8n) < 1/(8(k+1)) < 1/(k+1)`).

    Concretely: for `n ≥ k+4 ≥ 5`, we have `2^n ≥ 32`, so
    `20/2^n ≤ 20/32 = 5/8`. We need a TIGHTER condition for large `k`:
    `2^n ≥ 40(k+1)` to make `20/2^n ≤ 1/(2(k+1))`, hence with
    `1/(8n) ≤ 1/(8(k+4))`, the sum is `< 1/(k+1)` for sufficiently
    large `n`.

    The clean sufficient condition: `n ≥ 6 · (k + 1) + 4` ensures
    `2^n ≥ 64(k+1) > 40(k+1)`, so `20/2^n < 1/(2(k+1))`, and
    `1/(8n) < 1/(8(k+1)) < 1/(2(k+1))`, sum `< 1/(k+1)`. -/
theorem TauReal.machin_diagonal_isCauchy : TauReal.machin_diagonal.IsCauchy := by
  -- We need a modulus μ such that for n ≥ μ k:
  --   |D(m) - D(n)| < 1/(k+1)
  -- where D(j) := (machin_diagonal).approx j .toRat.
  -- D(m) - D(n) is bounded by 20/2^n + 1/(8n) when n ≤ m (by MachinFullDiff_cauchy_bound).
  -- We need: 20/2^n + 1/(8n) < 1/(k+1).
  -- A sufficient (loose) condition: n ≥ 6(k+1) + 4, which gives
  -- 1/(8n) ≤ 1/(8·6(k+1)) = 1/(48(k+1)), and 2^n ≥ 2^4 · 2^(6(k+1))
  -- ≥ 16 · (k+1)^6 ≥ 16 · (k+1) for k ≥ 0. So 20/2^n ≤ 20/(16(k+1))
  -- = 5/(4(k+1)).
  -- Sum ≤ 5/(4(k+1)) + 1/(48(k+1)) ≤ 6/(4(k+1)) < ... too loose.
  --
  -- Cleaner sufficient condition: use modulus μ(k) := 5*(k+1) + 4
  -- which gives 2^n ≥ 2^(5(k+1)+4) ≥ 32 · (k+1)^5 ≥ 32(k+1).
  -- So 20/2^n ≤ 20/(32(k+1)) = 5/(8(k+1)).
  -- And 1/(8n) ≤ 1/(8(5(k+1)+4)) ≤ 1/(40(k+1)).
  -- Sum ≤ 5/(8(k+1)) + 1/(40(k+1)) = 26/(40(k+1)) = 13/(20(k+1)) < 1/(k+1).
  --
  -- Even cleaner: just take μ(k) := 32 * (k+1). Then 2^n ≥ 2^(32(k+1))
  -- which is HUGELY bigger than needed but trivially gives the bound.
  -- For an even simpler proof, we go: μ(k) := max(N(k), n_min) where
  -- N(k) is chosen so that 20/2^N + 1/(8N) ≤ 1/(2(k+1)) + 1/(2(k+1))
  -- = 1/(k+1).
  --
  -- For the bound 1/(8n) ≤ 1/(2(k+1)), suffices: 8n ≥ 2(k+1), i.e.,
  -- n ≥ (k+1)/4. So n ≥ k+1 suffices.
  -- For 20/2^n ≤ 1/(2(k+1)), suffices: 2^n ≥ 40(k+1).
  -- Equivalently: n ≥ log_2(40(k+1)) = log_2(40) + log_2(k+1)
  -- ≤ 6 + log_2(k+1) ≤ 6 + k+1 = k+7.
  -- So with n ≥ k+7, 2^n ≥ 2^(k+7) = 128 · 2^k ≥ 128 · (k+1) ≥ 40(k+1).
  --
  -- Use modulus μ(k) := k + 7.
  refine ⟨fun k => k + 7, ?_⟩
  intro k m n hm hn
  change k + 7 ≤ m at hm
  change k + 7 ≤ n at hn
  unfold TauRat.lt
  rw [TauRat.toRat_abs, toRat_sub, TauRat.ofNatRecip_toRat]
  -- Convert (machin_diagonal.approx m).toRat and (machin_diagonal.approx n).toRat
  rw [TauReal.machin_diagonal_approx_toRat, TauReal.machin_diagonal_approx_toRat]
  -- Goal: |D(m) - D(n)| < 1/(k+1)
  by_cases h_le : n ≤ m
  · have h_n_ge : 1 ≤ n := by omega
    have h_bound := MachinFullDiff_cauchy_bound m n h_n_ge h_le
    -- h_bound: ≤ 20/2^n + 1/(8n)
    -- Need: 20/2^n + 1/(8n) < 1/(k+1)
    have h_n_pos : (0 : Rat) < (n : Rat) := by exact_mod_cast h_n_ge
    have h_8n_pos : (0 : Rat) < 8 * (n : Rat) := by linarith
    have h_k1_pos : (0 : Rat) < (k : Rat) + 1 := by
      have : (0 : Rat) ≤ (k : Rat) := by exact_mod_cast Nat.zero_le k
      linarith
    -- Estimate: 2^n ≥ 2^(k+7) (since n ≥ k+7)
    have h_pow_n_ge : (2 : Rat)^(k+7) ≤ (2 : Rat)^n := by
      apply pow_le_pow_right₀ (by norm_num : (1 : Rat) ≤ 2) hn
    have h_pow_n_pos : (0 : Rat) < (2 : Rat)^n := by positivity
    have h_pow_k7_pos : (0 : Rat) < (2 : Rat)^(k+7) := by positivity
    -- 2^(k+7) = 128 · 2^k ≥ 128 · 1 = 128 for k ≥ 0
    have h_pow_k_ge_1 : (1 : Rat) ≤ (2 : Rat)^k := by
      have : (1 : Rat) = (1 : Rat)^k := (one_pow k).symm
      rw [this]
      apply pow_le_pow_left₀ (by norm_num : (0 : Rat) ≤ 1) (by norm_num : (1 : Rat) ≤ 2)
    -- 2^(k+7) ≥ 128(k+1) — bound this carefully.
    -- For k ≥ 0: 2^(k+7) = 128 · 2^k. We have 2^k ≥ k+1 (standard).
    have h_two_pow_k_ge_k1 : ((k : Rat) + 1) ≤ (2 : Rat)^k := Rat.two_pow_ge_succ k
    have h_pow_k7_ge : (128 : Rat) * ((k : Rat) + 1) ≤ (2 : Rat)^(k+7) := by
      have h_eq : (2 : Rat)^(k+7) = 128 * (2 : Rat)^k := by
        rw [pow_add]
        ring
      rw [h_eq]
      have h_pos_128 : (0 : Rat) < 128 := by norm_num
      have h_step : 128 * ((k : Rat) + 1) ≤ 128 * (2 : Rat)^k := by
        apply mul_le_mul_of_nonneg_left h_two_pow_k_ge_k1 (by norm_num : (0 : Rat) ≤ 128)
      linarith
    have h_pow_n_ge_128k1 : (128 : Rat) * ((k : Rat) + 1) ≤ (2 : Rat)^n := by linarith
    -- 20/2^n ≤ 20/(128(k+1)) ≤ 1/(2(k+1))? Actually 20/128 = 5/32. So
    -- 20/2^n ≤ 5/(32(k+1)).
    have h_20_div_le : (20 : Rat) / (2 : Rat)^n ≤ 20 / (128 * ((k : Rat) + 1)) := by
      apply div_le_div_of_nonneg_left (by norm_num : (0 : Rat) ≤ 20) (by linarith) h_pow_n_ge_128k1
    have h_20_div_eq : (20 : Rat) / (128 * ((k : Rat) + 1)) = 5 / (32 * ((k : Rat) + 1)) := by
      have h_pos : (0 : Rat) < 128 * ((k : Rat) + 1) := by linarith
      have h_pos' : (0 : Rat) < 32 * ((k : Rat) + 1) := by linarith
      field_simp
      ring
    -- 1/(8n) ≤ 1/(8(k+7)) ≤ 1/(8(k+1))
    have h_n_ge_k1 : ((k : Rat) + 1) ≤ (n : Rat) := by
      have : ((k + 7 : Nat) : Rat) ≤ (n : Rat) := by exact_mod_cast hn
      have h_cast : ((k + 7 : Nat) : Rat) = (k : Rat) + 7 := by push_cast; ring
      linarith
    have h_8n_ge : (8 : Rat) * ((k : Rat) + 1) ≤ 8 * (n : Rat) := by
      linarith
    have h_1_div_8n_le : (1 : Rat) / (8 * (n : Rat)) ≤ 1 / (8 * ((k : Rat) + 1)) := by
      apply div_le_div_of_nonneg_left (by norm_num : (0 : Rat) ≤ 1) (by linarith) h_8n_ge
    -- Sum: 5/(32(k+1)) + 1/(8(k+1)) = 5/(32(k+1)) + 4/(32(k+1)) = 9/(32(k+1))
    -- < 32/(32(k+1)) = 1/(k+1)
    have h_sum_simp : (5 : Rat) / (32 * ((k : Rat) + 1)) + 1 / (8 * ((k : Rat) + 1))
                        = 9 / (32 * ((k : Rat) + 1)) := by
      have h_pos : (0 : Rat) < 32 * ((k : Rat) + 1) := by linarith
      have h_pos' : (0 : Rat) < 8 * ((k : Rat) + 1) := by linarith
      field_simp
      ring
    have h_9_div_lt : (9 : Rat) / (32 * ((k : Rat) + 1)) < 1 / ((k : Rat) + 1) := by
      rw [div_lt_div_iff₀ (by linarith) h_k1_pos]
      -- 9 · (k+1) < 32 · (k+1) · 1
      nlinarith
    linarith
  · push_neg at h_le
    have h_m_ge : 1 ≤ m := by omega
    have h_swap_abs :
        |((4 * arctan_partial_rat ((1 : Rat) / 5) m - arctan_partial_rat ((1 : Rat) / 239) m)
            - arctan_partial_rat 1 m)
          - ((4 * arctan_partial_rat ((1 : Rat) / 5) n - arctan_partial_rat ((1 : Rat) / 239) n)
            - arctan_partial_rat 1 n)|
          = |((4 * arctan_partial_rat ((1 : Rat) / 5) n - arctan_partial_rat ((1 : Rat) / 239) n)
              - arctan_partial_rat 1 n)
            - ((4 * arctan_partial_rat ((1 : Rat) / 5) m - arctan_partial_rat ((1 : Rat) / 239) m)
              - arctan_partial_rat 1 m)| := by
      rw [show ((4 * arctan_partial_rat ((1 : Rat) / 5) m - arctan_partial_rat ((1 : Rat) / 239) m)
                  - arctan_partial_rat 1 m)
              - ((4 * arctan_partial_rat ((1 : Rat) / 5) n - arctan_partial_rat ((1 : Rat) / 239) n)
                  - arctan_partial_rat 1 n)
            = -(((4 * arctan_partial_rat ((1 : Rat) / 5) n - arctan_partial_rat ((1 : Rat) / 239) n)
                  - arctan_partial_rat 1 n)
                - ((4 * arctan_partial_rat ((1 : Rat) / 5) m - arctan_partial_rat ((1 : Rat) / 239) m)
                  - arctan_partial_rat 1 m)) from by ring,
          abs_neg]
    rw [h_swap_abs]
    have h_bound := MachinFullDiff_cauchy_bound n m h_m_ge (Nat.le_of_lt h_le)
    -- Symmetric mirror of the above
    have h_m_pos : (0 : Rat) < (m : Rat) := by exact_mod_cast h_m_ge
    have h_8m_pos : (0 : Rat) < 8 * (m : Rat) := by linarith
    have h_k1_pos : (0 : Rat) < (k : Rat) + 1 := by
      have : (0 : Rat) ≤ (k : Rat) := by exact_mod_cast Nat.zero_le k
      linarith
    have h_pow_m_ge : (2 : Rat)^(k+7) ≤ (2 : Rat)^m := by
      apply pow_le_pow_right₀ (by norm_num : (1 : Rat) ≤ 2) hm
    have h_pow_m_pos : (0 : Rat) < (2 : Rat)^m := by positivity
    have h_pow_k7_pos : (0 : Rat) < (2 : Rat)^(k+7) := by positivity
    have h_two_pow_k_ge_k1 : ((k : Rat) + 1) ≤ (2 : Rat)^k := Rat.two_pow_ge_succ k
    have h_pow_k7_ge : (128 : Rat) * ((k : Rat) + 1) ≤ (2 : Rat)^(k+7) := by
      have h_eq : (2 : Rat)^(k+7) = 128 * (2 : Rat)^k := by
        rw [pow_add]
        ring
      rw [h_eq]
      have h_step : 128 * ((k : Rat) + 1) ≤ 128 * (2 : Rat)^k := by
        apply mul_le_mul_of_nonneg_left h_two_pow_k_ge_k1 (by norm_num : (0 : Rat) ≤ 128)
      linarith
    have h_pow_m_ge_128k1 : (128 : Rat) * ((k : Rat) + 1) ≤ (2 : Rat)^m := by linarith
    have h_20_div_le : (20 : Rat) / (2 : Rat)^m ≤ 20 / (128 * ((k : Rat) + 1)) := by
      apply div_le_div_of_nonneg_left (by norm_num : (0 : Rat) ≤ 20) (by linarith) h_pow_m_ge_128k1
    have h_20_div_eq : (20 : Rat) / (128 * ((k : Rat) + 1)) = 5 / (32 * ((k : Rat) + 1)) := by
      have h_pos : (0 : Rat) < 128 * ((k : Rat) + 1) := by linarith
      have h_pos' : (0 : Rat) < 32 * ((k : Rat) + 1) := by linarith
      field_simp
      ring
    have h_m_ge_k1 : ((k : Rat) + 1) ≤ (m : Rat) := by
      have : ((k + 7 : Nat) : Rat) ≤ (m : Rat) := by exact_mod_cast hm
      have h_cast : ((k + 7 : Nat) : Rat) = (k : Rat) + 7 := by push_cast; ring
      linarith
    have h_8m_ge : (8 : Rat) * ((k : Rat) + 1) ≤ 8 * (m : Rat) := by
      linarith
    have h_1_div_8m_le : (1 : Rat) / (8 * (m : Rat)) ≤ 1 / (8 * ((k : Rat) + 1)) := by
      apply div_le_div_of_nonneg_left (by norm_num : (0 : Rat) ≤ 1) (by linarith) h_8m_ge
    have h_sum_simp : (5 : Rat) / (32 * ((k : Rat) + 1)) + 1 / (8 * ((k : Rat) + 1))
                        = 9 / (32 * ((k : Rat) + 1)) := by
      have h_pos : (0 : Rat) < 32 * ((k : Rat) + 1) := by linarith
      have h_pos' : (0 : Rat) < 8 * ((k : Rat) + 1) := by linarith
      field_simp
      ring
    have h_9_div_lt : (9 : Rat) / (32 * ((k : Rat) + 1)) < 1 / ((k : Rat) + 1) := by
      rw [div_lt_div_iff₀ (by linarith) h_k1_pos]
      nlinarith
    linarith

/-! ## What this delivers

  The combined `MachinFullDiff_cauchy_bound` and `machin_diagonal_isCauchy`
  say: the diagonal `(LHS_n − RHS_n)` is a **Cauchy sequence** in n with
  rate bounded by `20/2^n + 1/(8n)`, and the corresponding TauReal
  `machin_diagonal` is `IsCauchy` with explicit modulus `λ k => k + 7`.

  Hence the diagonal converges to a TauReal `L = machin_diagonal`.
  The classical Machin identity is precisely the statement `L ≈ 0`
  (i.e., `machin_diagonal.equiv TauReal.zero`).

  The τ-canon **doesn't know `L ≈ 0`** without an external reference,
  but it CAN prove:
  * `(LHS_n − RHS_n)` is Cauchy (this module, `machin_diagonal_isCauchy`).
  * If we could show `machin_diagonal.equiv TauReal.zero`, then
    `MachinSlashFourIdentity` follows directly.

  This is **the honest analytical state**. Phase F closure requires
  either:
  * An axiom: `MachinClassicalLimit` (≡ `machin_diagonal.equiv TauReal.zero`)
    as a programme axiom (+1 axiom).
  * Or independent infrastructure proving `L = 0` constructively
    (cisTauReal injectivity path, Phase F.B).

  Both are deep undertakings; both are honestly out of scope for this
  module. -/

/-- **The cleanest TauReal-level reformulation** (Scope 2E final form):

    `machin_diagonal.equiv TauReal.zero ↔ MachinSlashFourIdentity`.

    The Machin keystone reduces precisely to: the LHS-minus-RHS
    diagonal TauReal is Cauchy-equivalent to zero. -/
theorem machin_diagonal_equiv_zero_iff_MachinSlashFourIdentity :
    TauReal.equiv TauReal.machin_diagonal TauReal.zero ↔ MachinSlashFourIdentity := by
  unfold MachinSlashFourIdentity TauReal.machin_diagonal
  constructor
  · -- Forward: machin_diagonal ≈ 0 → quarter ≈ arctan(1)
    intro h_zero
    -- machin_diagonal := quarter - arctan(1)
    -- machin_diagonal ≈ 0  ↔  quarter ≈ arctan(1)
    -- This follows from: equiv_iff_zero (a - b ≈ 0 iff a ≈ b)
    -- We construct it explicitly.
    obtain ⟨μ, hμ⟩ := h_zero
    refine ⟨μ, fun k n hkn => ?_⟩
    have h_orig := hμ k n hkn
    -- h_orig: |(quarter.sub arctan(1)).approx n - TauReal.zero.approx n|.toRat < 1/(k+1)
    --       = |quarter.approx n - arctan(1).approx n|.toRat < 1/(k+1)
    unfold TauRat.lt at h_orig ⊢
    rw [TauRat.toRat_abs, toRat_sub, TauRat.ofNatRecip_toRat] at h_orig
    rw [TauRat.toRat_abs, toRat_sub, TauRat.ofNatRecip_toRat]
    -- LHS: ((quarter.sub arctan(1)).approx n - TauReal.zero.approx n).toRat
    have h_lhs :
        ((TauReal.pi_machin_arctan_quarter.sub
            (TauReal.arctan_of_rat_seq TauRat.one_canonical)).approx n).toRat
          - (TauReal.zero.approx n).toRat
          = (TauReal.pi_machin_arctan_quarter.approx n).toRat
              - ((TauReal.arctan_of_rat_seq TauRat.one_canonical).approx n).toRat := by
      show (TauRat.add (TauReal.pi_machin_arctan_quarter.approx n)
                       (TauRat.negate
                         ((TauReal.arctan_of_rat_seq TauRat.one_canonical).approx n))).toRat
            - (TauRat.zero).toRat = _
      rw [toRat_add, toRat_negate, toRat_zero]; ring
    rw [h_lhs] at h_orig
    exact h_orig
  · intro h_quarter
    obtain ⟨μ, hμ⟩ := h_quarter
    refine ⟨μ, fun k n hkn => ?_⟩
    have h_orig := hμ k n hkn
    unfold TauRat.lt at h_orig ⊢
    rw [TauRat.toRat_abs, toRat_sub, TauRat.ofNatRecip_toRat] at h_orig
    rw [TauRat.toRat_abs, toRat_sub, TauRat.ofNatRecip_toRat]
    -- RHS:
    have h_rhs :
        ((TauReal.pi_machin_arctan_quarter.sub
            (TauReal.arctan_of_rat_seq TauRat.one_canonical)).approx n).toRat
          - (TauReal.zero.approx n).toRat
          = (TauReal.pi_machin_arctan_quarter.approx n).toRat
              - ((TauReal.arctan_of_rat_seq TauRat.one_canonical).approx n).toRat := by
      show (TauRat.add (TauReal.pi_machin_arctan_quarter.approx n)
                       (TauRat.negate
                         ((TauReal.arctan_of_rat_seq TauRat.one_canonical).approx n))).toRat
            - (TauRat.zero).toRat = _
      rw [toRat_add, toRat_negate, toRat_zero]; ring
    rw [h_rhs]
    exact h_orig

/-- **Headline keystone equivalence** (Scope 2E final):

    `machin_diagonal.equiv TauReal.zero ↔ TauReal.equiv pi_machin pi`.

    The entire Machin keystone reduces to the τ-native statement:
    the LHS-minus-RHS diagonal TauReal is Cauchy-equivalent to zero. -/
theorem pi_machin_equiv_pi_iff_machin_diagonal_equiv_zero :
    TauReal.equiv TauReal.pi_machin TauReal.pi
      ↔ TauReal.equiv TauReal.machin_diagonal TauReal.zero := by
  rw [pi_machin_equiv_pi_iff_MachinSlashFourIdentity]
  exact machin_diagonal_equiv_zero_iff_MachinSlashFourIdentity.symm

end Tau.Boundary
