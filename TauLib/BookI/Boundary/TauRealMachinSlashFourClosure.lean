import TauLib.BookI.Boundary.TauRealCisInjectivity
import TauLib.BookI.Boundary.TauRealArctanOneLeibniz
import Mathlib.Tactic.Ring
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.IntervalCases

/-!
# TauLib.BookI.Boundary.TauRealMachinSlashFourClosure

**Phase F.B.1 — structural closure of MachinSlashFourIdentity via F.B.0**.
**Phase F.C — structural reduction of `MachinDiagonalBoundedHalf`**.
**Phase F.C.1 — finite-arithmetic discharge of `MachinDiagonalBoundedHalf`**.

After Phase F.B.0 (`TauRealCisInjectivity.lean`) shipped the foundational
`cisTauReal_injectivity_at_zero` lemma and Phase E Scope 2E
(`TauRealArctanOneLeibniz.lean`) shipped the `machin_diagonal` TauReal
with the equivalence

> `machin_diagonal ≈ TauReal.zero ↔ MachinSlashFourIdentity`

this module composes these into the **conditional discharge route**: given
two named hypotheses about `machin_diagonal`, `MachinSlashFourIdentity`
(and hence the whole keystone chain `MachinIdentity`, `pi_machin ≈ pi`,
`MachinClassicalLimit`) follows.

With Phase F.C.1 (Part 9, this module), `MachinDiagonalBoundedHalf` is
now a full theorem (no hypothesis), discharged by composing the
structural reduction (`MachinDiagonalBoundedHalf_via_N20`) with finite
Rat-arithmetic checks at depths `0..20`. The entire keystone chain now
reduces to a SINGLE residual hypothesis: `CisMachinDiagonalImEquivZero`.

## What this module ships

* **`arctan_partial_rat_one_nonneg`** — for all `n`,
  `0 ≤ arctan_partial_rat 1 n` (since each pair_term at `x = 1` is the
  positive `(1/(4k+1) − 1/(4k+3))`, and the partial sums are sums of
  positives starting at `0`).

* **`arctan_partial_rat_one_le_19_over_24`** — for all `n`,
  `arctan_partial_rat 1 n ≤ 19/24`. Derived via the `pi_partial` bridge
  identity (`pi_partial n .toRat = 4 · arctan_partial_rat 1 n`) plus
  the telescoping sum bound `sumFromTo pi_pair_term 1 m ≤ 1/2`, giving
  `pi_partial m ≤ pi_partial 1 + 1/2 = 8/3 + 1/2 = 19/6` for `m ≥ 1`,
  hence `arctan_partial_rat 1 m ≤ 19/24 < 1` for `m ≥ 1`. At `m = 0`,
  `arctan_partial_rat 1 0 = 0 ≤ 19/24` trivially.

* **`arctan_partial_rat_one_abs_le_one`** — combining nonneg + 19/24
  upper bound, `|arctan_partial_rat 1 n| ≤ 1` for all `n`. This is the
  τ-canon's incarnation of `arctan(1) = π/4 < 1` at the partial-sum level,
  proved without any classical analysis.

* **`MachinSlashFourIdentity_via_machin_diagonal_FB0`** — the **headline
  conditional theorem**: if
    (a) `∀ n, ((machin_diagonal.approx n).abs).toRat ≤ 1/2` (principal-branch
        bound on the τ-native Machin diagonal at every depth), AND
    (b) `(cisTauReal machin_diagonal).im ≈ TauReal.zero` (the imaginary
        leg of `cis(D)` vanishes — equivalent classically to `sin(D) = 0`),
  then `MachinSlashFourIdentity` holds.

  Proof: by F.B.0 (`cisTauReal_injectivity_at_zero` applied to
  `machin_diagonal`), the hypotheses give `machin_diagonal ≈ TauReal.zero`.
  By Scope 2E's `machin_diagonal_equiv_zero_iff_MachinSlashFourIdentity`,
  this is logically equivalent to `MachinSlashFourIdentity`.

* **`pi_machin_equiv_pi_via_FB0`** — direct corollary chaining through
  the full Scope 2C/2D/2E reduction chain: under the same two hypotheses,
  `TauReal.equiv pi_machin pi` (the original Wave Γ₇ Phase 3F target).

* **`MachinIdentity_via_FB0`** — same content phrased as the named target
  `MachinIdentity`.

* **`MachinClassicalLimit_via_FB0`** — same content phrased as the named
  target `MachinClassicalLimit` (the Rat-level diagonal modulus existence).

## Phase F.C — structural reduction of MachinDiagonalBoundedHalf

The headline Phase F.C contribution is a **structural reduction** of
`MachinDiagonalBoundedHalf` to a finite small-`n` check:

* **`machin_diagonal_tail_bound`** — Cauchy-tail bound: for `N₀ ≤ n`,
  `|D(n)| ≤ |D(N₀)| + 20/2^N₀ + 1/(8·N₀)` (composes
  `MachinFullDiff_cauchy_bound` with the triangle inequality).

* **`MachinDiagonalBoundedHalf_from_basecase_at_depth`** — the headline
  structural-reduction theorem: given a strong base-case
  `|D(N₀)| ≤ 1/2 − 20/2^N₀ − 1/(8·N₀)` plus a finite check at depths
  `0..N₀ − 1`, conclude `MachinDiagonalBoundedHalf` for ALL `n`.

* **`MachinDiagonalBoundedHalf_via_N20` / `..._via_N30`** — specialized
  forms at canonical depths `N₀ ∈ {20, 30}`, with hard-baked numerical
  slack witnesses (`tail(20) ≤ 1/159`, `tail(30) ≤ 1/239`).

* **`pi_machin_equiv_pi_via_N20_route` / `..._via_N30_route`** —
  composite keystone bridges: composing the structural reduction with
  `pi_machin_equiv_pi_iff_FB0_hypotheses`, the keystone `pi_machin ≈ pi`
  reduces to a (small-`n` finite Rat check) ∧ (strong base-case) ∧
  `CisMachinDiagonalImEquivZero`.

This is the cleanest constructive structural decomposition of the
remaining keystone gap. The structural reduction does NOT invoke any
classical (limit/derivative) content — it composes the already-shipped
`MachinFullDiff_cauchy_bound` with the triangle inequality at the
Rat-arithmetic level.

## Significance — what the residual gap is

After Phase F.C.1, **`MachinDiagonalBoundedHalf` is a full theorem**
(Part 9 below). The entire keystone chain reduces to a SINGLE residual
TauReal proposition:

* **`CisMachinDiagonalImEquivZero`**: `(cisTauReal machin_diagonal).im ≈ TauReal.zero`.

Classical proof sketch of this (NOT formalised here):
* The 45°-line identity at TauReal-equiv level (Scope 2A-lift for
  `α = pi_machin_arctan_quarter`) plus an analogous identity at
  `β = arctan_of_rat_seq 1` would give the cisTauReal multiplicativity
  conditions yielding `(cisTauReal(α − β)).im ≈ 0`. The β = arctan(1)
  side requires either an extension of F.6 to wider domain, or a route
  via Scope 2B's `pi ≈ 4·arctan(1)` combined with `cisTauReal(pi/4)` =
  `(√2/2, √2/2)`-like infrastructure (which would be circular at the
  current programme state).

### What Phase F.C.1 ships (Part 9 below)

* **`MachinDiagonal_small_check_at_N20`** — the finite-arithmetic check
  for depths `0..19`, discharged by `interval_cases n <;>
  (simp only [...]; norm_num)`.

* **`MachinDiagonal_base_at_N20`** — the strong base-case at depth 20
  (`|D(20)| ≤ 157/318`), discharged by direct `norm_num` over the
  fully-unfolded partial-sum expression.

* **`MachinDiagonalBoundedHalf_proved`** — composition of the two above
  with `MachinDiagonalBoundedHalf_via_N20`, giving the full theorem
  `MachinDiagonalBoundedHalf` with no hypothesis.

* **`pi_machin_equiv_pi_from_CisIm`** (and the parallel `MachinSlashFour`,
  `MachinIdentity`, `MachinClassicalLimit` variants) — the entire
  keystone chain conditional on the SINGLE residual hypothesis
  `CisMachinDiagonalImEquivZero`.

## Build state

* `sorry` count: 0
* Axiom count: 3 (kernel: `propext`, `Classical.choice`, `Quot.sound`)
* Imports: `TauRealCisInjectivity` (F.B.0) + `TauRealArctanOneLeibniz`
  (Scope 2E) + Mathlib tactics only.

## Module name

This file is picked up by the `.submodules` glob in `lakefile.lean`.
-/

set_option autoImplicit false

namespace Tau.Boundary

open Tau.Denotation

-- ============================================================
-- PART 1: NONNEGATIVITY OF arctan_partial_rat 1 n
-- ============================================================

/-! ## Nonnegativity of the Leibniz partial sum at `x = 1`

The Leibniz partial sum at `x = 1` is

  `arctan_partial_rat 1 n = Σ_{k=0}^{n-1} (1/(4k+1) − 1/(4k+3))`.

Each pair-term `1/(4k+1) − 1/(4k+3) = 2/((4k+1)(4k+3)) > 0` is strictly
positive, so the partial sum is monotonically increasing from 0. -/

/-- **Per-term positivity at `x = 1`**:
    `arctan_pair_term_rat 1 k = 1/(4k+1) − 1/(4k+3) > 0`. -/
theorem arctan_pair_term_rat_one_pos (k : Nat) :
    0 < arctan_pair_term_rat 1 k := by
  unfold arctan_pair_term_rat
  -- 1^(4k+1) = 1, 1^(4k+3) = 1
  simp only [one_pow]
  -- Goal: 0 < 1 / (4 * ↑k + 1) - 1 / (4 * ↑k + 3)
  have h_4k1_pos : (0 : Rat) < 4 * (k : Rat) + 1 := by
    have h : (0 : Rat) ≤ (k : Rat) := by exact_mod_cast Nat.zero_le k
    linarith
  have h_4k3_pos : (0 : Rat) < 4 * (k : Rat) + 3 := by
    have h : (0 : Rat) ≤ (k : Rat) := by exact_mod_cast Nat.zero_le k
    linarith
  -- 1/(4k+1) > 1/(4k+3) since 4k+1 < 4k+3
  have h_lt : (4 * (k : Rat) + 1) < (4 * (k : Rat) + 3) := by linarith
  have h_gt : (1 : Rat) / (4 * (k : Rat) + 1) > 1 / (4 * (k : Rat) + 3) :=
    one_div_lt_one_div_of_lt h_4k1_pos h_lt
  linarith

/-- **Nonnegativity of arctan_partial_rat 1 n** at every depth:
    `0 ≤ arctan_partial_rat 1 n` for all `n`. -/
theorem arctan_partial_rat_one_nonneg (n : Nat) :
    0 ≤ arctan_partial_rat 1 n := by
  induction n with
  | zero => rw [arctan_partial_rat_zero]
  | succ n ih =>
    rw [arctan_partial_rat_succ]
    have h_term_pos := arctan_pair_term_rat_one_pos n
    linarith

-- ============================================================
-- PART 2: UPPER BOUND  arctan_partial_rat 1 n ≤ 19/24
-- ============================================================

/-! ## Upper bound via the `pi_partial` bridge

By `pi_partial_toRat_eq_four_arctan_partial_one`, we have

  `pi_partial n .toRat = 4 · arctan_partial_rat 1 n`

at every depth `n`. The τ-canon's pi_partial admits the telescoping sum
bound `sumFromTo pi_pair_term 1 m ≤ 1/2` (from
`TauReal.sumFromTo_pi_pair_term_bound`), which gives

  `pi_partial m .toRat ≤ pi_partial 1 .toRat + 1/2`
                       `= 8/3 + 1/2 = 19/6`

for `m ≥ 1`. Hence `arctan_partial_rat 1 m ≤ 19/24 < 1` for `m ≥ 1`. -/

/-- **Helper**: `pi_partial 1 .toRat = 8/3`. -/
private theorem pi_partial_one_toRat :
    (TauRat.pi_partial 1).toRat = 8/3 := by
  unfold TauRat.pi_partial
  rw [TauRat.sum_succ, toRat_add]
  rw [show TauRat.sum TauRat.pi_pair_term 0 = TauRat.zero from rfl]
  rw [toRat_zero, zero_add]
  rw [TauRat.pi_pair_term_toRat]
  norm_num

/-- **Bound via telescoping** for `m ≥ 1`: `pi_partial m .toRat ≤ 19/6`.
    Combines `pi_partial 1 .toRat = 8/3` with the telescoping bound
    `sumFromTo pi_pair_term 1 m ≤ 1/2 < 1/2 - 1/(2m) + 1/(2m)`. -/
private theorem pi_partial_toRat_le_19_6 (m : Nat) (hm : 1 ≤ m) :
    (TauRat.pi_partial m).toRat ≤ 19/6 := by
  -- pi_partial m = pi_partial 1 + sumFromTo pi_pair_term 1 m
  have h_sum_bound := TauReal.sumFromTo_pi_pair_term_bound 1 (by omega) m hm
  -- h_sum_bound: (sumFromTo pi_pair_term 1 m).toRat ≤ 1/(2·1) - 1/(2·m) = 1/2 - 1/(2m)
  -- Step 1: pi_partial m = pi_partial 1 + sumFromTo pi_pair_term 1 m at toRat
  have h_split : (TauRat.pi_partial m).toRat
                  = (TauRat.pi_partial 1).toRat
                    + (TauRat.sumFromTo TauRat.pi_pair_term 1 m).toRat := by
    -- Convert: pi_partial m = sum pi_pair_term m
    -- = sum pi_pair_term 1 + sumFromTo pi_pair_term 1 m  (when m ≥ 1)
    -- = pi_partial 1 + sumFromTo pi_pair_term 1 m
    unfold TauRat.pi_partial
    -- Use sum_sub_toRat_eq_sumFromTo (with m, 1):
    -- (sum f m - sum f 1).toRat = (sumFromTo f 1 m).toRat
    have h := TauRat.sum_sub_toRat_eq_sumFromTo TauRat.pi_pair_term 1 m hm
    -- h: ((sum f m).toRat - (sum f 1).toRat) = (sumFromTo f 1 m).toRat
    -- Equivalently: (sum f m).toRat = (sum f 1).toRat + (sumFromTo f 1 m).toRat
    linarith
  rw [h_split, pi_partial_one_toRat]
  -- Goal: 8/3 + (sumFromTo).toRat ≤ 19/6
  -- 8/3 + 1/2 = 16/6 + 3/6 = 19/6. So suffices (sumFromTo).toRat ≤ 1/2.
  -- h_sum_bound: ≤ 1/(2·1) - 1/(2m) = 1/2 - 1/(2m)
  -- Since 1/(2m) ≥ 0, sumFromTo ≤ 1/2 - 1/(2m) ≤ 1/2.
  have h_m_pos : (0 : Rat) < (m : Rat) := by exact_mod_cast hm
  have h_recip_nn : (0 : Rat) ≤ 1 / (2 * (m : Rat)) := by
    apply div_nonneg (by norm_num : (0 : Rat) ≤ 1) (by linarith)
  -- Reform h_sum_bound to use 1/(2·1) = 1/2.
  have h_2_one_eq : (1 : Rat) / (2 * ((1 : Nat) : Rat)) = 1/2 := by
    norm_num
  rw [h_2_one_eq] at h_sum_bound
  linarith

/-- **Upper bound on arctan_partial_rat 1 n** at every depth:
    `arctan_partial_rat 1 n ≤ 19/24` for all `n`. -/
theorem arctan_partial_rat_one_le_19_over_24 (n : Nat) :
    arctan_partial_rat 1 n ≤ 19/24 := by
  by_cases hn : 1 ≤ n
  · -- n ≥ 1: use the pi_partial bridge
    have h_bridge := pi_partial_toRat_eq_four_arctan_partial_one n
    have h_pi := pi_partial_toRat_le_19_6 n hn
    -- (pi_partial n).toRat = 4 · arctan_partial_rat 1 n ≤ 19/6
    -- ⟹ arctan_partial_rat 1 n ≤ 19/24
    rw [h_bridge] at h_pi
    linarith
  · -- n = 0: arctan_partial_rat 1 0 = 0 ≤ 19/24
    push_neg at hn
    have h_n_zero : n = 0 := by omega
    subst h_n_zero
    rw [arctan_partial_rat_zero]
    norm_num

/-- **Absolute-value bound on arctan_partial_rat 1 n**:
    `|arctan_partial_rat 1 n| ≤ 1` for all `n`. This is the τ-canon's
    incarnation of `arctan(1) = π/4 < 1` at the partial-sum level. -/
theorem arctan_partial_rat_one_abs_le_one (n : Nat) :
    |arctan_partial_rat 1 n| ≤ 1 := by
  have h_nn := arctan_partial_rat_one_nonneg n
  have h_ub := arctan_partial_rat_one_le_19_over_24 n
  rw [abs_of_nonneg h_nn]
  linarith

-- ============================================================
-- PART 3: THE F.B.0-BASED CONDITIONAL DISCHARGE THEOREM
-- ============================================================

/-! ## Conditional discharge via F.B.0

The main result: given the two named hypotheses on `machin_diagonal`,
`MachinSlashFourIdentity` follows by `cisTauReal_injectivity_at_zero`
(F.B.0) plus `machin_diagonal_equiv_zero_iff_MachinSlashFourIdentity`
(Scope 2E).

The two hypotheses are:
1. The principal-branch bound: `|machin_diagonal.approx n| ≤ 1/2` for all `n`.
2. The imaginary-vanishing: `(cisTauReal machin_diagonal).im ≈ TauReal.zero`.

Both are TauReal-level propositions, fully concrete. -/

/-- **🎯 Phase F.B.1 headline conditional theorem**:

    Given the principal-branch bound on `machin_diagonal` and the
    imaginary-vanishing of `cisTauReal machin_diagonal`,
    `MachinSlashFourIdentity` follows.

    Specifically: if
    * `∀ n, ((TauReal.machin_diagonal.approx n).abs).toRat ≤ 1/2` (bound), AND
    * `(TauComplex.cisTauReal TauReal.machin_diagonal).im ≈ TauReal.zero` (im
      vanishes),
    then `MachinSlashFourIdentity` holds.

    Proof:
    1. By F.B.0 (`cisTauReal_injectivity_at_zero`), the two hypotheses
       give `machin_diagonal ≈ TauReal.zero`.
    2. By Scope 2E (`machin_diagonal_equiv_zero_iff_MachinSlashFourIdentity`),
       this is equivalent to `MachinSlashFourIdentity`. -/
theorem MachinSlashFourIdentity_via_machin_diagonal_FB0
    (h_bound : ∀ n, ((TauReal.machin_diagonal.approx n).abs).toRat ≤ 1/2)
    (h_im : TauReal.equiv (TauComplex.cisTauReal TauReal.machin_diagonal).im
              TauReal.zero) :
    MachinSlashFourIdentity :=
  machin_diagonal_equiv_zero_iff_MachinSlashFourIdentity.mp
    (TauComplex.cisTauReal_injectivity_at_zero TauReal.machin_diagonal h_bound h_im)

/-- **Corollary**: under the same hypotheses, `pi_machin ≈ pi` (the
    original Wave Γ₇ Phase 3F target). -/
theorem pi_machin_equiv_pi_via_FB0
    (h_bound : ∀ n, ((TauReal.machin_diagonal.approx n).abs).toRat ≤ 1/2)
    (h_im : TauReal.equiv (TauComplex.cisTauReal TauReal.machin_diagonal).im
              TauReal.zero) :
    TauReal.equiv TauReal.pi_machin TauReal.pi :=
  pi_machin_equiv_pi_iff_MachinSlashFourIdentity.mpr
    (MachinSlashFourIdentity_via_machin_diagonal_FB0 h_bound h_im)

/-- **Corollary**: under the same hypotheses, `MachinIdentity` (the original
    Scope 2C named target). -/
theorem MachinIdentity_via_FB0
    (h_bound : ∀ n, ((TauReal.machin_diagonal.approx n).abs).toRat ≤ 1/2)
    (h_im : TauReal.equiv (TauComplex.cisTauReal TauReal.machin_diagonal).im
              TauReal.zero) :
    MachinIdentity :=
  MachinIdentity_iff_MachinSlashFourIdentity.mpr
    (MachinSlashFourIdentity_via_machin_diagonal_FB0 h_bound h_im)

/-- **Corollary**: under the same hypotheses, `MachinClassicalLimit` (the
    Scope 2E Rat-level diagonal modulus existence). -/
theorem MachinClassicalLimit_via_FB0
    (h_bound : ∀ n, ((TauReal.machin_diagonal.approx n).abs).toRat ≤ 1/2)
    (h_im : TauReal.equiv (TauComplex.cisTauReal TauReal.machin_diagonal).im
              TauReal.zero) :
    MachinClassicalLimit :=
  MachinClassicalLimit_iff_MachinSlashFourIdentity.mpr
    (MachinSlashFourIdentity_via_machin_diagonal_FB0 h_bound h_im)

-- ============================================================
-- PART 4: NAMED HYPOTHESIS PROPOSITIONS
-- ============================================================

/-! ## Naming the residual hypotheses

For inspectability and future formal reasoning, we give the two F.B.0-based
hypotheses canonical names. After Phase F.B.1, the entire Machin keystone
reduces to:

  >  `MachinDiagonalBoundedHalf ∧ CisMachinDiagonalImEquivZero → MachinSlashFourIdentity`

(and hence the whole chain `MachinIdentity ↔ pi_machin ≈ pi ↔ MachinClassicalLimit`).

Both propositions are fully concrete TauReal/TauRat propositions about
the τ-native objects `machin_diagonal` and `cisTauReal machin_diagonal`. -/

/-- **The principal-branch boundedness hypothesis** for `machin_diagonal`:
    asserts that the τ-native Machin diagonal stays within the
    principal-branch radius 1/2 at every depth.

    Classically, this is the statement that the truncation errors of
    `4·arctan_partial(1/5) − arctan_partial(1/239) − arctan_partial(1)`
    accumulate with magnitude `≤ 1/2` at every finite depth. At large
    depth, the Cauchy modulus (`MachinFullDiff_cauchy_bound`) gives
    `≤ 21/2^n` shrinkage, but at small depths we need a direct check
    that the partial sums don't overshoot. -/
def MachinDiagonalBoundedHalf : Prop :=
  ∀ n, ((TauReal.machin_diagonal.approx n).abs).toRat ≤ 1/2

/-- **The imaginary-vanishing hypothesis** for `cisTauReal machin_diagonal`:
    asserts that the imaginary leg of `cis(machin_diagonal)` is
    Cauchy-equivalent to zero.

    Classically, this is the statement `sin(machin_diagonal) = 0`. Under
    the principal-branch boundedness, by F.B.0 this implies
    `machin_diagonal = 0`, hence `MachinSlashFourIdentity`.

    Proving this directly at τ-canon requires either:
    * The 45°-line identity for `arctan(1)` (extending the Scope 2A-lift's
      result for the Machin LHS to the RHS = `arctan(1)`), OR
    * A direct partial-sum analysis showing the imaginary part of
      `cis(D_n)` converges to 0 with explicit modulus. -/
def CisMachinDiagonalImEquivZero : Prop :=
  TauReal.equiv (TauComplex.cisTauReal TauReal.machin_diagonal).im TauReal.zero

/-- **🎯 The final structural reduction** (Phase F.B.1 final form):

    `MachinDiagonalBoundedHalf ∧ CisMachinDiagonalImEquivZero ↔ pi_machin ≈ pi`.

    The entire Machin keystone — and consequently the BBPLeibniz
    correspondence chain — reduces to this conjunction. -/
theorem pi_machin_equiv_pi_iff_FB0_hypotheses :
    (MachinDiagonalBoundedHalf ∧ CisMachinDiagonalImEquivZero)
      → TauReal.equiv TauReal.pi_machin TauReal.pi :=
  fun ⟨h_bd, h_im⟩ => pi_machin_equiv_pi_via_FB0 h_bd h_im

-- ============================================================
-- PART 5: BASE-CASE WITNESS — bound at n = 0
-- ============================================================

/-! ## Boundedness base case at depth 0

At depth 0, all three component arctan partial sums are 0, so the
Machin diagonal is exactly 0. This gives the first witness for the
`MachinDiagonalBoundedHalf` proposition's universal-`n` quantifier.

While this alone doesn't close the bound at all `n` (the larger-`n` cases
remain a residual structural fact), it confirms the base case rigorously
and serves as the template for any inductive or computational extension. -/

/-- **Base case witness**: `((machin_diagonal.approx 0).abs).toRat = 0`,
    hence `≤ 1/2`. -/
theorem MachinDiagonalBoundedHalf_at_zero :
    ((TauReal.machin_diagonal.approx 0).abs).toRat ≤ 1/2 := by
  rw [TauRat.toRat_abs]
  rw [TauReal.machin_diagonal_approx_toRat]
  -- machin_diagonal.approx 0 .toRat = (4·a₅(0) − a₂₃₉(0)) − a₁(0)
  --                                  = (4·0 − 0) − 0 = 0
  rw [arctan_partial_rat_zero, arctan_partial_rat_zero, arctan_partial_rat_zero]
  norm_num

-- ============================================================
-- PART 6: TauReal-LEVEL EXISTENTIAL — diagonal is bounded somewhere
-- ============================================================

/-! ## Existential boundedness at n = 0

A simpler existential form of the base case, useful for any logical
chain that just needs "there exists `n` with bounded diagonal" rather
than the universal statement. -/

/-- **Existential base case**: there exists an `n` (namely `n = 0`) with
    `((machin_diagonal.approx n).abs).toRat ≤ 1/2`. -/
theorem MachinDiagonal_exists_bounded :
    ∃ n, ((TauReal.machin_diagonal.approx n).abs).toRat ≤ 1/2 :=
  ⟨0, MachinDiagonalBoundedHalf_at_zero⟩

-- ============================================================
-- PART 7: STRUCTURAL REDUCTION — MachinDiagonalBoundedHalf
--         from a base-case at depth N₀ via Cauchy tail decay
-- ============================================================

/-! ## Reducing the universal-`n` bound to a finite small-`n` check

By `MachinFullDiff_cauchy_bound`, for `1 ≤ N₀ ≤ n` we have the
Cauchy-tail bound

  `|D(n) − D(N₀)| ≤ 20/2^N₀ + 1/(8·N₀)`

at the Rat level. Composed with the absolute-value triangle inequality
(`|D(n)| ≤ |D(N₀)| + |D(n) − D(N₀)|`), this gives the structural
reduction: if at depth `N₀` we have the **strong** bound

  `|D(N₀)| ≤ 1/2 − 20/2^N₀ − 1/(8·N₀)`,

then for ALL `n ≥ N₀`, `|D(n)| ≤ 1/2`. Combined with a finite check
at depths `0, 1, …, N₀ − 1`, this discharges `MachinDiagonalBoundedHalf`.

At `N₀ = 20`, the tail is `20/2^20 + 1/160 ≈ 0.006272`, so the
strong base-case bound becomes `|D(20)| ≤ 0.4937…`. At `N₀ = 30`, the
tail is `20/2^30 + 1/240 ≈ 0.004167`, giving `|D(30)| ≤ 0.4958…`.
These are concrete Rat-arithmetic statements about the partial sums
at finite depth — no classical analysis is invoked.

**Significance**: this reduces the (still-undischarged) classical
content of the Machin keystone — `MachinDiagonalBoundedHalf` — from
an infinite universal-`n` statement to a **finite (Rat-computable)**
small-`n` check at depths `0..N₀`. The reduction is the first
constructively-shippable contribution toward closing the F.B.1
hypotheses without invoking the F.6 wider-domain extension. -/

/-- **Helper** — for `n ≥ 1`, the Cauchy-tail bound between `D(n)` and
    `D(N₀)` at the partial-sum level (composed from
    `MachinFullDiff_cauchy_bound` and the machin_diagonal_approx_toRat
    bridge). -/
private theorem machin_diagonal_approx_toRat_diff_bound
    (N₀ n : Nat) (hN₀_pos : 1 ≤ N₀) (hN₀_le_n : N₀ ≤ n) :
    |((TauReal.machin_diagonal.approx n).toRat
       - (TauReal.machin_diagonal.approx N₀).toRat)|
      ≤ 20 / (2 : Rat)^N₀ + 1 / (8 * (N₀ : Rat)) := by
  rw [TauReal.machin_diagonal_approx_toRat, TauReal.machin_diagonal_approx_toRat]
  exact MachinFullDiff_cauchy_bound n N₀ hN₀_pos hN₀_le_n

/-- **Tail bound**: for `n ≥ N₀ ≥ 1`,
    `|D(n)| ≤ |D(N₀)| + 20/2^N₀ + 1/(8·N₀)`.

    Direct consequence of `machin_diagonal_approx_toRat_diff_bound` plus
    the triangle inequality `|x| ≤ |x − y| + |y|`. -/
theorem machin_diagonal_tail_bound
    (N₀ n : Nat) (hN₀_pos : 1 ≤ N₀) (hN₀_le_n : N₀ ≤ n) :
    ((TauReal.machin_diagonal.approx n).abs).toRat
      ≤ ((TauReal.machin_diagonal.approx N₀).abs).toRat
        + 20 / (2 : Rat)^N₀ + 1 / (8 * (N₀ : Rat)) := by
  -- |D(n)| = |D(N₀) + (D(n) − D(N₀))| ≤ |D(N₀)| + |D(n) − D(N₀)|.
  rw [TauRat.toRat_abs, TauRat.toRat_abs]
  have h_diff_bd := machin_diagonal_approx_toRat_diff_bound N₀ n hN₀_pos hN₀_le_n
  -- Triangle: |x| ≤ |y| + |x - y|, with x = D(n), y = D(N₀).
  have h_tri : |((TauReal.machin_diagonal.approx n).toRat)|
             ≤ |((TauReal.machin_diagonal.approx N₀).toRat)|
              + |((TauReal.machin_diagonal.approx n).toRat
                  - (TauReal.machin_diagonal.approx N₀).toRat)| := by
    have h := abs_add_le
      ((TauReal.machin_diagonal.approx N₀).toRat)
      ((TauReal.machin_diagonal.approx n).toRat
        - (TauReal.machin_diagonal.approx N₀).toRat)
    have h_eq : (TauReal.machin_diagonal.approx N₀).toRat
              + ((TauReal.machin_diagonal.approx n).toRat
                  - (TauReal.machin_diagonal.approx N₀).toRat)
              = (TauReal.machin_diagonal.approx n).toRat := by ring
    rw [h_eq] at h
    exact h
  linarith [h_tri, h_diff_bd]

/-- **🎯 Structural reduction from a strong base case at depth N₀**:

    Given:
    * `N₀ ≥ 1`,
    * a finite small-`n` check at depths `0, 1, …, N₀ − 1`
      (`h_small`: each `|D(n)| ≤ 1/2`),
    * a strong bound at depth `N₀`:
      `|D(N₀)| ≤ 1/2 − 20/2^N₀ − 1/(8·N₀)`,
    conclude `MachinDiagonalBoundedHalf`.

    Proof sketch:
    * For `n < N₀`: by `h_small`.
    * For `n ≥ N₀`: by `machin_diagonal_tail_bound` plus `h_strong`,
      `|D(n)| ≤ |D(N₀)| + 20/2^N₀ + 1/(8·N₀) ≤ 1/2`.

    This is the **structural reduction** of `MachinDiagonalBoundedHalf`
    to a finite Rat-arithmetic check at depths `0..N₀`. The reduction
    does not invoke any classical (limit/derivative) content — it
    composes the already-shipped `MachinFullDiff_cauchy_bound` with
    the triangle inequality.

    Future closure path: combine this reduction with a Rat-level
    decidability check for the small-`n` partial sums at depth N₀
    (e.g., via `Nat.decEq` and exact-arithmetic Rat evaluation), then
    the keystone reduces to a single concrete Rat inequality
    `|D(N₀_chosen)| ≤ ...` that can in principle be discharged by
    direct computation. -/
theorem MachinDiagonalBoundedHalf_from_basecase_at_depth
    (N₀ : Nat) (hN₀_pos : 1 ≤ N₀)
    (h_small : ∀ n, n < N₀ → ((TauReal.machin_diagonal.approx n).abs).toRat ≤ 1/2)
    (h_strong : ((TauReal.machin_diagonal.approx N₀).abs).toRat
                  ≤ 1/2 - 20 / (2 : Rat)^N₀ - 1 / (8 * (N₀ : Rat))) :
    MachinDiagonalBoundedHalf := by
  unfold MachinDiagonalBoundedHalf
  intro n
  by_cases h_lt : n < N₀
  · exact h_small n h_lt
  · push_neg at h_lt
    -- h_lt : N₀ ≤ n
    have h_tail := machin_diagonal_tail_bound N₀ n hN₀_pos h_lt
    -- h_tail: |D(n)| ≤ |D(N₀)| + 20/2^N₀ + 1/(8·N₀)
    -- h_strong: |D(N₀)| ≤ 1/2 - 20/2^N₀ - 1/(8·N₀)
    linarith

/-- **Convenience corollary** — the structural reduction with a UNIFORM
    bound on `|D(N₀)|` only (no separate strong-tail bound): given
    `|D(N₀)| ≤ 1/2 − ε`, conclude `MachinDiagonalBoundedHalf`, provided
    the tail `20/2^N₀ + 1/(8·N₀)` is at most `ε`.

    Useful when the user has a "loose" base-case bound and wants the
    Cauchy-tail slack absorbed explicitly. -/
theorem MachinDiagonalBoundedHalf_from_basecase_with_slack
    (N₀ : Nat) (hN₀_pos : 1 ≤ N₀) (ε : Rat) (_hε_nn : 0 ≤ ε)
    (h_tail_le : 20 / (2 : Rat)^N₀ + 1 / (8 * (N₀ : Rat)) ≤ ε)
    (h_small : ∀ n, n < N₀ → ((TauReal.machin_diagonal.approx n).abs).toRat ≤ 1/2)
    (h_base : ((TauReal.machin_diagonal.approx N₀).abs).toRat ≤ 1/2 - ε) :
    MachinDiagonalBoundedHalf := by
  apply MachinDiagonalBoundedHalf_from_basecase_at_depth N₀ hN₀_pos h_small
  linarith [h_tail_le, h_base]

/-! ## Numerical witnesses at canonical depths

For an inspectable view of the slack thresholds, we record the explicit
Rat-arithmetic bounds at canonical small depths `N₀ ∈ {10, 20, 30}`.
These are pure rationals decidable by `norm_num`. They quantify the
"how close to 1/2" the small-`N₀` base case must be for the structural
reduction to apply. -/

/-- **Numerical witness at N₀ = 10**: `20/2^10 + 1/80 = 1/64 + 1/80
    = (5 + 4)/320 = 9/320 + 0/... actually let's compute: 20/1024 = 5/256.
    5/256 + 1/80 = (5·80 + 256)/(256·80) = (400 + 256)/20480 = 656/20480
    = 41/1280`. We bound by `1/30` (since `41/1280 < 1/30`: cross-mul:
    `30·41 = 1230 < 1280 = 1·1280` ✓). -/
theorem MachinDiagonalBoundedHalf_tail_at_10 :
    20 / (2 : Rat)^10 + 1 / (8 * (10 : Rat)) ≤ 1 / 30 := by
  norm_num

/-- **Numerical witness at N₀ = 20**: `20/2^20 + 1/160`.
    `20/2^20 = 20/1048576 = 5/262144`.
    `5/262144 + 1/160 = (5·160 + 262144)/(262144·160)
                      = (800 + 262144)/41943040 = 262944/41943040
                      < 1/159` (cross-mul: `159 · 262944 = 41808096
                                < 41943040`). -/
theorem MachinDiagonalBoundedHalf_tail_at_20 :
    20 / (2 : Rat)^20 + 1 / (8 * (20 : Rat)) ≤ 1 / 159 := by
  norm_num

/-- **Numerical witness at N₀ = 30**: `20/2^30 + 1/240`.
    The tail `1/(8·N₀) = 1/240` dominates by far, since `20/2^30 ≈ 1.86·10⁻⁸`.
    Bound by `1/239`. -/
theorem MachinDiagonalBoundedHalf_tail_at_30 :
    20 / (2 : Rat)^30 + 1 / (8 * (30 : Rat)) ≤ 1 / 239 := by
  norm_num

/-! ## Specialized reduction at canonical depths

These specialized forms hard-bake the canonical depth choice and the
matching numerical witness for the slack, leaving only the small-`n`
finite check and the strong base bound as user obligations. -/

/-- **🎯 Specialized at N₀ = 20**: given
    * a finite small-`n` check at depths `0..19`, AND
    * `|D(20)| ≤ 1/2 − 1/159 = 157/318`,
    conclude `MachinDiagonalBoundedHalf`.

    The depth `20` is chosen as the threshold where the geometric
    Cauchy-tail decay overwhelms the harmonic `1/(8n)` cost.

    The base-case bound `|D(20)| ≤ 157/318` is a CONCRETE RAT INEQUALITY
    over the (finite-depth) Leibniz partial sums at `1/5`, `1/239`, `1`. -/
theorem MachinDiagonalBoundedHalf_via_N20
    (h_small : ∀ n, n < 20 → ((TauReal.machin_diagonal.approx n).abs).toRat ≤ 1/2)
    (h_base : ((TauReal.machin_diagonal.approx 20).abs).toRat ≤ 157/318) :
    MachinDiagonalBoundedHalf := by
  apply MachinDiagonalBoundedHalf_from_basecase_with_slack
    20 (by norm_num : 1 ≤ 20) (1/159) (by norm_num : (0 : Rat) ≤ 1/159)
    MachinDiagonalBoundedHalf_tail_at_20 h_small
  have h_eq : (1 : Rat) / 2 - 1 / 159 = 157 / 318 := by norm_num
  linarith [h_eq.symm ▸ h_base]

/-- **🎯 Specialized at N₀ = 30**: given
    * a finite small-`n` check at depths `0..29`, AND
    * `|D(30)| ≤ 1/2 − 1/239 = 237/478`,
    conclude `MachinDiagonalBoundedHalf`. -/
theorem MachinDiagonalBoundedHalf_via_N30
    (h_small : ∀ n, n < 30 → ((TauReal.machin_diagonal.approx n).abs).toRat ≤ 1/2)
    (h_base : ((TauReal.machin_diagonal.approx 30).abs).toRat ≤ 237/478) :
    MachinDiagonalBoundedHalf := by
  apply MachinDiagonalBoundedHalf_from_basecase_with_slack
    30 (by norm_num : 1 ≤ 30) (1/239) (by norm_num : (0 : Rat) ≤ 1/239)
    MachinDiagonalBoundedHalf_tail_at_30 h_small
  have h_eq : (1 : Rat) / 2 - 1 / 239 = 237 / 478 := by norm_num
  linarith [h_eq.symm ▸ h_base]

-- ============================================================
-- PART 8: COMPOSITE KEYSTONE BRIDGE — combining the structural
--         reduction with the F.B.0-based discharge route
-- ============================================================

/-! ## Composite keystone closure from a finite-depth witness

The structural reduction (Part 7) reduces `MachinDiagonalBoundedHalf`
to a finite check. Composed with `pi_machin_equiv_pi_iff_FB0_hypotheses`,
we get a complete reduction of the keystone `pi_machin ≈ pi` to:

1. A FINITE small-`n` check at depths `0..N₀ − 1` (each ≤ 1/2),
2. A STRONG base-case at depth `N₀` (`|D(N₀)| ≤ 1/2 − tail(N₀)`),
3. The `CisMachinDiagonalImEquivZero` hypothesis (still residual).

This is the cleanest constructive structural decomposition of the
remaining keystone gap. -/

/-- **🎯 Keystone bridge via N₀ = 20**: given
    * small-`n` finite check at depths `0..19`,
    * strong base-case at depth `20` (`|D(20)| ≤ 157/318`), AND
    * `CisMachinDiagonalImEquivZero`,
    conclude `pi_machin ≈ pi`. -/
theorem pi_machin_equiv_pi_via_N20_route
    (h_small : ∀ n, n < 20 → ((TauReal.machin_diagonal.approx n).abs).toRat ≤ 1/2)
    (h_base : ((TauReal.machin_diagonal.approx 20).abs).toRat ≤ 157/318)
    (h_im : CisMachinDiagonalImEquivZero) :
    TauReal.equiv TauReal.pi_machin TauReal.pi :=
  pi_machin_equiv_pi_iff_FB0_hypotheses
    ⟨MachinDiagonalBoundedHalf_via_N20 h_small h_base, h_im⟩

/-- **🎯 Keystone bridge via N₀ = 30**: given
    * small-`n` finite check at depths `0..29`,
    * strong base-case at depth `30` (`|D(30)| ≤ 237/478`), AND
    * `CisMachinDiagonalImEquivZero`,
    conclude `pi_machin ≈ pi`. -/
theorem pi_machin_equiv_pi_via_N30_route
    (h_small : ∀ n, n < 30 → ((TauReal.machin_diagonal.approx n).abs).toRat ≤ 1/2)
    (h_base : ((TauReal.machin_diagonal.approx 30).abs).toRat ≤ 237/478)
    (h_im : CisMachinDiagonalImEquivZero) :
    TauReal.equiv TauReal.pi_machin TauReal.pi :=
  pi_machin_equiv_pi_iff_FB0_hypotheses
    ⟨MachinDiagonalBoundedHalf_via_N30 h_small h_base, h_im⟩

-- ============================================================
-- PART 9: PHASE F.C.1 — DISCHARGE OF THE FINITE ARITHMETIC CHECK
--         AT N₀ = 20, COMPLETING `MachinDiagonalBoundedHalf`
-- ============================================================

/-! ## Phase F.C.1 — discharging the finite Rat-arithmetic check

The structural reduction (Part 7) reduces `MachinDiagonalBoundedHalf` to
two finite Rat-arithmetic obligations at canonical depth `N₀ = 20`:

1. **Small-`n` check at depths `0..19`**: `|D(n)| ≤ 1/2` for each
   `n ∈ {0, 1, …, 19}`.
2. **Strong base-case at depth `20`**: `|D(20)| ≤ 157/318` (with the
   Cauchy-tail slack `1/159` absorbed into the gap `1/2 − 157/318
   = 1/2 − 157/318 = (159 − 157)/318 = 2/318 = 1/159`).

Both are pure Rat inequalities over the Leibniz partial sums
`arctan_partial_rat (1/5) n`, `arctan_partial_rat (1/239) n`,
`arctan_partial_rat 1 n` at the chosen depth `n`. They are decidable
by exact Rat arithmetic (`norm_num`) after unfolding the recursive
definition of `arctan_partial_rat`.

**Implementation**: a single `interval_cases n <;> ...` proof handles
all 20 small-`n` cases simultaneously. The strong base-case at depth 20
is a single `norm_num` after unfolding. Both proofs use ONLY the kernel
axioms `propext`, `Classical.choice`, `Quot.sound` — no `native_decide`,
no `Lean.ofReduceBool`. -/

/-- **Phase F.C.1 — finite small-`n` check at depths `0..19`**:
    for every `n < 20`, `((machin_diagonal.approx n).abs).toRat ≤ 1/2`.

    Proof: unfold to the Rat-level diagonal expression, then
    `interval_cases n` splits into 20 cases. In each case, unfolding
    the recursive `arctan_partial_rat` and the per-term definition
    leaves a pure rational inequality discharged by `norm_num`. -/
theorem MachinDiagonal_small_check_at_N20 :
    ∀ n, n < 20 → ((TauReal.machin_diagonal.approx n).abs).toRat ≤ 1/2 := by
  intro n hn
  rw [TauRat.toRat_abs, TauReal.machin_diagonal_approx_toRat]
  interval_cases n <;>
    (simp only [arctan_partial_rat, arctan_pair_term_rat]; norm_num)

/-- **Phase F.C.1 — strong base-case at depth `20`**:
    `((machin_diagonal.approx 20).abs).toRat ≤ 157/318`.

    The slack `1/2 − 157/318 = 1/159` matches the Cauchy-tail bound
    at depth 20 (`MachinDiagonalBoundedHalf_tail_at_20`), so the
    structural reduction (`MachinDiagonalBoundedHalf_via_N20`) applies
    to conclude `MachinDiagonalBoundedHalf` for all `n`.

    Proof: unfold to the Rat-level diagonal expression at depth 20,
    fully unfold `arctan_partial_rat` and `arctan_pair_term_rat`, and
    discharge the resulting concrete Rat inequality with `norm_num`. -/
theorem MachinDiagonal_base_at_N20 :
    ((TauReal.machin_diagonal.approx 20).abs).toRat ≤ 157/318 := by
  rw [TauRat.toRat_abs, TauReal.machin_diagonal_approx_toRat]
  simp only [arctan_partial_rat, arctan_pair_term_rat]
  norm_num

/-- **🎯 Phase F.C.1 HEADLINE — `MachinDiagonalBoundedHalf` discharged**:
    `∀ n, ((machin_diagonal.approx n).abs).toRat ≤ 1/2` is now a
    full theorem (no hypothesis), discharged by composing the structural
    reduction (`MachinDiagonalBoundedHalf_via_N20`) with the finite
    arithmetic checks (`MachinDiagonal_small_check_at_N20` and
    `MachinDiagonal_base_at_N20`).

    This closes one of the two remaining hypotheses of the keystone
    chain. The remaining hypothesis is `CisMachinDiagonalImEquivZero`
    (the imaginary-vanishing of `cis(machin_diagonal)`).

    Axiom budget: 3 kernel axioms (`propext`, `Classical.choice`,
    `Quot.sound`). No `native_decide`, no `Lean.ofReduceBool`. -/
theorem MachinDiagonalBoundedHalf_proved : MachinDiagonalBoundedHalf :=
  MachinDiagonalBoundedHalf_via_N20
    MachinDiagonal_small_check_at_N20
    MachinDiagonal_base_at_N20

-- ============================================================
-- PART 10: DOWNSTREAM — KEYSTONE CHAIN MODULO
--          `CisMachinDiagonalImEquivZero` ONLY
-- ============================================================

/-! ## Phase F.C.1 — downstream consequences

With `MachinDiagonalBoundedHalf` discharged, the entire keystone chain
now reduces to a SINGLE residual hypothesis: `CisMachinDiagonalImEquivZero`.

These corollaries surface the downstream content. -/

/-- **🎯 Phase F.C.1 — keystone reduces to `CisMachinDiagonalImEquivZero`**:
    `CisMachinDiagonalImEquivZero → pi_machin ≈ pi`.

    The keystone `pi_machin ≈ pi` no longer needs the `MachinDiagonalBoundedHalf`
    hypothesis — only the imaginary-vanishing of `cis(machin_diagonal)`. -/
theorem pi_machin_equiv_pi_from_CisIm :
    CisMachinDiagonalImEquivZero → TauReal.equiv TauReal.pi_machin TauReal.pi :=
  fun h_im => pi_machin_equiv_pi_iff_FB0_hypotheses
    ⟨MachinDiagonalBoundedHalf_proved, h_im⟩

/-- **🎯 Phase F.C.1 — `MachinSlashFourIdentity` reduces to `CisMachinDiagonalImEquivZero`**. -/
theorem MachinSlashFourIdentity_from_CisIm :
    CisMachinDiagonalImEquivZero → MachinSlashFourIdentity :=
  fun h_im => MachinSlashFourIdentity_via_machin_diagonal_FB0
    MachinDiagonalBoundedHalf_proved h_im

/-- **🎯 Phase F.C.1 — `MachinIdentity` reduces to `CisMachinDiagonalImEquivZero`**. -/
theorem MachinIdentity_from_CisIm :
    CisMachinDiagonalImEquivZero → MachinIdentity :=
  fun h_im => MachinIdentity_via_FB0
    MachinDiagonalBoundedHalf_proved h_im

/-- **🎯 Phase F.C.1 — `MachinClassicalLimit` reduces to `CisMachinDiagonalImEquivZero`**. -/
theorem MachinClassicalLimit_from_CisIm :
    CisMachinDiagonalImEquivZero → MachinClassicalLimit :=
  fun h_im => MachinClassicalLimit_via_FB0
    MachinDiagonalBoundedHalf_proved h_im

end Tau.Boundary
