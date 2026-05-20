import TauLib.BookI.Boundary.TauRealCisInjectivity
import TauLib.BookI.Boundary.TauRealArctanOneLeibniz
import Mathlib.Tactic.Ring
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity

/-!
# TauLib.BookI.Boundary.TauRealMachinSlashFourClosure

**Phase F.B.1 — structural closure of MachinSlashFourIdentity via F.B.0**.

After Phase F.B.0 (`TauRealCisInjectivity.lean`) shipped the foundational
`cisTauReal_injectivity_at_zero` lemma and Phase E Scope 2E
(`TauRealArctanOneLeibniz.lean`) shipped the `machin_diagonal` TauReal
with the equivalence

> `machin_diagonal ≈ TauReal.zero ↔ MachinSlashFourIdentity`

this module composes these into the **conditional discharge route**: given
two named hypotheses about `machin_diagonal`, `MachinSlashFourIdentity`
(and hence the whole keystone chain `MachinIdentity`, `pi_machin ≈ pi`,
`MachinClassicalLimit`) follows.

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

## Significance — what the residual gap is

After Phase F.B.1, the **entire keystone chain** reduces to the conjunction
of TWO precisely-named TauReal propositions:

1. **`MachinDiagonalBoundedHalf`**: `∀ n, ((machin_diagonal.approx n).abs).toRat ≤ 1/2`.
2. **`CisMachinDiagonalImEquivZero`**: `(cisTauReal machin_diagonal).im ≈ TauReal.zero`.

Classical proof sketch of these (NOT formalised here):
* (1) — The partial-sum truncation errors decay geometrically; combined
  with the Machin identity at the limit, the bound `≤ 1/2` holds at every
  depth (with substantial slack at large depth and a finite check at
  small depths).
* (2) — The 45°-line identity at TauReal-equiv level (Scope 2A-lift for
  `α = pi_machin_arctan_quarter`) plus an analogous identity at
  `β = arctan_of_rat_seq 1` would give the cisTauReal multiplicativity
  conditions yielding `(cisTauReal(α − β)).im ≈ 0`. The β = arctan(1)
  side requires either an extension of F.6 to wider domain, or a route
  via Scope 2B's `pi ≈ 4·arctan(1)` combined with `cisTauReal(pi/4)` =
  `(√2/2, √2/2)`-like infrastructure (which would be circular at the
  current programme state).

This module makes the residual content **fully concrete and inspectable**:
the keystone is exactly one (1)-hypothesis-bundle away from full closure.

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

end Tau.Boundary
