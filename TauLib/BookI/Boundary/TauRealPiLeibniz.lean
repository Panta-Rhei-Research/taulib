import TauLib.BookI.Boundary.TauRealPi
import TauLib.BookI.Boundary.TauRealArctan
import TauLib.BookI.Boundary.TauRealArctanDeriv
import TauLib.BookI.Boundary.TauRealMachin
import Mathlib.Tactic.Ring
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity

/-!
# TauLib.BookI.Boundary.TauRealPiLeibniz

**Phase E Scope 2B — τ-native Leibniz formula at unit argument.**

The classical Leibniz formula

  π = 4 · (1 − 1/3 + 1/5 − 1/7 + ...)

made τ-native: the existing `TauReal.pi` (defined as the Leibniz-pairs
all-positive series `Σ 8/((4k+1)(4k+3))`) is Cauchy-equivalent to
`4 · arctan_of_rat_seq(1)` (the general arctan partial-sum series
specialised to argument 1).

## Mathematical content

The renumbering / pairing identity:

  pi_pair_term k = 8/((4k+1)(4k+3))
                 = 4 · (1/(4k+1) − 1/(4k+3))
                 = 4 · arctan_pair_term_rat 1 k

(per-term equality — already shipped in `TauRealArctan` as
`pi_pair_term_eq_four_times_arctan_one` for the reciprocal form;
restated here directly for `arctan_pair_term_rat 1 k`).

Summing both sides over `k ∈ {0, ..., n − 1}`:

  (pi_partial n).toRat = 4 · arctan_partial_rat 1 n

— a **pointwise** equality of approximations at every depth. The
TauReal-equiv conclusion follows from `equiv_of_pointwise`.

## Scope note — why this proves the τ-native Leibniz formula

Note that `4 · arctan_of_rat_seq(1)` is **not** itself directly known
to be Cauchy — the per-term magnitude bound at `x = 1` does not satisfy
the standard `2|x| ≤ 1` convergence-domain hypothesis (cf.
`TauReal.arctan_of_rat_isCauchy` requires `2 * |x.toRat| ≤ 1`).

However, **Cauchy-ness of `pi`** is independently shipped
(`TauReal.pi_isCauchy`, Wave 3c). Combined with the pointwise
equality, we get:

* The shifted-and-scaled series `4 · arctan_partial 1 n` *is* Cauchy,
  derivable from `pi.IsCauchy` via the pointwise identity.
* The `TauReal.equiv` lifts via `equiv_of_pointwise`, no separate
  Cauchy proof needed.

This delivers the central renumbering identity that step 5 of the
Machin chain in `TauRealMachin.lean:489-500` documents:

  > Step 5 requires ... the `4·arctan(1) ≈ pi_leibniz` connection
  > (which is `pi_partial_rat n = pi_leibniz_partial_rat`'s renumbering).

with both directions now τ-natively connected.

## Registry Cross-References

* [I.T-Pi-IsCauchy] `TauReal.pi.IsCauchy` (Wave 3c)
* [I.D-Pi-Pair-Term] `TauRat.pi_pair_term` (Wave 3c)
* [I.D-Arctan-OfRat-Seq] `TauReal.arctan_of_rat_seq` (Γ₇ Phase 1 / Γ₇ M3)
* [I.T-PiPair-Eq-FourArctan1] `pi_pair_term_eq_four_times_arctan_one`
  (TauRealArctan Phase 1A)

## Build state

* `sorry` count: 0
* Axiom count: 3 (kernel)
* Imports: TauRealPi + TauRealArctan (which transitively imports
  TauRealAnalyticalHelpers + TauRealSum + TauRealExp) + Mathlib
  tactics.
-/

set_option autoImplicit false

namespace Tau.Boundary

open Tau.Denotation

-- ============================================================
-- PART 1: PER-TERM RENUMBERING IDENTITY (Rat level)
-- ============================================================

/-- **Per-term identity at the Rat level**: the `pi_pair_term` at depth
    `k` equals four times the general `arctan_pair_term_rat` at `x = 1`,
    depth `k`. Both sides simplify to `8/((4k+1)(4k+3))` algebraically.

    The classical Leibniz-pair identity:
        `8/((4k+1)(4k+3)) = 4·(1/(4k+1) − 1/(4k+3))`
    rewritten with the τ-canon's general arctan partial-sum at `x = 1`. -/
theorem pi_pair_term_toRat_eq_four_arctan_pair_one (k : Nat) :
    (TauRat.pi_pair_term k).toRat = 4 * arctan_pair_term_rat 1 k := by
  rw [TauRat.pi_pair_term_toRat]
  unfold arctan_pair_term_rat
  -- Goal: 8 / ((4k+1)(4k+3) : Nat).cast = 4 · (1^(4k+1)/(4k+1) − 1^(4k+3)/(4k+3))
  have h_4k1_pos : (0 : Rat) < ((4*k+1 : Nat) : Rat) := by
    have : (0 : Nat) < 4 * k + 1 := by omega
    exact_mod_cast this
  have h_4k3_pos : (0 : Rat) < ((4*k+3 : Nat) : Rat) := by
    have : (0 : Nat) < 4 * k + 3 := by omega
    exact_mod_cast this
  -- 1^(4k+1) = 1, 1^(4k+3) = 1
  simp only [one_pow]
  push_cast
  field_simp
  ring

-- ============================================================
-- PART 2: PER-DEPTH PARTIAL-SUM IDENTITY (Rat level)
-- ============================================================

/-- **Per-depth partial-sum identity at the Rat level**: at every depth
    `n`, the `.toRat` of `pi_partial n` equals four times
    `arctan_partial_rat 1 n`.

    Proof: induction on `n`. Base case trivial (both 0). Inductive step
    uses `pi_pair_term_toRat_eq_four_arctan_pair_one` (per-term identity)
    plus distributivity of `4·` over addition. -/
theorem pi_partial_toRat_eq_four_arctan_partial_one (n : Nat) :
    (TauRat.pi_partial n).toRat = 4 * arctan_partial_rat 1 n := by
  induction n with
  | zero =>
    -- (pi_partial 0).toRat = TauRat.zero.toRat = 0
    -- 4 · arctan_partial_rat 1 0 = 4 · 0 = 0
    show (TauRat.pi_partial 0).toRat = 4 * arctan_partial_rat 1 0
    unfold TauRat.pi_partial
    simp [TauRat.sum_zero, toRat_zero, arctan_partial_rat_zero]
  | succ n ih =>
    -- pi_partial (n+1) = (pi_partial n).add (pi_pair_term n)
    -- arctan_partial_rat 1 (n+1) = arctan_partial_rat 1 n + arctan_pair_term_rat 1 n
    show (TauRat.pi_partial (n+1)).toRat = 4 * arctan_partial_rat 1 (n+1)
    unfold TauRat.pi_partial
    rw [TauRat.sum_succ, toRat_add]
    -- Goal: (TauRat.sum pi_pair_term n).toRat + (pi_pair_term n).toRat
    --       = 4 · (arctan_partial_rat 1 n + arctan_pair_term_rat 1 n)
    have h_sum_ih : (TauRat.sum TauRat.pi_pair_term n).toRat = 4 * arctan_partial_rat 1 n := by
      have := ih
      unfold TauRat.pi_partial at this
      exact this
    rw [h_sum_ih, pi_pair_term_toRat_eq_four_arctan_pair_one, arctan_partial_rat_succ]
    ring

-- ============================================================
-- PART 3: TauReal-LEVEL POINTWISE IDENTITY  pi.approx n ≈ 4 · arctan 1 .approx n
-- ============================================================

/-- **Pointwise TauRat equivalence at every depth**: the n-th
    approximation of `TauReal.pi` equals the n-th approximation of
    `4 · arctan_of_rat_seq(1)` modulo `TauRat.equiv`.

    Concretely: `pi.approx n = pi_partial n`, and `(4 · arctan).approx n
    = TauRat.mul ⟨4, 1⟩ (arctan_partial 1 n)`. The `.toRat`-equality from
    `pi_partial_toRat_eq_four_arctan_partial_one` gives the equiv
    (via `equiv_iff_toRat_eq`). -/
theorem TauReal.pi_approx_equiv_four_arctan_one_approx (n : Nat) :
    TauRat.equiv
      (TauReal.pi.approx n)
      (((TauReal.fromTauRat ⟨⟨4, 0⟩, 1, by norm_num⟩).mul
        (TauReal.arctan_of_rat_seq TauRat.one_canonical)).approx n) := by
  -- RHS unfolds to TauRat.mul ⟨⟨4,0⟩,1,_⟩ (TauRat.arctan_partial 1 n)
  rw [equiv_iff_toRat_eq]
  show (TauRat.pi_partial n).toRat
        = (TauRat.mul ⟨⟨4, 0⟩, 1, by norm_num⟩
              (TauRat.arctan_partial TauRat.one_canonical n)).toRat
  rw [toRat_mul]
  -- (⟨⟨4,0⟩,1,_⟩ : TauRat).toRat = 4
  have h_four_toRat : (⟨⟨4, 0⟩, 1, by norm_num⟩ : TauRat).toRat = 4 := by
    unfold TauRat.toRat
    simp only [TauInt.toInt]
    push_cast
    ring
  rw [h_four_toRat]
  rw [TauRat.arctan_partial_toRat]
  -- Goal: (pi_partial n).toRat = 4 · arctan_partial_rat (one_canonical.toRat) n
  have h_one_toRat : TauRat.one_canonical.toRat = 1 := TauRat.one_canonical_toRat
  rw [h_one_toRat]
  exact pi_partial_toRat_eq_four_arctan_partial_one n

-- ============================================================
-- PART 4: HEADLINE — pi ≈ 4 · arctan_of_rat_seq(1)
-- ============================================================

/-- **🎯 Phase E Scope 2B headline theorem — τ-native Leibniz formula
    at unit argument**:

    `TauReal.pi ≈ (TauReal.fromTauRat 4) · (TauReal.arctan_of_rat_seq 1)`

    The existing `TauReal.pi` (defined Wave 3c as the Leibniz-pairs
    all-positive series `Σ 8/((4k+1)(4k+3))`) is Cauchy-equivalent to
    `4 · arctan_of_rat_seq(1)` (the general arctan partial-sum series
    at `x = 1`).

    This is the central renumbering identity required for step 5 of
    the Machin chain — connecting Machin's
    `16·arctan(1/5) − 4·arctan(1/239)` cisTauReal-level identity back
    to the existing TauLib π via `arctan(1) = π/4`. With this
    equivalence in hand, the path to `MachinIdentity` reduces to the
    cisTauReal-level chain plus the `arctan(1)`-vs-cisTauReal angle
    argument.

    Proof: via `equiv_of_pointwise` on the pointwise-equiv per-depth
    identity `pi.approx n ≈ (4·arctan(1)).approx n` shipped in
    `TauReal.pi_approx_equiv_four_arctan_one_approx`. -/
theorem TauReal.pi_equiv_four_arctan_one :
    TauReal.equiv
      TauReal.pi
      ((TauReal.fromTauRat ⟨⟨4, 0⟩, 1, by norm_num⟩).mul
        (TauReal.arctan_of_rat_seq TauRat.one_canonical)) := by
  apply TauReal.equiv_of_pointwise
  exact TauReal.pi_approx_equiv_four_arctan_one_approx

end Tau.Boundary
