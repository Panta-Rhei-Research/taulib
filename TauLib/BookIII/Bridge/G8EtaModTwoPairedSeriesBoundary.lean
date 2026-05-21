import TauLib.BookIII.Bridge.G8EtaModTwoExpZetaBoundaryDischarge

/-!
# TauLib.BookIII.Bridge.G8EtaModTwoPairedSeriesBoundary

Paired-series boundary reduction for the remaining Lane-A zero-height eta
payload.

The concrete eta value is currently represented by ordinary alternating
partial sums.  This module closes the finite grouping step: grouping the
odd/even positive-index terms in pairs has the same limit as the concrete eta
series on `0 < x < 1`.  The remaining analytic theorem is now the sharply
named boundary-value statement that the same paired partial sums tend to
`-expZeta`.

No result here uses RH, accepted coverage, the final live hinge, O3, full
divisor transfer, or analytic-completion uniqueness.
-/

set_option autoImplicit false

noncomputable section

namespace Tau.BookIII.Bridge

open Complex Filter

open scoped BigOperators Topology

-- ============================================================
-- CONCRETE PAIRED PARTIAL SUMS
-- ============================================================

/-- The concrete odd/even pair term in the real open-unit eta series.

This is deliberately expressed in the already theorem-backed concrete
conditional eta language, avoiding any analytic identification with Mathlib's
continued `expZeta`. -/
def g8EtaModTwoConcretePairedTerm (x : ℝ) (n : ℕ) : ℂ :=
  g8EtaModTwoNatCoeff (2 * n + 1) *
      (g8DirichletEtaMagnitude x (2 * n) : ℂ) +
    g8EtaModTwoNatCoeff (2 * n + 2) *
      (g8DirichletEtaMagnitude x (2 * n + 1) : ℂ)

/-- Finite partial sums of the concrete paired eta series. -/
def g8EtaModTwoConcretePairedPartial (x : ℝ) (n : ℕ) : ℂ :=
  ∑ k ∈ Finset.range n, g8EtaModTwoConcretePairedTerm x k

/-- One concrete pair is exactly the sum of the corresponding two naive
    positive-index eta terms. -/
theorem g8EtaModTwoConcretePairedTerm_eq_naive_pair
    (x : ℝ) (n : ℕ) :
    g8EtaModTwoConcretePairedTerm x n =
      g8EtaModTwoNatCoeff (2 * n + 1) *
          (g8DirichletEtaMagnitude x (2 * n) : ℂ) +
        g8EtaModTwoNatCoeff ((2 * n + 1) + 1) *
          (g8DirichletEtaMagnitude x (2 * n + 1) : ℂ) := by
  simp [g8EtaModTwoConcretePairedTerm, Nat.add_assoc]

/-- The paired concrete partial sum over `n` pairs is the naive conditional
    eta partial sum over the first `2n` terms. -/
theorem g8EtaModTwoConcretePairedPartial_eq_naive_even
    (x : ℝ) (n : ℕ) :
    g8EtaModTwoConcretePairedPartial x n =
      g8EtaModTwoNaiveConditionalPartial x (2 * n) := by
  induction n with
  | zero =>
      simp [g8EtaModTwoConcretePairedPartial,
        g8EtaModTwoNaiveConditionalPartial]
  | succ n ih =>
      rw [g8EtaModTwoConcretePairedPartial, Finset.sum_range_succ]
      rw [show 2 * Nat.succ n = 2 * n + 2 by omega]
      rw [g8EtaModTwoNaiveConditionalPartial, Finset.sum_range_succ]
      rw [Finset.sum_range_succ]
      change
        (∑ k ∈ Finset.range n, g8EtaModTwoConcretePairedTerm x k) +
            g8EtaModTwoConcretePairedTerm x n =
          (∑ k ∈ Finset.range (2 * n),
              g8EtaModTwoNatCoeff (k + 1) *
                (g8DirichletEtaMagnitude x k : ℂ)) +
            g8EtaModTwoNatCoeff (2 * n + 1) *
              (g8DirichletEtaMagnitude x (2 * n) : ℂ) +
            g8EtaModTwoNatCoeff (2 * n + 1 + 1) *
              (g8DirichletEtaMagnitude x (2 * n + 1) : ℂ)
      change
        g8EtaModTwoConcretePairedPartial x n +
            g8EtaModTwoConcretePairedTerm x n =
          (∑ k ∈ Finset.range (2 * n),
              g8EtaModTwoNatCoeff (k + 1) *
                (g8DirichletEtaMagnitude x k : ℂ)) +
            g8EtaModTwoNatCoeff (2 * n + 1) *
              (g8DirichletEtaMagnitude x (2 * n) : ℂ) +
            g8EtaModTwoNatCoeff (2 * n + 1 + 1) *
              (g8DirichletEtaMagnitude x (2 * n + 1) : ℂ)
      rw [ih]
      simp [g8EtaModTwoConcretePairedTerm,
        g8EtaModTwoNaiveConditionalPartial, Nat.add_comm]
      ring_nf

-- ============================================================
-- THEOREM-BACKED PAIRED LIMIT TO CONCRETE ETA
-- ============================================================

/-- The subsequence `n ↦ 2n` tends to infinity. -/
theorem g8_tendsto_two_mul_atTop :
    Tendsto (fun n : ℕ => 2 * n) atTop atTop := by
  rw [tendsto_atTop]
  intro b
  filter_upwards [eventually_ge_atTop b] with n hn
  omega

/-- The concrete paired partial sums tend to the same concrete conditional eta
    value on `0 < x < 1`. -/
theorem g8EtaModTwoConcretePairedPartial_tendsto_concreteEta
    (x : ℝ) (hx0 : 0 < x) (hx1 : x < 1) :
    Tendsto (g8EtaModTwoConcretePairedPartial x) atTop
      (𝓝 ((g8EtaModTwoNaiveLSeries_agreesWithConcreteEtaOnOpenUnit.naiveSeries
        x hx0 hx1).value)) := by
  have hNaive :=
    (g8EtaModTwoNaiveLSeries_agreesWithConcreteEtaOnOpenUnit.naiveSeries
      x hx0 hx1).partialTendsto
  have hEven :
      Tendsto
        (fun n : ℕ => g8EtaModTwoNaiveConditionalPartial x (2 * n))
        atTop
        (𝓝 ((g8EtaModTwoNaiveLSeries_agreesWithConcreteEtaOnOpenUnit.naiveSeries
          x hx0 hx1).value)) :=
    hNaive.comp g8_tendsto_two_mul_atTop
  exact hEven.congr'
    (Eventually.of_forall fun n =>
      (g8EtaModTwoConcretePairedPartial_eq_naive_even x n).symm)

-- ============================================================
-- EXACT EXPZETA BOUNDARY TARGET
-- ============================================================

/-- The exact remaining paired-series boundary theorem: the concrete paired
    partial sums have Mathlib's continued additive-character `expZeta` value
    as their boundary limit on the real open unit interval. -/
abbrev G8EtaModTwoPairedExpZetaBoundaryOnOpenUnit : Prop :=
  ∀ (x : ℝ) (_hx0 : 0 < x) (_hx1 : x < 1),
    Tendsto (g8EtaModTwoConcretePairedPartial x) atTop
      (𝓝 (- HurwitzZeta.expZeta
        (ZMod.toAddCircle (1 : ZMod 2)) (x : ℂ)))

/-- Paired ExpZeta boundary plus the theorem-backed concrete paired limit
    gives the pointwise ExpZeta/concrete-eta equality. -/
theorem g8EtaModTwoExpZetaConcreteEtaOnOpenUnit_of_pairedBoundary
    (hPaired : G8EtaModTwoPairedExpZetaBoundaryOnOpenUnit) :
    G8EtaModTwoExpZetaConcreteEtaOnOpenUnit := by
  intro x hx0 hx1
  exact tendsto_nhds_unique
    (g8EtaModTwoConcretePairedPartial_tendsto_concreteEta x hx0 hx1)
    (hPaired x hx0 hx1)

/-- The paired boundary theorem is enough to recover the ExpZeta Abel-boundary
    target. -/
theorem g8EtaModTwoExpZetaAbelBoundaryValueOnOpenUnit_of_pairedBoundary
    (hPaired : G8EtaModTwoPairedExpZetaBoundaryOnOpenUnit) :
    G8EtaModTwoExpZetaAbelBoundaryValueOnOpenUnit :=
  g8EtaModTwoExpZetaAbelBoundaryValueOnOpenUnit_of_concreteEta
    (g8EtaModTwoExpZetaConcreteEtaOnOpenUnit_of_pairedBoundary hPaired)

/-- The paired boundary theorem discharges the zero-height guard through the
    existing ExpZeta/concrete-eta corridor. -/
def G8ActualXiZeroHeightAxisGuardDischarge.ofEtaModTwoPairedBoundary
    (hPaired : G8EtaModTwoPairedExpZetaBoundaryOnOpenUnit) :
    G8ActualXiZeroHeightAxisGuardDischarge :=
  G8ActualXiZeroHeightAxisGuardDischarge.ofEtaModTwoExpZetaConcreteEta
    (g8EtaModTwoExpZetaConcreteEtaOnOpenUnit_of_pairedBoundary hPaired)

-- ============================================================
-- RED-TEAM FALSIFIERS
-- ============================================================

/-- A point where the theorem-backed paired concrete limit fails. -/
structure G8EtaModTwoConcretePairedLimitMismatch where
  x : ℝ
  pos : 0 < x
  lt_one : x < 1
  mismatch :
    ¬ Tendsto (g8EtaModTwoConcretePairedPartial x) atTop
      (𝓝 ((g8EtaModTwoNaiveLSeries_agreesWithConcreteEtaOnOpenUnit.naiveSeries
        x pos lt_one).value))

/-- The theorem-backed paired-limit lemma refutes a concrete paired-limit
    mismatch. -/
theorem G8EtaModTwoConcretePairedLimitMismatch.refutes
    (w : G8EtaModTwoConcretePairedLimitMismatch) :
    False :=
  w.mismatch
    (g8EtaModTwoConcretePairedPartial_tendsto_concreteEta
      w.x w.pos w.lt_one)

/-- A point where the paired partials do not tend to ExpZeta refutes the
    paired boundary theorem. -/
structure G8EtaModTwoPairedExpZetaBoundaryMismatch where
  x : ℝ
  pos : 0 < x
  lt_one : x < 1
  mismatch :
    ¬ Tendsto (g8EtaModTwoConcretePairedPartial x) atTop
      (𝓝 (- HurwitzZeta.expZeta
        (ZMod.toAddCircle (1 : ZMod 2)) (x : ℂ)))

/-- A pointwise paired-boundary mismatch refutes the global paired boundary
    theorem. -/
theorem G8EtaModTwoPairedExpZetaBoundaryMismatch.refutes
    (w : G8EtaModTwoPairedExpZetaBoundaryMismatch)
    (hPaired : G8EtaModTwoPairedExpZetaBoundaryOnOpenUnit) :
    False :=
  w.mismatch (hPaired w.x w.pos w.lt_one)

end Tau.BookIII.Bridge
