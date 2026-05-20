import TauLib.BookIII.Bridge.G8EtaModTwoAbelBoundaryClosure

/-!
# TauLib.BookIII.Bridge.G8EtaModTwoExpZetaBoundaryDischarge

Pointwise ExpZeta/concrete-eta discharge surface for the remaining Lane-A
zero-height payload.

The current theorem-backed Abel result already says that the shifted eta Abel
power series tends to the concrete conditional eta value.  Therefore the
remaining radial-boundary theorem is equivalent to the pointwise analytic
continuation equality

```text
concrete conditional eta value
  =
- HurwitzZeta.expZeta (ZMod.toAddCircle 1)
```

on `0 < x < 1`.  This module names that exact payload and proves all downstream
adapters from it.  It does not assert the equality unconditionally.
-/

set_option autoImplicit false

noncomputable section

namespace Tau.BookIII.Bridge

open Complex Filter

open scoped BigOperators Topology

-- ============================================================
-- EXACT POINTWISE EXPZETA / CONCRETE-ETA TARGET
-- ============================================================

/-- The exact remaining pointwise analytic-continuation payload: the concrete
    conditional eta value equals the negative additive-character `expZeta`
    value on the real open unit interval. -/
abbrev G8EtaModTwoExpZetaConcreteEtaOnOpenUnit : Prop :=
  ∀ (x : ℝ) (hx0 : 0 < x) (hx1 : x < 1),
    (g8EtaModTwoNaiveLSeries_agreesWithConcreteEtaOnOpenUnit.naiveSeries
      x hx0 hx1).value =
      - HurwitzZeta.expZeta (ZMod.toAddCircle (1 : ZMod 2)) (x : ℂ)

/-- The concrete-eta/ExpZeta equality is exactly sufficient for the remaining
    radial Abel-boundary theorem. -/
theorem g8EtaModTwoExpZetaAbelBoundaryValueOnOpenUnit_of_concreteEta
    (hConcrete : G8EtaModTwoExpZetaConcreteEtaOnOpenUnit) :
    G8EtaModTwoExpZetaAbelBoundaryValueOnOpenUnit := by
  intro x hx0 hx1
  have hAbel :=
    g8EtaModTwoAbelPowerSeries_tendsto_concreteEta x hx0 hx1
  simpa [hConcrete x hx0 hx1] using hAbel

/-- The concrete-eta/ExpZeta equality also supplies the previous
    L-function/concrete-eta identification target. -/
theorem g8EtaModTwoConditionalEtaAbelIdentificationOnOpenUnit_of_expZetaConcreteEta
    (hConcrete : G8EtaModTwoExpZetaConcreteEtaOnOpenUnit) :
    G8EtaModTwoConditionalEtaAbelIdentificationOnOpenUnit := by
  intro x hx0 hx1
  rw [g8EtaModTwoLFunction_eq_neg_expZeta]
  exact (hConcrete x hx0 hx1).symm

/-- The previous L-function/concrete-eta target is equivalent to the
    concrete-eta/ExpZeta equality, using the theorem-backed coefficient bridge. -/
theorem g8EtaModTwoExpZetaConcreteEtaOnOpenUnit_of_conditionalEta
    (hConditional : G8EtaModTwoConditionalEtaAbelIdentificationOnOpenUnit) :
    G8EtaModTwoExpZetaConcreteEtaOnOpenUnit := by
  intro x hx0 hx1
  rw [← g8EtaModTwoLFunction_eq_neg_expZeta]
  exact (hConditional x hx0 hx1).symm

/-- The pointwise equality recovers the open-unit eta-zeta identity through the
    existing Abel and product corridors. -/
theorem g8DirichletEtaZetaIdentityOnOpenUnit_of_expZetaConcreteEta
    (hConcrete : G8EtaModTwoExpZetaConcreteEtaOnOpenUnit) :
    G8DirichletEtaZetaIdentityOnOpenUnit :=
  g8DirichletEtaZetaIdentityOnOpenUnit_of_expZetaAbelBoundary
    (g8EtaModTwoExpZetaAbelBoundaryValueOnOpenUnit_of_concreteEta
      hConcrete)

/-- The pointwise equality discharges the zero-height axis guard through the
    existing eta corridor. -/
def G8ActualXiZeroHeightAxisGuardDischarge.ofEtaModTwoExpZetaConcreteEta
    (hConcrete : G8EtaModTwoExpZetaConcreteEtaOnOpenUnit) :
    G8ActualXiZeroHeightAxisGuardDischarge :=
  G8ActualXiZeroHeightAxisGuardDischarge.ofEtaModTwoExpZetaAbelBoundary
    (g8EtaModTwoExpZetaAbelBoundaryValueOnOpenUnit_of_concreteEta
      hConcrete)

-- ============================================================
-- PAIRED-SERIES PROOF TARGET
-- ============================================================

/-- The paired eta term that should be used in the future analytic proof on
    `0 < re s`: `(2n + 1)^(-s) - (2n + 2)^(-s)`. -/
def g8EtaModTwoPairedEtaTerm (s : ℂ) (n : ℕ) : ℂ :=
  ((2 * n + 1 : ℕ) : ℂ) ^ (-s) -
    ((2 * n + 2 : ℕ) : ℂ) ^ (-s)

/-- The paired eta series candidate.  The next analytic theorem should prove
    local convergence/analyticity on `0 < re s`, equality with `-expZeta` by
    continuation from the safe half-plane, and agreement with the concrete eta
    value on the real open unit interval. -/
def g8EtaModTwoPairedEtaSeries (s : ℂ) : ℂ :=
  ∑' n : ℕ, g8EtaModTwoPairedEtaTerm s n

/-- Named future proof target for the paired-series route.  It is deliberately
    just the exact pointwise payload needed by the current zero-height lane. -/
abbrev G8EtaModTwoPairedSeriesExpZetaDischargeTarget : Prop :=
  G8EtaModTwoExpZetaConcreteEtaOnOpenUnit

-- ============================================================
-- RED-TEAM FALSIFIER
-- ============================================================

/-- A point where the concrete conditional eta value differs from the
    additive-character `expZeta` value refutes the pointwise target. -/
structure G8EtaModTwoExpZetaConcreteEtaMismatch where
  x : ℝ
  pos : 0 < x
  lt_one : x < 1
  mismatch :
    (g8EtaModTwoNaiveLSeries_agreesWithConcreteEtaOnOpenUnit.naiveSeries
      x pos lt_one).value ≠
      - HurwitzZeta.expZeta (ZMod.toAddCircle (1 : ZMod 2)) (x : ℂ)

/-- A pointwise ExpZeta/concrete-eta mismatch refutes the global pointwise
    equality target. -/
theorem G8EtaModTwoExpZetaConcreteEtaMismatch.refutes
    (w : G8EtaModTwoExpZetaConcreteEtaMismatch)
    (hConcrete : G8EtaModTwoExpZetaConcreteEtaOnOpenUnit) :
    False :=
  w.mismatch (hConcrete w.x w.pos w.lt_one)

end Tau.BookIII.Bridge
