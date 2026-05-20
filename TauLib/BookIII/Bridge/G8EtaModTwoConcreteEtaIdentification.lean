import TauLib.BookIII.Bridge.G8EtaModTwoHurwitzOpenUnitProduct

/-!
# TauLib.BookIII.Bridge.G8EtaModTwoConcreteEtaIdentification

Concrete conditional-eta identification surface for the Lane-A eta bridge.

The bounded-sums corridor already proves that the naive conditional mod-two
series agrees with the concrete eta value.  The remaining analytic payload is
the Abel/Dirichlet identification of Mathlib's mod-two `ZMod.LFunction` with
that conditional value on `0 < x < 1`.  This module records that target
exactly and assembles the downstream zero-height guard path once product
continuation and concrete identification are supplied.

No result here uses RH, accepted coverage, the final live hinge, O3, full
divisor transfer, or analytic-completion uniqueness.
-/

set_option autoImplicit false

noncomputable section

namespace Tau.BookIII.Bridge

open Complex Filter

open scoped BigOperators Topology

-- ============================================================
-- ABEL / CONDITIONAL ETA IDENTIFICATION TARGET
-- ============================================================

/-- The precise Abel/Dirichlet continuation target on the real open unit
    interval: Mathlib's mod-two `LFunction` equals the concrete conditional eta
    value already theorem-backed by the bounded-sums module. -/
abbrev G8EtaModTwoConditionalEtaAbelIdentificationOnOpenUnit : Prop :=
  ∀ (x : ℝ) (hx0 : 0 < x) (hx1 : x < 1),
    g8EtaModTwoLFunction (x : ℂ) =
      (g8EtaModTwoNaiveLSeries_agreesWithConcreteEtaOnOpenUnit.naiveSeries
        x hx0 hx1).value

/-- The Abel-identification target is definitionally the existing concrete
    L-function/eta bridge. -/
theorem g8EtaModTwoConditionalEtaAbelIdentification_iff_concreteEta :
    G8EtaModTwoConditionalEtaAbelIdentificationOnOpenUnit ↔
      G8EtaModTwoLFunctionEqualsConcreteEtaOnOpenUnit :=
  Iff.rfl

/-- Abel identification supplies the existing concrete eta target. -/
theorem G8EtaModTwoConditionalEtaAbelIdentificationOnOpenUnit.toConcreteEta
    (hAbel : G8EtaModTwoConditionalEtaAbelIdentificationOnOpenUnit) :
    G8EtaModTwoLFunctionEqualsConcreteEtaOnOpenUnit :=
  hAbel

/-- The existing concrete eta target supplies the Abel-identification surface. -/
theorem G8EtaModTwoConditionalEtaAbelIdentificationOnOpenUnit.ofConcreteEta
    (hConcrete : G8EtaModTwoLFunctionEqualsConcreteEtaOnOpenUnit) :
    G8EtaModTwoConditionalEtaAbelIdentificationOnOpenUnit :=
  hConcrete

/-- Abel identification, together with the theorem-backed product identity,
    forces real-valued zeta on the open unit interval.  Thus the product
    continuation no longer needs an independent zeta-real hypothesis once the
    Abel target is supplied. -/
theorem g8RiemannZetaRealOnOpenUnit_of_conditionalEtaAbelIdentification
    (hAbel : G8EtaModTwoConditionalEtaAbelIdentificationOnOpenUnit) :
    G8RiemannZetaRealOnOpenUnit := by
  intro x hx0 hx1
  have hEq :
      (g8DirichletEtaDenominator x : ℂ) * riemannZeta (x : ℂ) =
        (g8EtaModTwoNaiveLSeries_agreesWithConcreteEtaOnOpenUnit.naiveSeries
          x hx0 hx1).value := by
    rw [← g8EtaModTwoLFunction_openUnitProductIdentity x hx0 hx1]
    exact hAbel x hx0 hx1
  have hImMul :
      ((g8DirichletEtaDenominator x : ℂ) *
          riemannZeta (x : ℂ)).im = 0 := by
    rw [hEq]
    exact
      g8EtaModTwoNaiveLSeries_agreesWithConcreteEtaOnOpenUnit.naiveIm_eq_zero
        x hx0 hx1
  have hDenNe : g8DirichletEtaDenominator x ≠ 0 :=
    g8DirichletEtaDenominator_ne_zero hx0 hx1
  have hMul :
      g8DirichletEtaDenominator x *
          (riemannZeta (x : ℂ)).im = 0 := by
    simpa using hImMul
  exact (mul_eq_zero.mp hMul).resolve_left hDenNe

-- ============================================================
-- OPEN-UNIT ETA CLOSURE DATA
-- ============================================================

/-- Full open-unit eta closure data after the right-half-plane product theorem:
    Hurwitz product continuation plus Abel identification with the concrete
    conditional eta value. -/
structure G8EtaModTwoOpenUnitEtaClosureData where
  productEvidence : G8EtaModTwoHurwitzProductContinuationEvidence
  abelIdentification :
    G8EtaModTwoConditionalEtaAbelIdentificationOnOpenUnit

/-- Reduced eta closure data after the product identity has been closed by
    analytic continuation.  The two remaining payloads are real-valued zeta on
    the open unit interval and Abel identification with the concrete eta
    value. -/
structure G8EtaModTwoReducedOpenUnitEtaClosureData where
  zetaReal : G8RiemannZetaRealOnOpenUnit
  abelIdentification :
    G8EtaModTwoConditionalEtaAbelIdentificationOnOpenUnit

/-- Reduced closure data expands into the previous closure package using the
    theorem-backed open-unit product identity. -/
def G8EtaModTwoReducedOpenUnitEtaClosureData.toClosureData
    (data : G8EtaModTwoReducedOpenUnitEtaClosureData) :
    G8EtaModTwoOpenUnitEtaClosureData where
  productEvidence :=
    G8EtaModTwoHurwitzProductContinuationEvidence.ofZetaReal
      data.zetaReal
  abelIdentification := data.abelIdentification

/-- Abel identification alone now supplies the reduced eta closure data:
    zeta-real follows from Abel plus the theorem-backed product identity. -/
def G8EtaModTwoReducedOpenUnitEtaClosureData.ofAbelIdentification
    (hAbel : G8EtaModTwoConditionalEtaAbelIdentificationOnOpenUnit) :
    G8EtaModTwoReducedOpenUnitEtaClosureData where
  zetaReal :=
    g8RiemannZetaRealOnOpenUnit_of_conditionalEtaAbelIdentification
      hAbel
  abelIdentification := hAbel

/-- Abel identification alone expands into the previous closure package. -/
def G8EtaModTwoOpenUnitEtaClosureData.ofAbelIdentification
    (hAbel : G8EtaModTwoConditionalEtaAbelIdentificationOnOpenUnit) :
    G8EtaModTwoOpenUnitEtaClosureData :=
  (G8EtaModTwoReducedOpenUnitEtaClosureData.ofAbelIdentification
    hAbel).toClosureData

/-- Reduced closure data is enough for the existing open-unit continuation
    package. -/
def G8EtaModTwoReducedOpenUnitEtaClosureData.toContinuationData
    (data : G8EtaModTwoReducedOpenUnitEtaClosureData) :
    G8EtaModTwoOpenUnitContinuationData where
  productContinuation :=
    (G8EtaModTwoHurwitzProductContinuationEvidence.ofZetaReal
      data.zetaReal).toProductContinuation
  lFunctionConcreteEta := data.abelIdentification.toConcreteEta

/-- Reduced closure data supplies the open-unit eta-zeta identity. -/
theorem G8EtaModTwoReducedOpenUnitEtaClosureData.etaZetaIdentity
    (data : G8EtaModTwoReducedOpenUnitEtaClosureData) :
    G8DirichletEtaZetaIdentityOnOpenUnit :=
  data.toContinuationData.etaZetaIdentity

/-- Reduced closure data discharges the zero-height axis guard. -/
def G8EtaModTwoReducedOpenUnitEtaClosureData.zeroHeightDischarge
    (data : G8EtaModTwoReducedOpenUnitEtaClosureData) :
    G8ActualXiZeroHeightAxisGuardDischarge :=
  data.toContinuationData.zeroHeightDischarge

/-- Abel identification is exactly sufficient for the open-unit eta-zeta
    identity after the product side is closed theorem-backed. -/
theorem g8DirichletEtaZetaIdentityOnOpenUnit_of_conditionalEtaAbelIdentification
    (hAbel : G8EtaModTwoConditionalEtaAbelIdentificationOnOpenUnit) :
    G8DirichletEtaZetaIdentityOnOpenUnit :=
  (G8EtaModTwoReducedOpenUnitEtaClosureData.ofAbelIdentification
    hAbel).etaZetaIdentity

/-- Abel identification alone discharges the zero-height axis guard through the
    closed product identity and the existing eta positivity/sign algebra. -/
def G8ActualXiZeroHeightAxisGuardDischarge.ofConditionalEtaAbelIdentification
    (hAbel : G8EtaModTwoConditionalEtaAbelIdentificationOnOpenUnit) :
    G8ActualXiZeroHeightAxisGuardDischarge :=
  (G8EtaModTwoReducedOpenUnitEtaClosureData.ofAbelIdentification
    hAbel).zeroHeightDischarge

/-- The closure data is exactly the existing open-unit continuation package. -/
def G8EtaModTwoOpenUnitEtaClosureData.toContinuationData
    (data : G8EtaModTwoOpenUnitEtaClosureData) :
    G8EtaModTwoOpenUnitContinuationData where
  productContinuation := data.productEvidence.toProductContinuation
  lFunctionConcreteEta := data.abelIdentification.toConcreteEta

/-- Closure data supplies the open-unit eta-zeta identity. -/
theorem G8EtaModTwoOpenUnitEtaClosureData.etaZetaIdentity
    (data : G8EtaModTwoOpenUnitEtaClosureData) :
    G8DirichletEtaZetaIdentityOnOpenUnit :=
  data.toContinuationData.etaZetaIdentity

/-- Closure data supplies real zeta nonvanishing on the open unit interval. -/
theorem G8EtaModTwoOpenUnitEtaClosureData.riemannZetaOpenUnitNonvanishing
    (data : G8EtaModTwoOpenUnitEtaClosureData) :
    G8RiemannZetaOpenUnitIntervalNonvanishing :=
  data.toContinuationData.riemannZetaOpenUnitNonvanishing

/-- Closure data discharges the zero-height axis guard. -/
def G8EtaModTwoOpenUnitEtaClosureData.zeroHeightDischarge
    (data : G8EtaModTwoOpenUnitEtaClosureData) :
    G8ActualXiZeroHeightAxisGuardDischarge :=
  data.toContinuationData.zeroHeightDischarge

-- ============================================================
-- RED-TEAM FALSIFIERS
-- ============================================================

/-- Missing Abel/conditional-eta identification refutes full eta closure data. -/
structure G8EtaModTwoMissingConditionalEtaAbelIdentification where
  missing : ¬ G8EtaModTwoConditionalEtaAbelIdentificationOnOpenUnit

/-- Missing Abel identification refutes closure data. -/
theorem G8EtaModTwoMissingConditionalEtaAbelIdentification.refutes
    (w : G8EtaModTwoMissingConditionalEtaAbelIdentification)
    (data : G8EtaModTwoOpenUnitEtaClosureData) :
    False :=
  w.missing data.abelIdentification

/-- A pointwise L-function/concrete-eta mismatch refutes Abel identification. -/
theorem G8EtaModTwoLFunctionNaiveSeriesMismatch.refutesAbelIdentification
    (w : G8EtaModTwoLFunctionNaiveSeriesMismatch
      g8EtaModTwoNaiveLSeries_agreesWithConcreteEtaOnOpenUnit)
    (hAbel : G8EtaModTwoConditionalEtaAbelIdentificationOnOpenUnit) :
    False :=
  w.refutesLFunctionBridge hAbel.toConcreteEta

/-- A Hurwitz product mismatch refutes full eta closure data. -/
theorem G8EtaModTwoHurwitzOpenUnitProductMismatch.refutesClosureData
    (w : G8EtaModTwoHurwitzOpenUnitProductMismatch)
    (data : G8EtaModTwoOpenUnitEtaClosureData) :
    False :=
  w.refutes data.productEvidence

/-- Missing real-valued zeta readout refutes reduced eta closure data. -/
structure G8EtaModTwoMissingOpenUnitZetaReal where
  missing : ¬ G8RiemannZetaRealOnOpenUnit

/-- Missing real-valued zeta readout refutes the reduced closure package. -/
theorem G8EtaModTwoMissingOpenUnitZetaReal.refutesReducedClosureData
    (w : G8EtaModTwoMissingOpenUnitZetaReal)
    (data : G8EtaModTwoReducedOpenUnitEtaClosureData) :
    False :=
  w.missing data.zetaReal

end Tau.BookIII.Bridge
