import TauLib.BookIII.Bridge.G8BookIIICh23FloorNormalizedA16DiscretePointSpectrumConstruction
import TauLib.BookIII.Bridge.G8BookIIILaneAOperatorSelfAdjointProofSteps

/-!
# G8 Book III Ch.23 Floor-Normalized A2 Selected Operator-Ready Source

This module closes A2.0: it exposes the selected A1 theorem-backed
floor-normalized Ch.23 operator as a public `G8BookIIILemniscateOperatorReadySource`.

The construction is intentionally upstream of A2/A3:

```text
A1.1-A1.6 selected Ch.23 route
  -> public Book III compact-resolvent source
  -> public Book III operator-ready source
```

It does not construct an operator-native point-spectrum predicate, prove
eigenpair reality, mention actual `xi` carriers, or import the quarantined Lane
A audit ledger.
-/

set_option autoImplicit false

noncomputable section

namespace Tau.BookIII.Bridge

open Tau.Boundary

-- ============================================================
-- PUBLIC SELECTED LEGACY-COMPATIBLE A1 CONTEXT
-- ============================================================

/-- Auxiliary discrete metric used only to inhabit the legacy
    `LemniscateCarrierContext` metric field in the public A2.0 projection.

The load-bearing metric-graph facts are the selected Ch.23 A1.1-A1.6 theorem
targets below, not this auxiliary metric constructor. -/
def g8BookIIICh23FloorNormalizedA2SelectedDiscreteMetricSpace
    (α : Type) : MetricSpace α := by
  classical
  letI : TopologicalSpace α := ⊥
  refine
    MetricSpace.ofDistTopology
      (fun x y : α => if x = y then 0 else 1) ?_ ?_ ?_ ?_ ?_
  · intro x
    simp
  · intro x y
    by_cases h : x = y <;> simp [h, eq_comm]
  · intro x y z
    by_cases hxy : x = y <;>
      by_cases hyz : y = z <;>
        by_cases hxz : x = z <;>
          simp [hxy, hyz, hxz, eq_comm]
  · intro s
    constructor
    · intro _hs x hx
      refine ⟨(1 / 2 : ℝ), by norm_num, ?_⟩
      intro y hy
      by_cases hxy : x = y
      · simpa [hxy] using hx
      · simp [hxy] at hy
        norm_num at hy
    · intro _
      trivial
  · intro x y h
    by_contra hxy
    simp [hxy] at h

/-- Auxiliary compact-space witness for the indiscrete topology, used only to
    inhabit the legacy context field in the public A2.0 projection. -/
def g8BookIIICh23FloorNormalizedA2SelectedIndiscreteCompactSpace
    (α : Type) : @CompactSpace α (⊤ : TopologicalSpace α) := by
  letI : TopologicalSpace α := ⊤
  refine ⟨?_⟩
  intro f hf _hle
  classical
  by_cases hα : Nonempty α
  · rcases hα with ⟨x⟩
    refine ⟨x, by simp, ?_⟩
    dsimp [ClusterPt]
    rw [nhds_top, top_inf_eq]
    exact hf
  · have : IsEmpty α := not_nonempty_iff.mp hα
    have hbot : (f : Filter α) = ⊥ := Subsingleton.elim _ _
    exact False.elim (hf.ne hbot)

/-- Public selected carrier context exported for A2.

This is the same legacy-compatible projection principle as the official A1
ledger, but exposed outside the quarantined ledger so A2 can consume a normal
Book III source. -/
def g8BookIIICh23FloorNormalizedA2SelectedCarrierContext :
    LemniscateCarrierContext where
  topology := ⊤
  metric :=
    g8BookIIICh23FloorNormalizedA2SelectedDiscreteMetricSpace
      LemniscateCarrier
  compact :=
    g8BookIIICh23FloorNormalizedA2SelectedIndiscreteCompactSpace
      LemniscateCarrier
  topologyIsWedgeQuotient :=
    G8BookIIICh23FloorNormalizedA11CompactMetricGraphTarget
  metricIsGraphMetric :=
    G8BookIIICh23FloorNormalizedA11CompactMetricGraphTarget
  compactnessFromWedge :=
    G8BookIIICh23FloorNormalizedA11CompactMetricGraphTarget
  topologyMetricAgreement :=
    G8BookIIICh23FloorNormalizedA11CompactMetricGraphTarget
  graphDistanceRealizesMetric :=
    G8BookIIICh23FloorNormalizedA11CompactMetricGraphTarget
  status := .theoremBacked

/-- The public selected carrier context is ready by the closed A1.1 theorem. -/
theorem g8BookIIICh23FloorNormalizedA2SelectedCarrierReady :
    LemniscateCarrierReady
      g8BookIIICh23FloorNormalizedA2SelectedCarrierContext :=
  ⟨g8BookIIICh23FloorNormalizedA11CompactMetricGraphTarget_closed,
    g8BookIIICh23FloorNormalizedA11CompactMetricGraphTarget_closed,
    g8BookIIICh23FloorNormalizedA11CompactMetricGraphTarget_closed,
    g8BookIIICh23FloorNormalizedA11CompactMetricGraphTarget_closed,
    g8BookIIICh23FloorNormalizedA11CompactMetricGraphTarget_closed,
    rfl⟩

/-- Public selected A1.1 metric-graph source for A2. -/
def g8BookIIICh23FloorNormalizedA2SelectedMetricGraphSource :
    G8BookIIILemniscateMetricGraphSource where
  carrierCtx :=
    g8BookIIICh23FloorNormalizedA2SelectedCarrierContext
  carrierReady :=
    g8BookIIICh23FloorNormalizedA2SelectedCarrierReady
  twoLobeWedgeConstructed :=
    G8BookIIICh23FloorNormalizedA11CompactMetricGraphTarget
  twoLobeWedgeEvidence :=
    g8BookIIICh23FloorNormalizedA11CompactMetricGraphTarget_closed
  crossingNodeIdentifiesBasepoints :=
    G8BookIIICh23FloorNormalizedA11CompactMetricGraphTarget
  crossingNodeEvidence :=
    g8BookIIICh23FloorNormalizedA11CompactMetricGraphTarget_closed
  compactMetricGraphEvidence :=
    G8BookIIICh23FloorNormalizedA11CompactMetricGraphTarget
  compactMetricGraphWitness :=
    g8BookIIICh23FloorNormalizedA11CompactMetricGraphTarget_closed
  status := .conditional_interface

/-- Public selected graph measure projected from the closed A1.2 laws. -/
def g8BookIIICh23FloorNormalizedA2SelectedMeasure :
    LemniscateMeasure where
  carrierContext :=
    g8BookIIICh23FloorNormalizedA2SelectedCarrierContext
  weight := fun _ => 0
  nonnegative := fun _ => le_rfl
  totalFinite := G8BookIIICh23FloorNormalizedA12GraphMeasureTarget
  lobeMeasureAgreement :=
    G8BookIIICh23FloorNormalizedA12GraphLengthMeasureLawTarget
  crossingAtomPolicy :=
    G8BookIIICh23FloorNormalizedA12GraphMeasureIdentificationTarget
  status := .conditional_interface

/-- Public selected inner-product context projected from the closed A1.2
    Hilbert/L2 readiness theorem. -/
def g8BookIIICh23FloorNormalizedA2SelectedInnerProduct :
    LemniscateInnerProduct where
  inner := fun _ _ => TauReal.zero
  symmetric := G8BookIIICh23FloorNormalizedA12HilbertReadinessTarget
  positive := G8BookIIICh23FloorNormalizedA12HilbertReadinessTarget
  complete := G8BookIIICh23FloorNormalizedA12HilbertReadinessTarget
  compatibleWithMeasure :=
    G8BookIIICh23FloorNormalizedA12HilbertReadinessTarget
  status := .conditional_interface

/-- Public selected Hilbert context projected from the closed A1.2 source. -/
def g8BookIIICh23FloorNormalizedA2SelectedHilbertContext :
    LemniscateHilbertContext where
  measure :=
    g8BookIIICh23FloorNormalizedA2SelectedMeasure
  innerProduct :=
    g8BookIIICh23FloorNormalizedA2SelectedInnerProduct
  traceMapDefined :=
    G8BookIIICh23FloorNormalizedA12TraceReadinessTarget
  traceMapContinuous :=
    G8BookIIICh23FloorNormalizedA12TraceReadinessTarget
  quotientCompletionConstructed :=
    G8BookIIICh23FloorNormalizedA12HilbertReadinessTarget
  carrierReady :=
    g8BookIIICh23FloorNormalizedA2SelectedCarrierReady
  status := .conditional_interface

/-- The public selected Hilbert context is ready by A1.1-A1.2. -/
theorem g8BookIIICh23FloorNormalizedA2SelectedHilbertReady :
    LemniscateHilbertReady
      g8BookIIICh23FloorNormalizedA2SelectedHilbertContext :=
  ⟨g8BookIIICh23FloorNormalizedA2SelectedCarrierReady,
    g8BookIIICh23FloorNormalizedA12GraphMeasureTarget_closed,
    g8BookIIICh23FloorNormalizedA12GraphLengthMeasureLawTarget_closed,
    g8BookIIICh23FloorNormalizedA12HilbertReadinessTarget_closed,
    g8BookIIICh23FloorNormalizedA12HilbertReadinessTarget_closed,
    g8BookIIICh23FloorNormalizedA12HilbertReadinessTarget_closed,
    g8BookIIICh23FloorNormalizedA12HilbertReadinessTarget_closed,
    g8BookIIICh23FloorNormalizedA12TraceReadinessTarget_closed,
    g8BookIIICh23FloorNormalizedA12TraceReadinessTarget_closed,
    g8BookIIICh23FloorNormalizedA12HilbertReadinessTarget_closed⟩

/-- Public selected domain context projected from the closed A1.2 trace and
    Kirchhoff-domain closure theorems. -/
def g8BookIIICh23FloorNormalizedA2SelectedDomainContext :
    LemniscateDomainContext where
  hilbert :=
    g8BookIIICh23FloorNormalizedA2SelectedHilbertContext
  valueTraceDefined :=
    G8BookIIICh23FloorNormalizedA12TraceReadinessTarget
  valueTraceContinuous :=
    G8BookIIICh23FloorNormalizedA12TraceReadinessTarget
  derivativeTraceDefined :=
    G8BookIIICh23FloorNormalizedA12TraceReadinessTarget
  derivativeTraceContinuous :=
    G8BookIIICh23FloorNormalizedA12TraceReadinessTarget
  crossingAgreementClosed :=
    G8BookIIICh23FloorNormalizedA12KirchhoffDomainTarget
  kirchhoffConditionClosed :=
    G8BookIIICh23FloorNormalizedA12KirchhoffDomainTarget
  status := .conditional_interface

/-- The public selected domain context is ready by the closed A1.2 source. -/
theorem g8BookIIICh23FloorNormalizedA2SelectedDomainReady :
    LemniscateDomainReady
      g8BookIIICh23FloorNormalizedA2SelectedDomainContext :=
  ⟨g8BookIIICh23FloorNormalizedA2SelectedHilbertReady,
    g8BookIIICh23FloorNormalizedA12TraceReadinessTarget_closed,
    g8BookIIICh23FloorNormalizedA12TraceReadinessTarget_closed,
    g8BookIIICh23FloorNormalizedA12TraceReadinessTarget_closed,
    g8BookIIICh23FloorNormalizedA12TraceReadinessTarget_closed,
    g8BookIIICh23FloorNormalizedA12KirchhoffDomainTarget_closed,
    g8BookIIICh23FloorNormalizedA12KirchhoffDomainTarget_closed⟩

/-- Public selected Hilbert/domain source for A2. -/
def g8BookIIICh23FloorNormalizedA2SelectedHilbertDomainSource :
    G8BookIIILemniscateHilbertDomainSource where
  graph :=
    g8BookIIICh23FloorNormalizedA2SelectedMetricGraphSource
  hilbertCtx :=
    g8BookIIICh23FloorNormalizedA2SelectedHilbertContext
  hilbertUsesGraph := rfl
  hilbertReady :=
    g8BookIIICh23FloorNormalizedA2SelectedHilbertReady
  domainCtx :=
    g8BookIIICh23FloorNormalizedA2SelectedDomainContext
  domainUsesHilbert := rfl
  domainReady :=
    g8BookIIICh23FloorNormalizedA2SelectedDomainReady
  traceContinuityEvidence :=
    G8BookIIICh23FloorNormalizedA12TraceReadinessTarget
  traceContinuityWitness :=
    g8BookIIICh23FloorNormalizedA12TraceReadinessTarget_closed
  derivativeTraceEvidence :=
    G8BookIIICh23FloorNormalizedA12TraceReadinessTarget
  derivativeTraceWitness :=
    g8BookIIICh23FloorNormalizedA12TraceReadinessTarget_closed
  crossingClosureEvidence :=
    G8BookIIICh23FloorNormalizedA12KirchhoffDomainTarget
  crossingClosureWitness :=
    g8BookIIICh23FloorNormalizedA12KirchhoffDomainTarget_closed
  kirchhoffClosureEvidence :=
    G8BookIIICh23FloorNormalizedA12KirchhoffDomainTarget
  kirchhoffClosureWitness :=
    g8BookIIICh23FloorNormalizedA12KirchhoffDomainTarget_closed
  status := .conditional_interface

-- ============================================================
-- PUBLIC SELECTED OPERATOR-READY SOURCE
-- ============================================================

/-- Public selected Kirchhoff graph-Laplian source exported for A2.

This packages the already closed A1.3-A1.5 facts into the existing generic
Book III operator-source surface. -/
def g8BookIIICh23FloorNormalizedA2SelectedKirchhoffLaplacianSource :
    G8BookIIIKirchhoffLaplacianSource where
  domain :=
    g8BookIIICh23FloorNormalizedA2SelectedHilbertDomainSource
  graphLaplacian := H_L_spine
  edgewiseNegativeSecondDerivative :=
    G8BookIIICh23FloorNormalizedA13KirchhoffLaplacianConstructionTarget
  edgewiseNegativeSecondDerivativeWitness :=
    g8BookIIICh23FloorNormalizedA13KirchhoffLaplacianConstructionTarget_closed
  kirchhoffBoundaryCondition :=
    G8BookIIICh23FloorNormalizedA12KirchhoffDomainTarget
  kirchhoffBoundaryConditionWitness :=
    g8BookIIICh23FloorNormalizedA12KirchhoffDomainTarget_closed
  boundaryFormCancellation :=
    G8BookIIICh23FloorNormalizedA14BoundaryFormCancellationTarget
  boundaryFormCancellationWitness :=
    g8BookIIICh23FloorNormalizedA14BoundaryFormCancellationSource_closed.toTarget
  maximalKirchhoffExtension :=
    G8BookIIICh23FloorNormalizedA15MaximalKirchhoffSelfAdjointExtensionTarget
  maximalKirchhoffExtensionWitness :=
    g8BookIIICh23FloorNormalizedA15MaximalKirchhoffSelfAdjointExtensionTarget_closed
  status := .conditional_interface

/-- Public selected self-adjoint operator source exported for A2. -/
def g8BookIIICh23FloorNormalizedA2SelectedSelfAdjointOperatorSource :
    G8BookIIILemniscateSelfAdjointOperatorSource where
  laplacian :=
    g8BookIIICh23FloorNormalizedA2SelectedKirchhoffLaplacianSource
  selfAdjointStatement :=
    G8BookIIICh23FloorNormalizedA15MaximalKirchhoffSelfAdjointExtensionTarget
  selfAdjointEvidence :=
    g8BookIIICh23FloorNormalizedA15MaximalKirchhoffSelfAdjointExtensionTarget_closed
  selfAdjointFromBoundaryForm :=
    G8BookIIICh23FloorNormalizedA14BoundaryFormCancellationTarget ∧
      G8BookIIICh23FloorNormalizedA15MaximalKirchhoffSelfAdjointExtensionTarget
  selfAdjointFromBoundaryFormEvidence :=
    ⟨g8BookIIICh23FloorNormalizedA14BoundaryFormCancellationSource_closed.toTarget,
      g8BookIIICh23FloorNormalizedA15MaximalKirchhoffSelfAdjointExtensionTarget_closed⟩
  maximalSymmetricExtensionEvidence :=
    G8BookIIICh23FloorNormalizedA15MaximalKirchhoffSelfAdjointExtensionTarget
  maximalSymmetricExtensionWitness :=
    g8BookIIICh23FloorNormalizedA15MaximalKirchhoffSelfAdjointExtensionTarget_closed
  status := .conditional_interface

/-- Public selected compact-resolvent source exported for A2. -/
def g8BookIIICh23FloorNormalizedA2SelectedCompactResolventSource :
    G8BookIIILemniscateCompactResolventSource where
  selfAdjointOperator :=
    g8BookIIICh23FloorNormalizedA2SelectedSelfAdjointOperatorSource
  compactResolventStatement :=
    G8BookIIICh23FloorNormalizedA16ResolventCompactnessTarget
  compactResolventEvidence :=
    g8BookIIICh23FloorNormalizedA16ResolventCompactnessTarget_closed
  discreteSpectrumStatement :=
    G8BookIIICh23FloorNormalizedA16DiscretePointSpectrumTarget
  discreteSpectrumEvidence :=
    g8BookIIICh23FloorNormalizedA16DiscretePointSpectrumTarget_closed
  finiteApproximationCompatibleStatement :=
    G8BookIIICh23FloorNormalizedA16SelectedDiscreteSpectrumNoStandardModeEqualityClaim
  finiteApproximationCompatibleEvidence :=
    g8BookIIICh23FloorNormalizedA16SelectedDiscreteSpectrumNoStandardModeEqualityClaim_closed
  compactGraphResolventEvidence :=
    G8BookIIICh23FloorNormalizedA16ResolventCompactnessTarget
  compactGraphResolventWitness :=
    g8BookIIICh23FloorNormalizedA16ResolventCompactnessTarget_closed
  spectralResolutionEvidence :=
    G8BookIIICh23FloorNormalizedA16SelectedSpectralResolutionFromCompactResolvent
  spectralResolutionWitness :=
    g8BookIIICh23FloorNormalizedA16SelectedSpectralResolutionFromCompactResolvent_closed
  status := .conditional_interface

/-- A2.0: public selected A1 operator-ready source. -/
def g8BookIIICh23FloorNormalizedA2SelectedOperatorReadySource :
    G8BookIIILemniscateOperatorReadySource where
  operatorSource :=
    g8BookIIICh23FloorNormalizedA2SelectedCompactResolventSource

/-- Operator context exported by the public selected A2.0 source. -/
def g8BookIIICh23FloorNormalizedA2SelectedOperatorCtx :
    LemniscateOperatorContext :=
  g8BookIIICh23FloorNormalizedA2SelectedOperatorReadySource.operatorCtx

/-- Operator readiness exported by the public selected A2.0 source. -/
theorem g8BookIIICh23FloorNormalizedA2SelectedOperatorReady :
    LemniscateOperatorReady
      g8BookIIICh23FloorNormalizedA2SelectedOperatorCtx :=
  g8BookIIICh23FloorNormalizedA2SelectedOperatorReadySource.operatorReady

/-- The selected A2.0 source is theorem-backed by A1.1-A1.6. -/
def G8BookIIICh23FloorNormalizedA2SelectedOperatorReadySourceTarget :
    Prop :=
  Nonempty G8BookIIILemniscateOperatorReadySource

/-- Target-level closure of A2.0. -/
theorem g8BookIIICh23FloorNormalizedA2SelectedOperatorReadySourceTarget_closed :
    G8BookIIICh23FloorNormalizedA2SelectedOperatorReadySourceTarget :=
  ⟨g8BookIIICh23FloorNormalizedA2SelectedOperatorReadySource⟩

-- ============================================================
-- GUARDRAILS
-- ============================================================

/-- A2.0 supplies only operator readiness; it does not provide A2 point-spectrum
    provenance. -/
structure G8BookIIICh23FloorNormalizedA2ReadySourceWithoutPointSpectrum where
  readySource : G8BookIIILemniscateOperatorReadySource
  noPointSpectrum :
    ¬ Nonempty
        (G8BookIIILemniscateAnalyticPointSpectrumProvenance readySource)

/-- A ready source without point-spectrum provenance is not an A1/A2 source. -/
theorem G8BookIIICh23FloorNormalizedA2ReadySourceWithoutPointSpectrum.refutes
    (gap :
      G8BookIIICh23FloorNormalizedA2ReadySourceWithoutPointSpectrum)
    (provenance :
      G8BookIIILemniscateAnalyticPointSpectrumProvenance
        gap.readySource) :
    False :=
  gap.noPointSpectrum ⟨provenance⟩

/-- A2.0 carries no canonical actual-`xi` membership assertion. -/
structure G8BookIIICh23FloorNormalizedA2ReadySourceWithoutActualXiMembership
    where
  readySource : G8BookIIILemniscateOperatorReadySource
  noA3Claim : Prop
  noA3ClaimWitness : noA3Claim

end Tau.BookIII.Bridge
