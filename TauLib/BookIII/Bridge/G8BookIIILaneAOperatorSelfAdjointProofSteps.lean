import TauLib.BookIII.Bridge.G8BookIIILaneAOperatorSelfAdjointProofSource

/-!
# TauLib.BookIII.Bridge.G8BookIIILaneAOperatorSelfAdjointProofSteps

Named proof-step refinement for Lane-A gates A1/A2.

The previous source module provides the proof-carrying chain.  This module
adds the exact theorem-target names from the A1/A2 proof map and sharpens the
A2 surface with an operator-native eigenpair predicate.  It still does not
construct the analytic Kirchhoff graph-operator theorem, does not touch A3,
and does not update the quarantined Lane-A axiom ledger.
-/

set_option autoImplicit false

noncomputable section

namespace Tau.BookIII.Bridge

-- ============================================================
-- PROOF-MAP THEOREM TARGET ALIASES
-- ============================================================

/-- Step 1 target: construct the Book III two-lobe compact metric graph. -/
def G8BookIIILemniscateMetricGraphReadinessTarget : Prop :=
  Nonempty G8BookIIILemniscateMetricGraphSource

/-- Step 2 target: construct Hilbert/domain readiness on the metric graph. -/
def G8BookIIILemniscateHilbertDomainReadinessTarget : Prop :=
  Nonempty G8BookIIILemniscateHilbertDomainSource

/-- Step 3 target: construct the Kirchhoff graph Laplacian source. -/
def G8BookIIIKirchhoffLaplacianConstructionTarget : Prop :=
  Nonempty G8BookIIIKirchhoffLaplacianSource

/-- Step 4 target: prove the Kirchhoff boundary-form cancellation. -/
def G8BookIIIBoundaryFormCancellationTarget
    (source : G8BookIIIKirchhoffLaplacianSource) : Prop :=
  source.boundaryFormCancellation

/-- Step 5 target: prove maximal Kirchhoff self-adjointness. -/
def G8BookIIIMaximalKirchhoffSelfAdjointExtensionTarget
    (source : G8BookIIILemniscateSelfAdjointOperatorSource) : Prop :=
  source.maximalSymmetricExtensionEvidence

/-- Step 6 target: prove compact resolvent for the Book III operator. -/
def G8BookIIILemniscateCompactResolventTarget
    (source : G8BookIIILemniscateCompactResolventSource) : Prop :=
  source.compactResolventStatement

/-- Step 6 target: prove the resulting point spectrum is discrete. -/
def G8BookIIILemniscateDiscretePointSpectrumTarget
    (source : G8BookIIILemniscateCompactResolventSource) : Prop :=
  source.discreteSpectrumStatement

/-- Step 9 target: prove analytic point-spectrum values are real-valued. -/
def G8BookIIILemniscateAnalyticPointSpectrumRealityTarget
    {operatorSource : G8BookIIILemniscateCompactResolventSource}
    (source :
      G8BookIIILemniscateAnalyticPointSpectrumSource operatorSource) :
    Prop :=
  ∀ spectralValue : ℂ,
    source.nativeMembership spectralValue → spectralValue.im = 0

/-- The current source packages expose every proof-map target as a field. -/
def G8BookIIIKirchhoffLaplacianSource.boundaryFormCancellationTarget
    (source : G8BookIIIKirchhoffLaplacianSource) :
    G8BookIIIBoundaryFormCancellationTarget source :=
  source.boundaryFormCancellationWitness

/-- The current self-adjoint source exposes the maximal-extension target. -/
def G8BookIIILemniscateSelfAdjointOperatorSource.maximalExtensionTarget
    (source : G8BookIIILemniscateSelfAdjointOperatorSource) :
    G8BookIIIMaximalKirchhoffSelfAdjointExtensionTarget source :=
  source.maximalSymmetricExtensionWitness

/-- The current compact-resolvent source exposes the compact-resolvent target. -/
def G8BookIIILemniscateCompactResolventSource.compactResolventTarget
    (source : G8BookIIILemniscateCompactResolventSource) :
    G8BookIIILemniscateCompactResolventTarget source :=
  source.compactResolventEvidence

/-- The current compact-resolvent source exposes the discrete-spectrum target. -/
def G8BookIIILemniscateCompactResolventSource.discretePointSpectrumTarget
    (source : G8BookIIILemniscateCompactResolventSource) :
    G8BookIIILemniscateDiscretePointSpectrumTarget source :=
  source.discreteSpectrumEvidence

/-- The current point-spectrum source exposes the reality target. -/
def G8BookIIILemniscateAnalyticPointSpectrumSource.realityTarget
    {operatorSource : G8BookIIILemniscateCompactResolventSource}
    (source :
      G8BookIIILemniscateAnalyticPointSpectrumSource operatorSource) :
    G8BookIIILemniscateAnalyticPointSpectrumRealityTarget source :=
  source.selfAdjointReality_native

-- ============================================================
-- MEMO-COMPATIBLE SOURCE NAMES
-- ============================================================

/-- Memo-compatible A1 wrapper: a ready Book III lemniscate operator source. -/
structure G8BookIIILemniscateOperatorReadySource where
  operatorSource : G8BookIIILemniscateCompactResolventSource

/-- Operator context exported by the memo-compatible A1 wrapper. -/
def G8BookIIILemniscateOperatorReadySource.operatorCtx
    (source : G8BookIIILemniscateOperatorReadySource) :
    LemniscateOperatorContext :=
  source.operatorSource.operatorContext

/-- Operator readiness exported by the memo-compatible A1 wrapper. -/
def G8BookIIILemniscateOperatorReadySource.operatorReady
    (source : G8BookIIILemniscateOperatorReadySource) :
    LemniscateOperatorReady source.operatorCtx :=
  source.operatorSource.operatorReady

/-- A1 wrapper to the existing compact-resolvent source. -/
def G8BookIIILemniscateOperatorReadySource.toCompactResolventSource
    (source : G8BookIIILemniscateOperatorReadySource) :
    G8BookIIILemniscateCompactResolventSource :=
  source.operatorSource

/-- Memo-compatible A2 wrapper: analytic point-spectrum provenance for a ready
    Book III operator source. -/
structure G8BookIIILemniscateAnalyticPointSpectrumProvenance
    (readySource : G8BookIIILemniscateOperatorReadySource) where
  pointSpectrumSource :
    G8BookIIILemniscateAnalyticPointSpectrumSource
      readySource.operatorSource

/-- A2 wrapper to strict operator-native provenance. -/
def
    G8BookIIILemniscateAnalyticPointSpectrumProvenance.toOperatorNativeProvenance
    {readySource : G8BookIIILemniscateOperatorReadySource}
    (source :
      G8BookIIILemniscateAnalyticPointSpectrumProvenance readySource) :
    G8OperatorNativeSpectralProvenance
      readySource.operatorCtx readySource.operatorReady :=
  source.pointSpectrumSource.toProvenance

/-- Memo-compatible combined A1/A2 source. -/
structure G8BookIIILaneAOperatorNativeSelfAdjointSource where
  readySource : G8BookIIILemniscateOperatorReadySource
  pointSpectrumProvenance :
    G8BookIIILemniscateAnalyticPointSpectrumProvenance readySource

/-- Combined memo-compatible source to the existing proof-source package. -/
def G8BookIIILaneAOperatorNativeSelfAdjointSource.toProofSource
    (source : G8BookIIILaneAOperatorNativeSelfAdjointSource) :
    G8BookIIILaneAOperatorSelfAdjointProofSource where
  operatorSource := source.readySource.operatorSource
  pointSpectrumSource :=
    source.pointSpectrumProvenance.pointSpectrumSource

/-- Combined memo-compatible source to the existing Lane-A A1/A2 source. -/
def G8BookIIILaneAOperatorNativeSelfAdjointSource.toLaneASource
    (source : G8BookIIILaneAOperatorNativeSelfAdjointSource) :
    G8LaneAOperatorNativeSelfAdjointSource :=
  source.toProofSource.toLaneASource

-- ============================================================
-- OPERATOR-NATIVE EIGENPAIR POINT SPECTRUM
-- ============================================================

/-- Operator-native eigenpair data for a complex spectral value.

This is the sharpened A2 membership surface: a value belongs to the native
point spectrum by carrying eigenfunction data, nonzero evidence, and the
operator eigen-equation evidence. -/
structure G8BookIIILemniscateEigenpairData
    (_operatorSource : G8BookIIILemniscateCompactResolventSource)
    (_spectralValue : ℂ) where
  eigenfunctionCarrier : Type 1
  eigenfunction : eigenfunctionCarrier
  nonzeroEigenfunction : Prop
  nonzeroEvidence : nonzeroEigenfunction
  eigenEquation : Prop
  eigenEquationEvidence : eigenEquation
  domainMembershipEvidence : Prop
  domainMembershipWitness : domainMembershipEvidence

/-- Native point-spectrum membership via eigenpair data. -/
def G8BookIIILemniscateEigenpairPointSpectrumMembership
    (operatorSource : G8BookIIILemniscateCompactResolventSource)
    (spectralValue : ℂ) : Prop :=
  Nonempty
    (G8BookIIILemniscateEigenpairData operatorSource spectralValue)

/-- Self-adjoint reality theorem for the eigenpair point-spectrum predicate.

The load-bearing field is the standard self-adjoint eigenvalue reality
argument.  The proof itself remains the next compact graph-operator payload. -/
structure G8BookIIILemniscateEigenpairRealitySource
    (operatorSource : G8BookIIILemniscateCompactResolventSource) where
  selfAdjointEigenpairReality :
    ∀ spectralValue : ℂ,
      G8BookIIILemniscateEigenpairPointSpectrumMembership
        operatorSource spectralValue →
        spectralValue.im = 0
  innerProductArgumentEvidence : Prop
  innerProductArgumentWitness : innerProductArgumentEvidence
  nonzeroNormCancellationEvidence : Prop
  nonzeroNormCancellationWitness : nonzeroNormCancellationEvidence

/-- Eigenpair-based point-spectrum provenance. -/
structure G8BookIIILemniscateEigenpairPointSpectrumProvenance
    (operatorSource : G8BookIIILemniscateCompactResolventSource) where
  realitySource :
    G8BookIIILemniscateEigenpairRealitySource operatorSource
  pointSpectrumDefinitionEvidence : Prop
  pointSpectrumDefinitionWitness : pointSpectrumDefinitionEvidence
  diagnostics : G8LemniscateSpectrumRealityDiagnostics := {}

/-- Eigenpair provenance induces the existing analytic point-spectrum source. -/
def G8BookIIILemniscateEigenpairPointSpectrumProvenance.toAnalyticPointSpectrumSource
    {operatorSource : G8BookIIILemniscateCompactResolventSource}
    (source :
      G8BookIIILemniscateEigenpairPointSpectrumProvenance
        operatorSource) :
    G8BookIIILemniscateAnalyticPointSpectrumSource operatorSource where
  exportedMembership :=
    G8BookIIILemniscateEigenpairPointSpectrumMembership operatorSource
  nativeMembership :=
    G8BookIIILemniscateEigenpairPointSpectrumMembership operatorSource
  pointSpectrumDefinitionEvidence :=
    source.pointSpectrumDefinitionEvidence
  pointSpectrumDefinitionWitness :=
    source.pointSpectrumDefinitionWitness
  exported_iff_native := by
    intro spectralValue
    rfl
  selfAdjointReality_native :=
    source.realitySource.selfAdjointEigenpairReality
  diagnostics := source.diagnostics

/-- A ready operator source plus eigenpair provenance gives the existing
    proof-source package. -/
def G8BookIIILemniscateOperatorReadySource.withEigenpairPointSpectrum
    (readySource : G8BookIIILemniscateOperatorReadySource)
    (provenance :
      G8BookIIILemniscateEigenpairPointSpectrumProvenance
        readySource.operatorSource) :
    G8BookIIILaneAOperatorSelfAdjointProofSource where
  operatorSource := readySource.operatorSource
  pointSpectrumSource := provenance.toAnalyticPointSpectrumSource

/-- A ready operator source plus analytic point-spectrum provenance gives the
    existing proof-source package. -/
def G8BookIIILemniscateOperatorReadySource.withAnalyticPointSpectrum
    (readySource : G8BookIIILemniscateOperatorReadySource)
    (provenance :
      G8BookIIILemniscateAnalyticPointSpectrumProvenance readySource) :
    G8BookIIILaneAOperatorSelfAdjointProofSource where
  operatorSource := readySource.operatorSource
  pointSpectrumSource := provenance.pointSpectrumSource

/-- Eigenpair provenance gives the memo-compatible A2 wrapper. -/
def
    G8BookIIILemniscateEigenpairPointSpectrumProvenance.toAnalyticProvenance
    {readySource : G8BookIIILemniscateOperatorReadySource}
    (source :
      G8BookIIILemniscateEigenpairPointSpectrumProvenance
        readySource.operatorSource) :
    G8BookIIILemniscateAnalyticPointSpectrumProvenance readySource where
  pointSpectrumSource := source.toAnalyticPointSpectrumSource

-- ============================================================
-- GUARDRAILS
-- ============================================================

/-- A non-real eigenpair member refutes the eigenpair reality source. -/
structure G8BookIIILemniscateEigenpairNonrealMember
    {operatorSource : G8BookIIILemniscateCompactResolventSource}
    (source :
      G8BookIIILemniscateEigenpairRealitySource operatorSource) where
  spectralValue : ℂ
  member :
    G8BookIIILemniscateEigenpairPointSpectrumMembership
      operatorSource spectralValue
  nonreal : spectralValue.im ≠ 0

/-- Non-real eigenpair membership is fatal for the eigenpair reality source. -/
theorem G8BookIIILemniscateEigenpairNonrealMember.refutes
    {operatorSource : G8BookIIILemniscateCompactResolventSource}
    {source :
      G8BookIIILemniscateEigenpairRealitySource operatorSource}
    (w : G8BookIIILemniscateEigenpairNonrealMember source) :
    False :=
  w.nonreal
    (source.selfAdjointEigenpairReality w.spectralValue w.member)

/-- A value with no eigenpair data refutes eigenpair point-spectrum membership. -/
structure G8BookIIILemniscateMissingEigenpairData
    (operatorSource : G8BookIIILemniscateCompactResolventSource)
    (spectralValue : ℂ) where
  noEigenpair :
    ¬ G8BookIIILemniscateEigenpairPointSpectrumMembership
      operatorSource spectralValue

/-- Missing eigenpair data refutes an attempted native point-spectrum member. -/
theorem G8BookIIILemniscateMissingEigenpairData.refutesMembership
    {operatorSource : G8BookIIILemniscateCompactResolventSource}
    {spectralValue : ℂ}
    (gap :
      G8BookIIILemniscateMissingEigenpairData
        operatorSource spectralValue)
    (member :
      G8BookIIILemniscateEigenpairPointSpectrumMembership
        operatorSource spectralValue) :
    False :=
  gap.noEigenpair member

end Tau.BookIII.Bridge
