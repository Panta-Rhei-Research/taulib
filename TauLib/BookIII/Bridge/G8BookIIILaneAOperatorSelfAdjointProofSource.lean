import TauLib.BookIII.Bridge.G8LaneAOperatorNativeSelfAdjointSource

/-!
# TauLib.BookIII.Bridge.G8BookIIILaneAOperatorSelfAdjointProofSource

Proof-facing Book III source chain for Lane-A gates A1/A2.

This module mirrors the A1/A2 proof map without pretending the analytic
Kirchhoff graph-operator theorem is already discharged.  It splits the source
into small packages:

* metric graph carrier readiness;
* Hilbert/domain readiness;
* Kirchhoff graph-Laplacian source data;
* self-adjointness;
* compact resolvent and discrete spectrum;
* analytic point-spectrum provenance.

The final adapter produces `G8LaneAOperatorNativeSelfAdjointSource` only from
these proof-carrying fields.  It does not mention A3/canonical actual-`xi`
membership and does not replace the quarantined Lane-A ledger axioms.
-/

set_option autoImplicit false

noncomputable section

namespace Tau.BookIII.Bridge

-- ============================================================
-- STEP 1: METRIC GRAPH SOURCE
-- ============================================================

/-- Book III source package for the lemniscate metric graph
    `S¹_B ∨ S¹_C`.

The load-bearing field is `carrierReady`.  The additional fields record the
manuscript provenance of the two-lobe wedge construction without promoting
finite diagnostics into operator readiness. -/
structure G8BookIIILemniscateMetricGraphSource where
  carrierCtx : LemniscateCarrierContext
  carrierReady : LemniscateCarrierReady carrierCtx
  twoLobeWedgeConstructed : Prop
  twoLobeWedgeEvidence : twoLobeWedgeConstructed
  crossingNodeIdentifiesBasepoints : Prop
  crossingNodeEvidence : crossingNodeIdentifiesBasepoints
  compactMetricGraphEvidence : Prop
  compactMetricGraphWitness : compactMetricGraphEvidence
  status : SpineStatus := .conditional_interface

/-- Recover carrier readiness from the metric-graph source. -/
def G8BookIIILemniscateMetricGraphSource.toCarrierReady
    (source : G8BookIIILemniscateMetricGraphSource) :
    LemniscateCarrierReady source.carrierCtx :=
  source.carrierReady

-- ============================================================
-- STEP 2: HILBERT AND DOMAIN SOURCE
-- ============================================================

/-- Book III source package for the graph Hilbert space and the Kirchhoff
    Sobolev/domain layer.

This is the Lean-facing version of the proof-map step proving trace
continuity, crossing closure, and Kirchhoff closure. -/
structure G8BookIIILemniscateHilbertDomainSource where
  graph : G8BookIIILemniscateMetricGraphSource
  hilbertCtx : LemniscateHilbertContext
  hilbertUsesGraph :
    hilbertCtx.measure.carrierContext = graph.carrierCtx
  hilbertReady : LemniscateHilbertReady hilbertCtx
  domainCtx : LemniscateDomainContext
  domainUsesHilbert : domainCtx.hilbert = hilbertCtx
  domainReady : LemniscateDomainReady domainCtx
  traceContinuityEvidence : Prop
  traceContinuityWitness : traceContinuityEvidence
  derivativeTraceEvidence : Prop
  derivativeTraceWitness : derivativeTraceEvidence
  crossingClosureEvidence : Prop
  crossingClosureWitness : crossingClosureEvidence
  kirchhoffClosureEvidence : Prop
  kirchhoffClosureWitness : kirchhoffClosureEvidence
  status : SpineStatus := .conditional_interface

/-- Recover domain readiness from the Hilbert/domain source. -/
def G8BookIIILemniscateHilbertDomainSource.toDomainReady
    (source : G8BookIIILemniscateHilbertDomainSource) :
    LemniscateDomainReady source.domainCtx :=
  source.domainReady

-- ============================================================
-- STEP 3: KIRCHHOFF LAPLACIAN SOURCE
-- ============================================================

/-- Book III source package for the Kirchhoff graph Laplacian `H_L=-d²/dx²`.

The current low-level spine still exposes `H_L_spine` as a placeholder.
Therefore this package carries the analytic operator and the exact evidence
needed later, rather than identifying finite checks with the operator theorem. -/
structure G8BookIIIKirchhoffLaplacianSource where
  domain : G8BookIIILemniscateHilbertDomainSource
  graphLaplacian : LemniscateOperatorDomain → LemniscateL2
  edgewiseNegativeSecondDerivative : Prop
  edgewiseNegativeSecondDerivativeWitness :
    edgewiseNegativeSecondDerivative
  kirchhoffBoundaryCondition : Prop
  kirchhoffBoundaryConditionWitness : kirchhoffBoundaryCondition
  boundaryFormCancellation : Prop
  boundaryFormCancellationWitness : boundaryFormCancellation
  maximalKirchhoffExtension : Prop
  maximalKirchhoffExtensionWitness : maximalKirchhoffExtension
  status : SpineStatus := .conditional_interface

/-- The Kirchhoff source inherits domain readiness. -/
def G8BookIIIKirchhoffLaplacianSource.toDomainReady
    (source : G8BookIIIKirchhoffLaplacianSource) :
    LemniscateDomainReady source.domain.domainCtx :=
  source.domain.domainReady

-- ============================================================
-- STEPS 4-5: SELF-ADJOINTNESS SOURCE
-- ============================================================

/-- Book III source package for self-adjointness of the Kirchhoff graph
    Laplacian.

The evidence fields correspond to the boundary-form cancellation and maximal
Kirchhoff-extension arguments from the proof map. -/
structure G8BookIIILemniscateSelfAdjointOperatorSource where
  laplacian : G8BookIIIKirchhoffLaplacianSource
  selfAdjointStatement : Prop
  selfAdjointEvidence : selfAdjointStatement
  selfAdjointFromBoundaryForm : Prop
  selfAdjointFromBoundaryFormEvidence : selfAdjointFromBoundaryForm
  maximalSymmetricExtensionEvidence : Prop
  maximalSymmetricExtensionWitness : maximalSymmetricExtensionEvidence
  status : SpineStatus := .conditional_interface

/-- The self-adjoint operator source inherits domain readiness. -/
def G8BookIIILemniscateSelfAdjointOperatorSource.toDomainReady
    (source : G8BookIIILemniscateSelfAdjointOperatorSource) :
    LemniscateDomainReady source.laplacian.domain.domainCtx :=
  source.laplacian.toDomainReady

-- ============================================================
-- STEP 6: COMPACT RESOLVENT AND DISCRETE SPECTRUM SOURCE
-- ============================================================

/-- Book III source package for compact resolvent and discrete spectrum.

Together with self-adjointness, this is exactly the A1 operator-readiness
payload consumed by the existing `LemniscateOperatorReady` interface. -/
structure G8BookIIILemniscateCompactResolventSource where
  selfAdjointOperator :
    G8BookIIILemniscateSelfAdjointOperatorSource
  compactResolventStatement : Prop
  compactResolventEvidence : compactResolventStatement
  discreteSpectrumStatement : Prop
  discreteSpectrumEvidence : discreteSpectrumStatement
  finiteApproximationCompatibleStatement : Prop
  finiteApproximationCompatibleEvidence :
    finiteApproximationCompatibleStatement
  compactGraphResolventEvidence : Prop
  compactGraphResolventWitness : compactGraphResolventEvidence
  spectralResolutionEvidence : Prop
  spectralResolutionWitness : spectralResolutionEvidence
  status : SpineStatus := .conditional_interface

/-- Operator context induced by a Book III compact-resolvent source. -/
def G8BookIIILemniscateCompactResolventSource.operatorContext
    (source : G8BookIIILemniscateCompactResolventSource) :
    LemniscateOperatorContext where
  domain := source.selfAdjointOperator.laplacian.domain.domainCtx
  obligations := {
    selfAdjoint :=
      source.selfAdjointOperator.selfAdjointStatement
    compactResolvent := source.compactResolventStatement
    discreteSpectrum := source.discreteSpectrumStatement
    obligationsRespectDomain :=
      LemniscateDomainReady
        source.selfAdjointOperator.laplacian.domain.domainCtx
  }
  finiteApproximationCompatible :=
    source.finiteApproximationCompatibleStatement
  status := .conditional_interface

/-- A Book III compact-resolvent source proves operator readiness for the
    induced operator context. -/
def G8BookIIILemniscateCompactResolventSource.operatorReady
    (source : G8BookIIILemniscateCompactResolventSource) :
    LemniscateOperatorReady source.operatorContext :=
  ⟨source.selfAdjointOperator.toDomainReady,
    source.selfAdjointOperator.selfAdjointEvidence,
    source.compactResolventEvidence,
    source.discreteSpectrumEvidence,
    source.selfAdjointOperator.toDomainReady,
    source.finiteApproximationCompatibleEvidence⟩

-- ============================================================
-- STEPS 8-9: ANALYTIC POINT-SPECTRUM PROVENANCE
-- ============================================================

/-- Book III source package for the operator-native analytic point spectrum.

The native predicate is explicitly supplied, along with exact agreement with
the exported predicate and self-adjoint real-valuedness for every native
member. -/
structure G8BookIIILemniscateAnalyticPointSpectrumSource
    (operatorSource : G8BookIIILemniscateCompactResolventSource) where
  exportedMembership :
    G8LemniscateSpectrumMembership
      operatorSource.operatorContext operatorSource.operatorReady
  nativeMembership : ℂ → Prop
  pointSpectrumDefinitionEvidence : Prop
  pointSpectrumDefinitionWitness : pointSpectrumDefinitionEvidence
  exported_iff_native :
    ∀ spectralValue : ℂ,
      exportedMembership spectralValue ↔
        nativeMembership spectralValue
  selfAdjointReality_native :
    ∀ spectralValue : ℂ,
      nativeMembership spectralValue → spectralValue.im = 0
  diagnostics : G8LemniscateSpectrumRealityDiagnostics := {}

/-- The analytic point-spectrum source is a strict operator-native provenance
    package of kind `.pointSpectrum`. -/
def G8BookIIILemniscateAnalyticPointSpectrumSource.toProvenance
    {operatorSource : G8BookIIILemniscateCompactResolventSource}
    (source :
      G8BookIIILemniscateAnalyticPointSpectrumSource operatorSource) :
    G8OperatorNativeSpectralProvenance
      operatorSource.operatorContext operatorSource.operatorReady where
  spectralMembership := source.exportedMembership
  nativeMembership := source.nativeMembership
  kind := .pointSpectrum
  spectralMembership_iff_native := source.exported_iff_native
  selfAdjointReality_native := source.selfAdjointReality_native
  diagnostics := source.diagnostics

-- ============================================================
-- STEP 10: COMBINED A1/A2 SOURCE
-- ============================================================

/-- Complete proof-facing A1/A2 source following the Book III proof map.

This package still carries no canonical actual-`xi` membership theorem.  A3
remains a separate payload. -/
structure G8BookIIILaneAOperatorSelfAdjointProofSource where
  operatorSource : G8BookIIILemniscateCompactResolventSource
  pointSpectrumSource :
    G8BookIIILemniscateAnalyticPointSpectrumSource operatorSource

/-- Prop target for the complete A1/A2 source. -/
def G8BookIIILaneAOperatorSelfAdjointProofSourceTarget : Prop :=
  Nonempty G8BookIIILaneAOperatorSelfAdjointProofSource

/-- The complete Book III A1/A2 proof source supplies the existing Lane-A
    operator-native self-adjoint source. -/
def G8BookIIILaneAOperatorSelfAdjointProofSource.toLaneASource
    (source : G8BookIIILaneAOperatorSelfAdjointProofSource) :
    G8LaneAOperatorNativeSelfAdjointSource where
  operatorCtx := source.operatorSource.operatorContext
  operatorReady := source.operatorSource.operatorReady
  provenance := source.pointSpectrumSource.toProvenance

/-- The complete Book III A1/A2 proof source supplies the existing target. -/
theorem G8BookIIILaneAOperatorSelfAdjointProofSource.toLaneATarget
    (source : G8BookIIILaneAOperatorSelfAdjointProofSource) :
    G8LaneAOperatorNativeSelfAdjointSourceTarget :=
  ⟨source.toLaneASource⟩

-- ============================================================
-- GUARDRAILS AND FALSIFIERS
-- ============================================================

/-- A missing domain-readiness theorem refutes a claimed Hilbert/domain source. -/
structure G8BookIIILemniscateDomainReadinessGap
    (source : G8BookIIILemniscateHilbertDomainSource) where
  notReady : ¬ LemniscateDomainReady source.domainCtx

/-- Domain-readiness gaps are fatal for a Hilbert/domain source. -/
theorem G8BookIIILemniscateDomainReadinessGap.refutes
    {source : G8BookIIILemniscateHilbertDomainSource}
    (gap : G8BookIIILemniscateDomainReadinessGap source) :
    False :=
  gap.notReady source.domainReady

/-- A non-real native point-spectrum member refutes the analytic point-spectrum
    source. -/
structure G8BookIIILemniscateAnalyticPointSpectrumNonrealMember
    {operatorSource : G8BookIIILemniscateCompactResolventSource}
    (source :
      G8BookIIILemniscateAnalyticPointSpectrumSource operatorSource) where
  spectralValue : ℂ
  nativeMember : source.nativeMembership spectralValue
  nonreal : spectralValue.im ≠ 0

/-- Non-real native point-spectrum membership is fatal. -/
theorem G8BookIIILemniscateAnalyticPointSpectrumNonrealMember.refutes
    {operatorSource : G8BookIIILemniscateCompactResolventSource}
    {source :
      G8BookIIILemniscateAnalyticPointSpectrumSource operatorSource}
    (w :
      G8BookIIILemniscateAnalyticPointSpectrumNonrealMember source) :
    False :=
  w.nonreal
    (source.selfAdjointReality_native w.spectralValue w.nativeMember)

/-- Diagnostic-only finite evidence still does not construct the A1/A2 proof
    source. -/
structure G8BookIIILaneAFiniteDiagnosticsOnly where
  finiteSelfAdjointDiagnostic : Prop
  finiteK5DiagonalDiagnostic : Prop
  finiteSpectralCorrespondenceDiagnostic : Prop
  selfAdjointEvidence : finiteSelfAdjointDiagnostic
  k5Evidence : finiteK5DiagonalDiagnostic
  correspondenceEvidence : finiteSpectralCorrespondenceDiagnostic
  noProofSource : ¬ G8BookIIILaneAOperatorSelfAdjointProofSourceTarget

/-- Finite diagnostics refute a claimed A1/A2 source only when they explicitly
    record that no proof source is available. -/
theorem G8BookIIILaneAFiniteDiagnosticsOnly.refutesProofSource
    (w : G8BookIIILaneAFiniteDiagnosticsOnly)
    (source : G8BookIIILaneAOperatorSelfAdjointProofSource) :
    False :=
  w.noProofSource ⟨source⟩

/-- A point-spectrum source whose exported predicate disagrees with the native
    predicate is impossible. -/
structure G8BookIIILemniscateAnalyticPointSpectrumMismatch
    {operatorSource : G8BookIIILemniscateCompactResolventSource}
    (source :
      G8BookIIILemniscateAnalyticPointSpectrumSource operatorSource) where
  spectralValue : ℂ
  exportedMember : source.exportedMembership spectralValue
  notNative : ¬ source.nativeMembership spectralValue

/-- Exported point-spectrum membership without native membership refutes exact
    exported/native agreement. -/
theorem G8BookIIILemniscateAnalyticPointSpectrumMismatch.refutes
    {operatorSource : G8BookIIILemniscateCompactResolventSource}
    {source :
      G8BookIIILemniscateAnalyticPointSpectrumSource operatorSource}
    (w : G8BookIIILemniscateAnalyticPointSpectrumMismatch source) :
    False :=
  w.notNative
    ((source.exported_iff_native w.spectralValue).mp w.exportedMember)

end Tau.BookIII.Bridge
