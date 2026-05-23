import TauLib.BookIII.Bridge.G8BookIIICh23FloorNormalizedA16ResolventCompactness
import TauLib.BookIII.Bridge.G8BookIIILaneAOperatorSelfAdjointProofSteps

/-!
# G8 Book III Ch.23 Floor-Normalized A1.6 Discrete Point Spectrum

This module packages the final A1.6 step:

```text
self-adjoint compact resolvent
  -> discrete point spectrum
  -> existing `G8BookIIILemniscateCompactResolventSource`
```

The selected compact-resolvent/discrete-spectrum chain is separate from A2
operator-native point-spectrum provenance and from A3 actual-`xi` membership.
-/

set_option autoImplicit false

namespace Tau.BookIII.Bridge

-- ============================================================
-- DISCRETE POINT-SPECTRUM CONSEQUENCE
-- ============================================================

/-- Discrete-spectrum source from self-adjoint compact resolvent. -/
structure
    G8BookIIICh23FloorNormalizedA16DiscretePointSpectrumSource
    where
  compactResolvent :
    G8BookIIICh23FloorNormalizedA16ResolventCompactnessSource
  compactSelfAdjointResolventSpectralTheorem : Prop
  compactSelfAdjointResolventSpectralTheoremWitness :
    compactSelfAdjointResolventSpectralTheorem
  finiteMultiplicityOfEigenvalues : Prop
  finiteMultiplicityOfEigenvaluesWitness :
    finiteMultiplicityOfEigenvalues
  eigenvalueEscapeToInfinity : Prop
  eigenvalueEscapeToInfinityWitness :
    eigenvalueEscapeToInfinity
  noContinuousSpectralResidueForLaneAPredicate : Prop
  noContinuousSpectralResidueForLaneAPredicateWitness :
    noContinuousSpectralResidueForLaneAPredicate
  spectralResolutionEvidence : Prop
  spectralResolutionWitness : spectralResolutionEvidence
  discretePointSpectrum : Prop
  discretePointSpectrumWitness : discretePointSpectrum
  noStandardModeEqualityClaim : Prop
  noStandardModeEqualityClaimWitness :
    noStandardModeEqualityClaim
  status : SpineStatus := .conditional_interface

/-- Selected discrete point-spectrum target. -/
def G8BookIIICh23FloorNormalizedA16DiscretePointSpectrumTarget :
    Prop :=
  Nonempty G8BookIIICh23FloorNormalizedA16DiscretePointSpectrumSource

/-- A discrete-spectrum source proves its target. -/
theorem
    G8BookIIICh23FloorNormalizedA16DiscretePointSpectrumSource.toTarget
    (source :
      G8BookIIICh23FloorNormalizedA16DiscretePointSpectrumSource) :
    G8BookIIICh23FloorNormalizedA16DiscretePointSpectrumTarget :=
  ⟨source⟩

-- ============================================================
-- A1.6 ASSEMBLY INTO THE EXISTING OPERATOR SOURCE
-- ============================================================

/-- Assembly source for the existing compact-resolvent operator package.

This is proof-carrying in two directions:

* the selected compact-resolvent/discrete-spectrum proof supplies the analytic
  A1.6 content;
* the legacy adapter supplies exact transport to the older raw
  `LemniscateOperatorDomain` surface consumed by existing downstream code.
-/
structure
    G8BookIIICh23FloorNormalizedA16CompactResolventDiscreteSpectrumAssemblySource
    where
  legacySelfAdjoint :
    G8BookIIICh23FloorNormalizedA16LegacySelfAdjointOperatorAdapterSource
  compactResolvent :
    G8BookIIICh23FloorNormalizedA16ResolventCompactnessSource
  discreteSpectrum :
    G8BookIIICh23FloorNormalizedA16DiscretePointSpectrumSource
  discreteUsesCompactResolvent :
    discreteSpectrum.compactResolvent = compactResolvent
  finiteApproximationCompatible : Prop
  finiteApproximationCompatibleEvidence :
    finiteApproximationCompatible
  finiteApproximationIsDiagnosticOnly : Prop
  finiteApproximationIsDiagnosticOnlyWitness :
    finiteApproximationIsDiagnosticOnly
  selectedCompactResolventTransportedToLegacy : Prop
  selectedCompactResolventTransportedToLegacyEvidence :
    selectedCompactResolventTransportedToLegacy
  selectedDiscreteSpectrumTransportedToLegacy : Prop
  selectedDiscreteSpectrumTransportedToLegacyEvidence :
    selectedDiscreteSpectrumTransportedToLegacy
  status : SpineStatus := .conditional_interface

/-- The complete A1.6 target: enough data to build the existing
    `G8BookIIILemniscateCompactResolventSource`. -/
def
    G8BookIIICh23FloorNormalizedA16CompactResolventDiscreteSpectrumAssemblyTarget :
    Prop :=
  Nonempty
    G8BookIIICh23FloorNormalizedA16CompactResolventDiscreteSpectrumAssemblySource

/-- Assembly source proves its target. -/
theorem
    G8BookIIICh23FloorNormalizedA16CompactResolventDiscreteSpectrumAssemblySource.toTarget
    (source :
      G8BookIIICh23FloorNormalizedA16CompactResolventDiscreteSpectrumAssemblySource) :
    G8BookIIICh23FloorNormalizedA16CompactResolventDiscreteSpectrumAssemblyTarget :=
  ⟨source⟩

/-- Convert the selected A1.6 assembly into the existing Book III
    compact-resolvent source. -/
def
    G8BookIIICh23FloorNormalizedA16CompactResolventDiscreteSpectrumAssemblySource.toCompactResolventSource
    (source :
      G8BookIIICh23FloorNormalizedA16CompactResolventDiscreteSpectrumAssemblySource) :
    G8BookIIILemniscateCompactResolventSource where
  selfAdjointOperator :=
    source.legacySelfAdjoint.toSelfAdjointOperatorSource
  compactResolventStatement :=
    source.selectedCompactResolventTransportedToLegacy
  compactResolventEvidence :=
    source.selectedCompactResolventTransportedToLegacyEvidence
  discreteSpectrumStatement :=
    source.selectedDiscreteSpectrumTransportedToLegacy
  discreteSpectrumEvidence :=
    source.selectedDiscreteSpectrumTransportedToLegacyEvidence
  finiteApproximationCompatibleStatement :=
    source.finiteApproximationCompatible
  finiteApproximationCompatibleEvidence :=
    source.finiteApproximationCompatibleEvidence
  compactGraphResolventEvidence :=
    source.selectedCompactResolventTransportedToLegacy
  compactGraphResolventWitness :=
    source.selectedCompactResolventTransportedToLegacyEvidence
  spectralResolutionEvidence :=
    source.discreteSpectrum.spectralResolutionEvidence
  spectralResolutionWitness :=
    source.discreteSpectrum.spectralResolutionWitness
  status := source.status

/-- Existing memo-compatible operator-ready source from the complete A1.6
    assembly. -/
def
    G8BookIIICh23FloorNormalizedA16CompactResolventDiscreteSpectrumAssemblySource.toOperatorReadySource
    (source :
      G8BookIIICh23FloorNormalizedA16CompactResolventDiscreteSpectrumAssemblySource) :
    G8BookIIILemniscateOperatorReadySource where
  operatorSource := source.toCompactResolventSource

-- ============================================================
-- GUARDRAILS
-- ============================================================

/-- Compact resolvent without the spectral-theorem/discreteness consequence is
    not yet A1.6. -/
structure
    G8BookIIICh23FloorNormalizedA16CompactResolventWithoutDiscreteSpectrum
    (source :
      G8BookIIICh23FloorNormalizedA16ResolventCompactnessSource)
    where
  noDiscreteSpectrum :
    ¬ G8BookIIICh23FloorNormalizedA16DiscretePointSpectrumTarget

theorem
    G8BookIIICh23FloorNormalizedA16CompactResolventWithoutDiscreteSpectrum.refutes
    {source :
      G8BookIIICh23FloorNormalizedA16ResolventCompactnessSource}
    (gap :
      G8BookIIICh23FloorNormalizedA16CompactResolventWithoutDiscreteSpectrum
        source)
    (target :
      G8BookIIICh23FloorNormalizedA16DiscretePointSpectrumTarget) :
    False :=
  gap.noDiscreteSpectrum target

/-- The selected compact-resolvent source cannot be exported to the existing
    raw operator-ready surface without the legacy transport bridge. -/
structure
    G8BookIIICh23FloorNormalizedA16SelectedA16WithoutLegacyTransport
    where
  compactResolvent :
    G8BookIIICh23FloorNormalizedA16ResolventCompactnessSource
  discreteSpectrum :
    G8BookIIICh23FloorNormalizedA16DiscretePointSpectrumSource
  noAssembly :
    ¬ G8BookIIICh23FloorNormalizedA16CompactResolventDiscreteSpectrumAssemblyTarget

theorem
    G8BookIIICh23FloorNormalizedA16SelectedA16WithoutLegacyTransport.refutes
    (gap :
      G8BookIIICh23FloorNormalizedA16SelectedA16WithoutLegacyTransport)
    (target :
      G8BookIIICh23FloorNormalizedA16CompactResolventDiscreteSpectrumAssemblyTarget) :
    False :=
  gap.noAssembly target

/-- Approximate or finite-mode agreement cannot replace the exact compact
    resolvent and discrete-spectrum fields. -/
structure
    G8BookIIICh23FloorNormalizedA16FiniteApproximationOnlyGap
    where
  finiteApproximationCompatible : Prop
  finiteApproximationCompatibleEvidence :
    finiteApproximationCompatible
  noCompactResolvent :
    ¬ G8BookIIICh23FloorNormalizedA16ResolventCompactnessTarget

theorem
    G8BookIIICh23FloorNormalizedA16FiniteApproximationOnlyGap.refutes
    (gap :
      G8BookIIICh23FloorNormalizedA16FiniteApproximationOnlyGap)
    (target :
      G8BookIIICh23FloorNormalizedA16ResolventCompactnessTarget) :
    False :=
  gap.noCompactResolvent target

end Tau.BookIII.Bridge
