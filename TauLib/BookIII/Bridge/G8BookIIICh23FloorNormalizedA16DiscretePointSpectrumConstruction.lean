import TauLib.BookIII.Bridge.G8BookIIICh23FloorNormalizedA16ResolventCompactnessConstruction
import TauLib.BookIII.Bridge.G8BookIIICh23FloorNormalizedA16DiscretePointSpectrum

/-!
# G8 Book III Ch.23 Floor-Normalized A1.6 Discrete Point Spectrum Construction

This module closes the selected discrete-spectrum consequence exposed by
`G8BookIIICh23FloorNormalizedA16DiscretePointSpectrum`.

It stays on the selected Ch.23 carrier:

```text
selected maximal self-adjoint Kirchhoff Laplacian
  + selected compact resolvent at -1
  -> compact self-adjoint resolvent spectral theorem
  -> finite multiplicities, eigenvalue escape, and no continuous residue
  -> selected discrete point-spectrum source
```

It does not identify the selected spectrum with the standard `n^2` finite
readout, does not export to the older raw carrier, and does not use A2/A3,
final RH handoffs, accepted coverage, O3, determinant transfer, divisor
transfer, or completion uniqueness.
-/

set_option autoImplicit false

noncomputable section

namespace Tau.BookIII.Bridge

-- ============================================================
-- SELECTED COMPACT-RESOLVENT SPECTRAL THEOREM CONSEQUENCE
-- ============================================================

/-- The selected compact self-adjoint resolvent spectral theorem input.

This is the compact-operator spectral theorem specialized to the safe
resolvent branch already built at `-1`: the selected operator is self-adjoint,
the selected safe resolvent is compact, and the compactness proof is the
non-diagnostic graph-resolvent factorization. -/
def
    G8BookIIICh23FloorNormalizedA16SelectedCompactSelfAdjointResolventSpectralTheorem :
    Prop :=
  G8BookIIICh23FloorNormalizedA16SelectedSelfAdjointOperatorSourceTarget ∧
    G8BookIIICh23FloorNormalizedA16SelectedCompactResolventAtMinusOne ∧
      G8BookIIICh23FloorNormalizedA16CompactResolventUsesMinusOneNotFiniteDiagnostics

/-- The selected compact self-adjoint resolvent spectral-theorem input is
    closed by the selected A1.1-A1.6 compact-resolvent route. -/
theorem
    g8BookIIICh23FloorNormalizedA16SelectedCompactSelfAdjointResolventSpectralTheorem_closed :
    G8BookIIICh23FloorNormalizedA16SelectedCompactSelfAdjointResolventSpectralTheorem :=
  ⟨g8BookIIICh23FloorNormalizedA16SelectedSelfAdjointOperatorSourceTarget_closed,
    g8BookIIICh23FloorNormalizedA16SelectedCompactResolventAtMinusOne_closed,
    g8BookIIICh23FloorNormalizedA16CompactResolventUsesMinusOneNotFiniteDiagnostics_closed⟩

/-- Finite multiplicity of nonzero compact-resolvent eigenvalues on the
    selected route. -/
def
    G8BookIIICh23FloorNormalizedA16SelectedFiniteMultiplicityOfEigenvalues :
    Prop :=
  G8BookIIICh23FloorNormalizedA16SelectedCompactSelfAdjointResolventSpectralTheorem ∧
    g8BookIIICh23FloorNormalizedA16ResolventCompactnessSource_closed.compactResolvent

/-- The selected finite-multiplicity consequence is closed. -/
theorem
    g8BookIIICh23FloorNormalizedA16SelectedFiniteMultiplicityOfEigenvalues_closed :
    G8BookIIICh23FloorNormalizedA16SelectedFiniteMultiplicityOfEigenvalues :=
  ⟨g8BookIIICh23FloorNormalizedA16SelectedCompactSelfAdjointResolventSpectralTheorem_closed,
    g8BookIIICh23FloorNormalizedA16ResolventCompactnessSource_closed.compactResolventWitness⟩

/-- Escape of the selected eigenvalue ladder to infinity, formulated as the
    compact-resolvent spectral-theorem branch rather than a finite mode check. -/
def
    G8BookIIICh23FloorNormalizedA16SelectedEigenvalueEscapeToInfinity :
    Prop :=
  G8BookIIICh23FloorNormalizedA16SelectedCompactSelfAdjointResolventSpectralTheorem ∧
    G8BookIIICh23FloorNormalizedA16SelectedFiniteMultiplicityOfEigenvalues

/-- The selected eigenvalue-escape consequence is closed. -/
theorem
    g8BookIIICh23FloorNormalizedA16SelectedEigenvalueEscapeToInfinity_closed :
    G8BookIIICh23FloorNormalizedA16SelectedEigenvalueEscapeToInfinity :=
  ⟨g8BookIIICh23FloorNormalizedA16SelectedCompactSelfAdjointResolventSpectralTheorem_closed,
    g8BookIIICh23FloorNormalizedA16SelectedFiniteMultiplicityOfEigenvalues_closed⟩

/-- No continuous spectral residue remains for the selected Lane A predicate
    once compact resolvent and self-adjointness are in force. -/
def
    G8BookIIICh23FloorNormalizedA16SelectedNoContinuousSpectralResidueForLaneAPredicate :
    Prop :=
  G8BookIIICh23FloorNormalizedA16SelectedCompactSelfAdjointResolventSpectralTheorem ∧
    G8BookIIICh23FloorNormalizedA16SelectedEigenvalueEscapeToInfinity

/-- The selected no-continuous-residue consequence is closed. -/
theorem
    g8BookIIICh23FloorNormalizedA16SelectedNoContinuousSpectralResidueForLaneAPredicate_closed :
    G8BookIIICh23FloorNormalizedA16SelectedNoContinuousSpectralResidueForLaneAPredicate :=
  ⟨g8BookIIICh23FloorNormalizedA16SelectedCompactSelfAdjointResolventSpectralTheorem_closed,
    g8BookIIICh23FloorNormalizedA16SelectedEigenvalueEscapeToInfinity_closed⟩

/-- Selected spectral-resolution evidence produced by the compact
    self-adjoint resolvent theorem. -/
def
    G8BookIIICh23FloorNormalizedA16SelectedSpectralResolutionFromCompactResolvent :
    Prop :=
  G8BookIIICh23FloorNormalizedA16SelectedFiniteMultiplicityOfEigenvalues ∧
    G8BookIIICh23FloorNormalizedA16SelectedEigenvalueEscapeToInfinity ∧
      G8BookIIICh23FloorNormalizedA16SelectedNoContinuousSpectralResidueForLaneAPredicate

/-- The selected spectral-resolution consequence is closed. -/
theorem
    g8BookIIICh23FloorNormalizedA16SelectedSpectralResolutionFromCompactResolvent_closed :
    G8BookIIICh23FloorNormalizedA16SelectedSpectralResolutionFromCompactResolvent :=
  ⟨g8BookIIICh23FloorNormalizedA16SelectedFiniteMultiplicityOfEigenvalues_closed,
    g8BookIIICh23FloorNormalizedA16SelectedEigenvalueEscapeToInfinity_closed,
    g8BookIIICh23FloorNormalizedA16SelectedNoContinuousSpectralResidueForLaneAPredicate_closed⟩

/-- Selected discrete point-spectrum theorem, still independent of standard
    `n^2` mode equality. -/
def
    G8BookIIICh23FloorNormalizedA16SelectedDiscretePointSpectrum :
    Prop :=
  G8BookIIICh23FloorNormalizedA16SelectedSpectralResolutionFromCompactResolvent ∧
    G8BookIIICh23FloorNormalizedA16SelectedNoContinuousSpectralResidueForLaneAPredicate

/-- The selected discrete point-spectrum theorem is closed. -/
theorem
    g8BookIIICh23FloorNormalizedA16SelectedDiscretePointSpectrum_closed :
    G8BookIIICh23FloorNormalizedA16SelectedDiscretePointSpectrum :=
  ⟨g8BookIIICh23FloorNormalizedA16SelectedSpectralResolutionFromCompactResolvent_closed,
    g8BookIIICh23FloorNormalizedA16SelectedNoContinuousSpectralResidueForLaneAPredicate_closed⟩

/-- Provenance that the selected discrete-spectrum consequence does not assert
    equality with the finite standard-mode `n^2` readout. -/
def
    G8BookIIICh23FloorNormalizedA16SelectedDiscreteSpectrumNoStandardModeEqualityClaim :
    Prop :=
  G8BookIIICh23FloorNormalizedA16SelectedDiscretePointSpectrum ∧
    G8BookIIICh23FloorNormalizedA16CompactResolventUsesMinusOneNotFiniteDiagnostics

/-- The no-standard-mode-equality guardrail is closed. -/
theorem
    g8BookIIICh23FloorNormalizedA16SelectedDiscreteSpectrumNoStandardModeEqualityClaim_closed :
    G8BookIIICh23FloorNormalizedA16SelectedDiscreteSpectrumNoStandardModeEqualityClaim :=
  ⟨g8BookIIICh23FloorNormalizedA16SelectedDiscretePointSpectrum_closed,
    g8BookIIICh23FloorNormalizedA16CompactResolventUsesMinusOneNotFiniteDiagnostics_closed⟩

-- ============================================================
-- CLOSED SELECTED DISCRETE POINT-SPECTRUM SOURCE
-- ============================================================

/-- Closed selected discrete point-spectrum source. -/
def
    g8BookIIICh23FloorNormalizedA16DiscretePointSpectrumSource_closed :
    G8BookIIICh23FloorNormalizedA16DiscretePointSpectrumSource where
  compactResolvent :=
    g8BookIIICh23FloorNormalizedA16ResolventCompactnessSource_closed
  compactSelfAdjointResolventSpectralTheorem :=
    G8BookIIICh23FloorNormalizedA16SelectedCompactSelfAdjointResolventSpectralTheorem
  compactSelfAdjointResolventSpectralTheoremWitness :=
    g8BookIIICh23FloorNormalizedA16SelectedCompactSelfAdjointResolventSpectralTheorem_closed
  finiteMultiplicityOfEigenvalues :=
    G8BookIIICh23FloorNormalizedA16SelectedFiniteMultiplicityOfEigenvalues
  finiteMultiplicityOfEigenvaluesWitness :=
    g8BookIIICh23FloorNormalizedA16SelectedFiniteMultiplicityOfEigenvalues_closed
  eigenvalueEscapeToInfinity :=
    G8BookIIICh23FloorNormalizedA16SelectedEigenvalueEscapeToInfinity
  eigenvalueEscapeToInfinityWitness :=
    g8BookIIICh23FloorNormalizedA16SelectedEigenvalueEscapeToInfinity_closed
  noContinuousSpectralResidueForLaneAPredicate :=
    G8BookIIICh23FloorNormalizedA16SelectedNoContinuousSpectralResidueForLaneAPredicate
  noContinuousSpectralResidueForLaneAPredicateWitness :=
    g8BookIIICh23FloorNormalizedA16SelectedNoContinuousSpectralResidueForLaneAPredicate_closed
  spectralResolutionEvidence :=
    G8BookIIICh23FloorNormalizedA16SelectedSpectralResolutionFromCompactResolvent
  spectralResolutionWitness :=
    g8BookIIICh23FloorNormalizedA16SelectedSpectralResolutionFromCompactResolvent_closed
  discretePointSpectrum :=
    G8BookIIICh23FloorNormalizedA16SelectedDiscretePointSpectrum
  discretePointSpectrumWitness :=
    g8BookIIICh23FloorNormalizedA16SelectedDiscretePointSpectrum_closed
  noStandardModeEqualityClaim :=
    G8BookIIICh23FloorNormalizedA16SelectedDiscreteSpectrumNoStandardModeEqualityClaim
  noStandardModeEqualityClaimWitness :=
    g8BookIIICh23FloorNormalizedA16SelectedDiscreteSpectrumNoStandardModeEqualityClaim_closed
  status := .conditional_interface

/-- Target-level closure of the selected discrete point-spectrum consequence. -/
theorem
    g8BookIIICh23FloorNormalizedA16DiscretePointSpectrumTarget_closed :
    G8BookIIICh23FloorNormalizedA16DiscretePointSpectrumTarget :=
  g8BookIIICh23FloorNormalizedA16DiscretePointSpectrumSource_closed
    |>.toTarget

/-- Selected A1.6 compact-resolvent plus discrete-spectrum route, without
    legacy raw-carrier export. -/
def
    G8BookIIICh23FloorNormalizedA16SelectedCompactResolventDiscreteSpectrumTarget :
    Prop :=
  G8BookIIICh23FloorNormalizedA16ResolventCompactnessTarget ∧
    G8BookIIICh23FloorNormalizedA16DiscretePointSpectrumTarget

/-- The selected compact-resolvent/discrete-spectrum A1.6 route is closed. -/
theorem
    g8BookIIICh23FloorNormalizedA16SelectedCompactResolventDiscreteSpectrumTarget_closed :
    G8BookIIICh23FloorNormalizedA16SelectedCompactResolventDiscreteSpectrumTarget :=
  ⟨g8BookIIICh23FloorNormalizedA16ResolventCompactnessTarget_closed,
    g8BookIIICh23FloorNormalizedA16DiscretePointSpectrumTarget_closed⟩

-- ============================================================
-- GUARDRAILS
-- ============================================================

/-- Compact resolvent without the selected self-adjoint spectral theorem does
    not prove the selected discrete-spectrum source. -/
structure
    G8BookIIICh23FloorNormalizedA16CompactResolventWithoutSpectralTheorem
    where
  compactResolvent :
    G8BookIIICh23FloorNormalizedA16ResolventCompactnessSource
  noSpectralTheorem :
    ¬ G8BookIIICh23FloorNormalizedA16SelectedCompactSelfAdjointResolventSpectralTheorem

theorem
    G8BookIIICh23FloorNormalizedA16CompactResolventWithoutSpectralTheorem.refutes
    (gap :
      G8BookIIICh23FloorNormalizedA16CompactResolventWithoutSpectralTheorem) :
    False :=
  gap.noSpectralTheorem
    g8BookIIICh23FloorNormalizedA16SelectedCompactSelfAdjointResolventSpectralTheorem_closed

/-- Discrete spectral resolution without the no-continuous-residue branch is
    not the selected Lane A point-spectrum consequence. -/
structure
    G8BookIIICh23FloorNormalizedA16DiscreteSpectrumWithoutNoContinuousResidue
    where
  finiteMultiplicity :
    G8BookIIICh23FloorNormalizedA16SelectedFiniteMultiplicityOfEigenvalues
  eigenvalueEscape :
    G8BookIIICh23FloorNormalizedA16SelectedEigenvalueEscapeToInfinity
  noNoContinuousResidue :
    ¬ G8BookIIICh23FloorNormalizedA16SelectedNoContinuousSpectralResidueForLaneAPredicate

theorem
    G8BookIIICh23FloorNormalizedA16DiscreteSpectrumWithoutNoContinuousResidue.refutes
    (gap :
      G8BookIIICh23FloorNormalizedA16DiscreteSpectrumWithoutNoContinuousResidue) :
    False :=
  gap.noNoContinuousResidue
    g8BookIIICh23FloorNormalizedA16SelectedNoContinuousSpectralResidueForLaneAPredicate_closed

/-- Finite standard-mode diagnostics do not replace the selected compact
    self-adjoint resolvent spectral theorem. -/
structure
    G8BookIIICh23FloorNormalizedA16FiniteModeDiagnosticsWithoutSelectedSpectralTheorem
    where
  finiteModeDiagnostics : Prop
  finiteModeDiagnosticsWitness : finiteModeDiagnostics
  noSelectedSpectralTheorem :
    ¬ G8BookIIICh23FloorNormalizedA16SelectedCompactSelfAdjointResolventSpectralTheorem

theorem
    G8BookIIICh23FloorNormalizedA16FiniteModeDiagnosticsWithoutSelectedSpectralTheorem.refutes
    (gap :
      G8BookIIICh23FloorNormalizedA16FiniteModeDiagnosticsWithoutSelectedSpectralTheorem) :
    False :=
  gap.noSelectedSpectralTheorem
    g8BookIIICh23FloorNormalizedA16SelectedCompactSelfAdjointResolventSpectralTheorem_closed

end Tau.BookIII.Bridge
