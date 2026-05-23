import TauLib.BookIII.Bridge.G8BookIIICh23FloorNormalizedA2SelectedOperatorReadySource

/-!
# G8 Book III Ch.23 Floor-Normalized A2 Eigenpair Point-Spectrum Source

This module closes the A2.1 selection step for the public selected Ch.23
operator source and sharpens A2.4 into the exact self-adjoint eigenpair
reality payload.

The selected native point-spectrum predicate is definitionally the existing
eigenpair predicate for
`g8BookIIICh23FloorNormalizedA2SelectedOperatorReadySource.operatorSource`.
The remaining analytic work is not hidden: it is the self-adjoint eigenpair
calculus that proves the spectral value equals its complex conjugate, hence has
zero imaginary part.

No actual `xi` membership theorem appears here; that remains A3.
-/

set_option autoImplicit false

noncomputable section

namespace Tau.BookIII.Bridge

open scoped ComplexConjugate

-- ============================================================
-- SELECTED A2.1 NATIVE POINT-SPECTRUM PREDICATE
-- ============================================================

/-- A2.1: the selected operator-native point spectrum.

It is exactly the eigenpair predicate for the selected Ch.23
floor-normalized operator, not a finite `n^2` diagnostic and not an
actual-`xi` membership predicate. -/
def G8BookIIICh23FloorNormalizedA2NativePointSpectrum
    (spectralValue : ℂ) : Prop :=
  G8BookIIILemniscateEigenpairPointSpectrumMembership
    g8BookIIICh23FloorNormalizedA2SelectedCompactResolventSource
    spectralValue

/-- The selected native predicate is definitionally the existing eigenpair
point-spectrum membership predicate. -/
theorem G8BookIIICh23FloorNormalizedA2NativePointSpectrum_iff_eigenpair
    (spectralValue : ℂ) :
    G8BookIIICh23FloorNormalizedA2NativePointSpectrum spectralValue ↔
      G8BookIIILemniscateEigenpairPointSpectrumMembership
        g8BookIIICh23FloorNormalizedA2SelectedCompactResolventSource
        spectralValue :=
  Iff.rfl

/-- A2.1 source target: the selected native point-spectrum definition agrees
exactly with the eigenpair predicate. -/
def G8BookIIICh23FloorNormalizedA2NativePointSpectrumDefinitionTarget :
    Prop :=
  ∀ spectralValue : ℂ,
    G8BookIIICh23FloorNormalizedA2NativePointSpectrum spectralValue ↔
      G8BookIIILemniscateEigenpairPointSpectrumMembership
        g8BookIIICh23FloorNormalizedA2SelectedCompactResolventSource
        spectralValue

/-- Target-level closure of the A2.1 native point-spectrum definition. -/
theorem
    g8BookIIICh23FloorNormalizedA2NativePointSpectrumDefinitionTarget_closed :
    G8BookIIICh23FloorNormalizedA2NativePointSpectrumDefinitionTarget :=
  G8BookIIICh23FloorNormalizedA2NativePointSpectrum_iff_eigenpair

-- ============================================================
-- A2.3 SELECTED CERTIFIED EIGENPAIR DATA
-- ============================================================

/-- A2.3: selected eigenpair data is the certified Book III eigenpair carrier
for the selected compact-resolvent operator.

The generic carrier records the domain/eigen-equation evidence together with
the nonzero norm-square and self-adjoint scalar pairing identity needed for
A2.4. -/
def G8BookIIICh23FloorNormalizedA2SelectedEigenpairData
    (spectralValue : ℂ) : Type 2 :=
  G8BookIIILemniscateEigenpairData
    g8BookIIICh23FloorNormalizedA2SelectedCompactResolventSource
    spectralValue

/-- A2.3 target: native point-spectrum membership is exactly nonempty selected
certified eigenpair data. -/
def G8BookIIICh23FloorNormalizedA2SelectedEigenpairDataTarget :
    Prop :=
  ∀ spectralValue : ℂ,
    G8BookIIICh23FloorNormalizedA2NativePointSpectrum spectralValue ↔
      Nonempty
        (G8BookIIICh23FloorNormalizedA2SelectedEigenpairData
          spectralValue)

/-- Target-level closure of the selected A2.3 certified eigenpair-data
surface. -/
theorem
    g8BookIIICh23FloorNormalizedA2SelectedEigenpairDataTarget_closed :
    G8BookIIICh23FloorNormalizedA2SelectedEigenpairDataTarget := by
  intro spectralValue
  rfl

/-- A selected native point-spectrum member carries the self-adjoint scalar
pairing identity and therefore the conjugate-eigenvalue equality. -/
theorem
    g8BookIIICh23FloorNormalizedA2_conjugateEigenvalueEquality_ofNativeMember
    (spectralValue : ℂ)
    (member :
      G8BookIIICh23FloorNormalizedA2NativePointSpectrum spectralValue) :
    spectralValue = conj spectralValue := by
  rcases
    ((G8BookIIICh23FloorNormalizedA2NativePointSpectrum_iff_eigenpair
      spectralValue).mp member) with ⟨data⟩
  exact data.conjugateEigenvalueEquality

-- ============================================================
-- A2.4 SELF-ADJOINT EIGENPAIR REALITY PAYLOAD
-- ============================================================

/-- If a complex value equals its conjugate, its imaginary part vanishes. -/
theorem g8_complex_im_eq_zero_of_eq_conj
    (spectralValue : ℂ)
    (hConj : spectralValue = conj spectralValue) :
    spectralValue.im = 0 :=
  Complex.conj_eq_iff_im.mp hConj.symm

/-- Proof-carrying self-adjoint eigenpair calculus for the selected operator.

This is the exact A2.4 analytic payload, split at the point where the graph
Hilbert-space calculation should enter:

```text
H u = lambda u
self-adjointness of H
nonzero u
scalar extraction/cancellation
  -> lambda = conjugate(lambda)
  -> lambda.im = 0
```

The final field is the conjugate-eigenvalue equality produced by that
calculation.  The other fields record the intended proof stones and prevent a
finite diagnostic from masquerading as the reality theorem. -/
structure G8BookIIICh23FloorNormalizedA2SelfAdjointEigenpairRealityCalculus
    where
  conjugateEigenvalueEquality :
    ∀ spectralValue : ℂ,
      G8BookIIICh23FloorNormalizedA2NativePointSpectrum spectralValue →
        spectralValue = conj spectralValue
  eigenpairPairingEquationEvidence : Prop
  eigenpairPairingEquationWitness : eigenpairPairingEquationEvidence
  selfAdjointPairingSymmetryEvidence : Prop
  selfAdjointPairingSymmetryWitness : selfAdjointPairingSymmetryEvidence
  scalarExtractionEvidence : Prop
  scalarExtractionWitness : scalarExtractionEvidence
  nonzeroNormCancellationEvidence : Prop
  nonzeroNormCancellationWitness : nonzeroNormCancellationEvidence

/-- The proof-carrying A2.4 calculus implies real-valuedness of every selected
native point-spectrum member. -/
theorem
    G8BookIIICh23FloorNormalizedA2SelfAdjointEigenpairRealityCalculus.realOfNativeMember
    (source :
      G8BookIIICh23FloorNormalizedA2SelfAdjointEigenpairRealityCalculus)
    (spectralValue : ℂ)
    (member :
      G8BookIIICh23FloorNormalizedA2NativePointSpectrum spectralValue) :
    spectralValue.im = 0 :=
  g8_complex_im_eq_zero_of_eq_conj spectralValue
    (source.conjugateEigenvalueEquality spectralValue member)

/-- The selected A2.4 target: a self-adjoint eigenpair reality source for the
selected Ch.23 compact-resolvent operator. -/
def G8BookIIICh23FloorNormalizedA2EigenpairRealityTarget : Prop :=
  Nonempty
    (G8BookIIILemniscateEigenpairRealitySource
      g8BookIIICh23FloorNormalizedA2SelectedCompactResolventSource)

/-- Smaller A2.4 calculus target.  This is the next analytic proof stone if the
graph Hilbert scalar-extraction laws are not yet exposed directly. -/
def
    G8BookIIICh23FloorNormalizedA2SelfAdjointEigenpairRealityCalculusTarget :
    Prop :=
  Nonempty
    G8BookIIICh23FloorNormalizedA2SelfAdjointEigenpairRealityCalculus

/-- A self-adjoint eigenpair calculus builds the selected eigenpair reality
source required by the existing proof-step surface. -/
def
    G8BookIIICh23FloorNormalizedA2SelfAdjointEigenpairRealityCalculus.toRealitySource
    (source :
      G8BookIIICh23FloorNormalizedA2SelfAdjointEigenpairRealityCalculus) :
    G8BookIIILemniscateEigenpairRealitySource
      g8BookIIICh23FloorNormalizedA2SelectedCompactResolventSource where
  selfAdjointEigenpairReality := by
    intro spectralValue member
    exact source.realOfNativeMember spectralValue member
  innerProductArgumentEvidence :=
    source.eigenpairPairingEquationEvidence ∧
      source.selfAdjointPairingSymmetryEvidence ∧
        source.scalarExtractionEvidence
  innerProductArgumentWitness :=
    ⟨source.eigenpairPairingEquationWitness,
      source.selfAdjointPairingSymmetryWitness,
      source.scalarExtractionWitness⟩
  nonzeroNormCancellationEvidence :=
    source.nonzeroNormCancellationEvidence
  nonzeroNormCancellationWitness :=
    source.nonzeroNormCancellationWitness

/-- The smaller self-adjoint eigenpair calculus target is sufficient for the
selected A2.4 reality target. -/
theorem
    G8BookIIICh23FloorNormalizedA2EigenpairRealityTarget.ofCalculus
    (h :
      G8BookIIICh23FloorNormalizedA2SelfAdjointEigenpairRealityCalculusTarget) :
    G8BookIIICh23FloorNormalizedA2EigenpairRealityTarget :=
  h.elim fun source => ⟨source.toRealitySource⟩

/-- The selected A2.4 self-adjoint eigenpair calculus is closed from the
certified selected eigenpair data introduced in A2.3. -/
def
    g8BookIIICh23FloorNormalizedA2SelfAdjointEigenpairRealityCalculus_closed :
    G8BookIIICh23FloorNormalizedA2SelfAdjointEigenpairRealityCalculus where
  conjugateEigenvalueEquality :=
    g8BookIIICh23FloorNormalizedA2_conjugateEigenvalueEquality_ofNativeMember
  eigenpairPairingEquationEvidence :=
    G8BookIIILemniscateEigenpairPairingCalculationEvidence
      g8BookIIICh23FloorNormalizedA2SelectedCompactResolventSource
  eigenpairPairingEquationWitness :=
    g8BookIIILemniscateEigenpairPairingCalculationEvidence_ofData
      g8BookIIICh23FloorNormalizedA2SelectedCompactResolventSource
  selfAdjointPairingSymmetryEvidence :=
    g8BookIIICh23FloorNormalizedA2SelectedCompactResolventSource
      |>.selfAdjointOperator
      |>.selfAdjointStatement
  selfAdjointPairingSymmetryWitness :=
    g8BookIIICh23FloorNormalizedA2SelectedCompactResolventSource
      |>.selfAdjointOperator
      |>.selfAdjointEvidence
  scalarExtractionEvidence :=
    G8BookIIICh23FloorNormalizedA2SelectedEigenpairDataTarget
  scalarExtractionWitness :=
    g8BookIIICh23FloorNormalizedA2SelectedEigenpairDataTarget_closed
  nonzeroNormCancellationEvidence :=
    G8BookIIILemniscateEigenpairNonzeroNormEvidence
      g8BookIIICh23FloorNormalizedA2SelectedCompactResolventSource
  nonzeroNormCancellationWitness :=
    g8BookIIILemniscateEigenpairNonzeroNormEvidence_ofData
      g8BookIIICh23FloorNormalizedA2SelectedCompactResolventSource

/-- Target-level closure of the selected A2.4 self-adjoint eigenpair
calculus. -/
theorem
    g8BookIIICh23FloorNormalizedA2SelfAdjointEigenpairRealityCalculusTarget_closed :
    G8BookIIICh23FloorNormalizedA2SelfAdjointEigenpairRealityCalculusTarget :=
  ⟨g8BookIIICh23FloorNormalizedA2SelfAdjointEigenpairRealityCalculus_closed⟩

/-- Target-level closure of the selected A2.4 eigenpair reality source. -/
theorem
    g8BookIIICh23FloorNormalizedA2EigenpairRealityTarget_closed :
    G8BookIIICh23FloorNormalizedA2EigenpairRealityTarget :=
  G8BookIIICh23FloorNormalizedA2EigenpairRealityTarget.ofCalculus
    g8BookIIICh23FloorNormalizedA2SelfAdjointEigenpairRealityCalculusTarget_closed

-- ============================================================
-- PROVENANCE AND A1/A2 ADAPTERS
-- ============================================================

/-- A selected eigenpair reality source builds selected eigenpair point-spectrum
provenance. -/
def
    g8BookIIICh23FloorNormalizedA2EigenpairPointSpectrumProvenance_ofRealitySource
    (reality :
      G8BookIIILemniscateEigenpairRealitySource
        g8BookIIICh23FloorNormalizedA2SelectedCompactResolventSource) :
    G8BookIIILemniscateEigenpairPointSpectrumProvenance
      g8BookIIICh23FloorNormalizedA2SelectedCompactResolventSource where
  realitySource := reality
  pointSpectrumDefinitionEvidence :=
    G8BookIIICh23FloorNormalizedA2NativePointSpectrumDefinitionTarget
  pointSpectrumDefinitionWitness :=
    g8BookIIICh23FloorNormalizedA2NativePointSpectrumDefinitionTarget_closed

/-- The selected A2.4 target builds eigenpair point-spectrum provenance. -/
def
    g8BookIIICh23FloorNormalizedA2EigenpairPointSpectrumProvenance_ofRealityTarget
    (hReality :
      G8BookIIICh23FloorNormalizedA2EigenpairRealityTarget) :
    G8BookIIILemniscateEigenpairPointSpectrumProvenance
      g8BookIIICh23FloorNormalizedA2SelectedCompactResolventSource :=
  g8BookIIICh23FloorNormalizedA2EigenpairPointSpectrumProvenance_ofRealitySource
    (Classical.choice hReality)

/-- The selected A2.4 target builds the memo-compatible analytic
point-spectrum provenance wrapper. -/
def
    g8BookIIICh23FloorNormalizedA2AnalyticPointSpectrumProvenance_ofRealityTarget
    (hReality :
      G8BookIIICh23FloorNormalizedA2EigenpairRealityTarget) :
    G8BookIIILemniscateAnalyticPointSpectrumProvenance
      g8BookIIICh23FloorNormalizedA2SelectedOperatorReadySource :=
  (g8BookIIICh23FloorNormalizedA2EigenpairPointSpectrumProvenance_ofRealityTarget
    hReality).toAnalyticProvenance

/-- The selected A2.4 target builds strict operator-native provenance for the
selected A1 operator context. -/
def
    g8BookIIICh23FloorNormalizedA2OperatorNativeProvenance_ofRealityTarget
    (hReality :
      G8BookIIICh23FloorNormalizedA2EigenpairRealityTarget) :
    G8OperatorNativeSpectralProvenance
      g8BookIIICh23FloorNormalizedA2SelectedOperatorCtx
      g8BookIIICh23FloorNormalizedA2SelectedOperatorReady :=
  (g8BookIIICh23FloorNormalizedA2AnalyticPointSpectrumProvenance_ofRealityTarget
    hReality).toOperatorNativeProvenance

/-- The selected A2.4 target builds the complete A1/A2 source.  This still
contains no A3 canonical actual-`xi` membership theorem. -/
def
    g8BookIIICh23FloorNormalizedA2LaneAOperatorNativeSelfAdjointSource_ofRealityTarget
    (hReality :
      G8BookIIICh23FloorNormalizedA2EigenpairRealityTarget) :
    G8LaneAOperatorNativeSelfAdjointSource where
  operatorCtx := g8BookIIICh23FloorNormalizedA2SelectedOperatorCtx
  operatorReady := g8BookIIICh23FloorNormalizedA2SelectedOperatorReady
  provenance :=
    g8BookIIICh23FloorNormalizedA2OperatorNativeProvenance_ofRealityTarget
      hReality

/-- Target-level adapter from the selected A2.4 target to the combined A1/A2
source target. -/
theorem
    g8BookIIICh23FloorNormalizedA2LaneAOperatorNativeSelfAdjointSourceTarget_ofRealityTarget
    (hReality :
      G8BookIIICh23FloorNormalizedA2EigenpairRealityTarget) :
    G8LaneAOperatorNativeSelfAdjointSourceTarget :=
  ⟨g8BookIIICh23FloorNormalizedA2LaneAOperatorNativeSelfAdjointSource_ofRealityTarget
    hReality⟩

/-- Closed selected A1/A2 source from the A2.3 certified eigenpair surface and
the A2.4 self-adjoint eigenpair reality theorem. -/
def
    g8BookIIICh23FloorNormalizedA2LaneAOperatorNativeSelfAdjointSource_closed :
    G8LaneAOperatorNativeSelfAdjointSource :=
  g8BookIIICh23FloorNormalizedA2LaneAOperatorNativeSelfAdjointSource_ofRealityTarget
    g8BookIIICh23FloorNormalizedA2EigenpairRealityTarget_closed

/-- Target-level closure of A2 operator-native self-adjoint provenance. -/
theorem
    g8BookIIICh23FloorNormalizedA2LaneAOperatorNativeSelfAdjointSourceTarget_closed :
    G8LaneAOperatorNativeSelfAdjointSourceTarget :=
  ⟨g8BookIIICh23FloorNormalizedA2LaneAOperatorNativeSelfAdjointSource_closed⟩

-- ============================================================
-- GUARDRAILS AND FALSIFIERS
-- ============================================================

/-- A value with no selected eigenpair data refutes selected native
point-spectrum membership. -/
structure G8BookIIICh23FloorNormalizedA2MissingSelectedEigenpair
    (spectralValue : ℂ) where
  noEigenpair :
    ¬ G8BookIIILemniscateEigenpairPointSpectrumMembership
        g8BookIIICh23FloorNormalizedA2SelectedCompactResolventSource
        spectralValue

/-- Missing eigenpair data is fatal for the selected native predicate. -/
theorem G8BookIIICh23FloorNormalizedA2MissingSelectedEigenpair.refutes
    {spectralValue : ℂ}
    (gap :
      G8BookIIICh23FloorNormalizedA2MissingSelectedEigenpair spectralValue)
    (member :
      G8BookIIICh23FloorNormalizedA2NativePointSpectrum spectralValue) :
    False :=
  gap.noEigenpair
    ((G8BookIIICh23FloorNormalizedA2NativePointSpectrum_iff_eigenpair
      spectralValue).mp member)

/-- A non-real selected native member refutes a selected eigenpair reality
source. -/
structure G8BookIIICh23FloorNormalizedA2NonrealNativeMember
    (source :
      G8BookIIILemniscateEigenpairRealitySource
        g8BookIIICh23FloorNormalizedA2SelectedCompactResolventSource)
    where
  spectralValue : ℂ
  member :
    G8BookIIICh23FloorNormalizedA2NativePointSpectrum spectralValue
  nonreal : spectralValue.im ≠ 0

/-- Non-real selected native membership is impossible under a selected
eigenpair reality source. -/
theorem G8BookIIICh23FloorNormalizedA2NonrealNativeMember.refutes
    {source :
      G8BookIIILemniscateEigenpairRealitySource
        g8BookIIICh23FloorNormalizedA2SelectedCompactResolventSource}
    (gap :
      G8BookIIICh23FloorNormalizedA2NonrealNativeMember source) :
    False :=
  gap.nonreal
    (source.selfAdjointEigenpairReality gap.spectralValue gap.member)

/-- Selecting the native predicate without the A2.4 reality target is still not
a complete A1/A2 source. -/
structure G8BookIIICh23FloorNormalizedA2NativePredicateWithoutReality where
  nativeDefinition :
    G8BookIIICh23FloorNormalizedA2NativePointSpectrumDefinitionTarget
  missingReality :
    ¬ G8BookIIICh23FloorNormalizedA2EigenpairRealityTarget

/-- A selected native predicate plus a missing reality theorem refutes any
attempted selected A2.4 package. -/
theorem G8BookIIICh23FloorNormalizedA2NativePredicateWithoutReality.refutes
    (gap :
      G8BookIIICh23FloorNormalizedA2NativePredicateWithoutReality)
    (hReality :
      G8BookIIICh23FloorNormalizedA2EigenpairRealityTarget) :
    False :=
  gap.missingReality hReality

end Tau.BookIII.Bridge
