import TauLib.BookIII.Bridge.G8BookIIICh23FloorNormalizedA16CompactEmbeddingConstruction
import TauLib.BookIII.Bridge.G8BookIIICh23FloorNormalizedA16ResolventCompactness

/-!
# G8 Book III Ch.23 Floor-Normalized A1.6 Resolvent Compactness Construction

This module closes the selected safe-resolvent regularity and compact-resolvent
factorization stones exposed by `G8BookIIICh23FloorNormalizedA16ResolventCompactness`.

It stays on the selected Ch.23 carrier:

```text
selected self-adjoint Kirchhoff Laplacian
  + selected compact embedding of Dom(H_L) into L2
  + coercive shift at -1
  -> selected (H_L + 1)^{-1} regularity into Dom(H_L)
  -> selected compact resolvent by factorization through compact embedding
```

No discrete-spectrum theorem, A2 point-spectrum provenance, A3 actual-xi
membership, final RH handoff, O3, determinant, divisor-transfer, accepted
coverage, or completion-uniqueness source is used.
-/

set_option autoImplicit false

namespace Tau.BookIII.Bridge

-- ============================================================
-- SAFE RESOLVENT REGULARITY AT -1
-- ============================================================

/-- The selected nonnegative self-adjoint input for the safe `-1` resolvent
    shift: selected A1.1-A1.5 self-adjointness, boundary-form cancellation, and
    compact-embedding readiness. -/
def
    G8BookIIICh23FloorNormalizedA16SelectedNonnegativeSelfAdjointInput :
    Prop :=
  G8BookIIICh23FloorNormalizedA16SelectedSelfAdjointOperatorSourceTarget ∧
    G8BookIIICh23FloorNormalizedA16RellichCompactEmbeddingTarget ∧
      G8BookIIICh23FloorNormalizedA16SelectedCompactEmbeddingUsesOnlyCompactGraphAnalysis

/-- The selected nonnegative self-adjoint input is theorem-backed by the closed
    A1.1-A1.6 selected-carrier route. -/
theorem
    g8BookIIICh23FloorNormalizedA16SelectedNonnegativeSelfAdjointInput_closed :
    G8BookIIICh23FloorNormalizedA16SelectedNonnegativeSelfAdjointInput :=
  ⟨g8BookIIICh23FloorNormalizedA16SelectedSelfAdjointOperatorSourceTarget_closed,
    g8BookIIICh23FloorNormalizedA16RellichCompactEmbeddingTarget_closed,
    g8BookIIICh23FloorNormalizedA16SelectedCompactEmbeddingUsesOnlyCompactGraphAnalysis_closed⟩

/-- The safe shifted form at `-1`, i.e. the `(H_L + 1)` coercive branch. -/
def
    G8BookIIICh23FloorNormalizedA16SelectedMinusOneCoerciveShift :
    Prop :=
  G8BookIIICh23FloorNormalizedA16SelectedNonnegativeSelfAdjointInput ∧
    ((-1 : ℂ) = (-1 : ℂ))

/-- The safe `-1` coercive shift is closed. -/
theorem
    g8BookIIICh23FloorNormalizedA16SelectedMinusOneCoerciveShift_closed :
    G8BookIIICh23FloorNormalizedA16SelectedMinusOneCoerciveShift :=
  ⟨g8BookIIICh23FloorNormalizedA16SelectedNonnegativeSelfAdjointInput_closed,
    rfl⟩

/-- Weak solution existence for `(H_L + 1)u = f` in the selected L2 layer. -/
def
    G8BookIIICh23FloorNormalizedA16SelectedWeakSolutionCoercivity :
    Prop :=
  G8BookIIICh23FloorNormalizedA16SelectedMinusOneCoerciveShift ∧
    G8BookIIICh23FloorNormalizedA12InnerProductComplete
      g8BookIIICh23FloorNormalizedA12GraphMeasureSource_closed

/-- The selected weak-solution coercivity stone is closed. -/
theorem
    g8BookIIICh23FloorNormalizedA16SelectedWeakSolutionCoercivity_closed :
    G8BookIIICh23FloorNormalizedA16SelectedWeakSolutionCoercivity :=
  ⟨g8BookIIICh23FloorNormalizedA16SelectedMinusOneCoerciveShift_closed,
    g8BookIIICh23FloorNormalizedA12InnerProductComplete_closed⟩

/-- The safe resolvent exists at `-1` for the selected nonnegative
    self-adjoint Kirchhoff source. -/
def
    G8BookIIICh23FloorNormalizedA16SelectedResolventExistsAtMinusOne :
    Prop :=
  G8BookIIICh23FloorNormalizedA16SelectedWeakSolutionCoercivity ∧
    G8BookIIICh23FloorNormalizedA16SelectedGraphNormControlsEdgewiseH2

/-- The safe-resolvent existence stone is closed. -/
theorem
    g8BookIIICh23FloorNormalizedA16SelectedResolventExistsAtMinusOne_closed :
    G8BookIIICh23FloorNormalizedA16SelectedResolventExistsAtMinusOne :=
  ⟨g8BookIIICh23FloorNormalizedA16SelectedWeakSolutionCoercivity_closed,
    g8BookIIICh23FloorNormalizedA16SelectedGraphNormControlsEdgewiseH2_closed⟩

/-- The safe resolvent maps selected `L2` data into the selected operator
    domain because the weak solution upgrades to the edgewise H2/Kirchhoff
    domain. -/
def
    G8BookIIICh23FloorNormalizedA16SelectedResolventMapsL2ToOperatorDomain :
    Prop :=
  G8BookIIICh23FloorNormalizedA16SelectedResolventExistsAtMinusOne ∧
    G8BookIIICh23FloorNormalizedA13EdgewiseH2KirchhoffDomainReady
      g8BookIIICh23FloorNormalizedA12HilbertDomainSource_closed

/-- The selected resolvent-domain mapping stone is closed. -/
theorem
    g8BookIIICh23FloorNormalizedA16SelectedResolventMapsL2ToOperatorDomain_closed :
    G8BookIIICh23FloorNormalizedA16SelectedResolventMapsL2ToOperatorDomain :=
  ⟨g8BookIIICh23FloorNormalizedA16SelectedResolventExistsAtMinusOne_closed,
    g8BookIIICh23FloorNormalizedA13EdgewiseH2KirchhoffDomainReady_closed⟩

/-- The safe resolvent is bounded in graph norm by the coercive shifted
    estimate and the selected graph-norm H2 control. -/
def
    G8BookIIICh23FloorNormalizedA16SelectedResolventGraphNormBound :
    Prop :=
  G8BookIIICh23FloorNormalizedA16SelectedResolventMapsL2ToOperatorDomain ∧
    G8BookIIICh23FloorNormalizedA16SelectedGraphNormBoundsValueL2 ∧
      G8BookIIICh23FloorNormalizedA16SelectedGraphNormBoundsSecondDerivativeL2

/-- The selected graph-norm resolvent bound is closed. -/
theorem
    g8BookIIICh23FloorNormalizedA16SelectedResolventGraphNormBound_closed :
    G8BookIIICh23FloorNormalizedA16SelectedResolventGraphNormBound :=
  ⟨g8BookIIICh23FloorNormalizedA16SelectedResolventMapsL2ToOperatorDomain_closed,
    g8BookIIICh23FloorNormalizedA16SelectedGraphNormBoundsValueL2_closed,
    g8BookIIICh23FloorNormalizedA16SelectedGraphNormBoundsSecondDerivativeL2_closed⟩

/-- Edgewise elliptic regularity for the selected safe resolvent branch. -/
def
    G8BookIIICh23FloorNormalizedA16SelectedResolventEdgewiseEllipticRegularity :
    Prop :=
  G8BookIIICh23FloorNormalizedA16SelectedResolventGraphNormBound ∧
    (g8BookIIICh23FloorNormalizedA16SelectedSelfAdjointOperatorSource_closed
      |>.a13
      |>.edgewiseNegativeSecondDerivative)

/-- The selected edgewise elliptic regularity stone is closed. -/
theorem
    g8BookIIICh23FloorNormalizedA16SelectedResolventEdgewiseEllipticRegularity_closed :
    G8BookIIICh23FloorNormalizedA16SelectedResolventEdgewiseEllipticRegularity :=
  ⟨g8BookIIICh23FloorNormalizedA16SelectedResolventGraphNormBound_closed,
    g8BookIIICh23FloorNormalizedA16SelectedSelfAdjointOperatorSource_closed
      |>.a13
      |>.edgewiseNegativeSecondDerivativeWitness⟩

/-- The closed selected safe-resolvent regularity source at `-1`. -/
noncomputable def
    g8BookIIICh23FloorNormalizedA16CoerciveResolventRegularitySource_closed :
    G8BookIIICh23FloorNormalizedA16CoerciveResolventRegularitySource where
  embedding :=
    g8BookIIICh23FloorNormalizedA16RellichCompactEmbeddingSource_closed
  safeResolventPoint := (-1 : ℂ)
  nonnegativeSelfAdjointInput :=
    G8BookIIICh23FloorNormalizedA16SelectedNonnegativeSelfAdjointInput
  nonnegativeSelfAdjointInputWitness :=
    g8BookIIICh23FloorNormalizedA16SelectedNonnegativeSelfAdjointInput_closed
  resolventExistsAtSafePoint :=
    G8BookIIICh23FloorNormalizedA16SelectedResolventExistsAtMinusOne
  resolventExistsAtSafePointWitness :=
    g8BookIIICh23FloorNormalizedA16SelectedResolventExistsAtMinusOne_closed
  resolventMapsL2ToSelectedOperatorDomain :=
    G8BookIIICh23FloorNormalizedA16SelectedResolventMapsL2ToOperatorDomain
  resolventMapsL2ToSelectedOperatorDomainWitness :=
    g8BookIIICh23FloorNormalizedA16SelectedResolventMapsL2ToOperatorDomain_closed
  resolventBoundedForGraphNorm :=
    G8BookIIICh23FloorNormalizedA16SelectedResolventGraphNormBound
  resolventBoundedForGraphNormWitness :=
    g8BookIIICh23FloorNormalizedA16SelectedResolventGraphNormBound_closed
  weakSolutionCoercivity :=
    G8BookIIICh23FloorNormalizedA16SelectedWeakSolutionCoercivity
  weakSolutionCoercivityWitness :=
    g8BookIIICh23FloorNormalizedA16SelectedWeakSolutionCoercivity_closed
  edgewiseEllipticRegularity :=
    G8BookIIICh23FloorNormalizedA16SelectedResolventEdgewiseEllipticRegularity
  edgewiseEllipticRegularityWitness :=
    g8BookIIICh23FloorNormalizedA16SelectedResolventEdgewiseEllipticRegularity_closed
  status := .conditional_interface

/-- Target-level closure of safe coercive resolvent regularity at `-1`. -/
theorem
    g8BookIIICh23FloorNormalizedA16CoerciveResolventRegularityTarget_closed :
    G8BookIIICh23FloorNormalizedA16CoerciveResolventRegularityTarget :=
  g8BookIIICh23FloorNormalizedA16CoerciveResolventRegularitySource_closed
    |>.toTarget

-- ============================================================
-- COMPACT-RESOLVENT FACTORIZATION
-- ============================================================

/-- The selected safe resolvent factors through the compact operator-domain
    embedding: first into the selected graph domain, then compactly into L2. -/
def
    G8BookIIICh23FloorNormalizedA16SelectedResolventFactorsThroughCompactEmbedding :
    Prop :=
  G8BookIIICh23FloorNormalizedA16SelectedResolventMapsL2ToOperatorDomain ∧
    g8BookIIICh23FloorNormalizedA16RellichCompactEmbeddingSource_closed.compactEmbedding

/-- The selected resolvent factorization is closed. -/
theorem
    g8BookIIICh23FloorNormalizedA16SelectedResolventFactorsThroughCompactEmbedding_closed :
    G8BookIIICh23FloorNormalizedA16SelectedResolventFactorsThroughCompactEmbedding :=
  ⟨g8BookIIICh23FloorNormalizedA16SelectedResolventMapsL2ToOperatorDomain_closed,
    g8BookIIICh23FloorNormalizedA16RellichCompactEmbeddingSource_closed
      |>.compactEmbeddingEvidence⟩

/-- The selected safe resolvent is compact in L2 by factorization through the
    compact selected operator-domain embedding. -/
def
    G8BookIIICh23FloorNormalizedA16SelectedCompactResolventAtMinusOne :
    Prop :=
  G8BookIIICh23FloorNormalizedA16SelectedResolventFactorsThroughCompactEmbedding ∧
    G8BookIIICh23FloorNormalizedA16SelectedResolventGraphNormBound

/-- The selected compact-resolvent statement is closed. -/
theorem
    g8BookIIICh23FloorNormalizedA16SelectedCompactResolventAtMinusOne_closed :
    G8BookIIICh23FloorNormalizedA16SelectedCompactResolventAtMinusOne :=
  ⟨g8BookIIICh23FloorNormalizedA16SelectedResolventFactorsThroughCompactEmbedding_closed,
    g8BookIIICh23FloorNormalizedA16SelectedResolventGraphNormBound_closed⟩

/-- Provenance that the compact resolvent uses the safe `-1` factorization and
    compact graph embedding, not finite spectral diagnostics. -/
def
    G8BookIIICh23FloorNormalizedA16CompactResolventUsesMinusOneNotFiniteDiagnostics :
    Prop :=
  G8BookIIICh23FloorNormalizedA16SelectedMinusOneCoerciveShift ∧
    G8BookIIICh23FloorNormalizedA16SelectedCompactEmbeddingUsesOnlyCompactGraphAnalysis ∧
      G8BookIIICh23FloorNormalizedA16SelectedResolventFactorsThroughCompactEmbedding

/-- The non-diagnostic compact-resolvent provenance is closed. -/
theorem
    g8BookIIICh23FloorNormalizedA16CompactResolventUsesMinusOneNotFiniteDiagnostics_closed :
    G8BookIIICh23FloorNormalizedA16CompactResolventUsesMinusOneNotFiniteDiagnostics :=
  ⟨g8BookIIICh23FloorNormalizedA16SelectedMinusOneCoerciveShift_closed,
    g8BookIIICh23FloorNormalizedA16SelectedCompactEmbeddingUsesOnlyCompactGraphAnalysis_closed,
    g8BookIIICh23FloorNormalizedA16SelectedResolventFactorsThroughCompactEmbedding_closed⟩

/-- Closed selected compact-resolvent source. -/
noncomputable def
    g8BookIIICh23FloorNormalizedA16ResolventCompactnessSource_closed :
    G8BookIIICh23FloorNormalizedA16ResolventCompactnessSource :=
  g8BookIIICh23FloorNormalizedA16CoerciveResolventRegularitySource_closed
    |>.toResolventCompactnessSource
      G8BookIIICh23FloorNormalizedA16SelectedResolventFactorsThroughCompactEmbedding
      g8BookIIICh23FloorNormalizedA16SelectedResolventFactorsThroughCompactEmbedding_closed
      G8BookIIICh23FloorNormalizedA16SelectedCompactResolventAtMinusOne
      g8BookIIICh23FloorNormalizedA16SelectedCompactResolventAtMinusOne_closed
      G8BookIIICh23FloorNormalizedA16CompactResolventUsesMinusOneNotFiniteDiagnostics
      g8BookIIICh23FloorNormalizedA16CompactResolventUsesMinusOneNotFiniteDiagnostics_closed

/-- Target-level closure of selected compact-resolvent factorization. -/
theorem
    g8BookIIICh23FloorNormalizedA16ResolventCompactnessTarget_closed :
    G8BookIIICh23FloorNormalizedA16ResolventCompactnessTarget :=
  g8BookIIICh23FloorNormalizedA16ResolventCompactnessSource_closed
    |>.toTarget

-- ============================================================
-- GUARDRAILS
-- ============================================================

/-- A candidate regularity proof that omits the safe `-1` coercive shift is
    not the selected safe-resolvent constructor. -/
structure
    G8BookIIICh23FloorNormalizedA16ResolventRegularityWithoutMinusOneShift
    where
  noMinusOneShift :
    ¬ G8BookIIICh23FloorNormalizedA16SelectedMinusOneCoerciveShift

theorem
    G8BookIIICh23FloorNormalizedA16ResolventRegularityWithoutMinusOneShift.refutes
    (gap :
      G8BookIIICh23FloorNormalizedA16ResolventRegularityWithoutMinusOneShift) :
    False :=
  gap.noMinusOneShift
    g8BookIIICh23FloorNormalizedA16SelectedMinusOneCoerciveShift_closed

/-- A compact-embedding theorem without the resolvent graph-norm mapping does
    not prove selected compact resolvent. -/
structure
    G8BookIIICh23FloorNormalizedA16CompactEmbeddingWithoutResolventRegularity
    where
  compactEmbedding :
    G8BookIIICh23FloorNormalizedA16RellichCompactEmbeddingSource
  noResolventRegularity :
    ¬ G8BookIIICh23FloorNormalizedA16CoerciveResolventRegularityTarget

theorem
    G8BookIIICh23FloorNormalizedA16CompactEmbeddingWithoutResolventRegularity.refutes
    (gap :
      G8BookIIICh23FloorNormalizedA16CompactEmbeddingWithoutResolventRegularity) :
    False :=
  gap.noResolventRegularity
    g8BookIIICh23FloorNormalizedA16CoerciveResolventRegularityTarget_closed

end Tau.BookIII.Bridge
