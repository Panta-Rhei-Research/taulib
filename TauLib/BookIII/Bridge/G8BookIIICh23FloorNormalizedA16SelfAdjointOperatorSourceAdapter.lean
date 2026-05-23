import TauLib.BookIII.Bridge.G8BookIIICh23FloorNormalizedA15ReverseInclusionMaximalityAssembly
import TauLib.BookIII.Bridge.G8BookIIILaneAOperatorSelfAdjointProofSource

/-!
# G8 Book III Ch.23 Floor-Normalized A1.6 Self-Adjoint Source Adapter

This module starts the A1.6 compact-resolvent/discrete-spectrum lane by
packaging the closed selected-carrier A1.1-A1.5 route as a self-adjoint
operator source.

The selected route is theorem-backed.  The legacy `LemniscateOperatorDomain`
surface remains separate: transporting the selected operator into that older
raw carrier requires an explicit bridge and exact alignment fields.
-/

set_option autoImplicit false

namespace Tau.BookIII.Bridge

-- ============================================================
-- SELECTED SELF-ADJOINT SOURCE
-- ============================================================

/-- Selected-carrier source for A1.1-A1.5, ready for the compact-resolvent
    step.  This is the closed floor-normalized Ch.23 route, not the older raw
    `LemniscateCarrier` operator surface. -/
structure
    G8BookIIICh23FloorNormalizedA16SelectedSelfAdjointOperatorSource
    where
  a13 :
    G8BookIIICh23FloorNormalizedA13KirchhoffLaplacianConstructionSource
  a13Closed :
    a13 = g8BookIIICh23FloorNormalizedA13KirchhoffLaplacianConstructionSource_closed
  a14 :
    G8BookIIICh23FloorNormalizedA14BoundaryFormCancellationSource
  a14Closed :
    a14 = g8BookIIICh23FloorNormalizedA14BoundaryFormCancellationSource_closed
  a15Maximality :
    G8BookIIICh23FloorNormalizedA15MaximalKirchhoffSelfAdjointExtensionTarget
  edgewiseNegativeSecondDerivative :
    a13.edgewiseNegativeSecondDerivative
  boundaryFormCancellation :
    G8BookIIICh23FloorNormalizedA14BoundaryFormCancellation
      a13
  maximalKirchhoffSelfAdjointness :
    G8BookIIICh23FloorNormalizedA15MaximalKirchhoffSelfAdjointExtensionTarget
  noCompactResolventClaim : Prop
  noCompactResolventClaimWitness : noCompactResolventClaim
  status : SpineStatus := .conditional_interface

/-- Target for the selected self-adjoint source that A1.6 may consume. -/
def
    G8BookIIICh23FloorNormalizedA16SelectedSelfAdjointOperatorSourceTarget :
    Prop :=
  Nonempty
    G8BookIIICh23FloorNormalizedA16SelectedSelfAdjointOperatorSource

/-- The selected A1.1-A1.5 source is closed by the upstream floor-normalized
    route. -/
noncomputable def
    g8BookIIICh23FloorNormalizedA16SelectedSelfAdjointOperatorSource_closed :
    G8BookIIICh23FloorNormalizedA16SelectedSelfAdjointOperatorSource where
  a13 :=
    g8BookIIICh23FloorNormalizedA13KirchhoffLaplacianConstructionSource_closed
  a13Closed := rfl
  a14 :=
    g8BookIIICh23FloorNormalizedA14BoundaryFormCancellationSource_closed
  a14Closed := rfl
  a15Maximality :=
    g8BookIIICh23FloorNormalizedA15MaximalKirchhoffSelfAdjointExtensionTarget_closed
  edgewiseNegativeSecondDerivative :=
    g8BookIIICh23FloorNormalizedA13KirchhoffLaplacianConstructionSource_closed
      |>.edgewiseNegativeSecondDerivativeWitness
  boundaryFormCancellation :=
    g8BookIIICh23FloorNormalizedA14BoundaryFormCancellation_closed
  maximalKirchhoffSelfAdjointness :=
    g8BookIIICh23FloorNormalizedA15MaximalKirchhoffSelfAdjointExtensionTarget_closed
  noCompactResolventClaim := True
  noCompactResolventClaimWitness := trivial
  status := .conditional_interface

/-- Target-level closure of the selected A1.1-A1.5 self-adjoint source. -/
theorem
    g8BookIIICh23FloorNormalizedA16SelectedSelfAdjointOperatorSourceTarget_closed :
    G8BookIIICh23FloorNormalizedA16SelectedSelfAdjointOperatorSourceTarget :=
  ⟨g8BookIIICh23FloorNormalizedA16SelectedSelfAdjointOperatorSource_closed⟩

-- ============================================================
-- LEGACY RAW-CARRIER ADAPTER SURFACE
-- ============================================================

/-- Exact bridge from the selected self-adjoint source to the older
    `G8BookIIIKirchhoffLaplacianSource` surface.

The bridge is intentionally proof-carrying.  It requires the selected-to-raw
Hilbert/domain transfer plus exact legacy operator facts, so selected-carrier
A1.5 is not silently treated as a raw-carrier theorem. -/
structure
    G8BookIIICh23FloorNormalizedA16LegacySelfAdjointOperatorAdapterSource
    where
  selected :
    G8BookIIICh23FloorNormalizedA16SelectedSelfAdjointOperatorSource
  rawDomain :
    G8BookIIICh23FloorNormalizedA12RawHilbertDomainTransferSource
  selectedRawDomainAlignment : Prop
  selectedRawDomainAlignmentEvidence : selectedRawDomainAlignment
  legacyGraphLaplacian :
    LemniscateOperatorDomain → LemniscateL2
  legacyGraphLaplacian_eq_HL_spine :
    legacyGraphLaplacian = H_L_spine
  legacyEdgewiseNegativeSecondDerivative : Prop
  legacyEdgewiseNegativeSecondDerivativeWitness :
    legacyEdgewiseNegativeSecondDerivative
  legacyKirchhoffBoundaryCondition : Prop
  legacyKirchhoffBoundaryConditionWitness :
    legacyKirchhoffBoundaryCondition
  legacyBoundaryFormCancellation : Prop
  legacyBoundaryFormCancellationWitness :
    legacyBoundaryFormCancellation
  legacyMaximalKirchhoffExtension : Prop
  legacyMaximalKirchhoffExtensionWitness :
    legacyMaximalKirchhoffExtension
  legacySelfAdjointStatement : Prop
  legacySelfAdjointEvidence : legacySelfAdjointStatement
  selfAdjointTransportUsesSelectedA15 : Prop
  selfAdjointTransportUsesSelectedA15Witness :
    selfAdjointTransportUsesSelectedA15
  status : SpineStatus := .conditional_interface

/-- Legacy adapter target.  This remains open unless an exact selected-to-raw
    operator transfer is supplied. -/
def
    G8BookIIICh23FloorNormalizedA16LegacySelfAdjointOperatorAdapterTarget :
    Prop :=
  Nonempty
    G8BookIIICh23FloorNormalizedA16LegacySelfAdjointOperatorAdapterSource

/-- The legacy adapter supplies the older Kirchhoff-Laplacian source surface. -/
def
    G8BookIIICh23FloorNormalizedA16LegacySelfAdjointOperatorAdapterSource.toKirchhoffLaplacianSource
    (source :
      G8BookIIICh23FloorNormalizedA16LegacySelfAdjointOperatorAdapterSource) :
    G8BookIIIKirchhoffLaplacianSource where
  domain := source.rawDomain.toHilbertDomainSource
  graphLaplacian := source.legacyGraphLaplacian
  edgewiseNegativeSecondDerivative :=
    source.legacyEdgewiseNegativeSecondDerivative
  edgewiseNegativeSecondDerivativeWitness :=
    source.legacyEdgewiseNegativeSecondDerivativeWitness
  kirchhoffBoundaryCondition :=
    source.legacyKirchhoffBoundaryCondition
  kirchhoffBoundaryConditionWitness :=
    source.legacyKirchhoffBoundaryConditionWitness
  boundaryFormCancellation :=
    source.legacyBoundaryFormCancellation
  boundaryFormCancellationWitness :=
    source.legacyBoundaryFormCancellationWitness
  maximalKirchhoffExtension :=
    source.legacyMaximalKirchhoffExtension
  maximalKirchhoffExtensionWitness :=
    source.legacyMaximalKirchhoffExtensionWitness
  status := source.status

/-- The legacy adapter supplies the existing self-adjoint operator source. -/
def
    G8BookIIICh23FloorNormalizedA16LegacySelfAdjointOperatorAdapterSource.toSelfAdjointOperatorSource
    (source :
      G8BookIIICh23FloorNormalizedA16LegacySelfAdjointOperatorAdapterSource) :
    G8BookIIILemniscateSelfAdjointOperatorSource where
  laplacian := source.toKirchhoffLaplacianSource
  selfAdjointStatement := source.legacySelfAdjointStatement
  selfAdjointEvidence := source.legacySelfAdjointEvidence
  selfAdjointFromBoundaryForm :=
    source.legacyBoundaryFormCancellation ∧
      source.legacyMaximalKirchhoffExtension
  selfAdjointFromBoundaryFormEvidence :=
    ⟨source.legacyBoundaryFormCancellationWitness,
      source.legacyMaximalKirchhoffExtensionWitness⟩
  maximalSymmetricExtensionEvidence :=
    source.legacyMaximalKirchhoffExtension
  maximalSymmetricExtensionWitness :=
    source.legacyMaximalKirchhoffExtensionWitness
  status := source.status

-- ============================================================
-- GUARDRAILS
-- ============================================================

/-- Selected self-adjointness alone does not produce the legacy raw-carrier
    self-adjoint source without exact operator transfer. -/
structure
    G8BookIIICh23FloorNormalizedA16SelectedWithoutLegacyTransfer
    where
  selected :
    G8BookIIICh23FloorNormalizedA16SelectedSelfAdjointOperatorSource
  noLegacyAdapter :
    ¬ G8BookIIICh23FloorNormalizedA16LegacySelfAdjointOperatorAdapterTarget

theorem
    G8BookIIICh23FloorNormalizedA16SelectedWithoutLegacyTransfer.refutes
    (gap :
      G8BookIIICh23FloorNormalizedA16SelectedWithoutLegacyTransfer) :
    ¬ G8BookIIICh23FloorNormalizedA16LegacySelfAdjointOperatorAdapterTarget :=
  gap.noLegacyAdapter

/-- A legacy adapter whose declared graph Laplacian is not the spine operator
    fails the exact alignment required by this compatibility route. -/
structure
    G8BookIIICh23FloorNormalizedA16LegacyGraphLaplacianMismatch
    (source :
      G8BookIIICh23FloorNormalizedA16LegacySelfAdjointOperatorAdapterSource)
    where
  mismatch : source.legacyGraphLaplacian ≠ H_L_spine

theorem
    G8BookIIICh23FloorNormalizedA16LegacyGraphLaplacianMismatch.refutes
    {source :
      G8BookIIICh23FloorNormalizedA16LegacySelfAdjointOperatorAdapterSource}
    (gap :
      G8BookIIICh23FloorNormalizedA16LegacyGraphLaplacianMismatch
        source) :
    False :=
  gap.mismatch source.legacyGraphLaplacian_eq_HL_spine

end Tau.BookIII.Bridge
