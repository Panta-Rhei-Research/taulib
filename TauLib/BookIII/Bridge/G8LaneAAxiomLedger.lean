import TauLib.BookIII.Bridge.G8LaneAOperatorNativeSelfAdjointSource
import TauLib.BookIII.Bridge.G8ActualXiNonzeroHeightSpectralReality
import TauLib.BookIII.Bridge.G8BookIIICh23FloorNormalizedA16DiscretePointSpectrumConstruction
import TauLib.BookIII.Bridge.G8BookIIICh23FloorNormalizedA2EigenpairPointSpectrumSource

/-!
# TauLib.BookIII.Bridge.G8LaneAAxiomLedger

Quarantined axiom ledger for the remaining Lane-A discharge gates.

This module is intentionally **not** imported by `TauLib.BookIII` or by the
axiom-free RH spine.  It exists as an audit harness: each remaining Lane-A
mathematical gate is represented by one explicitly named axiom, and the
theorem-backed downstream adapters show exactly what those gates would close.

Gates A1 and A2 are now theorem-backed by the selected Ch.23
floor-normalized operator route and the selected certified eigenpair
point-spectrum route.  The remaining temporary gate is:

1. canonical actual-`xi` membership in that legitimate spectral source.

As each gate is discharged theorem-backed, its axiom should be replaced by the
proved constructor and the expected axiom count for this module should drop.
-/

set_option autoImplicit false

noncomputable section

namespace Tau.BookIII.Bridge

open Tau.Boundary

-- ============================================================
-- QUARANTINED GATE OBJECTS
-- ============================================================

/-- Gate A1: independent readiness of the Book III lemniscate operator package. -/
structure G8LaneAOperatorReadyGate where
  operatorCtx : LemniscateOperatorContext
  operatorReady : LemniscateOperatorReady operatorCtx

/-- Gate A2: an operator-native self-adjoint spectral predicate whose members
    are real-valued. -/
structure G8LaneAOperatorNativeSelfAdjointGate
    (gate : G8LaneAOperatorReadyGate) where
  legitimacy :
    G8LemniscateSpectralMembershipLegitimacy
      gate.operatorCtx gate.operatorReady

/-- Gate A3: each canonical scaled actual nonzero-height `xi` value is a member
    of the operator-native self-adjoint spectral predicate. -/
structure G8LaneACanonicalActualXiMembershipGate
    (readyGate : G8LaneAOperatorReadyGate)
    (selfAdjointGate :
      G8LaneAOperatorNativeSelfAdjointGate readyGate) where
  membershipSource :
      G8ActualXiCanonicalAbstractSpectralMembershipSource
      selfAdjointGate.legitimacy

-- ============================================================
-- THEOREM-BACKED ADAPTERS FROM THE CLEAN A1/A2 SOURCE
-- ============================================================

/-- A clean A1/A2 source supplies the Lane-A ready gate object. -/
def G8LaneAOperatorNativeSelfAdjointSource.toOperatorReadyGate
    (source : G8LaneAOperatorNativeSelfAdjointSource) :
    G8LaneAOperatorReadyGate where
  operatorCtx := source.operatorCtx
  operatorReady := source.operatorReady

/-- A clean A1/A2 source supplies the Lane-A operator-native self-adjoint gate
    over its ready gate. -/
def G8LaneAOperatorNativeSelfAdjointSource.toOperatorNativeSelfAdjointGate
    (source : G8LaneAOperatorNativeSelfAdjointSource) :
    G8LaneAOperatorNativeSelfAdjointGate
      source.toOperatorReadyGate where
  legitimacy := source.legitimacy

/-- A clean A1/A2 source plus the separate A3 membership theorem supplies the
    canonical actual-`xi` membership gate. -/
def G8LaneAOperatorNativeSelfAdjointSource.toCanonicalActualXiMembershipGate
    (source : G8LaneAOperatorNativeSelfAdjointSource)
    (membership :
      G8ActualXiCanonicalAbstractSpectralMembershipSource
        source.legitimacy) :
    G8LaneACanonicalActualXiMembershipGate
      source.toOperatorReadyGate
      source.toOperatorNativeSelfAdjointGate where
  membershipSource := membership

-- ============================================================
-- TEMPORARY AXIOM LEDGER
-- ============================================================

-- ------------------------------------------------------------
-- Gate A1: theorem-backed selected Book III operator readiness
-- ------------------------------------------------------------

/-- Auxiliary discrete metric used only to inhabit the legacy
    `LemniscateCarrierContext` metric field in the quarantined ledger
    projection.  The load-bearing metric-graph facts below are the selected
    Ch.23 A1.1-A1.6 theorems, not this auxiliary metric constructor. -/
private noncomputable def g8LaneA_discreteMetricSpace
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
    inhabit the legacy context field in this ledger projection. -/
private noncomputable def g8LaneA_indiscreteCompactSpace
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

/-- The official ledger carrier context selected by the closed A1 route.

This is a projection from the theorem-backed floor-normalized Ch.23 operator
route into the legacy `LemniscateOperatorReady` interface.  It does not assert
standard-mode equality or any A2/A3 spectral-membership fact. -/
private noncomputable def g8LaneA_theoremBackedCarrierContext :
    LemniscateCarrierContext where
  topology := ⊤
  metric := g8LaneA_discreteMetricSpace LemniscateCarrier
  compact := g8LaneA_indiscreteCompactSpace LemniscateCarrier
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

/-- Carrier readiness follows from the closed selected A1.1 compact graph
    theorem. -/
private theorem g8LaneA_theoremBackedCarrierReady :
    LemniscateCarrierReady g8LaneA_theoremBackedCarrierContext :=
  ⟨g8BookIIICh23FloorNormalizedA11CompactMetricGraphTarget_closed,
    g8BookIIICh23FloorNormalizedA11CompactMetricGraphTarget_closed,
    g8BookIIICh23FloorNormalizedA11CompactMetricGraphTarget_closed,
    g8BookIIICh23FloorNormalizedA11CompactMetricGraphTarget_closed,
    g8BookIIICh23FloorNormalizedA11CompactMetricGraphTarget_closed,
    rfl⟩

/-- The official ledger measure context projected from the selected A1.2 graph
    measure laws. -/
private noncomputable def g8LaneA_theoremBackedMeasure :
    LemniscateMeasure where
  carrierContext := g8LaneA_theoremBackedCarrierContext
  weight := fun _ => 0
  nonnegative := fun _ => le_rfl
  totalFinite := G8BookIIICh23FloorNormalizedA12GraphMeasureTarget
  lobeMeasureAgreement :=
    G8BookIIICh23FloorNormalizedA12GraphLengthMeasureLawTarget
  crossingAtomPolicy :=
    G8BookIIICh23FloorNormalizedA12GraphMeasureIdentificationTarget
  status := .conditional_interface

/-- The official ledger inner-product context projected from the selected A1.2
    Hilbert/L2 readiness theorem. -/
private noncomputable def g8LaneA_theoremBackedInnerProduct :
    LemniscateInnerProduct where
  inner := fun _ _ => TauReal.zero
  symmetric := G8BookIIICh23FloorNormalizedA12HilbertReadinessTarget
  positive := G8BookIIICh23FloorNormalizedA12HilbertReadinessTarget
  complete := G8BookIIICh23FloorNormalizedA12HilbertReadinessTarget
  compatibleWithMeasure :=
    G8BookIIICh23FloorNormalizedA12HilbertReadinessTarget
  status := .conditional_interface

/-- The official ledger Hilbert context projected from the closed selected
    A1.2 source. -/
private noncomputable def g8LaneA_theoremBackedHilbertContext :
    LemniscateHilbertContext where
  measure := g8LaneA_theoremBackedMeasure
  innerProduct := g8LaneA_theoremBackedInnerProduct
  traceMapDefined :=
    G8BookIIICh23FloorNormalizedA12TraceReadinessTarget
  traceMapContinuous :=
    G8BookIIICh23FloorNormalizedA12TraceReadinessTarget
  quotientCompletionConstructed :=
    G8BookIIICh23FloorNormalizedA12HilbertReadinessTarget
  carrierReady := g8LaneA_theoremBackedCarrierReady
  status := .conditional_interface

/-- Hilbert readiness follows from the closed selected A1.1-A1.2 route. -/
private theorem g8LaneA_theoremBackedHilbertReady :
    LemniscateHilbertReady g8LaneA_theoremBackedHilbertContext :=
  ⟨g8LaneA_theoremBackedCarrierReady,
    g8BookIIICh23FloorNormalizedA12GraphMeasureTarget_closed,
    g8BookIIICh23FloorNormalizedA12GraphLengthMeasureLawTarget_closed,
    g8BookIIICh23FloorNormalizedA12HilbertReadinessTarget_closed,
    g8BookIIICh23FloorNormalizedA12HilbertReadinessTarget_closed,
    g8BookIIICh23FloorNormalizedA12HilbertReadinessTarget_closed,
    g8BookIIICh23FloorNormalizedA12HilbertReadinessTarget_closed,
    g8BookIIICh23FloorNormalizedA12TraceReadinessTarget_closed,
    g8BookIIICh23FloorNormalizedA12TraceReadinessTarget_closed,
    g8BookIIICh23FloorNormalizedA12HilbertReadinessTarget_closed⟩

/-- The official ledger domain context projected from the selected A1.2 trace
    and Kirchhoff-domain closure theorems. -/
private noncomputable def g8LaneA_theoremBackedDomainContext :
    LemniscateDomainContext where
  hilbert := g8LaneA_theoremBackedHilbertContext
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

/-- Domain readiness follows from the closed selected A1.2 source. -/
private theorem g8LaneA_theoremBackedDomainReady :
    LemniscateDomainReady g8LaneA_theoremBackedDomainContext :=
  ⟨g8LaneA_theoremBackedHilbertReady,
    g8BookIIICh23FloorNormalizedA12TraceReadinessTarget_closed,
    g8BookIIICh23FloorNormalizedA12TraceReadinessTarget_closed,
    g8BookIIICh23FloorNormalizedA12TraceReadinessTarget_closed,
    g8BookIIICh23FloorNormalizedA12TraceReadinessTarget_closed,
    g8BookIIICh23FloorNormalizedA12KirchhoffDomainTarget_closed,
    g8BookIIICh23FloorNormalizedA12KirchhoffDomainTarget_closed⟩

/-- The official ledger operator context projected from the closed selected
    A1.3-A1.6 operator route. -/
private noncomputable def g8LaneA_theoremBackedOperatorContext :
    LemniscateOperatorContext where
  domain := g8LaneA_theoremBackedDomainContext
  obligations := {
    selfAdjoint :=
      G8BookIIICh23FloorNormalizedA15MaximalKirchhoffSelfAdjointExtensionTarget
    compactResolvent :=
      G8BookIIICh23FloorNormalizedA16ResolventCompactnessTarget
    discreteSpectrum :=
      G8BookIIICh23FloorNormalizedA16DiscretePointSpectrumTarget
    obligationsRespectDomain :=
      LemniscateDomainReady g8LaneA_theoremBackedDomainContext
  }
  finiteApproximationCompatible :=
    G8BookIIICh23FloorNormalizedA16SelectedDiscreteSpectrumNoStandardModeEqualityClaim
  status := .conditional_interface

/-- Gate A1 is discharged by the closed selected Ch.23 A1.1-A1.6 route. -/
private theorem g8LaneA_theoremBackedOperatorReady :
    LemniscateOperatorReady g8LaneA_theoremBackedOperatorContext :=
  ⟨g8LaneA_theoremBackedDomainReady,
    g8BookIIICh23FloorNormalizedA15MaximalKirchhoffSelfAdjointExtensionTarget_closed,
    g8BookIIICh23FloorNormalizedA16ResolventCompactnessTarget_closed,
    g8BookIIICh23FloorNormalizedA16DiscretePointSpectrumTarget_closed,
    g8LaneA_theoremBackedDomainReady,
    g8BookIIICh23FloorNormalizedA16SelectedDiscreteSpectrumNoStandardModeEqualityClaim_closed⟩

/-- Former temporary Lane-A axiom gate A1.

The legacy `_axiom` name is retained for downstream audit stability, but this
is now a definition, not an axiom. -/
noncomputable def g8LaneA_operatorReadyGate_axiom :
    G8LaneAOperatorReadyGate where
  operatorCtx :=
    g8BookIIICh23FloorNormalizedA2LaneAOperatorNativeSelfAdjointSource_closed
      |>.operatorCtx
  operatorReady :=
    g8BookIIICh23FloorNormalizedA2LaneAOperatorNativeSelfAdjointSource_closed
      |>.operatorReady

/-- Former temporary Lane-A axiom gate A2.

The legacy `_axiom` name is retained for downstream audit stability, but this
is now a definition, not an axiom.  It is backed by the selected certified
eigenpair point-spectrum source and its self-adjoint scalar-pairing reality
calculus. -/
noncomputable def g8LaneA_operatorNativeSelfAdjointGate_axiom :
    G8LaneAOperatorNativeSelfAdjointGate
      g8LaneA_operatorReadyGate_axiom where
  legitimacy :=
    g8BookIIICh23FloorNormalizedA2LaneAOperatorNativeSelfAdjointSource_closed
      |>.legitimacy

/-- Temporary Lane-A axiom gate A3.  Replace with the canonical actual-`xi`
    spectral-membership theorem when available. -/
axiom g8LaneA_canonicalActualXiMembershipGate_axiom :
    G8LaneACanonicalActualXiMembershipGate
      g8LaneA_operatorReadyGate_axiom
      g8LaneA_operatorNativeSelfAdjointGate_axiom

-- ============================================================
-- AXIOM-BACKED LANE-A CONSEQUENCES
-- ============================================================

/-- The axiom-backed operator context selected by gate A1. -/
def g8LaneA_axiomLedgerOperatorCtx : LemniscateOperatorContext :=
  g8LaneA_operatorReadyGate_axiom.operatorCtx

/-- The axiom-backed operator readiness selected by gate A1. -/
def g8LaneA_axiomLedgerOperatorReady :
    LemniscateOperatorReady g8LaneA_axiomLedgerOperatorCtx :=
  g8LaneA_operatorReadyGate_axiom.operatorReady

/-- The axiom-backed operator-native self-adjoint spectral legitimacy source. -/
def g8LaneA_axiomLedgerSpectralLegitimacy :
    G8LemniscateSpectralMembershipLegitimacy
      g8LaneA_axiomLedgerOperatorCtx
      g8LaneA_axiomLedgerOperatorReady :=
  g8LaneA_operatorNativeSelfAdjointGate_axiom.legitimacy

/-- The axiom-backed canonical actual-`xi` spectral-membership source. -/
def g8LaneA_axiomLedgerCanonicalMembershipSource :
    G8ActualXiCanonicalAbstractSpectralMembershipSource
      g8LaneA_axiomLedgerSpectralLegitimacy :=
  g8LaneA_canonicalActualXiMembershipGate_axiom.membershipSource

/-- The compact axiom-backed weak Lane-A route source. -/
def g8LaneA_axiomLedgerAbstractSelfAdjointRoute :
    G8ActualXiCanonicalAbstractSelfAdjointRouteSource
      g8LaneA_axiomLedgerOperatorCtx
      g8LaneA_axiomLedgerOperatorReady where
  legitimacy := g8LaneA_axiomLedgerSpectralLegitimacy
  membershipSource := g8LaneA_axiomLedgerCanonicalMembershipSource

/-- The axiom-backed weak route supplies the remaining nonzero-height Lane-A
    spectral-parameter reality payload. -/
theorem g8LaneA_axiomLedgerNonzeroHeightSpectralParameterReal :
    G8ActualXiNonzeroHeightSpectralParameterReal :=
  g8LaneA_axiomLedgerAbstractSelfAdjointRoute.toSpectralParameterReal

/-- Combining the axiom-backed nonzero-height payload with the theorem-backed
    paired-eta zero-height branch supplies the sharpened Lane-A inputs. -/
def g8LaneA_axiomLedgerNonzeroHeightInputs :
    G8ActualXiNonzeroHeightSpectralRealityInputs :=
  G8ActualXiNonzeroHeightSpectralRealityInputs.ofPairedEtaClosure
    g8LaneA_axiomLedgerNonzeroHeightSpectralParameterReal

/-- The axiom-backed Lane-A ledger closes actual sigma-fixedness, modulo the
    single remaining explicit axiom gate above. -/
theorem g8LaneA_axiomLedgerActualSigmaFixed :
    G8ActualXiBoundaryCharacterSigmaFixed :=
  g8LaneA_axiomLedgerNonzeroHeightInputs.actualSigmaFixed

/-- The axiom-backed Lane-A ledger supplies crossing-mediated evidence, modulo
    the single remaining explicit axiom gate above. -/
theorem g8LaneA_axiomLedgerCrossingMediatedAll :
    G8ActualXiBoundaryReadoutCrossingMediatedAll :=
  g8LaneA_axiomLedgerNonzeroHeightInputs.toCrossingMediatedAll

end Tau.BookIII.Bridge
