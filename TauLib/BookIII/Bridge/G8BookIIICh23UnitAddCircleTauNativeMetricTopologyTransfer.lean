import TauLib.BookIII.Bridge.G8BookIIICh23UnitAddCircleTauNativeA11Closure
import TauLib.BookIII.Bridge.G8BookIIICh23UnitAddCircleGlueQuotientMap

/-!
# TauLib.BookIII.Bridge.G8BookIIICh23UnitAddCircleTauNativeMetricTopologyTransfer

Conditional tau-native A1.1 transfer from the closed concrete Ch.23 graph.

The concrete `UnitAddCircle` wedge compact metric graph is now theorem-backed.
This module proves the next two transfer stones:

```text
basepoint-preserving UnitAddCircle/TauCirclePoint lobe equivalence
  -> transported topology/metric/compactness on LemniscateCarrier
  -> G8BookIIICh23UnitAddCircleTauNativeA11ClosureSource
  -> G8BookIIILemniscateCompactMetricGraphPackageTarget.
```

It deliberately does not manufacture the lobe equivalence.  The remaining
load-bearing theorem is still the tau-circle parametrization completeness
target.
-/

set_option autoImplicit false

namespace Tau.BookIII.Bridge

-- ============================================================
-- CLOSED CONCRETE GRAPH SOURCE
-- ============================================================

/-- Select the theorem-backed concrete Ch.23 compact metric graph source. -/
noncomputable def g8BookIIICh23ConcreteUnitAddCircleCompactMetricGraphSource_closed :
    G8BookIIICh23ConcreteUnitAddCircleCompactMetricGraphSource :=
  Classical.choice
    g8BookIIICh23ConcreteCompactMetricGraphTarget_from_glueQuotientMetricTransfer

-- ============================================================
-- TRANSPORTED TAU-NATIVE TOPOLOGY, METRIC, AND COMPACTNESS
-- ============================================================

/-- The tau-native topology transported from the closed concrete wedge along a
    basepoint-preserving lobe equivalence. -/
noncomputable def g8BookIIICh23TauNativeTopologyFromLobeEquivalence
    (concrete : G8BookIIICh23ConcreteUnitAddCircleCompactMetricGraphSource)
    (lobe : G8BookIIICh23UnitAddCircleTauCircleLobeEquivalence) :
    TopologicalSpace LemniscateCarrier :=
  TopologicalSpace.induced lobe.toCarrierEquiv.symm concrete.topology

/-- The induced map from tau-native carrier back to the concrete wedge is an
    embedding for the transported topology. -/
noncomputable def g8BookIIICh23TauNativeTopologyEmbeddingFromLobeEquivalence
    (concrete : G8BookIIICh23ConcreteUnitAddCircleCompactMetricGraphSource)
    (lobe : G8BookIIICh23UnitAddCircleTauCircleLobeEquivalence) :
    @Topology.IsEmbedding LemniscateCarrier G8Ch23UnitAddCircleWedgeCarrier
      (g8BookIIICh23TauNativeTopologyFromLobeEquivalence concrete lobe)
      concrete.topology
      lobe.toCarrierEquiv.symm := by
  letI : TopologicalSpace LemniscateCarrier :=
    g8BookIIICh23TauNativeTopologyFromLobeEquivalence concrete lobe
  letI : TopologicalSpace G8Ch23UnitAddCircleWedgeCarrier :=
    concrete.topology
  exact Function.Injective.isEmbedding_induced lobe.toCarrierEquiv.symm.injective

/-- The transported topology is homeomorphic to the concrete quotient topology. -/
noncomputable def g8BookIIICh23TauNativeHomeomorphToConcreteFromLobeEquivalence
    (concrete : G8BookIIICh23ConcreteUnitAddCircleCompactMetricGraphSource)
    (lobe : G8BookIIICh23UnitAddCircleTauCircleLobeEquivalence) :
    @Homeomorph LemniscateCarrier G8Ch23UnitAddCircleWedgeCarrier
      (g8BookIIICh23TauNativeTopologyFromLobeEquivalence concrete lobe)
      concrete.topology := by
  letI : TopologicalSpace LemniscateCarrier :=
    g8BookIIICh23TauNativeTopologyFromLobeEquivalence concrete lobe
  letI : TopologicalSpace G8Ch23UnitAddCircleWedgeCarrier :=
    concrete.topology
  exact
    (g8BookIIICh23TauNativeTopologyEmbeddingFromLobeEquivalence
      concrete lobe).toHomeomorphOfSurjective
        lobe.toCarrierEquiv.symm.surjective

/-- Compactness transfers from the closed concrete wedge to the tau-native
    carrier. -/
noncomputable def g8BookIIICh23TauNativeCompactSpaceFromLobeEquivalence
    (concrete : G8BookIIICh23ConcreteUnitAddCircleCompactMetricGraphSource)
    (lobe : G8BookIIICh23UnitAddCircleTauCircleLobeEquivalence) :
    @CompactSpace LemniscateCarrier
      (g8BookIIICh23TauNativeTopologyFromLobeEquivalence concrete lobe) := by
  letI : TopologicalSpace LemniscateCarrier :=
    g8BookIIICh23TauNativeTopologyFromLobeEquivalence concrete lobe
  letI : TopologicalSpace G8Ch23UnitAddCircleWedgeCarrier :=
    concrete.topology
  exact
    @Homeomorph.compactSpace
      G8Ch23UnitAddCircleWedgeCarrier
      LemniscateCarrier
      concrete.topology
      (g8BookIIICh23TauNativeTopologyFromLobeEquivalence concrete lobe)
      concrete.compact
      (g8BookIIICh23TauNativeHomeomorphToConcreteFromLobeEquivalence
        concrete lobe).symm

/-- The tau-native metric transported from the closed concrete wedge. -/
noncomputable def g8BookIIICh23TauNativeMetricFromLobeEquivalence
    (concrete : G8BookIIICh23ConcreteUnitAddCircleCompactMetricGraphSource)
    (lobe : G8BookIIICh23UnitAddCircleTauCircleLobeEquivalence) :
    MetricSpace LemniscateCarrier :=
  MetricSpace.induced lobe.toCarrierEquiv.symm
    lobe.toCarrierEquiv.symm.injective concrete.metric

/-- The transported metric is exactly the pullback of the concrete graph
    metric along the lobe-induced carrier equivalence. -/
theorem g8BookIIICh23TauNativeMetricFromLobeEquivalence_dist
    (concrete : G8BookIIICh23ConcreteUnitAddCircleCompactMetricGraphSource)
    (lobe : G8BookIIICh23UnitAddCircleTauCircleLobeEquivalence)
    (x y : LemniscateCarrier) :
    let _ : MetricSpace LemniscateCarrier :=
      g8BookIIICh23TauNativeMetricFromLobeEquivalence concrete lobe
    let _ : MetricSpace G8Ch23UnitAddCircleWedgeCarrier :=
      concrete.metric
    dist x y = dist (lobe.toCarrierEquiv.symm x)
      (lobe.toCarrierEquiv.symm y) :=
  rfl

-- ============================================================
-- TRANSFER PROPOSITIONS FOR THE LEMNISCATE CARRIER CONTEXT
-- ============================================================

/-- The tau-native topology is the transported concrete wedge quotient
    topology. -/
def G8BookIIICh23TauNativeTopologyTransferred
    (concrete : G8BookIIICh23ConcreteUnitAddCircleCompactMetricGraphSource)
    (lobe : G8BookIIICh23UnitAddCircleTauCircleLobeEquivalence) : Prop :=
  @Topology.IsEmbedding LemniscateCarrier G8Ch23UnitAddCircleWedgeCarrier
    (g8BookIIICh23TauNativeTopologyFromLobeEquivalence concrete lobe)
    concrete.topology
    lobe.toCarrierEquiv.symm

/-- The tau-native metric is the transported concrete graph metric. -/
def G8BookIIICh23TauNativeMetricTransferred
    (concrete : G8BookIIICh23ConcreteUnitAddCircleCompactMetricGraphSource)
    (lobe : G8BookIIICh23UnitAddCircleTauCircleLobeEquivalence) : Prop :=
  ∀ x y : LemniscateCarrier,
    let _ : MetricSpace LemniscateCarrier :=
      g8BookIIICh23TauNativeMetricFromLobeEquivalence concrete lobe
    let _ : MetricSpace G8Ch23UnitAddCircleWedgeCarrier :=
      concrete.metric
    dist x y = dist (lobe.toCarrierEquiv.symm x)
      (lobe.toCarrierEquiv.symm y)

/-- Compactness is transported from the concrete two-circle wedge. -/
def G8BookIIICh23TauNativeCompactnessTransferred
    (concrete : G8BookIIICh23ConcreteUnitAddCircleCompactMetricGraphSource)
    (lobe : G8BookIIICh23UnitAddCircleTauCircleLobeEquivalence) : Prop :=
  @CompactSpace LemniscateCarrier
    (g8BookIIICh23TauNativeTopologyFromLobeEquivalence concrete lobe)

/-- The transported topology and metric agree by construction. -/
def G8BookIIICh23TauNativeTopologyMetricAgreement
    (concrete : G8BookIIICh23ConcreteUnitAddCircleCompactMetricGraphSource)
    (lobe : G8BookIIICh23UnitAddCircleTauCircleLobeEquivalence) : Prop :=
  G8BookIIICh23TauNativeTopologyTransferred concrete lobe

/-- The tau-native graph-distance field is realized by pullback from the
    concrete graph metric.  This deliberately does not use the old
    zero-distance scaffold. -/
def G8BookIIICh23TauNativeGraphDistanceRealizesMetric
    (concrete : G8BookIIICh23ConcreteUnitAddCircleCompactMetricGraphSource)
    (lobe : G8BookIIICh23UnitAddCircleTauCircleLobeEquivalence) : Prop :=
  concrete.graphDistanceRealizesMetric ∧
    G8BookIIICh23TauNativeMetricTransferred concrete lobe

/-- The concrete quotient carrier matches `LemniscateCarrier` through the
    lobe-induced quotient equivalence. -/
def G8BookIIICh23TauNativeQuotientMatchesLemniscateCarrier
    (lobe : G8BookIIICh23UnitAddCircleTauCircleLobeEquivalence) : Prop :=
  Nonempty (G8Ch23UnitAddCircleWedgeCarrier ≃ LemniscateCarrier) ∧
    lobe.toCarrierEquiv G8Ch23UnitAddCircleWedgeCarrier.crossing =
      LemniscateCarrier.crossing ∧
    ∀ (s : LemniscateSector) (p : UnitAddCircle),
      lobe.toCarrierEquiv (G8Ch23UnitAddCircleWedgeCarrier.lobe s p) =
        LemniscateCarrier.lobe s (lobe.lobeEquiv p)

/-- The metric transfer from the concrete wedge is exactly the transported
    metric plus the already-closed concrete graph-distance evidence. -/
def G8BookIIICh23TauNativeMetricTransferFromConcreteWedge
    (concrete : G8BookIIICh23ConcreteUnitAddCircleCompactMetricGraphSource)
    (lobe : G8BookIIICh23UnitAddCircleTauCircleLobeEquivalence) : Prop :=
  G8BookIIICh23TauNativeMetricTransferred concrete lobe ∧
    concrete.shortestPathGraphMetric ∧
    concrete.topologyMetricAgreement ∧
    concrete.graphDistanceRealizesMetric

theorem g8BookIIICh23TauNativeTopologyTransferred_from_lobeEquivalence
    (concrete : G8BookIIICh23ConcreteUnitAddCircleCompactMetricGraphSource)
    (lobe : G8BookIIICh23UnitAddCircleTauCircleLobeEquivalence) :
    G8BookIIICh23TauNativeTopologyTransferred concrete lobe :=
  g8BookIIICh23TauNativeTopologyEmbeddingFromLobeEquivalence concrete lobe

theorem g8BookIIICh23TauNativeMetricTransferred_from_lobeEquivalence
    (concrete : G8BookIIICh23ConcreteUnitAddCircleCompactMetricGraphSource)
    (lobe : G8BookIIICh23UnitAddCircleTauCircleLobeEquivalence) :
    G8BookIIICh23TauNativeMetricTransferred concrete lobe := by
  intro x y
  exact
    g8BookIIICh23TauNativeMetricFromLobeEquivalence_dist concrete lobe x y

theorem g8BookIIICh23TauNativeCompactnessTransferred_from_lobeEquivalence
    (concrete : G8BookIIICh23ConcreteUnitAddCircleCompactMetricGraphSource)
    (lobe : G8BookIIICh23UnitAddCircleTauCircleLobeEquivalence) :
    G8BookIIICh23TauNativeCompactnessTransferred concrete lobe :=
  g8BookIIICh23TauNativeCompactSpaceFromLobeEquivalence concrete lobe

theorem g8BookIIICh23TauNativeTopologyMetricAgreement_from_lobeEquivalence
    (concrete : G8BookIIICh23ConcreteUnitAddCircleCompactMetricGraphSource)
    (lobe : G8BookIIICh23UnitAddCircleTauCircleLobeEquivalence) :
    G8BookIIICh23TauNativeTopologyMetricAgreement concrete lobe :=
  g8BookIIICh23TauNativeTopologyTransferred_from_lobeEquivalence
    concrete lobe

theorem g8BookIIICh23TauNativeGraphDistanceRealizesMetric_from_lobeEquivalence
    (concrete : G8BookIIICh23ConcreteUnitAddCircleCompactMetricGraphSource)
    (lobe : G8BookIIICh23UnitAddCircleTauCircleLobeEquivalence) :
    G8BookIIICh23TauNativeGraphDistanceRealizesMetric concrete lobe :=
  ⟨concrete.graphDistanceRealizesMetricEvidence,
    g8BookIIICh23TauNativeMetricTransferred_from_lobeEquivalence
      concrete lobe⟩

theorem g8BookIIICh23TauNativeQuotientMatchesLemniscateCarrier_from_lobeEquivalence
    (lobe : G8BookIIICh23UnitAddCircleTauCircleLobeEquivalence) :
    G8BookIIICh23TauNativeQuotientMatchesLemniscateCarrier lobe :=
  ⟨⟨lobe.toCarrierEquiv⟩,
    lobe.toCarrierEquiv_crossing,
    lobe.toCarrierEquiv_lobe⟩

theorem g8BookIIICh23TauNativeMetricTransferFromConcreteWedge_from_lobeEquivalence
    (concrete : G8BookIIICh23ConcreteUnitAddCircleCompactMetricGraphSource)
    (lobe : G8BookIIICh23UnitAddCircleTauCircleLobeEquivalence) :
    G8BookIIICh23TauNativeMetricTransferFromConcreteWedge concrete lobe :=
  ⟨g8BookIIICh23TauNativeMetricTransferred_from_lobeEquivalence
      concrete lobe,
    concrete.shortestPathGraphMetricEvidence,
    concrete.topologyMetricAgreementEvidence,
    concrete.graphDistanceRealizesMetricEvidence⟩

-- ============================================================
-- TAU-NATIVE CARRIER CONTEXT AND A1.1 CLOSURE
-- ============================================================

/-- The theorem-backed `LemniscateCarrierContext` transported from the concrete
    Ch.23 graph along a lobe equivalence. -/
noncomputable def g8BookIIICh23TauNativeCarrierContextFromLobeEquivalence
    (concrete : G8BookIIICh23ConcreteUnitAddCircleCompactMetricGraphSource)
    (lobe : G8BookIIICh23UnitAddCircleTauCircleLobeEquivalence) :
    LemniscateCarrierContext where
  topology :=
    g8BookIIICh23TauNativeTopologyFromLobeEquivalence concrete lobe
  metric :=
    g8BookIIICh23TauNativeMetricFromLobeEquivalence concrete lobe
  compact :=
    g8BookIIICh23TauNativeCompactSpaceFromLobeEquivalence concrete lobe
  topologyIsWedgeQuotient :=
    G8BookIIICh23TauNativeTopologyTransferred concrete lobe
  metricIsGraphMetric :=
    G8BookIIICh23TauNativeMetricTransferred concrete lobe
  compactnessFromWedge :=
    G8BookIIICh23TauNativeCompactnessTransferred concrete lobe
  topologyMetricAgreement :=
    G8BookIIICh23TauNativeTopologyMetricAgreement concrete lobe
  graphDistanceRealizesMetric :=
    G8BookIIICh23TauNativeGraphDistanceRealizesMetric concrete lobe
  status := .theoremBacked

/-- A basepoint-preserving lobe equivalence closes the tau-native A1.1 source
    because the concrete Ch.23 compact graph is already theorem-backed. -/
noncomputable def
    g8BookIIICh23UnitAddCircleTauNativeA11ClosureSource_of_lobeEquivalence
    (lobe : G8BookIIICh23UnitAddCircleTauCircleLobeEquivalence) :
    G8BookIIICh23UnitAddCircleTauNativeA11ClosureSource :=
  let concrete :=
    g8BookIIICh23ConcreteUnitAddCircleCompactMetricGraphSource_closed
  let carrierCtx :=
    g8BookIIICh23TauNativeCarrierContextFromLobeEquivalence concrete lobe
  { concrete := concrete
    lobeEquivalence := lobe
    carrierCtx := carrierCtx
    topologyTransferred :=
      g8BookIIICh23TauNativeTopologyTransferred_from_lobeEquivalence
        concrete lobe
    metricTransferred :=
      g8BookIIICh23TauNativeMetricTransferred_from_lobeEquivalence
        concrete lobe
    compactnessTransferred :=
      g8BookIIICh23TauNativeCompactnessTransferred_from_lobeEquivalence
        concrete lobe
    topologyMetricAgreement :=
      g8BookIIICh23TauNativeTopologyMetricAgreement_from_lobeEquivalence
        concrete lobe
    graphDistanceRealizesMetric :=
      g8BookIIICh23TauNativeGraphDistanceRealizesMetric_from_lobeEquivalence
        concrete lobe
    theoremBackedStatus := rfl
    quotientMatchesLemniscateCarrier :=
      G8BookIIICh23TauNativeQuotientMatchesLemniscateCarrier lobe
    quotientMatchesLemniscateCarrierEvidence :=
      g8BookIIICh23TauNativeQuotientMatchesLemniscateCarrier_from_lobeEquivalence
        lobe
    metricTransferFromConcreteWedge :=
      G8BookIIICh23TauNativeMetricTransferFromConcreteWedge concrete lobe
    metricTransferFromConcreteWedgeEvidence :=
      g8BookIIICh23TauNativeMetricTransferFromConcreteWedge_from_lobeEquivalence
        concrete lobe
    status := lobe.status }

/-- Lobe equivalence is sufficient for the full tau-native A1.1 closure target. -/
theorem
    g8BookIIICh23UnitAddCircleTauNativeA11ClosureTarget_of_lobeEquivalence
    (target :
      Nonempty G8BookIIICh23UnitAddCircleTauCircleLobeEquivalence) :
    G8BookIIICh23UnitAddCircleTauNativeA11ClosureTarget := by
  rcases target with ⟨lobe⟩
  exact
    ⟨g8BookIIICh23UnitAddCircleTauNativeA11ClosureSource_of_lobeEquivalence
      lobe⟩

/-- Tau-circle parametrization completeness is sufficient for the full
    tau-native A1.1 closure target. -/
theorem
    g8BookIIICh23TauCircleParametrizationCompletenessTarget_toA11ClosureTarget
    (target : G8BookIIICh23TauCircleParametrizationCompletenessTarget) :
    G8BookIIICh23UnitAddCircleTauNativeA11ClosureTarget := by
  rcases target with ⟨param⟩
  exact
    g8BookIIICh23UnitAddCircleTauNativeA11ClosureTarget_of_lobeEquivalence
      ⟨param.toLobeEquivalence⟩

/-- Parametrization completeness is also sufficient for the stricter
    parametrized A1.1 closure target. -/
noncomputable def
    g8BookIIICh23TauCircleParametrizedA11ClosureSource_of_parametrization
    (param : G8BookIIICh23TauCircleParametrizationCompletenessSource) :
    G8BookIIICh23TauCircleParametrizedA11ClosureSource :=
  let concrete :=
    g8BookIIICh23ConcreteUnitAddCircleCompactMetricGraphSource_closed
  let lobe := param.toLobeEquivalence
  let carrierCtx :=
    g8BookIIICh23TauNativeCarrierContextFromLobeEquivalence concrete lobe
  { concrete := concrete
    tauCircleParam := param
    carrierCtx := carrierCtx
    topologyTransferred :=
      g8BookIIICh23TauNativeTopologyTransferred_from_lobeEquivalence
        concrete lobe
    metricTransferred :=
      g8BookIIICh23TauNativeMetricTransferred_from_lobeEquivalence
        concrete lobe
    compactnessTransferred :=
      g8BookIIICh23TauNativeCompactnessTransferred_from_lobeEquivalence
        concrete lobe
    topologyMetricAgreement :=
      g8BookIIICh23TauNativeTopologyMetricAgreement_from_lobeEquivalence
        concrete lobe
    graphDistanceRealizesMetric :=
      g8BookIIICh23TauNativeGraphDistanceRealizesMetric_from_lobeEquivalence
        concrete lobe
    theoremBackedStatus := rfl
    quotientMatchesLemniscateCarrier :=
      G8BookIIICh23TauNativeQuotientMatchesLemniscateCarrier lobe
    quotientMatchesLemniscateCarrierEvidence :=
      g8BookIIICh23TauNativeQuotientMatchesLemniscateCarrier_from_lobeEquivalence
        lobe
    metricTransferFromConcreteWedge :=
      G8BookIIICh23TauNativeMetricTransferFromConcreteWedge concrete lobe
    metricTransferFromConcreteWedgeEvidence :=
      g8BookIIICh23TauNativeMetricTransferFromConcreteWedge_from_lobeEquivalence
        concrete lobe
    status := param.status }

theorem
    g8BookIIICh23TauCircleParametrizationCompletenessTarget_toParametrizedA11ClosureTarget
    (target : G8BookIIICh23TauCircleParametrizationCompletenessTarget) :
    G8BookIIICh23TauCircleParametrizedA11ClosureTarget := by
  rcases target with ⟨param⟩
  exact
    ⟨g8BookIIICh23TauCircleParametrizedA11ClosureSource_of_parametrization
      param⟩

-- ============================================================
-- GUARDRAILS
-- ============================================================

/-- The transfer module still does not construct the tau-circle
    parametrization theorem. -/
structure G8BookIIICh23TauNativeMetricTransferWithoutLobeEquivalence where
  noLobeEquivalence :
    ¬ Nonempty G8BookIIICh23UnitAddCircleTauCircleLobeEquivalence

/-- The A1.1 target produced here still requires a lobe equivalence source. -/
theorem
    G8BookIIICh23TauNativeMetricTransferWithoutLobeEquivalence.refutesParametrizationRoute
    (gap :
      G8BookIIICh23TauNativeMetricTransferWithoutLobeEquivalence) :
    ¬ G8BookIIICh23TauCircleParametrizationCompletenessTarget := by
  intro target
  rcases target with ⟨param⟩
  exact gap.noLobeEquivalence ⟨param.toLobeEquivalence⟩

/-- If the transported metric is replaced by a non-pullback metric, the
    transfer source is not the one constructed in this module. -/
structure G8BookIIICh23TauNativeMetricPullbackMismatch
    (concrete : G8BookIIICh23ConcreteUnitAddCircleCompactMetricGraphSource)
    (lobe : G8BookIIICh23UnitAddCircleTauCircleLobeEquivalence) where
  mismatch :
    ¬ G8BookIIICh23TauNativeMetricTransferred concrete lobe

/-- The transported metric construction carries exact pullback equality. -/
theorem G8BookIIICh23TauNativeMetricPullbackMismatch.refutesTransferredMetric
    {concrete : G8BookIIICh23ConcreteUnitAddCircleCompactMetricGraphSource}
    {lobe : G8BookIIICh23UnitAddCircleTauCircleLobeEquivalence}
    (gap :
      G8BookIIICh23TauNativeMetricPullbackMismatch concrete lobe) :
    False :=
  gap.mismatch
    (g8BookIIICh23TauNativeMetricTransferred_from_lobeEquivalence
      concrete lobe)

end Tau.BookIII.Bridge
