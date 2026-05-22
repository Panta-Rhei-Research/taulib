import TauLib.BookIII.Bridge.G8BookIIICh23PeriodCanonicalCompatibilitySplit
import TauLib.BookIII.Bridge.G8BookIIICh23UnitAddCircleTauNativeMetricTopologyTransfer

/-!
# G8 Book III Ch.23 Floor-Normalized A1.1 Compact Graph Route

This module makes the floor-normalized lobe the selected A1.1 carrier.  The
unrestricted `TauCirclePoint`/Cauchy-parametrized carrier remains available as
an optional strengthening, but the load-bearing Ch.23 compact graph route now
has a theorem-backed target:

```text
UnitAddCircle concrete wedge
  ≃ floor-normalized Cauchy lobe wedge
  -> transported compact topology, graph metric, and compactness.
```

No full-lobe coverage theorem is used here.
-/

set_option autoImplicit false

namespace Tau.BookIII.Bridge

-- ============================================================
-- FLOOR-NORMALIZED TWO-LOBE WEDGE CARRIER
-- ============================================================

/-- Raw points for the floor-normalized Ch.23 lemniscate: one crossing point
    plus a floor-normalized Cauchy lobe point on each sector. -/
inductive G8BookIIICh23FloorNormalizedLemniscatePoint where
  | crossing : G8BookIIICh23FloorNormalizedLemniscatePoint
  | lobe :
      LemniscateSector →
        G8BookIIICh23FloorNormalizedCauchyLobePoint →
          G8BookIIICh23FloorNormalizedLemniscatePoint

namespace G8BookIIICh23FloorNormalizedLemniscatePoint

/-- The raw crossing point. -/
def omega : G8BookIIICh23FloorNormalizedLemniscatePoint :=
  .crossing

/-- The floor-normalized basepoint on a selected lobe. -/
noncomputable def basepoint :
    G8BookIIICh23FloorNormalizedCauchyLobePoint :=
  G8BookIIICh23FloorNormalizedCauchyLobePoint.ofUnitAddCircle
    G8Ch23UnitAddCircleWedgePoint.basepoint

/-- The raw basepoint on a selected sector. -/
noncomputable def lobeBase (s : LemniscateSector) :
    G8BookIIICh23FloorNormalizedLemniscatePoint :=
  .lobe s basepoint

/-- Crossing-class predicate for the floor-normalized wedge. -/
def InCrossingClass :
    G8BookIIICh23FloorNormalizedLemniscatePoint → Prop
  | .crossing => True
  | .lobe _ p => p = basepoint

/-- Wedge equivalence for the floor-normalized two-lobe carrier. -/
def WedgeEquivalent
    (x y : G8BookIIICh23FloorNormalizedLemniscatePoint) : Prop :=
  x = y ∨ (InCrossingClass x ∧ InCrossingClass y)

/-- Wedge equivalence is reflexive. -/
theorem WedgeEquivalent.refl
    (x : G8BookIIICh23FloorNormalizedLemniscatePoint) :
    WedgeEquivalent x x :=
  Or.inl rfl

/-- Wedge equivalence is symmetric. -/
theorem WedgeEquivalent.symm
    {x y : G8BookIIICh23FloorNormalizedLemniscatePoint}
    (h : WedgeEquivalent x y) :
    WedgeEquivalent y x := by
  cases h with
  | inl hxy =>
      exact Or.inl hxy.symm
  | inr hxy =>
      exact Or.inr ⟨hxy.right, hxy.left⟩

/-- Wedge equivalence is transitive. -/
theorem WedgeEquivalent.trans
    {x y z : G8BookIIICh23FloorNormalizedLemniscatePoint}
    (hxy : WedgeEquivalent x y)
    (hyz : WedgeEquivalent y z) :
    WedgeEquivalent x z := by
  cases hxy with
  | inl hxy =>
      subst y
      exact hyz
  | inr hxyc =>
      cases hyz with
      | inl hyz =>
          subst z
          exact Or.inr hxyc
      | inr hyzc =>
          exact Or.inr ⟨hxyc.left, hyzc.right⟩

/-- Setoid implementing the floor-normalized two-lobe wedge quotient. -/
def wedgeSetoid :
    Setoid G8BookIIICh23FloorNormalizedLemniscatePoint where
  r := WedgeEquivalent
  iseqv :=
    ⟨WedgeEquivalent.refl,
      WedgeEquivalent.symm,
      WedgeEquivalent.trans⟩

end G8BookIIICh23FloorNormalizedLemniscatePoint

/-- Quotient carrier for the floor-normalized Ch.23 lemniscate. -/
abbrev G8BookIIICh23FloorNormalizedLemniscateCarrier : Type :=
  Quotient G8BookIIICh23FloorNormalizedLemniscatePoint.wedgeSetoid

namespace G8BookIIICh23FloorNormalizedLemniscateCarrier

/-- Carrier crossing class. -/
def crossing : G8BookIIICh23FloorNormalizedLemniscateCarrier :=
  Quotient.mk G8BookIIICh23FloorNormalizedLemniscatePoint.wedgeSetoid
    G8BookIIICh23FloorNormalizedLemniscatePoint.omega

/-- Carrier lobe point. -/
def lobe
    (s : LemniscateSector)
    (p : G8BookIIICh23FloorNormalizedCauchyLobePoint) :
    G8BookIIICh23FloorNormalizedLemniscateCarrier :=
  Quotient.mk G8BookIIICh23FloorNormalizedLemniscatePoint.wedgeSetoid
    (G8BookIIICh23FloorNormalizedLemniscatePoint.lobe s p)

/-- The floor-normalized lobe basepoint is glued to the crossing. -/
theorem lobe_base_eq_crossing (s : LemniscateSector) :
    lobe s G8BookIIICh23FloorNormalizedLemniscatePoint.basepoint =
      crossing := by
  apply Quotient.sound
  exact Or.inr ⟨rfl, trivial⟩

/-- The two floor-normalized lobe basepoints are glued together. -/
theorem plus_base_eq_minus_base :
    lobe .plus G8BookIIICh23FloorNormalizedLemniscatePoint.basepoint =
      lobe .minus
        G8BookIIICh23FloorNormalizedLemniscatePoint.basepoint := by
  apply Quotient.sound
  exact Or.inr ⟨rfl, rfl⟩

end G8BookIIICh23FloorNormalizedLemniscateCarrier

-- ============================================================
-- EQUIVALENCE WITH THE CONCRETE UNITADDCIRCLE WEDGE
-- ============================================================

private noncomputable abbrev g8FloorNormalizedLobeEquiv :
    UnitAddCircle ≃ G8BookIIICh23FloorNormalizedCauchyLobePoint :=
  g8BookIIICh23UnitAddCircleEquivFloorNormalizedCauchyLobe

/-- Raw map from the concrete `UnitAddCircle` wedge to the floor-normalized
    wedge. -/
noncomputable def g8BookIIICh23UnitAddCircleToFloorNormalizedRaw :
    G8Ch23UnitAddCircleWedgePoint →
      G8BookIIICh23FloorNormalizedLemniscatePoint
  | .crossing => .crossing
  | .lobe s p => .lobe s (g8FloorNormalizedLobeEquiv p)

/-- Raw inverse map from the floor-normalized wedge to the concrete
    `UnitAddCircle` wedge. -/
noncomputable def g8BookIIICh23FloorNormalizedToUnitAddCircleRaw :
    G8BookIIICh23FloorNormalizedLemniscatePoint →
      G8Ch23UnitAddCircleWedgePoint
  | .crossing => .crossing
  | .lobe s p => .lobe s (g8FloorNormalizedLobeEquiv.symm p)

/-- Concrete crossing-class membership maps into floor-normalized
    crossing-class membership. -/
theorem g8BookIIICh23UnitAddCircleToFloorNormalizedRaw_inCrossingClass
    {x : G8Ch23UnitAddCircleWedgePoint}
    (h : G8Ch23UnitAddCircleWedgePoint.InCrossingClass x) :
    G8BookIIICh23FloorNormalizedLemniscatePoint.InCrossingClass
      (g8BookIIICh23UnitAddCircleToFloorNormalizedRaw x) := by
  cases x with
  | crossing =>
      trivial
  | lobe s p =>
      dsimp [G8Ch23UnitAddCircleWedgePoint.InCrossingClass] at h
      dsimp [g8BookIIICh23UnitAddCircleToFloorNormalizedRaw,
        G8BookIIICh23FloorNormalizedLemniscatePoint.InCrossingClass,
        G8BookIIICh23FloorNormalizedLemniscatePoint.basepoint]
      rw [h]
      rfl

/-- Floor-normalized crossing-class membership maps back into concrete
    crossing-class membership. -/
theorem g8BookIIICh23FloorNormalizedToUnitAddCircleRaw_inCrossingClass
    {x : G8BookIIICh23FloorNormalizedLemniscatePoint}
    (h :
      G8BookIIICh23FloorNormalizedLemniscatePoint.InCrossingClass x) :
    G8Ch23UnitAddCircleWedgePoint.InCrossingClass
      (g8BookIIICh23FloorNormalizedToUnitAddCircleRaw x) := by
  cases x with
  | crossing =>
      trivial
  | lobe s p =>
      dsimp
        [G8BookIIICh23FloorNormalizedLemniscatePoint.InCrossingClass] at h
      dsimp [g8BookIIICh23FloorNormalizedToUnitAddCircleRaw,
        G8BookIIICh23FloorNormalizedLemniscatePoint.basepoint,
        G8Ch23UnitAddCircleWedgePoint.InCrossingClass]
      rw [h]
      rfl

/-- The raw forward map respects the concrete wedge equivalence. -/
theorem g8BookIIICh23UnitAddCircleToFloorNormalizedRaw_respects
    {x y : G8Ch23UnitAddCircleWedgePoint}
    (h : G8Ch23UnitAddCircleWedgePoint.WedgeEquivalent x y) :
    G8BookIIICh23FloorNormalizedLemniscatePoint.WedgeEquivalent
      (g8BookIIICh23UnitAddCircleToFloorNormalizedRaw x)
      (g8BookIIICh23UnitAddCircleToFloorNormalizedRaw y) := by
  cases h with
  | inl hxy =>
      exact Or.inl (by rw [hxy])
  | inr hxy =>
      exact Or.inr
        ⟨g8BookIIICh23UnitAddCircleToFloorNormalizedRaw_inCrossingClass
            hxy.left,
          g8BookIIICh23UnitAddCircleToFloorNormalizedRaw_inCrossingClass
            hxy.right⟩

/-- The raw inverse map respects the floor-normalized wedge equivalence. -/
theorem g8BookIIICh23FloorNormalizedToUnitAddCircleRaw_respects
    {x y : G8BookIIICh23FloorNormalizedLemniscatePoint}
    (h :
      G8BookIIICh23FloorNormalizedLemniscatePoint.WedgeEquivalent x y) :
    G8Ch23UnitAddCircleWedgePoint.WedgeEquivalent
      (g8BookIIICh23FloorNormalizedToUnitAddCircleRaw x)
      (g8BookIIICh23FloorNormalizedToUnitAddCircleRaw y) := by
  cases h with
  | inl hxy =>
      exact Or.inl (by rw [hxy])
  | inr hxy =>
      exact Or.inr
        ⟨g8BookIIICh23FloorNormalizedToUnitAddCircleRaw_inCrossingClass
            hxy.left,
          g8BookIIICh23FloorNormalizedToUnitAddCircleRaw_inCrossingClass
            hxy.right⟩

/-- Quotient map from the concrete wedge to the floor-normalized wedge. -/
noncomputable def g8BookIIICh23UnitAddCircleToFloorNormalizedCarrier :
    G8Ch23UnitAddCircleWedgeCarrier →
      G8BookIIICh23FloorNormalizedLemniscateCarrier :=
  Quotient.map g8BookIIICh23UnitAddCircleToFloorNormalizedRaw (by
    intro x y h
    exact g8BookIIICh23UnitAddCircleToFloorNormalizedRaw_respects h)

/-- Quotient inverse map from the floor-normalized wedge to the concrete
    wedge. -/
noncomputable def g8BookIIICh23FloorNormalizedToUnitAddCircleCarrier :
    G8BookIIICh23FloorNormalizedLemniscateCarrier →
      G8Ch23UnitAddCircleWedgeCarrier :=
  Quotient.map g8BookIIICh23FloorNormalizedToUnitAddCircleRaw (by
    intro x y h
    exact g8BookIIICh23FloorNormalizedToUnitAddCircleRaw_respects h)

/-- The concrete-to-floor map followed by its inverse is identity. -/
theorem g8BookIIICh23FloorNormalized_from_to_carrier
    (x : G8Ch23UnitAddCircleWedgeCarrier) :
    g8BookIIICh23FloorNormalizedToUnitAddCircleCarrier
        (g8BookIIICh23UnitAddCircleToFloorNormalizedCarrier x) =
      x := by
  refine Quotient.inductionOn x ?_
  intro raw
  apply Quotient.sound
  cases raw with
  | crossing =>
      exact Or.inl rfl
  | lobe s p =>
      exact Or.inl (by
        simp [g8BookIIICh23UnitAddCircleToFloorNormalizedRaw,
          g8BookIIICh23FloorNormalizedToUnitAddCircleRaw])

/-- The floor-to-concrete map followed by its inverse is identity. -/
theorem g8BookIIICh23FloorNormalized_to_from_carrier
    (x : G8BookIIICh23FloorNormalizedLemniscateCarrier) :
    g8BookIIICh23UnitAddCircleToFloorNormalizedCarrier
        (g8BookIIICh23FloorNormalizedToUnitAddCircleCarrier x) =
      x := by
  refine Quotient.inductionOn x ?_
  intro raw
  apply Quotient.sound
  cases raw with
  | crossing =>
      exact Or.inl rfl
  | lobe s p =>
      exact Or.inl (by
        simp [g8BookIIICh23UnitAddCircleToFloorNormalizedRaw,
          g8BookIIICh23FloorNormalizedToUnitAddCircleRaw])

/-- The concrete Ch.23 wedge is theorem-backed equivalent to the
    floor-normalized selected carrier. -/
noncomputable def g8BookIIICh23UnitAddCircleEquivFloorNormalizedCarrier :
    G8Ch23UnitAddCircleWedgeCarrier ≃
      G8BookIIICh23FloorNormalizedLemniscateCarrier where
  toFun := g8BookIIICh23UnitAddCircleToFloorNormalizedCarrier
  invFun := g8BookIIICh23FloorNormalizedToUnitAddCircleCarrier
  left_inv := g8BookIIICh23FloorNormalized_from_to_carrier
  right_inv := g8BookIIICh23FloorNormalized_to_from_carrier

@[simp] theorem g8BookIIICh23UnitAddCircleEquivFloorNormalizedCarrier_crossing :
    g8BookIIICh23UnitAddCircleEquivFloorNormalizedCarrier
        G8Ch23UnitAddCircleWedgeCarrier.crossing =
      G8BookIIICh23FloorNormalizedLemniscateCarrier.crossing :=
  rfl

@[simp] theorem g8BookIIICh23UnitAddCircleEquivFloorNormalizedCarrier_lobe
    (s : LemniscateSector) (p : UnitAddCircle) :
    g8BookIIICh23UnitAddCircleEquivFloorNormalizedCarrier
        (G8Ch23UnitAddCircleWedgeCarrier.lobe s p) =
      G8BookIIICh23FloorNormalizedLemniscateCarrier.lobe s
        (g8FloorNormalizedLobeEquiv p) :=
  rfl

-- ============================================================
-- TRANSPORTED COMPACT METRIC GRAPH PACKAGE
-- ============================================================

/-- The selected floor-normalized topology transported from the closed concrete
    Ch.23 wedge. -/
noncomputable def g8BookIIICh23FloorNormalizedTopology
    (concrete : G8BookIIICh23ConcreteUnitAddCircleCompactMetricGraphSource) :
    TopologicalSpace G8BookIIICh23FloorNormalizedLemniscateCarrier :=
  TopologicalSpace.induced
    g8BookIIICh23UnitAddCircleEquivFloorNormalizedCarrier.symm
    concrete.topology

/-- The transported topology embeds into the concrete quotient topology. -/
noncomputable def g8BookIIICh23FloorNormalizedTopologyEmbedding
    (concrete : G8BookIIICh23ConcreteUnitAddCircleCompactMetricGraphSource) :
    @Topology.IsEmbedding
      G8BookIIICh23FloorNormalizedLemniscateCarrier
      G8Ch23UnitAddCircleWedgeCarrier
      (g8BookIIICh23FloorNormalizedTopology concrete)
      concrete.topology
      g8BookIIICh23UnitAddCircleEquivFloorNormalizedCarrier.symm := by
  letI : TopologicalSpace G8BookIIICh23FloorNormalizedLemniscateCarrier :=
    g8BookIIICh23FloorNormalizedTopology concrete
  letI : TopologicalSpace G8Ch23UnitAddCircleWedgeCarrier :=
    concrete.topology
  exact
    Function.Injective.isEmbedding_induced
      g8BookIIICh23UnitAddCircleEquivFloorNormalizedCarrier.symm.injective

/-- The transported floor-normalized topology is homeomorphic to the concrete
    quotient topology. -/
noncomputable def g8BookIIICh23FloorNormalizedHomeomorphToConcrete
    (concrete : G8BookIIICh23ConcreteUnitAddCircleCompactMetricGraphSource) :
    @Homeomorph
      G8BookIIICh23FloorNormalizedLemniscateCarrier
      G8Ch23UnitAddCircleWedgeCarrier
      (g8BookIIICh23FloorNormalizedTopology concrete)
      concrete.topology := by
  letI : TopologicalSpace G8BookIIICh23FloorNormalizedLemniscateCarrier :=
    g8BookIIICh23FloorNormalizedTopology concrete
  letI : TopologicalSpace G8Ch23UnitAddCircleWedgeCarrier :=
    concrete.topology
  exact
    (g8BookIIICh23FloorNormalizedTopologyEmbedding concrete).toHomeomorphOfSurjective
      g8BookIIICh23UnitAddCircleEquivFloorNormalizedCarrier.symm.surjective

/-- Compactness transfers from the closed concrete wedge. -/
noncomputable def g8BookIIICh23FloorNormalizedCompactSpace
    (concrete : G8BookIIICh23ConcreteUnitAddCircleCompactMetricGraphSource) :
    @CompactSpace G8BookIIICh23FloorNormalizedLemniscateCarrier
      (g8BookIIICh23FloorNormalizedTopology concrete) := by
  letI : TopologicalSpace G8BookIIICh23FloorNormalizedLemniscateCarrier :=
    g8BookIIICh23FloorNormalizedTopology concrete
  letI : TopologicalSpace G8Ch23UnitAddCircleWedgeCarrier :=
    concrete.topology
  exact
    @Homeomorph.compactSpace
      G8Ch23UnitAddCircleWedgeCarrier
      G8BookIIICh23FloorNormalizedLemniscateCarrier
      concrete.topology
      (g8BookIIICh23FloorNormalizedTopology concrete)
      concrete.compact
      (g8BookIIICh23FloorNormalizedHomeomorphToConcrete concrete).symm

/-- The selected floor-normalized metric transported from the closed concrete
    graph metric. -/
noncomputable def g8BookIIICh23FloorNormalizedMetric
    (concrete : G8BookIIICh23ConcreteUnitAddCircleCompactMetricGraphSource) :
    MetricSpace G8BookIIICh23FloorNormalizedLemniscateCarrier :=
  MetricSpace.induced
    g8BookIIICh23UnitAddCircleEquivFloorNormalizedCarrier.symm
    g8BookIIICh23UnitAddCircleEquivFloorNormalizedCarrier.symm.injective
    concrete.metric

/-- The transported metric is exactly the pullback of the concrete graph
    metric. -/
theorem g8BookIIICh23FloorNormalizedMetric_dist
    (concrete : G8BookIIICh23ConcreteUnitAddCircleCompactMetricGraphSource)
    (x y : G8BookIIICh23FloorNormalizedLemniscateCarrier) :
    let _ : MetricSpace G8BookIIICh23FloorNormalizedLemniscateCarrier :=
      g8BookIIICh23FloorNormalizedMetric concrete
    let _ : MetricSpace G8Ch23UnitAddCircleWedgeCarrier :=
      concrete.metric
    dist x y =
      dist
        (g8BookIIICh23UnitAddCircleEquivFloorNormalizedCarrier.symm x)
        (g8BookIIICh23UnitAddCircleEquivFloorNormalizedCarrier.symm y) :=
  rfl

/-- Topology transfer for the floor-normalized selected carrier. -/
def G8BookIIICh23FloorNormalizedTopologyTransferred
    (concrete : G8BookIIICh23ConcreteUnitAddCircleCompactMetricGraphSource) :
    Prop :=
  @Topology.IsEmbedding
    G8BookIIICh23FloorNormalizedLemniscateCarrier
    G8Ch23UnitAddCircleWedgeCarrier
    (g8BookIIICh23FloorNormalizedTopology concrete)
    concrete.topology
    g8BookIIICh23UnitAddCircleEquivFloorNormalizedCarrier.symm

/-- Metric transfer for the floor-normalized selected carrier. -/
def G8BookIIICh23FloorNormalizedMetricTransferred
    (concrete : G8BookIIICh23ConcreteUnitAddCircleCompactMetricGraphSource) :
    Prop :=
  ∀ x y : G8BookIIICh23FloorNormalizedLemniscateCarrier,
    let _ : MetricSpace G8BookIIICh23FloorNormalizedLemniscateCarrier :=
      g8BookIIICh23FloorNormalizedMetric concrete
    let _ : MetricSpace G8Ch23UnitAddCircleWedgeCarrier :=
      concrete.metric
    dist x y =
      dist
        (g8BookIIICh23UnitAddCircleEquivFloorNormalizedCarrier.symm x)
        (g8BookIIICh23UnitAddCircleEquivFloorNormalizedCarrier.symm y)

/-- Compactness transfer for the floor-normalized selected carrier. -/
def G8BookIIICh23FloorNormalizedCompactnessTransferred
    (concrete : G8BookIIICh23ConcreteUnitAddCircleCompactMetricGraphSource) :
    Prop :=
  @CompactSpace G8BookIIICh23FloorNormalizedLemniscateCarrier
    (g8BookIIICh23FloorNormalizedTopology concrete)

/-- Topology/metric agreement is inherited from the transported topology. -/
def G8BookIIICh23FloorNormalizedTopologyMetricAgreement
    (concrete : G8BookIIICh23ConcreteUnitAddCircleCompactMetricGraphSource) :
    Prop :=
  G8BookIIICh23FloorNormalizedTopologyTransferred concrete

/-- The graph metric is realized by pullback from the concrete Ch.23 graph. -/
def G8BookIIICh23FloorNormalizedGraphDistanceRealizesMetric
    (concrete : G8BookIIICh23ConcreteUnitAddCircleCompactMetricGraphSource) :
    Prop :=
  concrete.graphDistanceRealizesMetric ∧
    G8BookIIICh23FloorNormalizedMetricTransferred concrete

/-- The selected carrier is exactly the concrete quotient carrier transported
    through the floor-normalized lobe equivalence. -/
def G8BookIIICh23FloorNormalizedQuotientMatchesConcrete :
    Prop :=
  Nonempty
    (G8Ch23UnitAddCircleWedgeCarrier ≃
      G8BookIIICh23FloorNormalizedLemniscateCarrier) ∧
    g8BookIIICh23UnitAddCircleEquivFloorNormalizedCarrier
        G8Ch23UnitAddCircleWedgeCarrier.crossing =
      G8BookIIICh23FloorNormalizedLemniscateCarrier.crossing ∧
    ∀ (s : LemniscateSector) (p : UnitAddCircle),
      g8BookIIICh23UnitAddCircleEquivFloorNormalizedCarrier
          (G8Ch23UnitAddCircleWedgeCarrier.lobe s p) =
        G8BookIIICh23FloorNormalizedLemniscateCarrier.lobe s
          (g8FloorNormalizedLobeEquiv p)

theorem g8BookIIICh23FloorNormalizedTopologyTransferred_closed
    (concrete : G8BookIIICh23ConcreteUnitAddCircleCompactMetricGraphSource) :
    G8BookIIICh23FloorNormalizedTopologyTransferred concrete :=
  g8BookIIICh23FloorNormalizedTopologyEmbedding concrete

theorem g8BookIIICh23FloorNormalizedMetricTransferred_closed
    (concrete : G8BookIIICh23ConcreteUnitAddCircleCompactMetricGraphSource) :
    G8BookIIICh23FloorNormalizedMetricTransferred concrete := by
  intro x y
  exact g8BookIIICh23FloorNormalizedMetric_dist concrete x y

theorem g8BookIIICh23FloorNormalizedCompactnessTransferred_closed
    (concrete : G8BookIIICh23ConcreteUnitAddCircleCompactMetricGraphSource) :
    G8BookIIICh23FloorNormalizedCompactnessTransferred concrete :=
  g8BookIIICh23FloorNormalizedCompactSpace concrete

theorem g8BookIIICh23FloorNormalizedTopologyMetricAgreement_closed
    (concrete : G8BookIIICh23ConcreteUnitAddCircleCompactMetricGraphSource) :
    G8BookIIICh23FloorNormalizedTopologyMetricAgreement concrete :=
  g8BookIIICh23FloorNormalizedTopologyTransferred_closed concrete

theorem g8BookIIICh23FloorNormalizedGraphDistanceRealizesMetric_closed
    (concrete : G8BookIIICh23ConcreteUnitAddCircleCompactMetricGraphSource) :
    G8BookIIICh23FloorNormalizedGraphDistanceRealizesMetric concrete :=
  ⟨concrete.graphDistanceRealizesMetricEvidence,
    g8BookIIICh23FloorNormalizedMetricTransferred_closed concrete⟩

theorem g8BookIIICh23FloorNormalizedQuotientMatchesConcrete_closed :
    G8BookIIICh23FloorNormalizedQuotientMatchesConcrete :=
  ⟨⟨g8BookIIICh23UnitAddCircleEquivFloorNormalizedCarrier⟩,
    g8BookIIICh23UnitAddCircleEquivFloorNormalizedCarrier_crossing,
    g8BookIIICh23UnitAddCircleEquivFloorNormalizedCarrier_lobe⟩

/-- Closed floor-normalized A1.1 compact graph source. -/
structure G8BookIIICh23FloorNormalizedA11CompactMetricGraphSource where
  concrete :
    G8BookIIICh23ConcreteUnitAddCircleCompactMetricGraphSource
  carrierEquiv :
    G8Ch23UnitAddCircleWedgeCarrier ≃
      G8BookIIICh23FloorNormalizedLemniscateCarrier :=
        g8BookIIICh23UnitAddCircleEquivFloorNormalizedCarrier
  topology :
    TopologicalSpace G8BookIIICh23FloorNormalizedLemniscateCarrier
  metric :
    MetricSpace G8BookIIICh23FloorNormalizedLemniscateCarrier
  compact :
    @CompactSpace G8BookIIICh23FloorNormalizedLemniscateCarrier topology
  topologyTransferred :
    G8BookIIICh23FloorNormalizedTopologyTransferred concrete
  metricTransferred :
    G8BookIIICh23FloorNormalizedMetricTransferred concrete
  compactnessTransferred :
    G8BookIIICh23FloorNormalizedCompactnessTransferred concrete
  topologyMetricAgreement :
    G8BookIIICh23FloorNormalizedTopologyMetricAgreement concrete
  graphDistanceRealizesMetric :
    G8BookIIICh23FloorNormalizedGraphDistanceRealizesMetric concrete
  quotientMatchesConcrete :
    G8BookIIICh23FloorNormalizedQuotientMatchesConcrete
  compactGraphFromFloorNormalizedCarrier : Prop
  compactGraphFromFloorNormalizedCarrierEvidence :
    compactGraphFromFloorNormalizedCarrier
  status : SpineStatus := .conditional_interface

/-- Target for the selected floor-normalized A1.1 compact graph theorem. -/
def G8BookIIICh23FloorNormalizedA11CompactMetricGraphTarget : Prop :=
  Nonempty G8BookIIICh23FloorNormalizedA11CompactMetricGraphSource

/-- The floor-normalized A1.1 compact graph target is closed from the concrete
    Ch.23 graph and the floor-normalized lobe equivalence. -/
noncomputable def g8BookIIICh23FloorNormalizedA11CompactMetricGraphSource_closed :
    G8BookIIICh23FloorNormalizedA11CompactMetricGraphSource :=
  let concrete :=
    g8BookIIICh23ConcreteUnitAddCircleCompactMetricGraphSource_closed
  { concrete := concrete
    topology := g8BookIIICh23FloorNormalizedTopology concrete
    metric := g8BookIIICh23FloorNormalizedMetric concrete
    compact := g8BookIIICh23FloorNormalizedCompactSpace concrete
    topologyTransferred :=
      g8BookIIICh23FloorNormalizedTopologyTransferred_closed concrete
    metricTransferred :=
      g8BookIIICh23FloorNormalizedMetricTransferred_closed concrete
    compactnessTransferred :=
      g8BookIIICh23FloorNormalizedCompactnessTransferred_closed concrete
    topologyMetricAgreement :=
      g8BookIIICh23FloorNormalizedTopologyMetricAgreement_closed concrete
    graphDistanceRealizesMetric :=
      g8BookIIICh23FloorNormalizedGraphDistanceRealizesMetric_closed concrete
    quotientMatchesConcrete :=
      g8BookIIICh23FloorNormalizedQuotientMatchesConcrete_closed
    compactGraphFromFloorNormalizedCarrier :=
      concrete.compactnessFromCircleWedge ∧
        concrete.shortestPathGraphMetric ∧
        concrete.topologyMetricAgreement ∧
        concrete.graphDistanceRealizesMetric ∧
        G8BookIIICh23FloorNormalizedQuotientMatchesConcrete
    compactGraphFromFloorNormalizedCarrierEvidence :=
      ⟨concrete.compactnessFromCircleWedgeEvidence,
        concrete.shortestPathGraphMetricEvidence,
        concrete.topologyMetricAgreementEvidence,
        concrete.graphDistanceRealizesMetricEvidence,
        g8BookIIICh23FloorNormalizedQuotientMatchesConcrete_closed⟩
    status := .conditional_interface }

/-- Closed target for the floor-normalized A1.1 route. -/
theorem g8BookIIICh23FloorNormalizedA11CompactMetricGraphTarget_closed :
    G8BookIIICh23FloorNormalizedA11CompactMetricGraphTarget :=
  ⟨g8BookIIICh23FloorNormalizedA11CompactMetricGraphSource_closed⟩

-- ============================================================
-- OPTIONAL RAW-CARRIER UPGRADE SURFACE
-- ============================================================

/-- Optional bridge from the selected floor-normalized carrier to the current
    raw `LemniscateCarrier`.  This is not needed for the selected-carrier
    A1.1 route, but records exactly what would be required to recover the old
    raw-carrier package. -/
structure G8BookIIICh23FloorNormalizedToRawLemniscateCarrierBridge where
  floorSource :
    G8BookIIICh23FloorNormalizedA11CompactMetricGraphSource
  carrierEquiv :
    G8BookIIICh23FloorNormalizedLemniscateCarrier ≃ LemniscateCarrier
  carrierCtx : LemniscateCarrierContext
  topologyTransferred : carrierCtx.topologyIsWedgeQuotient
  metricTransferred : carrierCtx.metricIsGraphMetric
  compactnessTransferred : carrierCtx.compactnessFromWedge
  topologyMetricAgreement : LemniscateTopologyMetricAgreement carrierCtx
  graphDistanceRealizesMetric : carrierCtx.graphDistanceRealizesMetric
  theoremBackedStatus : carrierCtx.status = .theoremBacked
  exactCarrierAlignment : Prop
  exactCarrierAlignmentEvidence : exactCarrierAlignment
  status : SpineStatus := .conditional_interface

/-- The optional raw-carrier upgrade is the exact remaining bridge if we want
    the selected floor-normalized route to inhabit the old `LemniscateCarrier`
    compact graph package. -/
def G8BookIIICh23FloorNormalizedToRawCarrierBridgeTarget : Prop :=
  Nonempty G8BookIIICh23FloorNormalizedToRawLemniscateCarrierBridge

/-- The selected-carrier route does not assert the optional raw-carrier bridge. -/
structure G8BookIIICh23FloorNormalizedRouteWithoutRawCarrierUpgrade where
  floorTarget :
    G8BookIIICh23FloorNormalizedA11CompactMetricGraphTarget
  noRawUpgrade :
    ¬ G8BookIIICh23FloorNormalizedToRawCarrierBridgeTarget

theorem
    G8BookIIICh23FloorNormalizedRouteWithoutRawCarrierUpgrade.refutesRawUpgrade
    (gap : G8BookIIICh23FloorNormalizedRouteWithoutRawCarrierUpgrade) :
    ¬ G8BookIIICh23FloorNormalizedToRawCarrierBridgeTarget :=
  gap.noRawUpgrade

end Tau.BookIII.Bridge
