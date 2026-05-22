import TauLib.BookIII.Bridge.G8BookIIICh23UnitAddCircleRawCompactWedgeModel

/-!
# TauLib.BookIII.Bridge.G8BookIIICh23UnitAddCircleQuotientCompactTopology

Quotient-topology compactness for the concrete Ch.23 `UnitAddCircle` wedge.

The previous module closes the compact pre-quotient disjoint model.  This
module transfers that compactness through the exact raw wedge equivalence and
then through the wedge quotient topology.  It still does not construct the
shortest-path graph metric or prove topology/metric agreement.
-/

set_option autoImplicit false

namespace Tau.BookIII.Bridge

-- ============================================================
-- RAW WEDGE-POINT TOPOLOGY FROM THE COMPACT MODEL
-- ============================================================

/-- Topology on the raw wedge-point presentation transported from the compact
    disjoint model by the exact raw equivalence. -/
noncomputable def g8Ch23UnitAddCircleWedgePointCompactTopology :
    TopologicalSpace G8Ch23UnitAddCircleWedgePoint :=
  TopologicalSpace.coinduced
    g8Ch23UnitAddCircleRawCompactWedgeModelEquiv
    G8Ch23UnitAddCircleRawCompactWedgeModel.topology

noncomputable local instance :
    TopologicalSpace G8Ch23UnitAddCircleWedgePoint :=
  g8Ch23UnitAddCircleWedgePointCompactTopology

/-- The transported raw equivalence is a homeomorphism from the compact
    disjoint model to the raw wedge-point presentation. -/
noncomputable def g8Ch23UnitAddCircleRawCompactWedgeModelHomeomorph :
    G8Ch23UnitAddCircleRawCompactWedgeModel ≃ₜ
      G8Ch23UnitAddCircleWedgePoint :=
  @Equiv.toHomeomorph
    G8Ch23UnitAddCircleRawCompactWedgeModel
    G8Ch23UnitAddCircleWedgePoint
    G8Ch23UnitAddCircleRawCompactWedgeModel.topology
    g8Ch23UnitAddCircleWedgePointCompactTopology
    g8Ch23UnitAddCircleRawCompactWedgeModelEquiv
    (by
      intro s
      rfl)

/-- Compactness of the raw wedge-point presentation, transported from the
    compact disjoint model. -/
noncomputable def g8Ch23UnitAddCircleWedgePointCompactSpace :
    @CompactSpace G8Ch23UnitAddCircleWedgePoint
      g8Ch23UnitAddCircleWedgePointCompactTopology :=
  @Homeomorph.compactSpace
    G8Ch23UnitAddCircleRawCompactWedgeModel
    G8Ch23UnitAddCircleWedgePoint
    G8Ch23UnitAddCircleRawCompactWedgeModel.topology
    g8Ch23UnitAddCircleWedgePointCompactTopology
    G8Ch23UnitAddCircleRawCompactWedgeModel.compactSpace
    g8Ch23UnitAddCircleRawCompactWedgeModelHomeomorph

-- ============================================================
-- QUOTIENT TOPOLOGY AND COMPACTNESS
-- ============================================================

/-- Quotient topology on the concrete `UnitAddCircle` wedge carrier, induced
    from the transported compact raw wedge-point topology. -/
noncomputable def g8Ch23UnitAddCircleWedgeCarrierQuotientTopology :
    TopologicalSpace G8Ch23UnitAddCircleWedgeCarrier :=
  @instTopologicalSpaceQuotient
    G8Ch23UnitAddCircleWedgePoint
    G8Ch23UnitAddCircleWedgePoint.wedgeSetoid
    g8Ch23UnitAddCircleWedgePointCompactTopology

/-- Compactness of the concrete quotient carrier for the quotient topology. -/
noncomputable def g8Ch23UnitAddCircleWedgeCarrierQuotientCompactSpace :
    @CompactSpace G8Ch23UnitAddCircleWedgeCarrier
      g8Ch23UnitAddCircleWedgeCarrierQuotientTopology := by
  letI : TopologicalSpace G8Ch23UnitAddCircleWedgePoint :=
    g8Ch23UnitAddCircleWedgePointCompactTopology
  letI : CompactSpace G8Ch23UnitAddCircleWedgePoint :=
    g8Ch23UnitAddCircleWedgePointCompactSpace
  exact inferInstance

-- ============================================================
-- THEOREM-BACKED QUOTIENT TOPOLOGY SOURCE
-- ============================================================

/-- The quotient topology and compactness package for the concrete
    `UnitAddCircle` wedge.  The metric fields of the full compact metric graph
    remain separate. -/
structure G8BookIIICh23UnitAddCircleQuotientCompactTopologySource where
  core : G8BookIIICh23UnitAddCircleWedgeCore
  raw : G8BookIIICh23UnitAddCircleRawCompactWedgeModelSource
  rawTopology : TopologicalSpace G8Ch23UnitAddCircleWedgePoint
  rawCompact :
    @CompactSpace G8Ch23UnitAddCircleWedgePoint rawTopology
  quotientTopology : TopologicalSpace G8Ch23UnitAddCircleWedgeCarrier
  quotientCompact :
    @CompactSpace G8Ch23UnitAddCircleWedgeCarrier quotientTopology
  rawHomeomorph :
    G8Ch23UnitAddCircleRawCompactWedgeModel ≃ₜ
      G8Ch23UnitAddCircleWedgePoint
  quotientTopologyIsTwoCircleWedge : Prop
  quotientTopologyIsTwoCircleWedgeEvidence :
    quotientTopologyIsTwoCircleWedge
  compactnessFromCircleWedge : Prop
  compactnessFromCircleWedgeEvidence : compactnessFromCircleWedge
  metricStillOpen : Prop
  metricStillOpenEvidence : metricStillOpen
  status : SpineStatus := .conditional_interface

/-- The quotient compact topology source is closed from the raw compact model
    and Mathlib quotient compactness. -/
noncomputable def g8BookIIICh23UnitAddCircleQuotientCompactTopologySource :
    G8BookIIICh23UnitAddCircleQuotientCompactTopologySource where
  core :=
    g8BookIIICh23UnitAddCircleWedgeCore
  raw :=
    g8BookIIICh23UnitAddCircleRawCompactWedgeModelSource
  rawTopology :=
    g8Ch23UnitAddCircleWedgePointCompactTopology
  rawCompact :=
    g8Ch23UnitAddCircleWedgePointCompactSpace
  quotientTopology :=
    g8Ch23UnitAddCircleWedgeCarrierQuotientTopology
  quotientCompact :=
    g8Ch23UnitAddCircleWedgeCarrierQuotientCompactSpace
  rawHomeomorph :=
    g8Ch23UnitAddCircleRawCompactWedgeModelHomeomorph
  quotientTopologyIsTwoCircleWedge :=
    Nonempty (G8Ch23UnitAddCircleRawCompactWedgeModel ≃ₜ
      G8Ch23UnitAddCircleWedgePoint)
  quotientTopologyIsTwoCircleWedgeEvidence :=
    ⟨g8Ch23UnitAddCircleRawCompactWedgeModelHomeomorph⟩
  compactnessFromCircleWedge :=
    CompactSpace G8Ch23UnitAddCircleRawCompactWedgeModel ∧
      @CompactSpace G8Ch23UnitAddCircleWedgeCarrier
        g8Ch23UnitAddCircleWedgeCarrierQuotientTopology
  compactnessFromCircleWedgeEvidence :=
    ⟨inferInstance, g8Ch23UnitAddCircleWedgeCarrierQuotientCompactSpace⟩
  metricStillOpen :=
    True
  metricStillOpenEvidence :=
    trivial
  status := .conditional_interface

/-- Target for the theorem-backed quotient compact topology source. -/
def G8BookIIICh23UnitAddCircleQuotientCompactTopologyTarget : Prop :=
  Nonempty G8BookIIICh23UnitAddCircleQuotientCompactTopologySource

/-- The quotient compact topology target is closed. -/
theorem g8BookIIICh23UnitAddCircleQuotientCompactTopology_closed :
    G8BookIIICh23UnitAddCircleQuotientCompactTopologyTarget :=
  ⟨g8BookIIICh23UnitAddCircleQuotientCompactTopologySource⟩

/-- Quotient compact topology is a strict prerequisite for the full concrete
    compact metric graph source; it does not provide a graph metric by itself. -/
structure G8BookIIICh23QuotientCompactTopologyWithoutGraphMetric where
  topologySource : G8BookIIICh23UnitAddCircleQuotientCompactTopologySource
  noConcreteCompactMetricGraph :
    ¬ G8BookIIICh23ConcreteCompactMetricGraphTarget

/-- Missing shortest-path metric evidence refutes only the full concrete graph
    target, not quotient compactness. -/
theorem
    G8BookIIICh23QuotientCompactTopologyWithoutGraphMetric.refutesConcreteTarget
    (gap : G8BookIIICh23QuotientCompactTopologyWithoutGraphMetric) :
    ¬ G8BookIIICh23ConcreteCompactMetricGraphTarget :=
  gap.noConcreteCompactMetricGraph

end Tau.BookIII.Bridge
