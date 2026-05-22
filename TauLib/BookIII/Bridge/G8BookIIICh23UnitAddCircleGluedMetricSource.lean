import TauLib.BookIII.Bridge.G8BookIIICh23UnitAddCircleQuotientCompactTopology

/-!
# TauLib.BookIII.Bridge.G8BookIIICh23UnitAddCircleGluedMetricSource

Mathlib glued-metric source for the concrete Ch.23 two-lobe wedge.

The quotient topology and compactness for `G8Ch23UnitAddCircleWedgeCarrier`
are already theorem-backed.  This module adds the next metric-side source:
two copies of `UnitAddCircle` glued at the basepoint using Mathlib's
`Metric.GlueSpace`.

It deliberately keeps the final transfer from this glued metric space to the
previous quotient carrier as a proof-carrying field.  That transfer is exactly
where the quotient presentation, topology agreement, shortest-path graph
metric, and metric realization must be identified.
-/

set_option autoImplicit false

namespace Tau.BookIII.Bridge

-- ============================================================
-- MATHLIB GLUED METRIC MODEL
-- ============================================================

/-- Singleton crossing domain used to glue the two `UnitAddCircle` lobes. -/
abbrev G8Ch23UnitAddCircleCrossingDomain : Type :=
  Unit

/-- The crossing inclusion into the plus lobe. -/
def g8Ch23UnitAddCircleCrossingToPlus
    (_ : G8Ch23UnitAddCircleCrossingDomain) : UnitAddCircle :=
  0

/-- The crossing inclusion into the minus lobe. -/
def g8Ch23UnitAddCircleCrossingToMinus
    (_ : G8Ch23UnitAddCircleCrossingDomain) : UnitAddCircle :=
  0

/-- The singleton crossing includes isometrically into the plus lobe. -/
theorem g8Ch23UnitAddCircleCrossingToPlus_isometry :
    Isometry g8Ch23UnitAddCircleCrossingToPlus := by
  refine Isometry.of_dist_eq ?_
  intro x y
  cases x
  cases y
  simp [g8Ch23UnitAddCircleCrossingToPlus]

/-- The singleton crossing includes isometrically into the minus lobe. -/
theorem g8Ch23UnitAddCircleCrossingToMinus_isometry :
    Isometry g8Ch23UnitAddCircleCrossingToMinus := by
  refine Isometry.of_dist_eq ?_
  intro x y
  cases x
  cases y
  simp [g8Ch23UnitAddCircleCrossingToMinus]

/-- Mathlib's metric gluing of the two `UnitAddCircle` lobes at the chosen
    basepoint. -/
abbrev G8Ch23UnitAddCircleGluedMetricSpace : Type :=
  Metric.GlueSpace
    g8Ch23UnitAddCircleCrossingToPlus_isometry
    g8Ch23UnitAddCircleCrossingToMinus_isometry

/-- Inclusion of the plus lobe into the glued metric space. -/
def g8Ch23UnitAddCirclePlusToGlue :
    UnitAddCircle → G8Ch23UnitAddCircleGluedMetricSpace :=
  Metric.toGlueL
    g8Ch23UnitAddCircleCrossingToPlus_isometry
    g8Ch23UnitAddCircleCrossingToMinus_isometry

/-- Inclusion of the minus lobe into the glued metric space. -/
def g8Ch23UnitAddCircleMinusToGlue :
    UnitAddCircle → G8Ch23UnitAddCircleGluedMetricSpace :=
  Metric.toGlueR
    g8Ch23UnitAddCircleCrossingToPlus_isometry
    g8Ch23UnitAddCircleCrossingToMinus_isometry

/-- The plus-lobe inclusion into the glued metric space is an isometry. -/
theorem g8Ch23UnitAddCirclePlusToGlue_isometry :
    Isometry g8Ch23UnitAddCirclePlusToGlue :=
  Metric.toGlueL_isometry
    g8Ch23UnitAddCircleCrossingToPlus_isometry
    g8Ch23UnitAddCircleCrossingToMinus_isometry

/-- The minus-lobe inclusion into the glued metric space is an isometry. -/
theorem g8Ch23UnitAddCircleMinusToGlue_isometry :
    Isometry g8Ch23UnitAddCircleMinusToGlue :=
  Metric.toGlueR_isometry
    g8Ch23UnitAddCircleCrossingToPlus_isometry
    g8Ch23UnitAddCircleCrossingToMinus_isometry

/-- The two lobe basepoints are identified in the glued metric space. -/
theorem g8Ch23UnitAddCircleGlue_basepoints_eq :
    g8Ch23UnitAddCirclePlusToGlue
        G8Ch23UnitAddCircleWedgePoint.basepoint =
      g8Ch23UnitAddCircleMinusToGlue
        G8Ch23UnitAddCircleWedgePoint.basepoint := by
  simpa [g8Ch23UnitAddCirclePlusToGlue,
    g8Ch23UnitAddCircleMinusToGlue,
    g8Ch23UnitAddCircleCrossingToPlus,
    g8Ch23UnitAddCircleCrossingToMinus,
    G8Ch23UnitAddCircleWedgePoint.basepoint]
    using congrFun
      (Metric.toGlue_commute
        g8Ch23UnitAddCircleCrossingToPlus_isometry
        g8Ch23UnitAddCircleCrossingToMinus_isometry)
      ()

-- ============================================================
-- GLUED METRIC SOURCE
-- ============================================================

/-- The theorem-backed Mathlib glued-metric source for the two
    `UnitAddCircle` lobes.  This source proves the basepoint gluing and lobe
    isometries, but it is intentionally not yet the quotient-carrier metric. -/
structure G8BookIIICh23UnitAddCircleGluedMetricGraphSource where
  topologySource :
    G8BookIIICh23UnitAddCircleQuotientCompactTopologySource
  glueMetric : MetricSpace G8Ch23UnitAddCircleGluedMetricSpace
  plusLobeIsometry : Isometry g8Ch23UnitAddCirclePlusToGlue
  minusLobeIsometry : Isometry g8Ch23UnitAddCircleMinusToGlue
  basepointsGlued :
    g8Ch23UnitAddCirclePlusToGlue
        G8Ch23UnitAddCircleWedgePoint.basepoint =
      g8Ch23UnitAddCircleMinusToGlue
        G8Ch23UnitAddCircleWedgePoint.basepoint
  gluedMetricRealizesTwoLobeBasepointWedge : Prop
  gluedMetricRealizesTwoLobeBasepointWedgeEvidence :
    gluedMetricRealizesTwoLobeBasepointWedge
  quotientMetricTransferStillOpen : Prop
  quotientMetricTransferStillOpenEvidence :
    quotientMetricTransferStillOpen
  status : SpineStatus := .conditional_interface

/-- The Mathlib glued-metric two-lobe source is theorem-backed. -/
noncomputable def g8BookIIICh23UnitAddCircleGluedMetricGraphSource :
    G8BookIIICh23UnitAddCircleGluedMetricGraphSource where
  topologySource :=
    g8BookIIICh23UnitAddCircleQuotientCompactTopologySource
  glueMetric :=
    inferInstance
  plusLobeIsometry :=
    g8Ch23UnitAddCirclePlusToGlue_isometry
  minusLobeIsometry :=
    g8Ch23UnitAddCircleMinusToGlue_isometry
  basepointsGlued :=
    g8Ch23UnitAddCircleGlue_basepoints_eq
  gluedMetricRealizesTwoLobeBasepointWedge :=
    Isometry g8Ch23UnitAddCirclePlusToGlue ∧
      Isometry g8Ch23UnitAddCircleMinusToGlue ∧
      g8Ch23UnitAddCirclePlusToGlue
          G8Ch23UnitAddCircleWedgePoint.basepoint =
        g8Ch23UnitAddCircleMinusToGlue
          G8Ch23UnitAddCircleWedgePoint.basepoint
  gluedMetricRealizesTwoLobeBasepointWedgeEvidence :=
    ⟨g8Ch23UnitAddCirclePlusToGlue_isometry,
      g8Ch23UnitAddCircleMinusToGlue_isometry,
      g8Ch23UnitAddCircleGlue_basepoints_eq⟩
  quotientMetricTransferStillOpen :=
    True
  quotientMetricTransferStillOpenEvidence :=
    trivial
  status := .conditional_interface

/-- Target for the theorem-backed glued metric source. -/
def G8BookIIICh23UnitAddCircleGluedMetricGraphTarget : Prop :=
  Nonempty G8BookIIICh23UnitAddCircleGluedMetricGraphSource

/-- The glued metric graph target is closed. -/
theorem g8BookIIICh23UnitAddCircleGluedMetricGraph_closed :
    G8BookIIICh23UnitAddCircleGluedMetricGraphTarget :=
  ⟨g8BookIIICh23UnitAddCircleGluedMetricGraphSource⟩

-- ============================================================
-- TRANSFER TO THE QUOTIENT CARRIER
-- ============================================================

/-- Exact transfer from the Mathlib glued metric model to the concrete quotient
    wedge carrier.

This is the remaining concrete A1.1 metric theorem: identify the glued metric
space with the already constructed quotient carrier, transport the metric, and
prove that the transported topology is the quotient topology and that the
metric is the intended shortest-path graph metric. -/
structure G8BookIIICh23UnitAddCircleGlueToQuotientMetricTransferSource where
  glueSource : G8BookIIICh23UnitAddCircleGluedMetricGraphSource
  carrierEquiv :
    G8Ch23UnitAddCircleGluedMetricSpace ≃
      G8Ch23UnitAddCircleWedgeCarrier
  quotientMetric : MetricSpace G8Ch23UnitAddCircleWedgeCarrier
  quotientTopology :
    TopologicalSpace G8Ch23UnitAddCircleWedgeCarrier :=
      g8Ch23UnitAddCircleWedgeCarrierQuotientTopology
  quotientCompact :
    @CompactSpace G8Ch23UnitAddCircleWedgeCarrier quotientTopology
  quotientTopologyIsTwoCircleWedge : Prop
  quotientTopologyIsTwoCircleWedgeEvidence :
    quotientTopologyIsTwoCircleWedge
  compactnessFromCircleWedge : Prop
  compactnessFromCircleWedgeEvidence :
    compactnessFromCircleWedge
  shortestPathGraphMetric : Prop
  shortestPathGraphMetricEvidence :
    shortestPathGraphMetric
  topologyMetricAgreement : Prop
  topologyMetricAgreementEvidence :
    topologyMetricAgreement
  graphDistanceRealizesMetric : Prop
  graphDistanceRealizesMetricEvidence :
    graphDistanceRealizesMetric
  status : SpineStatus := .conditional_interface

namespace G8BookIIICh23UnitAddCircleGlueToQuotientMetricTransferSource

/-- A glue-to-quotient metric transfer supplies the full concrete compact
    metric graph source. -/
def toConcreteCompactMetricGraphSource
    (source :
      G8BookIIICh23UnitAddCircleGlueToQuotientMetricTransferSource) :
    G8BookIIICh23ConcreteUnitAddCircleCompactMetricGraphSource where
  core :=
    source.glueSource.topologySource.core
  topology :=
    source.quotientTopology
  metric :=
    source.quotientMetric
  compact :=
    source.quotientCompact
  quotientTopologyIsTwoCircleWedge :=
    source.quotientTopologyIsTwoCircleWedge
  quotientTopologyIsTwoCircleWedgeEvidence :=
    source.quotientTopologyIsTwoCircleWedgeEvidence
  compactnessFromCircleWedge :=
    source.compactnessFromCircleWedge
  compactnessFromCircleWedgeEvidence :=
    source.compactnessFromCircleWedgeEvidence
  shortestPathGraphMetric :=
    source.shortestPathGraphMetric
  shortestPathGraphMetricEvidence :=
    source.shortestPathGraphMetricEvidence
  topologyMetricAgreement :=
    source.topologyMetricAgreement
  topologyMetricAgreementEvidence :=
    source.topologyMetricAgreementEvidence
  graphDistanceRealizesMetric :=
    source.graphDistanceRealizesMetric
  graphDistanceRealizesMetricEvidence :=
    source.graphDistanceRealizesMetricEvidence
  status := source.status

end G8BookIIICh23UnitAddCircleGlueToQuotientMetricTransferSource

/-- Target for the exact glue-to-quotient metric transfer. -/
def G8BookIIICh23UnitAddCircleGlueToQuotientMetricTransferTarget :
    Prop :=
  Nonempty G8BookIIICh23UnitAddCircleGlueToQuotientMetricTransferSource

/-- The glue-to-quotient metric transfer closes the full concrete compact
    metric graph target. -/
theorem
    g8BookIIICh23UnitAddCircleGlueToQuotientMetricTransferTarget_toConcreteTarget
    (target :
      G8BookIIICh23UnitAddCircleGlueToQuotientMetricTransferTarget) :
    G8BookIIICh23ConcreteCompactMetricGraphTarget := by
  rcases target with ⟨source⟩
  exact source.toConcreteCompactMetricGraphSource.toTarget

-- ============================================================
-- GUARDRAILS
-- ============================================================

/-- The Mathlib glued metric source alone does not identify the metric with
    the concrete quotient carrier metric. -/
structure G8BookIIICh23GluedMetricWithoutQuotientTransfer where
  glueSource : G8BookIIICh23UnitAddCircleGluedMetricGraphSource
  noTransfer :
    ¬ G8BookIIICh23UnitAddCircleGlueToQuotientMetricTransferTarget

/-- Missing glue-to-quotient transfer refutes only the quotient transfer
    target, not the theorem-backed glued metric source. -/
theorem
    G8BookIIICh23GluedMetricWithoutQuotientTransfer.refutesTransferTarget
    (gap : G8BookIIICh23GluedMetricWithoutQuotientTransfer) :
    ¬ G8BookIIICh23UnitAddCircleGlueToQuotientMetricTransferTarget :=
  gap.noTransfer

/-- A candidate transfer with wrong topology/metric agreement refutes the
    concrete source it tries to build. -/
structure G8BookIIICh23GlueTransferWrongTopologyMetricAgreement
    (source :
      G8BookIIICh23UnitAddCircleGlueToQuotientMetricTransferSource) where
  noAgreement : ¬ source.topologyMetricAgreement

/-- Exact topology/metric agreement is a load-bearing field of the transfer. -/
theorem
    G8BookIIICh23GlueTransferWrongTopologyMetricAgreement.refutesTransfer
    {source :
      G8BookIIICh23UnitAddCircleGlueToQuotientMetricTransferSource}
    (gap :
      G8BookIIICh23GlueTransferWrongTopologyMetricAgreement source) :
    False :=
  gap.noAgreement source.topologyMetricAgreementEvidence

end Tau.BookIII.Bridge
