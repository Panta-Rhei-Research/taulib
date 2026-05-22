import TauLib.BookIII.Bridge.LemniscateOperatorSpine

/-!
# TauLib.BookIII.Bridge.G8BookIIILemniscateGraphDomainCore

Low-level A1.1/A1.2 source layer for the Lane-A operator route.

This module stays below actual-`xi`, spectral membership, final-spine, and
tower-admission machinery.  It records the theorem-backed raw two-lobe wedge
facts already present in the lemniscate carrier, then names the exact metric
graph and Hilbert/Kirchhoff-domain readiness packages needed by the A1/A2 proof
map.

The raw wedge quotient is theorem-backed here.  The genuine compact metric
graph topology/metric theorem and Sobolev/Kirchhoff trace-readiness theorem
remain explicit proof-carrying inputs.
-/

set_option autoImplicit false

namespace Tau.BookIII.Bridge

-- ============================================================
-- A1.1 RAW TWO-LOBE WEDGE CORE
-- ============================================================

/-- The theorem-backed raw two-lobe wedge facts for
    `L = S¹_B ∨ S¹_C`.

This is still below metric-graph readiness: it proves the carrier-level wedge
identifications, not the analytic graph metric or compactness theorem. -/
structure G8BookIIILemniscateTwoLobeWedgeCore where
  plusBase_eq_crossing :
    LemniscateCarrier.lobe .plus TauCirclePoint.base =
      LemniscateCarrier.crossing
  minusBase_eq_crossing :
    LemniscateCarrier.lobe .minus TauCirclePoint.base =
      LemniscateCarrier.crossing
  plusBase_eq_minusBase :
    LemniscateCarrier.lobe .plus TauCirclePoint.base =
      LemniscateCarrier.lobe .minus TauCirclePoint.base
  crossing_on_plus :
    LemniscateCarrier.OnSector .plus LemniscateCarrier.crossing
  crossing_on_minus :
    LemniscateCarrier.OnSector .minus LemniscateCarrier.crossing
  wedgeRelated_sound :
    ∀ {x y : LemniscatePoint},
      LemniscatePoint.WedgeRelated x y →
        Quotient.mk LemniscatePoint.wedgeSetoid x =
          Quotient.mk LemniscatePoint.wedgeSetoid y
  status : SpineStatus := .conditional_interface

/-- The current raw two-lobe wedge quotient facts are theorem-backed by
    `LemniscateGraph`. -/
def g8BookIIILemniscateTwoLobeWedgeCore :
    G8BookIIILemniscateTwoLobeWedgeCore where
  plusBase_eq_crossing :=
    LemniscateCarrier.lobe_base_eq_crossing .plus
  minusBase_eq_crossing :=
    LemniscateCarrier.lobe_base_eq_crossing .minus
  plusBase_eq_minusBase :=
    LemniscateCarrier.plus_base_eq_minus_base
  crossing_on_plus :=
    LemniscateCarrier.crossing_onSector .plus
  crossing_on_minus :=
    LemniscateCarrier.crossing_onSector .minus
  wedgeRelated_sound := by
    intro x y h
    exact LemniscateCarrier.sound_wedge_related h

/-- Compact proposition target for the raw wedge core. -/
def G8BookIIILemniscateTwoLobeWedgeCoreTarget : Prop :=
  Nonempty G8BookIIILemniscateTwoLobeWedgeCore

/-- The raw wedge core target is already closed. -/
theorem g8BookIIILemniscateTwoLobeWedgeCore_closed :
    G8BookIIILemniscateTwoLobeWedgeCoreTarget :=
  ⟨g8BookIIILemniscateTwoLobeWedgeCore⟩

-- ============================================================
-- A1.1 METRIC GRAPH READINESS INPUT
-- ============================================================

/-- Proof-carrying readiness data for a compact metric graph carrier context.

Supplying this data is exactly the remaining A1.1 metric/topology theorem:
the raw wedge carrier has the intended compact graph topology and metric. -/
structure G8BookIIILemniscateMetricGraphReadinessData where
  carrierCtx : LemniscateCarrierContext
  topologyIsWedgeQuotient : carrierCtx.topologyIsWedgeQuotient
  metricIsGraphMetric : carrierCtx.metricIsGraphMetric
  compactnessFromWedge : carrierCtx.compactnessFromWedge
  topologyMetricAgreement : LemniscateTopologyMetricAgreement carrierCtx
  graphDistanceRealizesMetric : carrierCtx.graphDistanceRealizesMetric
  theoremBackedStatus : carrierCtx.status = .theoremBacked

/-- Readiness data discharges the primitive carrier-readiness predicate. -/
def G8BookIIILemniscateMetricGraphReadinessData.toCarrierReady
    (data : G8BookIIILemniscateMetricGraphReadinessData) :
    LemniscateCarrierReady data.carrierCtx :=
  ⟨data.topologyIsWedgeQuotient,
    data.metricIsGraphMetric,
    data.compactnessFromWedge,
    data.topologyMetricAgreement,
    data.graphDistanceRealizesMetric,
    data.theoremBackedStatus⟩

/-- A1.1 constructor package: raw two-lobe wedge plus compact metric graph
    readiness. -/
structure G8BookIIILemniscateMetricGraphConstructor where
  rawWedge : G8BookIIILemniscateTwoLobeWedgeCore :=
    g8BookIIILemniscateTwoLobeWedgeCore
  readiness : G8BookIIILemniscateMetricGraphReadinessData
  compactMetricGraphFromRawWedge : Prop
  compactMetricGraphFromRawWedgeEvidence : compactMetricGraphFromRawWedge
  status : SpineStatus := .conditional_interface

/-- Carrier context selected by a metric graph constructor. -/
def G8BookIIILemniscateMetricGraphConstructor.carrierCtx
    (source : G8BookIIILemniscateMetricGraphConstructor) :
    LemniscateCarrierContext :=
  source.readiness.carrierCtx

/-- Carrier readiness selected by a metric graph constructor. -/
def G8BookIIILemniscateMetricGraphConstructor.carrierReady
    (source : G8BookIIILemniscateMetricGraphConstructor) :
    LemniscateCarrierReady source.carrierCtx :=
  source.readiness.toCarrierReady

/-- Exact remaining A1.1 target after the raw wedge quotient facts. -/
def G8BookIIILemniscateMetricGraphConstructorTarget : Prop :=
  Nonempty G8BookIIILemniscateMetricGraphConstructor

-- ============================================================
-- A1.2 HILBERT AND KIRCHHOFF DOMAIN READINESS INPUTS
-- ============================================================

/-- Proof-carrying data for the graph Hilbert/L2 layer. -/
structure G8BookIIILemniscateHilbertReadinessData where
  metricGraph : G8BookIIILemniscateMetricGraphConstructor
  hilbertCtx : LemniscateHilbertContext
  hilbertUsesGraph :
    hilbertCtx.measure.carrierContext = metricGraph.carrierCtx
  measureTotalFinite : hilbertCtx.measure.totalFinite
  lobeMeasureAgreement : hilbertCtx.measure.lobeMeasureAgreement
  innerProductSymmetric : hilbertCtx.innerProduct.symmetric
  innerProductPositive : hilbertCtx.innerProduct.positive
  innerProductComplete : hilbertCtx.innerProduct.complete
  innerProductCompatibleWithMeasure :
    hilbertCtx.innerProduct.compatibleWithMeasure
  traceMapDefined : hilbertCtx.traceMapDefined
  traceMapContinuous : hilbertCtx.traceMapContinuous
  quotientCompletionConstructed :
    hilbertCtx.quotientCompletionConstructed

/-- Hilbert readiness follows from the explicit Hilbert/L2 readiness data. -/
def G8BookIIILemniscateHilbertReadinessData.toHilbertReady
    (data : G8BookIIILemniscateHilbertReadinessData) :
    LemniscateHilbertReady data.hilbertCtx :=
  ⟨data.hilbertCtx.carrierReady,
    data.measureTotalFinite,
    data.lobeMeasureAgreement,
    data.innerProductSymmetric,
    data.innerProductPositive,
    data.innerProductComplete,
    data.innerProductCompatibleWithMeasure,
    data.traceMapDefined,
    data.traceMapContinuous,
    data.quotientCompletionConstructed⟩

/-- Proof-carrying data for the Sobolev/Kirchhoff operator domain. -/
structure G8BookIIILemniscateKirchhoffDomainReadinessData where
  hilbert : G8BookIIILemniscateHilbertReadinessData
  domainCtx : LemniscateDomainContext
  domainUsesHilbert : domainCtx.hilbert = hilbert.hilbertCtx
  valueTraceDefined : domainCtx.valueTraceDefined
  valueTraceContinuous : domainCtx.valueTraceContinuous
  derivativeTraceDefined : domainCtx.derivativeTraceDefined
  derivativeTraceContinuous : domainCtx.derivativeTraceContinuous
  crossingAgreementClosed : domainCtx.crossingAgreementClosed
  kirchhoffConditionClosed : domainCtx.kirchhoffConditionClosed
  traceContinuityEvidence : Prop
  traceContinuityWitness : traceContinuityEvidence
  derivativeTraceEvidence : Prop
  derivativeTraceWitness : derivativeTraceEvidence
  crossingClosureEvidence : Prop
  crossingClosureWitness : crossingClosureEvidence
  kirchhoffClosureEvidence : Prop
  kirchhoffClosureWitness : kirchhoffClosureEvidence
  status : SpineStatus := .conditional_interface

/-- Domain readiness follows from the explicit Sobolev/Kirchhoff readiness
    data. -/
def G8BookIIILemniscateKirchhoffDomainReadinessData.toDomainReady
    (data : G8BookIIILemniscateKirchhoffDomainReadinessData) :
    LemniscateDomainReady data.domainCtx :=
  have hHilbert :
      LemniscateHilbertReady data.domainCtx.hilbert := by
    rw [data.domainUsesHilbert]
    exact data.hilbert.toHilbertReady
  ⟨hHilbert,
    data.valueTraceDefined,
    data.valueTraceContinuous,
    data.derivativeTraceDefined,
    data.derivativeTraceContinuous,
    data.crossingAgreementClosed,
    data.kirchhoffConditionClosed⟩

/-- Exact remaining A1.2 target: graph Hilbert/domain readiness for the
    Kirchhoff operator domain. -/
def G8BookIIILemniscateKirchhoffDomainReadinessTarget : Prop :=
  Nonempty G8BookIIILemniscateKirchhoffDomainReadinessData

-- ============================================================
-- GUARDRAILS
-- ============================================================

/-- A non-ready carrier context refutes metric graph readiness data. -/
structure G8BookIIILemniscateMetricGraphNotReady
    (data : G8BookIIILemniscateMetricGraphReadinessData) where
  notReady : ¬ LemniscateCarrierReady data.carrierCtx

/-- Metric graph readiness data cannot coexist with a carrier-readiness
    refuter. -/
theorem G8BookIIILemniscateMetricGraphNotReady.refutes
    {data : G8BookIIILemniscateMetricGraphReadinessData}
    (gap : G8BookIIILemniscateMetricGraphNotReady data) :
    False :=
  gap.notReady data.toCarrierReady

/-- A non-ready Hilbert context refutes Hilbert readiness data. -/
structure G8BookIIILemniscateHilbertNotReady
    (data : G8BookIIILemniscateHilbertReadinessData) where
  notReady : ¬ LemniscateHilbertReady data.hilbertCtx

/-- Hilbert readiness data cannot coexist with a Hilbert-readiness refuter. -/
theorem G8BookIIILemniscateHilbertNotReady.refutes
    {data : G8BookIIILemniscateHilbertReadinessData}
    (gap : G8BookIIILemniscateHilbertNotReady data) :
    False :=
  gap.notReady data.toHilbertReady

/-- A non-ready Kirchhoff domain refutes domain readiness data. -/
structure G8BookIIILemniscateDomainNotReady
    (data : G8BookIIILemniscateKirchhoffDomainReadinessData) where
  notReady : ¬ LemniscateDomainReady data.domainCtx

/-- Domain readiness data cannot coexist with a domain-readiness refuter. -/
theorem G8BookIIILemniscateDomainNotReady.refutes
    {data : G8BookIIILemniscateKirchhoffDomainReadinessData}
    (gap : G8BookIIILemniscateDomainNotReady data) :
    False :=
  gap.notReady data.toDomainReady

end Tau.BookIII.Bridge
