import TauLib.BookIII.Bridge.G8BookIIILemniscateCh23CompactMetricGraphSource

/-!
# TauLib.BookIII.Bridge.G8BookIIILemniscateCh23LoopConstructor

Ch.23-native compact loop constructor for A1.1.

The compact metric graph source introduced the full two-lobe wedge target for

```text
L = S1_B wedge S1_C.
```

This module moves one step lower: it isolates the theorem target for a single
Ch.23 circle lobe as a compact metric loop with a distinguished crossing
basepoint.  Two copies of this loop constructor supply the plus/minus lobe
models consumed by the Ch.23 compact metric graph source.

It does not prove the wedge quotient, shortest-path graph metric, or
topology/metric agreement on `LemniscateCarrier`.  It also does not derive
compactness from the current `TauCirclePoint` scaffold.  Those remain explicit
proof-carrying fields.
-/

set_option autoImplicit false

namespace Tau.BookIII.Bridge

-- ============================================================
-- SINGLE CH.23 LOOP SOURCE
-- ============================================================

/-- A single Ch.23 compact metric loop with a distinguished basepoint.

This is the one-lobe theorem target behind `S1_B` and `S1_C`.  The fields are
the exact topology/metric/compactness data needed to view a lobe as a compact
metric circle, together with the endpoint-identification and shortest-arc
metric evidence used later by the wedge graph. -/
structure G8BookIIICh23CompactLoopConstructor where
  loopCarrier : Type 1
  topology : TopologicalSpace loopCarrier
  metric : MetricSpace loopCarrier
  compact : @CompactSpace loopCarrier topology
  basepoint : loopCarrier
  intervalParameterModel : Prop
  intervalParameterModelEvidence : intervalParameterModel
  endpointsIdentifiedAtBasepoint : Prop
  endpointsIdentifiedAtBasepointEvidence :
    endpointsIdentifiedAtBasepoint
  quotientTopologyIsCircle : Prop
  quotientTopologyIsCircleEvidence : quotientTopologyIsCircle
  shortestArcMetric : Prop
  shortestArcMetricEvidence : shortestArcMetric
  topologyMetricAgreement : Prop
  topologyMetricAgreementEvidence : topologyMetricAgreement
  compactnessFromIntervalQuotient : Prop
  compactnessFromIntervalQuotientEvidence :
    compactnessFromIntervalQuotient
  basepointIsCrossingEndpoint : Prop
  basepointIsCrossingEndpointEvidence : basepointIsCrossingEndpoint
  ch23LoopTheoremBacked : Prop
  ch23LoopTheoremBackedEvidence : ch23LoopTheoremBacked
  status : SpineStatus := .conditional_interface

/-- Target for the one-loop Ch.23 compact metric theorem. -/
def G8BookIIICh23CompactLoopConstructorTarget : Prop :=
  Nonempty G8BookIIICh23CompactLoopConstructor

/-- A compact loop constructor supplies the existing Ch.23 circle-lobe model. -/
def G8BookIIICh23CompactLoopConstructor.toCircleLobeModel
    (loop : G8BookIIICh23CompactLoopConstructor) :
    G8BookIIICh23CircleLobeModel where
  lobeCarrier := loop.loopCarrier
  topology := loop.topology
  metric := loop.metric
  compact := loop.compact
  basepoint := loop.basepoint
  isCircleLobe :=
    loop.intervalParameterModel ∧
      loop.endpointsIdentifiedAtBasepoint ∧
      loop.quotientTopologyIsCircle
  isCircleLobeEvidence :=
    ⟨loop.intervalParameterModelEvidence,
      loop.endpointsIdentifiedAtBasepointEvidence,
      loop.quotientTopologyIsCircleEvidence⟩
  compactMetricCircle :=
    loop.shortestArcMetric ∧
      loop.topologyMetricAgreement ∧
      loop.compactnessFromIntervalQuotient ∧
      loop.ch23LoopTheoremBacked
  compactMetricCircleEvidence :=
    ⟨loop.shortestArcMetricEvidence,
      loop.topologyMetricAgreementEvidence,
      loop.compactnessFromIntervalQuotientEvidence,
      loop.ch23LoopTheoremBackedEvidence⟩
  basepointIsCrossingEndpoint :=
    loop.basepointIsCrossingEndpoint
  basepointIsCrossingEndpointEvidence :=
    loop.basepointIsCrossingEndpointEvidence
  status := loop.status

/-- Target-level adapter from the loop theorem to the lobe-model surface. -/
theorem g8BookIIICh23CompactLoopConstructorTarget_toCircleLobeModel
    (target : G8BookIIICh23CompactLoopConstructorTarget) :
    Nonempty G8BookIIICh23CircleLobeModel := by
  rcases target with ⟨loop⟩
  exact ⟨loop.toCircleLobeModel⟩

-- ============================================================
-- TWO-LOBE LOOP PACKAGE
-- ============================================================

/-- Two Ch.23 compact loops, one for each lemniscate lobe.

This is still below the wedge quotient.  It supplies the plus/minus lobe
models, but it does not identify their basepoints or construct the graph
metric on the wedge. -/
structure G8BookIIICh23TwoLobeLoopConstructor where
  plusLoop : G8BookIIICh23CompactLoopConstructor
  minusLoop : G8BookIIICh23CompactLoopConstructor
  plusRepresentsSector : Prop
  plusRepresentsSectorEvidence : plusRepresentsSector
  minusRepresentsSector : Prop
  minusRepresentsSectorEvidence : minusRepresentsSector
  sectorsAreDistinctLobes : Prop
  sectorsAreDistinctLobesEvidence : sectorsAreDistinctLobes
  status : SpineStatus := .conditional_interface

/-- Target for constructing both Ch.23 lobe loops. -/
def G8BookIIICh23TwoLobeLoopConstructorTarget : Prop :=
  Nonempty G8BookIIICh23TwoLobeLoopConstructor

/-- Plus lobe model selected by a two-lobe loop constructor. -/
def G8BookIIICh23TwoLobeLoopConstructor.plusLobeModel
    (source : G8BookIIICh23TwoLobeLoopConstructor) :
    G8BookIIICh23CircleLobeModel :=
  source.plusLoop.toCircleLobeModel

/-- Minus lobe model selected by a two-lobe loop constructor. -/
def G8BookIIICh23TwoLobeLoopConstructor.minusLobeModel
    (source : G8BookIIICh23TwoLobeLoopConstructor) :
    G8BookIIICh23CircleLobeModel :=
  source.minusLoop.toCircleLobeModel

/-- The two-loop constructor supplies both lobe models needed by the Ch.23
    compact metric graph source. -/
theorem G8BookIIICh23TwoLobeLoopConstructor.toLobeModels
    (source : G8BookIIICh23TwoLobeLoopConstructor) :
    Nonempty (G8BookIIICh23CircleLobeModel ×
      G8BookIIICh23CircleLobeModel) :=
  ⟨(source.plusLobeModel, source.minusLobeModel)⟩

/-- Target-level adapter from the two-loop theorem to the lobe-pair surface. -/
theorem g8BookIIICh23TwoLobeLoopConstructorTarget_toLobeModels
    (target : G8BookIIICh23TwoLobeLoopConstructorTarget) :
    Nonempty (G8BookIIICh23CircleLobeModel ×
      G8BookIIICh23CircleLobeModel) := by
  rcases target with ⟨source⟩
  exact source.toLobeModels

-- ============================================================
-- RELATION TO THE FULL CH.23 WEDGE GRAPH SOURCE
-- ============================================================

/-- A full Ch.23 compact metric graph source can record that its plus/minus
    lobes came from the one-loop constructor.

This is a provenance wrapper only.  The full wedge source still carries the
basepoint identification, quotient-to-carrier realization, graph metric,
compactness, and shortest-path evidence separately. -/
structure G8BookIIICh23LoopBackedCompactMetricGraphSource where
  loops : G8BookIIICh23TwoLobeLoopConstructor
  graph : G8BookIIILemniscateCh23CompactMetricGraphSource
  graph_plus_from_loop :
    graph.plusLobe = loops.plusLobeModel
  graph_minus_from_loop :
    graph.minusLobe = loops.minusLobeModel
  wedgeUsesLoopBasepoints : Prop
  wedgeUsesLoopBasepointsEvidence : wedgeUsesLoopBasepoints
  status : SpineStatus := .conditional_interface

/-- Forget loop provenance and recover the full Ch.23 compact metric graph
    source. -/
def G8BookIIICh23LoopBackedCompactMetricGraphSource.toCh23GraphSource
    (source : G8BookIIICh23LoopBackedCompactMetricGraphSource) :
    G8BookIIILemniscateCh23CompactMetricGraphSource :=
  source.graph

/-- Loop-backed graph provenance supplies the existing Ch.23 graph target. -/
theorem
    G8BookIIICh23LoopBackedCompactMetricGraphSource.toCh23GraphTarget
    (source : G8BookIIICh23LoopBackedCompactMetricGraphSource) :
    G8BookIIILemniscateCh23CompactMetricGraphTarget :=
  ⟨source.toCh23GraphSource⟩

-- ============================================================
-- GUARDRAILS
-- ============================================================

/-- Endpoint interval data alone does not construct a compact metric loop. -/
structure G8BookIIICh23IntervalWithoutCompactMetricLoop where
  intervalParameterModel : Prop
  intervalParameterModelEvidence : intervalParameterModel
  noCompactMetricLoop :
    ¬ G8BookIIICh23CompactLoopConstructorTarget

/-- Interval data refutes the loop target exactly when it records absence of
    the compact metric loop theorem. -/
theorem G8BookIIICh23IntervalWithoutCompactMetricLoop.refutesTarget
    (gap : G8BookIIICh23IntervalWithoutCompactMetricLoop) :
    ¬ G8BookIIICh23CompactLoopConstructorTarget :=
  gap.noCompactMetricLoop

/-- A loop constructor requires endpoint identification at the basepoint. -/
structure G8BookIIICh23LoopMissingEndpointIdentification
    (loop : G8BookIIICh23CompactLoopConstructor) where
  noEndpointIdentification :
    ¬ loop.endpointsIdentifiedAtBasepoint

/-- Missing endpoint identification refutes a loop constructor. -/
theorem G8BookIIICh23LoopMissingEndpointIdentification.refutesLoop
    {loop : G8BookIIICh23CompactLoopConstructor}
    (gap : G8BookIIICh23LoopMissingEndpointIdentification loop) :
    False :=
  gap.noEndpointIdentification loop.endpointsIdentifiedAtBasepointEvidence

/-- A loop constructor requires its shortest-arc metric evidence. -/
structure G8BookIIICh23LoopMissingShortestArcMetric
    (loop : G8BookIIICh23CompactLoopConstructor) where
  noShortestArcMetric : ¬ loop.shortestArcMetric

/-- Missing shortest-arc metric evidence refutes a loop constructor. -/
theorem G8BookIIICh23LoopMissingShortestArcMetric.refutesLoop
    {loop : G8BookIIICh23CompactLoopConstructor}
    (gap : G8BookIIICh23LoopMissingShortestArcMetric loop) :
    False :=
  gap.noShortestArcMetric loop.shortestArcMetricEvidence

/-- Two constructed loops without the wedge theorem still do not construct the
    full Ch.23 compact metric graph. -/
structure G8BookIIICh23TwoLoopsWithoutWedgeGraph where
  loops : G8BookIIICh23TwoLobeLoopConstructor
  noCh23Graph : ¬ G8BookIIILemniscateCh23CompactMetricGraphTarget

/-- Two compact metric loops alone refute the graph target exactly when the
    wedge graph theorem is absent. -/
theorem G8BookIIICh23TwoLoopsWithoutWedgeGraph.refutesGraphTarget
    (gap : G8BookIIICh23TwoLoopsWithoutWedgeGraph) :
    ¬ G8BookIIILemniscateCh23CompactMetricGraphTarget :=
  gap.noCh23Graph

end Tau.BookIII.Bridge
