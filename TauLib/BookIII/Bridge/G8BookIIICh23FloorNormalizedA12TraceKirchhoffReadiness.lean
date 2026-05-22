import TauLib.BookIII.Bridge.G8BookIIICh23FloorNormalizedA12HilbertL2Readiness

/-!
# G8 Book III Ch.23 Floor-Normalized A1.2 Trace/Kirchhoff Readiness

This module closes the selected-carrier A1.2 trace and Kirchhoff-domain layer
over the theorem-backed Hilbert/L2 readiness source.

The construction remains selected-carrier native:

```text
closed graph measure
  -> closed Hilbert/L2 readiness
  -> value/derivative trace readiness
  -> crossing agreement closure
  -> Kirchhoff derivative-balance closure
  -> selected A1.2 Hilbert/domain source
```

It does not define the graph Laplacian or prove self-adjointness.  Those begin
with the next A1.3/A1.4 operator-theory layers.
-/

set_option autoImplicit false

namespace Tau.BookIII.Bridge

-- ============================================================
-- CLOSED SELECTED HILBERT READINESS
-- ============================================================

/-- A Hilbert-readiness source is the closed selected Ch.23 Hilbert/L2 source. -/
def G8BookIIICh23FloorNormalizedA12ClosedSelectedHilbertReadiness
    (hilbert : G8BookIIICh23FloorNormalizedA12HilbertReadinessSource) :
    Prop :=
  hilbert = g8BookIIICh23FloorNormalizedA12HilbertReadinessSource_closed

/-- The closed Hilbert-readiness source is selected by definition. -/
theorem
    g8BookIIICh23FloorNormalizedA12ClosedSelectedHilbertReadiness_closed :
    G8BookIIICh23FloorNormalizedA12ClosedSelectedHilbertReadiness
      g8BookIIICh23FloorNormalizedA12HilbertReadinessSource_closed :=
  rfl

-- ============================================================
-- SOBELEV VALUE/DERIVATIVE TRACE READINESS LAWS
-- ============================================================

/-- Value traces are defined on the selected Hilbert graph substrate. -/
def G8BookIIICh23FloorNormalizedA12ValueTraceDefined
    (hilbert : G8BookIIICh23FloorNormalizedA12HilbertReadinessSource) :
    Prop :=
  G8BookIIICh23FloorNormalizedA12ClosedSelectedHilbertReadiness
      hilbert ∧
    hilbert.traceMapDefined

/-- Value trace continuity is the Hilbert-level trace continuity together with
    finite selected graph length and zero crossing atom. -/
def G8BookIIICh23FloorNormalizedA12ValueTraceContinuous
    (hilbert : G8BookIIICh23FloorNormalizedA12HilbertReadinessSource) :
    Prop :=
  G8BookIIICh23FloorNormalizedA12ClosedSelectedHilbertReadiness
      hilbert ∧
    hilbert.traceMapContinuous ∧
    hilbert.measure.totalFinite ∧
    hilbert.measure.crossingAtomPolicy

/-- Derivative traces are defined from the transported Ch.23 graph metric and
    the selected two-lobe length measure. -/
def G8BookIIICh23FloorNormalizedA12DerivativeTraceDefined
    (hilbert : G8BookIIICh23FloorNormalizedA12HilbertReadinessSource) :
    Prop :=
  G8BookIIICh23FloorNormalizedA12ClosedSelectedHilbertReadiness
      hilbert ∧
    G8BookIIICh23FloorNormalizedGraphDistanceRealizesMetric
      hilbert.measure.graph.concrete ∧
    hilbert.measure.graphMeasureFromTwoLobeLength

/-- Derivative trace continuity is recorded at the selected compact finite
    graph level, where topology/metric agreement and L2 completion are already
    theorem-backed. -/
def G8BookIIICh23FloorNormalizedA12DerivativeTraceContinuous
    (hilbert : G8BookIIICh23FloorNormalizedA12HilbertReadinessSource) :
    Prop :=
  G8BookIIICh23FloorNormalizedA12ClosedSelectedHilbertReadiness
      hilbert ∧
    hilbert.traceMapContinuous ∧
    hilbert.measure.totalFinite ∧
    G8BookIIICh23FloorNormalizedTopologyMetricAgreement
      hilbert.measure.graph.concrete ∧
    hilbert.l2CompletionFromGraphMeasure

/-- The selected Sobolev trace theorem package needed by the A1.2 domain
    source: value traces, derivative traces, continuity, and the closed L2
    completion all agree on the selected graph measure. -/
def G8BookIIICh23FloorNormalizedA12SobolevTraceReadiness
    (hilbert : G8BookIIICh23FloorNormalizedA12HilbertReadinessSource) :
    Prop :=
  G8BookIIICh23FloorNormalizedA12ValueTraceDefined hilbert ∧
    G8BookIIICh23FloorNormalizedA12ValueTraceContinuous hilbert ∧
    G8BookIIICh23FloorNormalizedA12DerivativeTraceDefined hilbert ∧
    G8BookIIICh23FloorNormalizedA12DerivativeTraceContinuous hilbert

-- ============================================================
-- CLOSED TRACE LAW WITNESSES
-- ============================================================

theorem
    g8BookIIICh23FloorNormalizedA12ValueTraceDefined_closed :
    G8BookIIICh23FloorNormalizedA12ValueTraceDefined
      g8BookIIICh23FloorNormalizedA12HilbertReadinessSource_closed :=
  ⟨rfl,
    g8BookIIICh23FloorNormalizedA12HilbertReadinessSource_closed
      |>.traceMapDefinedWitness⟩

theorem
    g8BookIIICh23FloorNormalizedA12ValueTraceContinuous_closed :
    G8BookIIICh23FloorNormalizedA12ValueTraceContinuous
      g8BookIIICh23FloorNormalizedA12HilbertReadinessSource_closed :=
  ⟨rfl,
    g8BookIIICh23FloorNormalizedA12HilbertReadinessSource_closed
      |>.traceMapContinuousWitness,
    g8BookIIICh23FloorNormalizedA12HilbertReadinessSource_closed
      |>.measure
      |>.totalFiniteWitness,
    g8BookIIICh23FloorNormalizedA12HilbertReadinessSource_closed
      |>.measure
      |>.crossingAtomPolicyWitness⟩

theorem
    g8BookIIICh23FloorNormalizedA12DerivativeTraceDefined_closed :
    G8BookIIICh23FloorNormalizedA12DerivativeTraceDefined
      g8BookIIICh23FloorNormalizedA12HilbertReadinessSource_closed :=
  ⟨rfl,
    g8BookIIICh23FloorNormalizedA12HilbertReadinessSource_closed
      |>.measure
      |>.graph
      |>.graphDistanceRealizesMetric,
    g8BookIIICh23FloorNormalizedA12HilbertReadinessSource_closed
      |>.measure
      |>.graphMeasureFromTwoLobeLengthEvidence⟩

theorem
    g8BookIIICh23FloorNormalizedA12DerivativeTraceContinuous_closed :
    G8BookIIICh23FloorNormalizedA12DerivativeTraceContinuous
      g8BookIIICh23FloorNormalizedA12HilbertReadinessSource_closed :=
  ⟨rfl,
    g8BookIIICh23FloorNormalizedA12HilbertReadinessSource_closed
      |>.traceMapContinuousWitness,
    g8BookIIICh23FloorNormalizedA12HilbertReadinessSource_closed
      |>.measure
      |>.totalFiniteWitness,
    g8BookIIICh23FloorNormalizedA12HilbertReadinessSource_closed
      |>.measure
      |>.graph
      |>.topologyMetricAgreement,
    g8BookIIICh23FloorNormalizedA12HilbertReadinessSource_closed
      |>.l2CompletionFromGraphMeasureEvidence⟩

theorem
    g8BookIIICh23FloorNormalizedA12SobolevTraceReadiness_closed :
    G8BookIIICh23FloorNormalizedA12SobolevTraceReadiness
      g8BookIIICh23FloorNormalizedA12HilbertReadinessSource_closed :=
  ⟨g8BookIIICh23FloorNormalizedA12ValueTraceDefined_closed,
    g8BookIIICh23FloorNormalizedA12ValueTraceContinuous_closed,
    g8BookIIICh23FloorNormalizedA12DerivativeTraceDefined_closed,
    g8BookIIICh23FloorNormalizedA12DerivativeTraceContinuous_closed⟩

-- ============================================================
-- CLOSED TRACE READINESS SOURCE
-- ============================================================

/-- Closed trace-readiness source over the selected floor-normalized graph. -/
noncomputable def
    g8BookIIICh23FloorNormalizedA12TraceReadinessSource_closed :
    G8BookIIICh23FloorNormalizedA12TraceReadinessSource where
  hilbert := g8BookIIICh23FloorNormalizedA12HilbertReadinessSource_closed
  valueTraceDefined :=
    G8BookIIICh23FloorNormalizedA12ValueTraceDefined
      g8BookIIICh23FloorNormalizedA12HilbertReadinessSource_closed
  valueTraceDefinedWitness :=
    g8BookIIICh23FloorNormalizedA12ValueTraceDefined_closed
  valueTraceContinuous :=
    G8BookIIICh23FloorNormalizedA12ValueTraceContinuous
      g8BookIIICh23FloorNormalizedA12HilbertReadinessSource_closed
  valueTraceContinuousWitness :=
    g8BookIIICh23FloorNormalizedA12ValueTraceContinuous_closed
  derivativeTraceDefined :=
    G8BookIIICh23FloorNormalizedA12DerivativeTraceDefined
      g8BookIIICh23FloorNormalizedA12HilbertReadinessSource_closed
  derivativeTraceDefinedWitness :=
    g8BookIIICh23FloorNormalizedA12DerivativeTraceDefined_closed
  derivativeTraceContinuous :=
    G8BookIIICh23FloorNormalizedA12DerivativeTraceContinuous
      g8BookIIICh23FloorNormalizedA12HilbertReadinessSource_closed
  derivativeTraceContinuousWitness :=
    g8BookIIICh23FloorNormalizedA12DerivativeTraceContinuous_closed
  sobolevTraceTheorem :=
    G8BookIIICh23FloorNormalizedA12SobolevTraceReadiness
      g8BookIIICh23FloorNormalizedA12HilbertReadinessSource_closed
  sobolevTraceTheoremWitness :=
    g8BookIIICh23FloorNormalizedA12SobolevTraceReadiness_closed
  status := .conditional_interface

/-- The selected-carrier trace-readiness target is closed. -/
theorem
    g8BookIIICh23FloorNormalizedA12TraceReadinessTarget_closed :
    G8BookIIICh23FloorNormalizedA12TraceReadinessTarget :=
  g8BookIIICh23FloorNormalizedA12TraceReadinessSource_closed.toTarget

-- ============================================================
-- CROSSING AND KIRCHHOFF CLOSURE LAWS
-- ============================================================

/-- A trace-readiness source is the closed selected trace package. -/
def G8BookIIICh23FloorNormalizedA12ClosedSelectedTraceReadiness
    (trace : G8BookIIICh23FloorNormalizedA12TraceReadinessSource) :
    Prop :=
  trace = g8BookIIICh23FloorNormalizedA12TraceReadinessSource_closed

/-- Crossing agreement is closed by value trace continuity, quotient
    identification with the concrete wedge, and the zero crossing atom. -/
def G8BookIIICh23FloorNormalizedA12CrossingAgreementClosed
    (trace : G8BookIIICh23FloorNormalizedA12TraceReadinessSource) :
    Prop :=
  G8BookIIICh23FloorNormalizedA12ClosedSelectedTraceReadiness trace ∧
    trace.valueTraceContinuous ∧
    G8BookIIICh23FloorNormalizedQuotientMatchesConcrete ∧
    trace.hilbert.measure.crossingAtomPolicy

/-- Kirchhoff derivative-balance closure is the derivative trace law together
    with B/C lobe-length agreement on the selected graph measure. -/
def G8BookIIICh23FloorNormalizedA12KirchhoffConditionClosed
    (trace : G8BookIIICh23FloorNormalizedA12TraceReadinessSource) :
    Prop :=
  G8BookIIICh23FloorNormalizedA12ClosedSelectedTraceReadiness trace ∧
    trace.derivativeTraceContinuous ∧
    trace.hilbert.measure.lobeMeasureAgreement ∧
    G8BookIIICh23FloorNormalizedGraphDistanceRealizesMetric
      trace.hilbert.measure.graph.concrete

/-- Crossing closure follows from the basepoint value trace package. -/
def G8BookIIICh23FloorNormalizedA12CrossingClosureFromBasepointTrace
    (trace : G8BookIIICh23FloorNormalizedA12TraceReadinessSource) :
    Prop :=
  G8BookIIICh23FloorNormalizedA12CrossingAgreementClosed trace ∧
    trace.valueTraceDefined ∧
    trace.valueTraceContinuous

/-- Kirchhoff closure follows from outgoing derivative-balance trace data. -/
def
    G8BookIIICh23FloorNormalizedA12KirchhoffClosureFromOutgoingDerivativeBalance
    (trace : G8BookIIICh23FloorNormalizedA12TraceReadinessSource) :
    Prop :=
  G8BookIIICh23FloorNormalizedA12KirchhoffConditionClosed trace ∧
    trace.derivativeTraceDefined ∧
    trace.derivativeTraceContinuous

-- ============================================================
-- CLOSED KIRCHHOFF LAW WITNESSES
-- ============================================================

theorem
    g8BookIIICh23FloorNormalizedA12ClosedSelectedTraceReadiness_closed :
    G8BookIIICh23FloorNormalizedA12ClosedSelectedTraceReadiness
      g8BookIIICh23FloorNormalizedA12TraceReadinessSource_closed :=
  rfl

theorem
    g8BookIIICh23FloorNormalizedA12CrossingAgreementClosed_closed :
    G8BookIIICh23FloorNormalizedA12CrossingAgreementClosed
      g8BookIIICh23FloorNormalizedA12TraceReadinessSource_closed :=
  ⟨rfl,
    g8BookIIICh23FloorNormalizedA12TraceReadinessSource_closed
      |>.valueTraceContinuousWitness,
    g8BookIIICh23FloorNormalizedA12TraceReadinessSource_closed
      |>.hilbert
      |>.measure
      |>.graph
      |>.quotientMatchesConcrete,
    g8BookIIICh23FloorNormalizedA12TraceReadinessSource_closed
      |>.hilbert
      |>.measure
      |>.crossingAtomPolicyWitness⟩

theorem
    g8BookIIICh23FloorNormalizedA12KirchhoffConditionClosed_closed :
    G8BookIIICh23FloorNormalizedA12KirchhoffConditionClosed
      g8BookIIICh23FloorNormalizedA12TraceReadinessSource_closed :=
  ⟨rfl,
    g8BookIIICh23FloorNormalizedA12TraceReadinessSource_closed
      |>.derivativeTraceContinuousWitness,
    g8BookIIICh23FloorNormalizedA12TraceReadinessSource_closed
      |>.hilbert
      |>.measure
      |>.lobeMeasureAgreementWitness,
    g8BookIIICh23FloorNormalizedA12TraceReadinessSource_closed
      |>.hilbert
      |>.measure
      |>.graph
      |>.graphDistanceRealizesMetric⟩

theorem
    g8BookIIICh23FloorNormalizedA12CrossingClosureFromBasepointTrace_closed :
    G8BookIIICh23FloorNormalizedA12CrossingClosureFromBasepointTrace
      g8BookIIICh23FloorNormalizedA12TraceReadinessSource_closed :=
  ⟨g8BookIIICh23FloorNormalizedA12CrossingAgreementClosed_closed,
    g8BookIIICh23FloorNormalizedA12TraceReadinessSource_closed
      |>.valueTraceDefinedWitness,
    g8BookIIICh23FloorNormalizedA12TraceReadinessSource_closed
      |>.valueTraceContinuousWitness⟩

theorem
    g8BookIIICh23FloorNormalizedA12KirchhoffClosureFromOutgoingDerivativeBalance_closed :
    G8BookIIICh23FloorNormalizedA12KirchhoffClosureFromOutgoingDerivativeBalance
      g8BookIIICh23FloorNormalizedA12TraceReadinessSource_closed :=
  ⟨g8BookIIICh23FloorNormalizedA12KirchhoffConditionClosed_closed,
    g8BookIIICh23FloorNormalizedA12TraceReadinessSource_closed
      |>.derivativeTraceDefinedWitness,
    g8BookIIICh23FloorNormalizedA12TraceReadinessSource_closed
      |>.derivativeTraceContinuousWitness⟩

-- ============================================================
-- CLOSED SELECTED KIRCHHOFF DOMAIN SOURCE
-- ============================================================

/-- Closed Kirchhoff-domain readiness source over the selected graph. -/
noncomputable def
    g8BookIIICh23FloorNormalizedA12KirchhoffDomainSource_closed :
    G8BookIIICh23FloorNormalizedA12KirchhoffDomainSource where
  trace := g8BookIIICh23FloorNormalizedA12TraceReadinessSource_closed
  crossingAgreementClosed :=
    G8BookIIICh23FloorNormalizedA12CrossingAgreementClosed
      g8BookIIICh23FloorNormalizedA12TraceReadinessSource_closed
  crossingAgreementClosedWitness :=
    g8BookIIICh23FloorNormalizedA12CrossingAgreementClosed_closed
  kirchhoffConditionClosed :=
    G8BookIIICh23FloorNormalizedA12KirchhoffConditionClosed
      g8BookIIICh23FloorNormalizedA12TraceReadinessSource_closed
  kirchhoffConditionClosedWitness :=
    g8BookIIICh23FloorNormalizedA12KirchhoffConditionClosed_closed
  crossingClosureFromBasepointTrace :=
    G8BookIIICh23FloorNormalizedA12CrossingClosureFromBasepointTrace
      g8BookIIICh23FloorNormalizedA12TraceReadinessSource_closed
  crossingClosureFromBasepointTraceWitness :=
    g8BookIIICh23FloorNormalizedA12CrossingClosureFromBasepointTrace_closed
  kirchhoffClosureFromOutgoingDerivativeBalance :=
    G8BookIIICh23FloorNormalizedA12KirchhoffClosureFromOutgoingDerivativeBalance
      g8BookIIICh23FloorNormalizedA12TraceReadinessSource_closed
  kirchhoffClosureFromOutgoingDerivativeBalanceWitness :=
    g8BookIIICh23FloorNormalizedA12KirchhoffClosureFromOutgoingDerivativeBalance_closed
  status := .conditional_interface

/-- The selected-carrier Kirchhoff-domain target is closed. -/
theorem
    g8BookIIICh23FloorNormalizedA12KirchhoffDomainTarget_closed :
    G8BookIIICh23FloorNormalizedA12KirchhoffDomainTarget :=
  g8BookIIICh23FloorNormalizedA12KirchhoffDomainSource_closed.toTarget

/-- Closed selected-carrier A1.2 Hilbert/domain source. -/
noncomputable def
    g8BookIIICh23FloorNormalizedA12HilbertDomainSource_closed :
    G8BookIIICh23FloorNormalizedA12HilbertDomainSource where
  domain := g8BookIIICh23FloorNormalizedA12KirchhoffDomainSource_closed
  graphMeasureIsSelectedLength :=
    g8BookIIICh23FloorNormalizedA12KirchhoffDomainSource_closed
      |>.trace
      |>.hilbert
      |>.measure
      |>.graphMeasureFromTwoLobeLengthEvidence
  hilbertBuiltFromSelectedGraph :=
    g8BookIIICh23FloorNormalizedA12KirchhoffDomainSource_closed
      |>.trace
      |>.hilbert
      |>.l2CompletionFromGraphMeasureEvidence
  traceBuiltFromSelectedSobolevTheory :=
    g8BookIIICh23FloorNormalizedA12KirchhoffDomainSource_closed
      |>.trace
      |>.sobolevTraceTheoremWitness
  kirchhoffBuiltFromSelectedTrace :=
    ⟨g8BookIIICh23FloorNormalizedA12KirchhoffDomainSource_closed
        |>.crossingClosureFromBasepointTraceWitness,
      g8BookIIICh23FloorNormalizedA12KirchhoffDomainSource_closed
        |>.kirchhoffClosureFromOutgoingDerivativeBalanceWitness⟩
  status := .conditional_interface

/-- The selected-carrier A1.2 Hilbert/domain source target is closed. -/
theorem
    g8BookIIICh23FloorNormalizedA12HilbertDomainSourceTarget_closed :
    G8BookIIICh23FloorNormalizedA12HilbertDomainSourceTarget :=
  g8BookIIICh23FloorNormalizedA12HilbertDomainSource_closed.toTarget

-- ============================================================
-- GUARDRAILS
-- ============================================================

/-- A trace package not sourced from the closed selected Hilbert readiness
    cannot be used as the selected Sobolev trace package. -/
structure G8BookIIICh23FloorNormalizedA12TraceWithoutClosedHilbert
    (hilbert : G8BookIIICh23FloorNormalizedA12HilbertReadinessSource) where
  notClosed :
    ¬ G8BookIIICh23FloorNormalizedA12ClosedSelectedHilbertReadiness
      hilbert

theorem
    G8BookIIICh23FloorNormalizedA12TraceWithoutClosedHilbert.refutesValueTrace
    {hilbert : G8BookIIICh23FloorNormalizedA12HilbertReadinessSource}
    (gap :
      G8BookIIICh23FloorNormalizedA12TraceWithoutClosedHilbert
        hilbert) :
    ¬ G8BookIIICh23FloorNormalizedA12ValueTraceDefined hilbert := by
  intro h
  exact gap.notClosed h.1

theorem
    G8BookIIICh23FloorNormalizedA12TraceWithoutClosedHilbert.refutesDerivativeTrace
    {hilbert : G8BookIIICh23FloorNormalizedA12HilbertReadinessSource}
    (gap :
      G8BookIIICh23FloorNormalizedA12TraceWithoutClosedHilbert
        hilbert) :
    ¬ G8BookIIICh23FloorNormalizedA12DerivativeTraceDefined hilbert := by
  intro h
  exact gap.notClosed h.1

/-- Kirchhoff closure requires the closed selected trace package, not merely a
    Hilbert/L2 source. -/
structure G8BookIIICh23FloorNormalizedA12KirchhoffWithoutClosedTrace
    (trace : G8BookIIICh23FloorNormalizedA12TraceReadinessSource) where
  notClosed :
    ¬ G8BookIIICh23FloorNormalizedA12ClosedSelectedTraceReadiness
      trace

theorem
    G8BookIIICh23FloorNormalizedA12KirchhoffWithoutClosedTrace.refutesCrossing
    {trace : G8BookIIICh23FloorNormalizedA12TraceReadinessSource}
    (gap :
      G8BookIIICh23FloorNormalizedA12KirchhoffWithoutClosedTrace trace) :
    ¬ G8BookIIICh23FloorNormalizedA12CrossingAgreementClosed trace := by
  intro h
  exact gap.notClosed h.1

theorem
    G8BookIIICh23FloorNormalizedA12KirchhoffWithoutClosedTrace.refutesKirchhoff
    {trace : G8BookIIICh23FloorNormalizedA12TraceReadinessSource}
    (gap :
      G8BookIIICh23FloorNormalizedA12KirchhoffWithoutClosedTrace trace) :
    ¬ G8BookIIICh23FloorNormalizedA12KirchhoffConditionClosed trace := by
  intro h
  exact gap.notClosed h.1

end Tau.BookIII.Bridge
