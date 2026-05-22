# G8 Lane A A1/A2 Proof-Step Ledger

Private working ledger for the A1/A2 operator self-adjoint route.

Readable current version: `docs/g8-lane-a-a1-a2-proof-step-ledger-v2.md`.
This original file is retained as the detailed historical trace.

This document tracks the ten proof-map steps from
`docs/g8-lane-a-a1-a2-operator-self-adjoint-proof-map.tex` against the current
Lean implementation. It is an unofficial proof-obligation ledger, not a new
formal axiom file. The official Lane A axiom ledger remains unchanged until a
step has an actual theorem-backed constructor.

## Scope

The A1/A2 target is:

```text
compact Kirchhoff lemniscate metric-graph operator
  -> LemniscateOperatorReady
  -> operator-native analytic point-spectrum provenance
  -> G8LaneAOperatorNativeSelfAdjointSource
```

This ledger is A1/A2 only. It does not use A3 canonical actual-xi membership,
accepted coverage, determinant transfer, O3, divisor transfer, completion
uniqueness, final live hinge, or any RH discharge module.

## Status Legend

- `Closed adapter`: the Lean wrapper/adapter is theorem-backed once its input
  package is supplied.
- `Interface landed`: the exact proof-carrying target exists, but the
  mathematical constructor is still a live obligation.
- `Open payload`: the actual analytic/operator theorem still needs to be
  formalized.

## Current Lean Anchors

- Proof-map source packages:
  `TauLib.BookIII.Bridge.G8BookIIILaneAOperatorSelfAdjointProofSource`
- Low-level graph/domain core:
  `TauLib.BookIII.Bridge.G8BookIIILemniscateGraphDomainCore`
- Compact metric graph package:
  `TauLib.BookIII.Bridge.G8BookIIILemniscateCompactMetricGraphPackage`
- Compact metric graph realization surface:
  `TauLib.BookIII.Bridge.G8BookIIILemniscateCompactMetricGraphRealization`
- TauProfinite compact metric reuse corridor:
  `TauLib.BookIII.Bridge.G8BookIIILemniscateTauProfiniteCompactMetricSource`
- TauProfinite lobe/wedge and Hilbert/domain transfer surface:
  `TauLib.BookIII.Bridge.G8BookIIILemniscateTauProfiniteHilbertDomainTransfer`
- Three-target compression/coherence layer:
  `TauLib.BookIII.Bridge.G8BookIIILemniscateTauProfiniteA1A2TargetCompression`
- Ch.23-native compact metric graph source:
  `TauLib.BookIII.Bridge.G8BookIIILemniscateCh23CompactMetricGraphSource`
- Ch.23-native compact loop/lobe constructor:
  `TauLib.BookIII.Bridge.G8BookIIILemniscateCh23LoopConstructor`
- Theorem-backed `UnitAddCircle` Ch.23 loop constructor:
  `TauLib.BookIII.Bridge.G8BookIIICh23UnitAddCircleLoopConstructor`
- Concrete `UnitAddCircle` Ch.23 wedge graph constructor:
  `TauLib.BookIII.Bridge.G8BookIIICh23UnitAddCircleWedgeGraphConstructor`
- Theorem-backed raw compact two-lobe model for that wedge:
  `TauLib.BookIII.Bridge.G8BookIIICh23UnitAddCircleRawCompactWedgeModel`
- Theorem-backed quotient topology and compactness for the concrete wedge:
  `TauLib.BookIII.Bridge.G8BookIIICh23UnitAddCircleQuotientCompactTopology`
- Theorem-backed Mathlib glued-metric source for the concrete wedge:
  `TauLib.BookIII.Bridge.G8BookIIICh23UnitAddCircleGluedMetricSource`
- Theorem-backed quotient-carrier-to-glued-metric map source:
  `TauLib.BookIII.Bridge.G8BookIIICh23UnitAddCircleGlueQuotientMap`
- Split concrete-to-tau-native bridge source:
  `TauLib.BookIII.Bridge.G8BookIIICh23UnitAddCircleTauNativeBridgeSource`
- A1.1 concrete-to-tau-native closure assembly:
  `TauLib.BookIII.Bridge.G8BookIIICh23UnitAddCircleTauNativeA11Closure`
- A1.1 tau-circle parametrization reality check:
  `TauLib.BookIII.Bridge.G8BookIIICh23TauCircleParametrizationCompletenessRealityCheck`
- A1.1 Cauchy-parametrized angle-period source:
  `TauLib.BookIII.Bridge.G8BookIIICh23UnitAddCircleCauchyParametrizedAngleSource`
- A1.1 real-Ico Cauchy angle readout split:
  `TauLib.BookIII.Bridge.G8BookIIICh23UnitAddCircleRealIcoCauchyAngleReadout`
- A1.1 real-Ico bounded tau representative source:
  `TauLib.BookIII.Bridge.G8BookIIICh23RealIcoBoundedTauLiftSource`
- A1.1 theorem-backed floor bounded tau representatives:
  `TauLib.BookIII.Bridge.G8BookIIICh23RealIcoFloorBoundedTauRepresentative`
- Proof-step aliases and wrappers:
  `TauLib.BookIII.Bridge.G8BookIIILaneAOperatorSelfAdjointProofSteps`
- Strict A2 provenance surface:
  `TauLib.BookIII.Bridge.G8LaneAOperatorNativeSelfAdjointSource`
- Official weak Lane A ledger:
  `TauLib.BookIII.Bridge.G8LaneAAxiomLedger`

## Ten-Step Ledger

| Step | Proof-map obligation | Lean surface now present | Current status | What remains to discharge |
| --- | --- | --- | --- | --- |
| A1.1 | Construct the lemniscate metric graph `L = S^1_B vee S^1_C`. | `G8BookIIILemniscateTwoLobeWedgeCore`; `g8BookIIILemniscateTwoLobeWedgeCore_closed`; `G8BookIIILemniscateCompactMetricGraphPackage`; `G8BookIIILemniscateTauNativeCompactMetricGraphRealizationSource`; `g8BookIIILemniscateTauNativeCompactMetricGraphRealizationTarget_iff_packageTarget`; `G8BookIIICh23CompactLoopConstructor`; `G8BookIIICh23TwoLobeLoopConstructor`; `G8BookIIICh23TwoLobeLoopConstructorTarget`; `g8BookIIICh23CompactLoopConstructorTarget_unitAddCircle`; `g8BookIIICh23TwoLobeLoopConstructorTarget_unitAddCircle`; `G8BookIIICh23UnitAddCircleWedgeCore`; `g8BookIIICh23UnitAddCircleWedgeCore_closed`; `G8BookIIICh23UnitAddCircleRawCompactWedgeModelTarget`; `g8BookIIICh23UnitAddCircleRawCompactWedgeModel_closed`; `G8BookIIICh23UnitAddCircleQuotientCompactTopologyTarget`; `g8BookIIICh23UnitAddCircleQuotientCompactTopology_closed`; `G8BookIIICh23UnitAddCircleGluedMetricGraphTarget`; `g8BookIIICh23UnitAddCircleGluedMetricGraph_closed`; `G8BookIIICh23UnitAddCircleGlueQuotientMapTarget`; `g8BookIIICh23UnitAddCircleGlueQuotientMap_closed`; `G8BookIIICh23UnitAddCircleGlueQuotientInjectivityTarget`; `g8BookIIICh23UnitAddCircleGlueQuotientInjectivity_closed`; `G8BookIIICh23UnitAddCircleGlueQuotientMetricTransferFromInjectiveTarget`; `g8BookIIICh23UnitAddCircleGlueQuotientMetricTransferFromInjective_closed`; `G8BookIIICh23UnitAddCircleGlueToQuotientMetricTransferTarget`; `G8BookIIICh23ConcreteCompactMetricGraphTarget`; `g8BookIIICh23ConcreteCompactMetricGraphTarget_from_glueQuotientMetricTransfer`; `G8BookIIICh23UnitAddCircleTauCircleLobeEquivalence`; `G8BookIIICh23UnitAddCircleTauNativeQuotientBridgeTarget`; `G8BookIIICh23UnitAddCircleTauNativeMetricTransferTarget`; `G8BookIIICh23UnitAddCircleTauNativeA11ClosureTarget`; `g8BookIIICh23UnitAddCircleTauNativeA11ClosureTarget_of_lobeEquivalence`; `g8BookIIICh23TauCircleParametrizationCompletenessTarget_toA11ClosureTarget`; `G8BookIIICh23TauCircleRawStatusFiberGuardrail`; `g8BookIIICh23TauCircleStatusCanonicalParametrizationSource_refutesRawSurjectivity`; `TauCircleCauchyParametrizedCanonicalPoint`; `G8BookIIICh23TauCircleParametrizedCauchyComplete`; `G8BookIIICh23UnitAddCircleCauchyAnglePeriodSource`; `g8BookIIICh23UnitAddCircleCauchyAnglePeriodSourceTarget_toParametrizedTarget`; `G8BookIIICh23UnitAddCircleWedgeTauNativeBridgeTarget`; `G8BookIIILemniscateCh23CompactMetricGraphSource`; `G8BookIIILemniscateCh23CompactMetricGraphTarget`; `G8TauProfiniteCompactMetricSubstrate`; `g8TauProfiniteCompactMetricSubstrate_closed`; `G8BookIIILemniscateTauProfiniteCompactMetricCorridor`; `G8BookIIILemniscateTauProfiniteLobeIdentificationSource`; `G8BookIIILemniscateTauProfiniteWedgeTransferSource`; `G8BookIIILemniscateTauProfiniteA1A2ThreeTargetPackage`. | Raw tau-native wedge closed; Ch.23 one-loop and two-loop constructor targets are theorem-backed by `UnitAddCircle`; concrete `UnitAddCircle` wedge quotient core, raw compact two-lobe model, quotient topology/compactness, Mathlib glued metric model, quotient-to-glue map, injectivity, induced quotient metric transfer, lobe isometries, topology/metric embedding, graph-distance realization, and the concrete compact metric graph target are theorem-backed. Conditional on a basepoint-preserving `UnitAddCircle`/`TauCirclePoint` lobe equivalence, tau-native topology, metric, compactness, topology/metric agreement, graph-distance realization, and the A1.1 closure/package targets are theorem-backed by transfer. The reality-check module proves the current raw `TauCirclePoint` carrier has noncanonical status fibers, so a semantic parametrization whose image is only canonical tau-cis/status data cannot be surjective onto the raw carrier. The real-Ico bounded representative source is now theorem-backed by floor-grid rational Cauchy representatives, so the controlled lift target is closed. The Cauchy-parametrized source now theorem-backs the remaining inverse corridor: a period inverse on these Cauchy bounded-angle representatives upgrades to the existing parametrized source exactly when `G8BookIIICh23TauCircleParametrizedCauchyComplete` is supplied. TauProfinite compact metric substrate remains compatibility scaffolding. | Concrete Ch.23 graph side and the lobe-equivalence-to-A1.1 transfer are closed. The remaining A1.1 load-bearing theorem is now sharpened: prove the Cauchy bounded-angle period readout and Cauchy completeness for the parametrized canonical tau-circle lobe, then either canonicalize/quotient the tau-circle lobe carrier and prove the basepoint-preserving `UnitAddCircle` equivalence there, or prove a genuine raw-carrier encoding theorem that accounts for all `TauCirclePoint` presentation fibers. A plain semantic `cis` parametrization is theorem-backed insufficient for `G8BookIIICh23TauCircleParametrizationCompletenessTarget`. |
| A1.2 | Construct the Hilbert space and Sobolev/Kirchhoff domain. | `G8BookIIILemniscateHilbertReadinessData`; `G8BookIIILemniscateKirchhoffDomainReadinessData`; `toHilbertReady`; `toDomainReady`; `toHilbertDomainSource`; `G8BookIIILemniscateTauProfiniteHilbertDomainTransferSource`; `g8BookIIILemniscateTauProfiniteA1A2ThreeTarget_iff_domainTransferTarget`. | Interface landed; graph-measure/L2/Sobolev-domain transfer from the profinite compact graph corridor is now explicitly surfaced; the three recommended targets compress to the Hilbert/domain transfer target because it contains the coherent graph and lobe sources. | Prove graph measure transfer, total finite measure, lobe measure agreement, inner-product readiness, value/derivative trace continuity, crossing closure, and Kirchhoff closure for the graph domain. |
| A1.3 | Define the graph Laplacian `H_L = -d^2/dx^2` on the Kirchhoff domain. | `G8BookIIIKirchhoffLaplacianSource`; `G8BookIIIKirchhoffLaplacianConstructionTarget`; `toDomainReady`. | Interface landed. | Replace the proof-carrying fields with the analytic edgewise Kirchhoff Laplacian construction. |
| A1.4 | Prove symmetry by boundary-form cancellation. | `G8BookIIIBoundaryFormCancellationTarget`; `boundaryFormCancellationTarget`. | Interface landed. | Formalize integration by parts on both lobes and show Kirchhoff boundary terms cancel. |
| A1.5 | Prove maximal Kirchhoff self-adjoint extension. | `G8BookIIILemniscateSelfAdjointOperatorSource`; `G8BookIIIMaximalKirchhoffSelfAdjointExtensionTarget`; `maximalExtensionTarget`. | Interface landed. | Prove the Kirchhoff extension is maximal symmetric, hence self-adjoint, for the compact metric graph operator. |
| A1.6 | Prove compact resolvent and discrete point spectrum. | `G8BookIIILemniscateCompactResolventSource`; `G8BookIIILemniscateCompactResolventTarget`; `G8BookIIILemniscateDiscretePointSpectrumTarget`. | Interface landed. | Formalize compactness of the graph/Sobolev embedding, compact resolvent, and the discrete point-spectrum consequence. |
| A1.7 | Package A1 as a ready operator. | `G8BookIIILemniscateOperatorReadySource`; `operatorCtx`; `operatorReady`; `toCompactResolventSource`. | Closed adapter, constructor open. | Once A1.1-A1.6 are theorem-backed, this wrapper immediately yields `LemniscateOperatorReady`. |
| A2.8 | Define the operator-native analytic point-spectrum predicate. | `G8BookIIILemniscateAnalyticPointSpectrumProvenance`; `G8BookIIILemniscateEigenpairData`; `G8BookIIILemniscateEigenpairPointSpectrumMembership`; `kind := .pointSpectrum` through `toProvenance`. | Interface landed. | Tie the native eigenpair predicate to the actual analytic point spectrum of the ready operator, not to finite diagnostics or standard `n^2` readouts. |
| A2.9 | Prove self-adjoint spectral reality for point-spectrum members. | `G8BookIIILemniscateAnalyticPointSpectrumRealityTarget`; `G8BookIIILemniscateEigenpairRealitySource`; `toAnalyticPointSpectrumSource`. | Interface landed. | Formalize the eigenpair inner-product argument: self-adjointness plus nonzero eigenfunction implies `lambda.im = 0`. |
| A2.10 | Package A2 and the combined A1/A2 source. | `G8BookIIILaneAOperatorNativeSelfAdjointSource`; `toProofSource`; `toLaneASource`; `withEigenpairPointSpectrum`; `withAnalyticPointSpectrum`. | Closed adapter, constructor open. | Once A1.7 and A2.8-A2.9 are theorem-backed, this yields `G8LaneAOperatorNativeSelfAdjointSource`. |

## Compressed Live Obligations

The ten proof-map steps currently compress to these live theorem obligations:

1. Ch.23 compact metric graph topology/metric/compactness for the concrete
   `UnitAddCircle` wedge carrier is now theorem-backed, isolated as
   `G8BookIIICh23ConcreteCompactMetricGraphTarget` and closed by
   `g8BookIIICh23ConcreteCompactMetricGraphTarget_from_glueQuotientMetricTransfer`.
   The first subtarget is theorem-backed as
   `g8BookIIICh23CompactLoopConstructorTarget_unitAddCircle`, and two copies
   are theorem-backed by
   `g8BookIIICh23TwoLobeLoopConstructorTarget_unitAddCircle`.  The concrete
   quotient-core wedge built from those loops is theorem-backed by
   `g8BookIIICh23UnitAddCircleWedgeCore_closed`.  The pre-quotient compact
   two-lobe disjoint model is now theorem-backed by
   `g8BookIIICh23UnitAddCircleRawCompactWedgeModel_closed`, and quotient
   topology/compactness is theorem-backed by
   `g8BookIIICh23UnitAddCircleQuotientCompactTopology_closed`.  The
   Mathlib glued-metric two-lobe model is theorem-backed by
   `g8BookIIICh23UnitAddCircleGluedMetricGraph_closed`.  The canonical
   quotient-carrier-to-glue map is theorem-backed by
   `g8BookIIICh23UnitAddCircleGlueQuotientMap_closed`; it respects the wedge
   quotient, is surjective, and its injectivity target is theorem-backed by
   `g8BookIIICh23UnitAddCircleGlueQuotientInjectivity_closed`.  The
   induced-metric/topology/shortest-path package is now theorem-backed as
   `G8BookIIICh23UnitAddCircleGlueQuotientMetricTransferFromInjectiveTarget`,
   closed by
   `g8BookIIICh23UnitAddCircleGlueQuotientMetricTransferFromInjective_closed`,
   and it implies the older
   `G8BookIIICh23UnitAddCircleGlueToQuotientMetricTransferTarget`.
2. Exact concrete-to-tau-native carrier transfer.  The metric/topology half is
   now theorem-backed by
   `G8BookIIICh23UnitAddCircleTauNativeMetricTopologyTransfer`: a
   basepoint-preserving lobe equivalence transports the closed concrete
   topology, metric, compactness, topology/metric agreement, and graph-distance
   realization into a theorem-backed `LemniscateCarrierContext`, then closes
   `G8BookIIICh23UnitAddCircleTauNativeA11ClosureTarget` and the compact metric
   graph package target.  The remaining load-bearing theorem is exactly
   `G8BookIIICh23TauCircleParametrizationCompletenessTarget`, or equivalently a
   `G8BookIIICh23UnitAddCircleTauCircleLobeEquivalence`.
3. Hilbert/Sobolev/Kirchhoff domain readiness.
4. Analytic Kirchhoff graph Laplacian construction.
5. Boundary-form cancellation.
6. Maximal Kirchhoff self-adjointness.
7. Compact resolvent and discrete point-spectrum theorem.
8. Operator-native point-spectrum predicate identification.
9. Self-adjoint eigenpair reality theorem.

Steps A1.7 and A2.10 are packaging steps; their adapters are already closed,
but their constructors remain unavailable until the preceding obligations are
proved.

## Current Axiom-Ledger Meaning

The official weak Lane A ledger still has three gates:

```text
A1 operator readiness
A2 operator-native self-adjoint spectral provenance
A3 canonical actual-xi membership
```

This document refines only A1/A2. It does not lower any official axiom count.
When the eight compressed A1/A2 obligations above are theorem-backed, A1 and A2
can be replaced by constructors in the official ledger. A3 remains separate.

## Next Recommended Milestone

Continue with A1.1-A1.2 as a pure operator core:

```text
lemniscate metric graph
  -> Hilbert space and Kirchhoff domain
  -> LemniscateDomainReady
```

The raw two-lobe wedge quotient is now theorem-backed in Lean. The primary
source truth for the next breakthrough is the Book III Ch.23 compact metric
graph, not the TauProfinite compatibility corridor. The single-loop theorem is
now discharged by `UnitAddCircle`:

```text
g8BookIIICh23CompactLoopConstructorTarget_unitAddCircle
```

Two copies then supply:

```text
g8BookIIICh23TwoLobeLoopConstructorTarget_unitAddCircle
```

The concrete quotient-core wedge target is now also closed:

```text
g8BookIIICh23UnitAddCircleWedgeCore_closed
```

The Mathlib glued-metric source for two `UnitAddCircle` lobes glued at the
basepoint is now closed:

```text
g8BookIIICh23UnitAddCircleGluedMetricGraph_closed
```

The quotient-carrier-to-glue map is now closed and surjective:

```text
g8BookIIICh23UnitAddCircleGlueQuotientMap_closed
```

The exact injectivity of that map is now closed:

```text
g8BookIIICh23UnitAddCircleGlueQuotientInjectivity_closed
```

The induced-metric transfer target is now closed and supplies the previous
glue-to-quotient transfer:

```text
G8BookIIICh23UnitAddCircleGlueQuotientMetricTransferFromInjectiveTarget
g8BookIIICh23UnitAddCircleGlueQuotientMetricTransferFromInjective_closed
```

and then:

```text
G8BookIIICh23UnitAddCircleGlueToQuotientMetricTransferTarget
g8BookIIICh23ConcreteCompactMetricGraphTarget_from_glueQuotientMetricTransfer
```

The quotient-equivalence bridge is now split as:

```text
G8BookIIICh23UnitAddCircleTauCircleLobeEquivalence
  -> G8BookIIICh23UnitAddCircleTauNativeQuotientBridgeTarget
```

The tau-native graph-level transfer from this lobe equivalence is now closed
by:

```text
g8BookIIICh23UnitAddCircleTauNativeA11ClosureTarget_of_lobeEquivalence
g8BookIIICh23TauCircleParametrizationCompletenessTarget_toA11ClosureTarget
```

The angle-period corridor has one additional exact refinement:

```text
G8BookIIICh23UnitAddCircleCauchyAnglePeriodSourceTarget
  + G8BookIIICh23TauCircleParametrizedCauchyComplete
  -> G8BookIIICh23UnitAddCircleParametrizedCanonicalAnglePeriodSourceTarget
```

The real half-open period readout part of this corridor is now theorem-backed:

```text
g8BookIIICh23UnitAddCircleRealIcoAngle
g8BookIIICh23UnitAddCircleRealIcoAngle_basepoint
```

The quotient-level lift of these real periods into `TauRealQ` is also now
theorem-backed:

```text
g8BookIIICh23UnitRealIcoTauRealQ
g8BookIIICh23UnitRealIcoTauRealQ_representsReal
g8BookIIICh23UnitRealIcoZeroBoundedTauRepresentative
```

The tau-native bounded representative theorem is now theorem-backed by lower
floor-grid rational approximants:

```text
g8BookIIICh23RealIcoFloorApprox
g8BookIIICh23RealIcoFloorApproxCauSeq_real_mk
g8BookIIICh23RealIcoFloorBoundedTauAngle_quotient_eq
g8BookIIICh23RealIcoBoundedCauchyTauRepresentativeSourceTarget_closed
g8BookIIICh23RealIcoCauchyBoundedTauAngleLiftTarget_closed
```

The remaining Tau-native lift corridor has therefore collapsed to one exact
period-soundness target:

```text
G8BookIIICh23CauchyTauCirclePeriodSoundnessTarget
```

Together they imply:

```text
G8BookIIICh23UnitAddCircleCauchyAnglePeriodSourceTarget
```

This records the current kernel fact: inverse period readout should be built on
Cauchy bounded-angle representatives whose `TauRealQ` value agrees with the
canonical real period, not on arbitrary bounded presentations.

Thus the remaining A1.1 target is no longer the metric/topology transfer after
a lobe equivalence is supplied; it is the lobe equivalence itself, packaged as
`G8BookIIICh23TauCircleParametrizationCompletenessTarget`.  TauLib's existing
`TauProfinite` infrastructure still supplies a theorem-backed compact metric
substrate, but exact identification with the connected Ch.23 metric graph
remains a separate compatibility theorem. The TauProfinite compatibility
targets remain:

1. `G8BookIIILemniscateTauProfiniteLobeIdentificationSource`, identifying
   each τ-circle lobe with the profinite compact metric substrate.
2. `G8BookIIILemniscateTauProfiniteWedgeTransferSource`, transferring the
   two-lobe wedge quotient, compactness, topology/metric agreement, and
   shortest-path graph metric to `LemniscateCarrier`.
3. `G8BookIIILemniscateTauProfiniteHilbertDomainTransferSource`, transferring
   graph measure, L2/Hilbert readiness, trace continuity, and Kirchhoff-domain
   closure from that compact graph source.

These TauProfinite targets yield the A1.1 metric graph source and A1.2
Hilbert/domain source only after exact topology/metric agreement with the
Ch.23 graph is proved. They remain useful scaffolding, not the first
load-bearing theorem.

The compression theorem
`g8BookIIILemniscateTauProfiniteA1A2ThreeTarget_iff_domainTransferTarget`
records the current target economy: the third source carries the first two
coherently, so the next single constructor theorem can be stated as
`G8BookIIILemniscateTauProfiniteHilbertDomainTransferTarget` without losing the
lobe-identification or wedge-transfer obligations.
