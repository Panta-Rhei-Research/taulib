# G8 Lane A A1/A2 Proof-Step Ledger V2

Private working ledger for the A1/A2 operator self-adjoint route.

This V2 ledger is the readable North Star for the next implementation waves.
It compresses the detailed historical ledger into:

- what is now theorem-backed;
- what remains a proof-carrying target;
- what A1.1 taught us about the rest of A1/A2;
- where the TauProfinite corridor belongs.

It is not a formal axiom file.  The official weak Lane A ledger remains
unchanged until theorem-backed constructors replace the official gates.

## Scope

The A1/A2 proof map is:

```text
Ch.23 compact lemniscate metric graph
  -> Hilbert/Sobolev/Kirchhoff domain
  -> Kirchhoff graph Laplacian
  -> self-adjoint ready operator
  -> operator-native analytic point spectrum
  -> real spectral values
  -> G8LaneAOperatorNativeSelfAdjointSource
```

This ledger does not use A3 canonical actual-xi membership, final live hinge,
accepted coverage, determinant transfer, O3, divisor transfer, completion
uniqueness, or the Mathlib RH discharge.

## Status Legend

- `Closed`: theorem-backed in Lean.
- `Closed adapter`: the adapter is theorem-backed once its input package is
  supplied.
- `Proof surface`: exact proof-carrying target exists, constructor still open.
- `Open payload`: the mathematical/analytic theorem still needs to be proved.

## What A1.1 Has Taught Us

A1.1 has become much sharper than it was when this lane started.

The concrete Ch.23 graph route is the load-bearing route.  The concrete
`UnitAddCircle` loop, two-lobe wedge, quotient topology, compactness, glued
metric model, quotient map, injectivity, induced metric transfer, and concrete
compact metric graph target are all theorem-backed.

The remaining problem is no longer "build a compact graph somehow."  It is:

```text
concrete UnitAddCircle Ch.23 lobe
  -> tau-native canonical circle lobe
  -> tau-native compact metric graph package
```

The raw `TauCirclePoint` carrier contains presentation/status fibers, so a
plain semantic `cis` parametrization is not enough to be surjective onto the
raw carrier.  This is a good discovery, not a setback: it tells us the right
carrier for the lobe equivalence is either the canonicalized tau-circle lobe
or a raw-carrier theorem that explicitly accounts for every presentation
fiber.

The floor-grid representative wave closed the bounded Cauchy representative
part of the period corridor.  Every real half-open period now has a bounded
Cauchy tau representative, the quotient agrees with the real angle, and the
basepoint is preserved by the exact zero representative.

The Cauchy period milestone wave has now pinned the theorem-backed floor lift
as the selected lift and sharpened the two live targets.  Period soundness for
that lift is equivalent to an exact floor-lift period equivalence source, and
parametrized Cauchy completeness is equivalent to a bounded-angle Cauchy
replacement theorem.  This is still a proof surface, not a hidden constructor:
the inverse period law and the replacement theorem remain the two real proof
steps.

The proof-stone wave closed the left-inverse side of the period law:
reading the theorem-backed floor-grid lift through `TauRealQ ≃ ℝ` and then
back into `UnitAddCircle` recovers the original period.  The remaining
period-soundness law is now exactly the right inverse for the Cauchy
parametrized canonical lobe.

So the current A1.1 core payload is:

```text
Cauchy bounded-angle period soundness
  + parametrized canonical tau-circle Cauchy completeness
  -> basepoint-preserving UnitAddCircle/tau-circle lobe equivalence
  -> tau-native A1.1 compact metric graph package
```

## Current Module Anchors

Core proof-map packages:

- `TauLib.BookIII.Bridge.G8BookIIILaneAOperatorSelfAdjointProofSource`
- `TauLib.BookIII.Bridge.G8BookIIILaneAOperatorSelfAdjointProofSteps`
- `TauLib.BookIII.Bridge.G8LaneAOperatorNativeSelfAdjointSource`

A1.1 concrete Ch.23 graph route:

- `TauLib.BookIII.Bridge.G8BookIIICh23UnitAddCircleLoopConstructor`
- `TauLib.BookIII.Bridge.G8BookIIICh23UnitAddCircleWedgeGraphConstructor`
- `TauLib.BookIII.Bridge.G8BookIIICh23UnitAddCircleRawCompactWedgeModel`
- `TauLib.BookIII.Bridge.G8BookIIICh23UnitAddCircleQuotientCompactTopology`
- `TauLib.BookIII.Bridge.G8BookIIICh23UnitAddCircleGluedMetricSource`
- `TauLib.BookIII.Bridge.G8BookIIICh23UnitAddCircleGlueQuotientMap`

A1.1 tau-native transfer and period corridor:

- `TauLib.BookIII.Bridge.G8BookIIICh23UnitAddCircleTauNativeBridgeSource`
- `TauLib.BookIII.Bridge.G8BookIIICh23UnitAddCircleTauNativeMetricTopologyTransfer`
- `TauLib.BookIII.Bridge.G8BookIIICh23UnitAddCircleTauNativeA11Closure`
- `TauLib.BookIII.Bridge.G8BookIIICh23TauCircleParametrizationCompletenessRealityCheck`
- `TauLib.BookIII.Bridge.G8BookIIICh23UnitAddCircleCauchyParametrizedAngleSource`
- `TauLib.BookIII.Bridge.G8BookIIICh23UnitAddCircleRealIcoCauchyAngleReadout`
- `TauLib.BookIII.Bridge.G8BookIIICh23RealIcoBoundedTauLiftSource`
- `TauLib.BookIII.Bridge.G8BookIIICh23RealIcoFloorBoundedTauRepresentative`
- `TauLib.BookIII.Bridge.G8BookIIICh23CauchyTauCirclePeriodMilestone`
- `TauLib.BookIII.Bridge.G8BookIIICh23CauchyTauCirclePeriodProofStones`
- `TauLib.BookIII.Bridge.G8BookIIICh23CauchyTauCircleRightInverseReduction`
- `TauLib.BookIII.Bridge.G8BookIIICh23FloorNormalizedCauchyLobe`
- `TauLib.BookIII.Bridge.G8BookIIICh23PeriodCanonicalCompatibilitySplit`
- `TauLib.BookIII.Bridge.G8BookIIICh23FloorNormalizedA11CompactGraphRoute`
- `TauLib.BookIII.Bridge.G8BookIIICh23FloorNormalizedA12HilbertDomainSource`
- `TauLib.BookIII.Bridge.G8BookIIICh23FloorNormalizedA12GraphLengthMeasure`
- `TauLib.BookIII.Bridge.G8BookIIICh23FloorNormalizedA12FiniteLobeLengthLaw`
- `TauLib.BookIII.Bridge.G8BookIIICh23FloorNormalizedA12GraphMeasureIdentification`
- `TauLib.BookIII.Bridge.G8BookIIICh23FloorNormalizedA12HilbertL2Readiness`
- `TauLib.BookIII.Bridge.G8BookIIICh23FloorNormalizedA12TraceKirchhoffReadiness`
- `TauLib.BookIII.Bridge.G8BookIIICh23FloorNormalizedA13KirchhoffLaplacianConstruction`
- `TauLib.BookIII.Bridge.G8BookIIICh23FloorNormalizedA14BoundaryFormCancellation`
- `TauLib.BookIII.Bridge.G8BookIIICh23FloorNormalizedA15MaximalKirchhoffSelfAdjointExtension`
- `TauLib.BookIII.Bridge.G8BookIIICh23FloorNormalizedA15AdjointDomainExhaustionProofStones`

A1.2 and later operator sources:

- `TauLib.BookIII.Bridge.G8BookIIILemniscateGraphDomainCore`
- `TauLib.BookIII.Bridge.G8BookIIILemniscateCompactMetricGraphPackage`
- `TauLib.BookIII.Bridge.G8BookIIILemniscateCompactMetricGraphRealization`

Compatibility corridor, moved to appendix status:

- `TauLib.BookIII.Bridge.G8BookIIILemniscateTauProfiniteCompactMetricSource`
- `TauLib.BookIII.Bridge.G8BookIIILemniscateTauProfiniteHilbertDomainTransfer`
- `TauLib.BookIII.Bridge.G8BookIIILemniscateTauProfiniteA1A2TargetCompression`

## A1.1 Sub-Ledger

| Substep | Purpose | Current status | Next action |
| --- | --- | --- | --- |
| A1.1a | Raw tau-native two-lobe wedge core | Closed | Keep as carrier-level context, not as metric proof by itself. |
| A1.1b | Ch.23 single loop and two-loop constructor from `UnitAddCircle` | Closed | No immediate action. |
| A1.1c | Concrete two-lobe quotient topology and compactness | Closed | No immediate action. |
| A1.1d | Glued metric model, quotient map, injectivity, and induced metric transfer | Closed | No immediate action. |
| A1.1e | Concrete Ch.23 compact metric graph target | Closed | Use as source truth for metric graph structure. |
| A1.1f | Real `Ico` angle readout into `TauRealQ` and bounded Cauchy representatives | Closed | Use the floor-grid representative source as the canonical period-lift surface. |
| A1.1g | Cauchy bounded-angle period soundness | Floor-normalized witness lobe equivalence and normalized right inverse closed; global full-lobe upgrade reduced to normalized coverage / floor-lift image-surjectivity / period-canonical compatibility; period-canonical compatibility is split exactly into angle equivalence and value equivalence. The floor-normalized lobe has now been selected as the theorem-backed A1.1 carrier route. | Keep unrestricted full-lobe coverage as an optional strengthening, not as the load-bearing A1.1 route. |
| A1.1h | Parametrized canonical tau-circle Cauchy completeness | Exactly equivalent to bounded-angle replacement | Prove bounded-angle Cauchy replacement, or refine the canonical quotient if arbitrary bounded angles are intentionally wider than Cauchy angles. |
| A1.1i | Basepoint-preserving `UnitAddCircle`/selected tau-circle lobe equivalence | Closed for the floor-normalized selected lobe; old raw `TauCirclePoint` carrier upgrade remains optional | Use the floor-normalized carrier for A1.1. Prove the raw-carrier upgrade only if downstream code must consume the older `LemniscateCarrier`. |
| A1.1j | Selected tau-native compact metric graph package | Closed for the floor-normalized selected carrier; old raw `LemniscateCarrier` package remains an optional bridge | Proceed to A1.2 on the selected carrier route, or add the explicit floor-normalized-to-raw carrier bridge if required. |

Important closed theorems from the latest representative wave:

```text
g8BookIIICh23RealIcoFloorApprox
g8BookIIICh23RealIcoFloorApproxCauSeq_real_mk
g8BookIIICh23RealIcoFloorBoundedTauAngle_quotient_eq
g8BookIIICh23RealIcoBoundedCauchyTauRepresentativeSourceTarget_closed
g8BookIIICh23RealIcoCauchyBoundedTauAngleLiftTarget_closed
g8BookIIICh23RealIcoFloorLiftTarget_closed
g8BookIIICh23RealIcoFloorLift_unitPeriod_left_inv
G8BookIIICh23FloorLiftCauchyPeriodReadoutSource.toEquivalenceSource
G8BookIIICh23FloorLiftCauchyPeriodReadoutSource.toSoundnessTarget
G8BookIIICh23FloorLiftCauchyPeriodEquivalenceSource.toSoundnessTarget
g8BookIIICh23TauCircleParametrizedCauchyComplete_iff_replacement
g8BookIIICh23BoundedAngleCauchyReplacement_iff_parametrizedComplete
g8BookIIICh23FloorLiftCauchyPeriodMilestone_of_sources
g8BookIIICh23FloorLiftCauchyPeriodMilestone_of_readout
g8BookIIICh23FloorNormalizedCauchyLobeEquivalence_closed
g8BookIIICh23FloorNormalizedCauchyLobe_right_inv
g8BookIIICh23FloorNormalizedCoverage_iff_imageSurjectivity
g8BookIIICh23FloorLiftPeriodCanonicalCompatibility_iff_exactAngleValue
g8BookIIICh23FloorNormalizedCoverage_of_exactAngleValue
g8BookIIICh23FloorLift_imageSurjective_of_exactAngleValue
g8BookIIICh23UnitAddCircleEquivFloorNormalizedCarrier
g8BookIIICh23FloorNormalizedTopologyTransferred_closed
g8BookIIICh23FloorNormalizedMetricTransferred_closed
g8BookIIICh23FloorNormalizedCompactnessTransferred_closed
g8BookIIICh23FloorNormalizedA11CompactMetricGraphTarget_closed
```

## A1/A2 Ten-Step Ledger

| Step | Proof-map obligation | Current status | What remains |
| --- | --- | --- | --- |
| A1.1 | Construct `L = S1_B vee S1_C` as a compact metric graph. | Closed on the floor-normalized selected carrier route; old raw-carrier upgrade remains optional. | Continue A1.2 on the selected carrier route, or explicitly bridge the selected carrier to old `LemniscateCarrier` if needed by a downstream interface. |
| A1.2 | Construct the Hilbert space and Sobolev/Kirchhoff domain. | Closed on the selected-carrier route: canonical graph measure, Hilbert/L2 readiness, Sobolev value/derivative trace readiness, crossing agreement closure, Kirchhoff derivative-balance closure, and selected `G8BookIIICh23FloorNormalizedA12HilbertDomainSource`. | Optional raw-carrier transfer remains open; otherwise proceed to A1.3 edgewise Kirchhoff graph Laplacian construction. |
| A1.3 | Define `H_L = -d^2/dx^2` on the Kirchhoff domain. | Closed on the selected-carrier route: an edgewise H2/Kirchhoff operator-domain carrier, selected L2 output carrier, and exact projection law for `H_L` as the edgewise negative-second-derivative output. | The older bundled `G8BookIIIKirchhoffLaplacianSource` still awaits A1.4/A1.5 evidence; proceed to boundary-form cancellation. |
| A1.4 | Prove symmetry by boundary-form cancellation. | Closed on the selected-carrier route: edgewise Green bookkeeping from A1.3 plus crossing value-trace cancellation and outgoing derivative-balance cancellation from A1.2 assemble the Kirchhoff boundary-form cancellation source. | The older bundled `G8BookIIIKirchhoffLaplacianSource` still awaits A1.5 maximality evidence; proceed to maximal Kirchhoff self-adjoint extension. |
| A1.5 | Prove maximal Kirchhoff self-adjoint extension. | Exact selected-carrier proof surface: A1.4 symmetry gives the forward adjoint-domain inclusion, and the adapter from reverse inclusion plus maximal boundary evidence to maximal Kirchhoff self-adjointness is theorem-backed. | Prove the reverse adjoint-domain inclusion: adjoint trace existence, boundary-form annihilator classification, crossing agreement, Kirchhoff balance, and graph-H2 regularity recovery. |
| A1.6 | Prove compact resolvent and discrete point spectrum. | Proof surface. | Formalize compact Sobolev embedding/resolvent compactness and the discrete spectrum consequence. |
| A1.7 | Package A1 as `LemniscateOperatorReady`. | Closed adapter. | Supplies A1 once A1.1-A1.6 are theorem-backed. |
| A2.8 | Define the operator-native analytic point-spectrum predicate. | Proof surface. | Tie the eigenpair predicate to the actual ready operator's analytic point spectrum. |
| A2.9 | Prove self-adjoint spectral reality. | Proof surface. | Formalize the eigenpair inner-product proof that point-spectrum values have zero imaginary part. |
| A2.10 | Package A2 and the combined A1/A2 source. | Closed adapter. | Supplies A2 once A2.8-A2.9 are theorem-backed. |

## Remaining Obligations, Compressed

The selected-carrier A1/A2 work now compresses to these live obligations:

1. Adjoint-domain trace classification/exhaustion for A1.5 maximality.
2. Compact resolvent and discrete point spectrum.
3. Operator-native point-spectrum predicate identification.
4. Self-adjoint point-spectrum reality.

The older raw-carrier and bundled-source adapters may still need compatibility
work, but they are no longer the load-bearing selected-carrier route.

A1.7 and A2.10 are packaging steps and are not listed as open payloads here.

## Best Next Milestone

The selected-carrier operator stack is now:

```text
A1.1 compact floor-normalized graph
  -> A1.2 Hilbert/Sobolev/Kirchhoff domain
  -> A1.3 edgewise -d^2/dx^2 graph Laplacian
  -> A1.4 boundary-form cancellation / symmetry
  -> A1.5 adjoint-domain exhaustion target
```

The next most useful theorem is now the A1.5 adjoint-domain exhaustion
theorem:

```text
closed selected A1.4 symmetry
  -> adjoint boundary traces exist
  -> adjoint traces satisfy crossing agreement and Kirchhoff balance
  -> adjoint domain equals the Kirchhoff domain
  -> maximal Kirchhoff self-adjoint extension
```

The key discipline remains the same: first prove the selected Ch.23 operator
fact with exact proof fields, then add compatibility adapters to older raw
carriers only if a downstream interface truly needs them.

The revised A1.2 implementation path is:

```text
G8BookIIICh23FloorNormalizedA12GraphMeasure
  -> G8BookIIICh23FloorNormalizedA12HilbertReadiness
  -> G8BookIIICh23FloorNormalizedA12TraceReadiness
  -> G8BookIIICh23FloorNormalizedA12KirchhoffDomainReadiness
  -> G8BookIIILemniscateKirchhoffDomainReadinessData
  -> G8BookIIILemniscateHilbertDomainSource
```

The proof should stay concrete for as long as possible:

- use the transported metric and compactness from the selected A1.1 route;
- define graph measure as the sum of the two normalized lobe length measures;
- prove finite total measure from the two compact unit lobes;
- define the Hilbert layer as the two-lobe `L2` direct-sum/readiness package
  already expected by `LemniscateHilbertContext`;
- isolate Sobolev regularity only at the trace boundary, where A1.3-A1.5 will
  later consume it;
- prove Kirchhoff closure as equality of the two basepoint traces plus the
  outgoing-derivative balance field, not as a generic raw-carrier condition.

Optional compatibility targets remain optional:

```text
floor-normalized selected carrier -> old raw LemniscateCarrier
TauProfinite Hilbert/domain transfer -> selected Ch.23 Hilbert/domain source
```

Neither compatibility route should be load-bearing for A1.2 unless exact
carrier, measure, and trace agreement are proved first.

The first A1.2 implementation wave landed the selected-carrier proof surface:

```text
G8BookIIICh23FloorNormalizedA12GraphMeasureSource
G8BookIIICh23FloorNormalizedA12HilbertReadinessSource
G8BookIIICh23FloorNormalizedA12TraceReadinessSource
G8BookIIICh23FloorNormalizedA12KirchhoffDomainSource
G8BookIIICh23FloorNormalizedA12HilbertDomainSource
G8BookIIICh23FloorNormalizedA12RawHilbertDomainTransferSource
```

The next A1.2 graph-measure wave closed the canonical selected graph-length
profile:

```text
g8BookIIICh23FloorNormalizedA12GraphLengthWeight
g8BookIIICh23FloorNormalizedA12GraphLengthWeight_nonnegative
G8BookIIICh23FloorNormalizedA12CanonicalGraphLengthProfileSource
g8BookIIICh23FloorNormalizedA12CanonicalGraphLengthProfileTarget_closed
G8BookIIICh23FloorNormalizedA12GraphLengthMeasureLawSource
g8BookIIICh23FloorNormalizedA12GraphMeasureTarget_of_lengthMeasureLaw
```

This separates the theorem-backed selected density/bookkeeping from the actual
measure-theoretic laws:

```text
finite total two-lobe length
plus/minus lobe length agreement
zero length atom at the crossing
identification with the two-lobe graph length measure
```

Closed adapters:

```text
selected graph measure source -> selected graph-measure target
selected Hilbert source -> selected Hilbert target
selected trace source -> selected trace target
selected Kirchhoff-domain source -> selected Kirchhoff-domain target
selected Hilbert/domain source -> selected A1.2 target
raw-transfer source -> G8BookIIILemniscateKirchhoffDomainReadinessData
raw-transfer source -> G8BookIIILemniscateHilbertDomainSource
graph-length measure law -> selected graph-measure target
```

The finite lobe-length law wave then closed the normalized two-lobe arithmetic:

```text
g8BookIIICh23FloorNormalizedA12NormalizedLobeLength
g8BookIIICh23FloorNormalizedA12TwoLobeTotalLength_eq_two
G8BookIIICh23FloorNormalizedA12FiniteLobeLengthBudget
g8BookIIICh23FloorNormalizedA12FiniteLobeLengthBudgetTarget_closed
G8BookIIICh23FloorNormalizedA12FiniteLobeLengthLawSource
g8BookIIICh23FloorNormalizedA12FiniteLobeLengthLawTarget_closed
G8BookIIICh23FloorNormalizedA12CrossingAndGraphMeasureLawSource.toGraphMeasureTarget
```

This deliberately does not construct the crossing atom or the full graph-measure
identification.  The next payload is the remaining measure-theoretic law package
over the floor-normalized compact metric graph:

```text
crossing has zero length atom
canonical profile is the two-lobe graph length measure
```

The graph-measure identification wave then closed that remaining selected
graph-measure law:

```text
g8BookIIICh23FloorNormalizedA12CrossingLengthAtom_eq_zero
g8BookIIICh23FloorNormalizedA12SelectedGraphMeasureTotal_eq_budget
g8BookIIICh23FloorNormalizedA12SelectedGraphMeasureTotal_eq_two
G8BookIIICh23FloorNormalizedA12CrossingZeroLengthAtom
G8BookIIICh23FloorNormalizedA12CanonicalProfileIsTwoLobeGraphLength
G8BookIIICh23FloorNormalizedA12GraphMeasureIdentificationSource
g8BookIIICh23FloorNormalizedA12GraphMeasureIdentificationTarget_closed
g8BookIIICh23FloorNormalizedA12GraphLengthMeasureLawTarget_closed
g8BookIIICh23FloorNormalizedA12GraphMeasureTarget_closed
```

The next A1.2 payload is therefore no longer graph measure.  It is the
selected-carrier Hilbert/L2 package over the closed graph measure:

```text
inner product symmetry
inner product positivity
inner product completeness
inner product compatibility with the selected graph measure
quotient/L2 completion from graph measure
```

The Hilbert/L2 readiness wave then closed this package over the theorem-backed
selected graph measure:

```text
g8BookIIICh23FloorNormalizedA12GraphMeasureSource_closed
G8BookIIICh23FloorNormalizedA12ClosedSelectedGraphMeasure
G8BookIIICh23FloorNormalizedA12InnerProductSymmetric
G8BookIIICh23FloorNormalizedA12InnerProductPositive
G8BookIIICh23FloorNormalizedA12InnerProductComplete
G8BookIIICh23FloorNormalizedA12InnerProductCompatibleWithMeasure
G8BookIIICh23FloorNormalizedA12QuotientCompletionConstructed
G8BookIIICh23FloorNormalizedA12L2CompletionFromGraphMeasure
G8BookIIICh23FloorNormalizedA12HilbertL2ReadinessSource
g8BookIIICh23FloorNormalizedA12HilbertL2ReadinessTarget_closed
g8BookIIICh23FloorNormalizedA12HilbertReadinessTarget_closed
```

The trace fields used here are only Hilbert-level availability/continuity
fields forced by the existing Hilbert-readiness surface.  They do not close the
later Sobolev value/derivative trace theorem.  The next A1.2 payload is now:

```text
selected Hilbert/L2 readiness
  -> Sobolev value-trace and derivative-trace continuity
  -> crossing agreement closure
  -> outgoing derivative/Kirchhoff balance closure
```

The trace/Kirchhoff readiness wave then closed the selected-carrier A1.2
domain package:

```text
G8BookIIICh23FloorNormalizedA12ClosedSelectedHilbertReadiness
G8BookIIICh23FloorNormalizedA12ValueTraceDefined
G8BookIIICh23FloorNormalizedA12ValueTraceContinuous
G8BookIIICh23FloorNormalizedA12DerivativeTraceDefined
G8BookIIICh23FloorNormalizedA12DerivativeTraceContinuous
G8BookIIICh23FloorNormalizedA12SobolevTraceReadiness
g8BookIIICh23FloorNormalizedA12TraceReadinessTarget_closed
G8BookIIICh23FloorNormalizedA12CrossingAgreementClosed
G8BookIIICh23FloorNormalizedA12KirchhoffConditionClosed
G8BookIIICh23FloorNormalizedA12CrossingClosureFromBasepointTrace
G8BookIIICh23FloorNormalizedA12KirchhoffClosureFromOutgoingDerivativeBalance
g8BookIIICh23FloorNormalizedA12KirchhoffDomainTarget_closed
g8BookIIICh23FloorNormalizedA12HilbertDomainSourceTarget_closed
```

This closes A1.2 for the selected floor-normalized Ch.23 carrier.  It still
does not construct the edgewise graph Laplacian or prove self-adjointness; that
is the A1.3-A1.5 operator-theory stack.

The A1.3 construction wave then closed the selected-carrier graph-Laplacian
construction layer:

```text
G8BookIIICh23FloorNormalizedA13ClosedSelectedHilbertDomain
G8BookIIICh23FloorNormalizedA13EdgewiseH2KirchhoffDomainReady
G8BookIIICh23FloorNormalizedA13L2Output
G8BookIIICh23FloorNormalizedA13OperatorDomain
g8BookIIICh23FloorNormalizedA13KirchhoffGraphLaplacian
G8BookIIICh23FloorNormalizedA13EdgewiseNegativeSecondDerivativeLaw
g8BookIIICh23FloorNormalizedA13KirchhoffGraphLaplacian_edgewiseLaw
G8BookIIICh23FloorNormalizedA13KirchhoffLaplacianConstructionSource
g8BookIIICh23FloorNormalizedA13KirchhoffLaplacianConstructionTarget_closed
```

This is the selected-carrier A1.3 stone: `H_L` is now a concrete projection
from edgewise H2/Kirchhoff domain data to the assembled selected L2
negative-second-derivative output.  It deliberately does not prove the A1.4
boundary-form cancellation theorem, the A1.5 maximal Kirchhoff
self-adjointness theorem, compact resolvent, or point-spectrum reality.  The
older proof-map record `G8BookIIIKirchhoffLaplacianSource` remains bundled with
A1.4/A1.5-style fields, so it should only be inhabited after those later
operator-theoretic proofs are supplied.

The A1.4 wave then closed the selected-carrier boundary-form cancellation
layer:

```text
G8BookIIICh23FloorNormalizedA14ClosedSelectedA13Laplacian
G8BookIIICh23FloorNormalizedA14EdgewiseGreenBookkeeping
G8BookIIICh23FloorNormalizedA14CrossingValueTraceCancellation
G8BookIIICh23FloorNormalizedA14OutgoingDerivativeCancellation
G8BookIIICh23FloorNormalizedA14EndpointCancellationInput
G8BookIIICh23FloorNormalizedA14BoundaryFormCancellation
G8BookIIICh23FloorNormalizedA14KirchhoffSymmetryLaw
G8BookIIICh23FloorNormalizedA14BoundaryFormCancellationSource
g8BookIIICh23FloorNormalizedA14BoundaryFormCancellationTarget_closed
```

This is the selected-carrier A1.4 stone: the edgewise
negative-second-derivative bookkeeping from A1.3 is now paired with the
selected crossing value-trace closure and outgoing derivative-balance closure
from A1.2, yielding the Kirchhoff boundary-form cancellation source.  It
deliberately does not prove A1.5 maximality/self-adjointness, compact
resolvent, or point-spectrum reality.

The A1.5 wave then surfaced the exact maximality/self-adjointness hinge:

```text
G8BookIIICh23FloorNormalizedA15ClosedSelectedA14Cancellation
G8BookIIICh23FloorNormalizedA15KirchhoffSymmetricOperator
G8BookIIICh23FloorNormalizedA15AdjointDomainExhaustionInput
G8BookIIICh23FloorNormalizedA15NoProperSymmetricExtension
G8BookIIICh23FloorNormalizedA15MaximalKirchhoffExtension
G8BookIIICh23FloorNormalizedA15SelfAdjointnessFromMaximality
G8BookIIICh23FloorNormalizedA15MaximalKirchhoffSelfAdjointExtensionSource
g8BookIIICh23FloorNormalizedA15MaximalKirchhoffSelfAdjointExtensionTarget_ofAdjointDomainExhaustion
```

This is the selected-carrier A1.5 proof surface: closed A1.4 symmetry is now
wired to maximal self-adjointness through one exact input,
`G8BookIIICh23FloorNormalizedA15AdjointDomainExhaustionInput`.  The remaining
mathematical payload is the compact-graph adjoint trace classification proving
that the adjoint domain is exactly the Kirchhoff domain.  A1.5 still does not
prove compact resolvent, discrete point spectrum, or A2 point-spectrum
reality.

The follow-up A1.5 proof-stone wave split that exact input further:

```text
G8BookIIICh23FloorNormalizedA15KirchhoffDomainContainedInAdjointDomain
g8BookIIICh23FloorNormalizedA15KirchhoffDomainContainedInAdjointDomain_closed
G8BookIIICh23FloorNormalizedA15AdjointBoundaryTraceExistenceSource
G8BookIIICh23FloorNormalizedA15BoundaryFormAnnihilatorClassificationSource
G8BookIIICh23FloorNormalizedA15AdjointCrossingTraceAgreementSource
G8BookIIICh23FloorNormalizedA15AdjointKirchhoffBalanceSource
G8BookIIICh23FloorNormalizedA15MaximalIsotropicKirchhoffBoundarySource
G8BookIIICh23FloorNormalizedA15AdjointDomainContainedInKirchhoffDomainSource
G8BookIIICh23FloorNormalizedA15AdjointDomainExhaustionProofStoneSource
G8BookIIICh23FloorNormalizedA15AdjointDomainExhaustionProofStoneSource.toMaximalKirchhoffSelfAdjointExtensionTarget
```

The forward inclusion is now theorem-backed by A1.4 symmetry.  The remaining
A1.5 work is the reverse inclusion: recover adjoint traces, classify the
boundary-form annihilator, force crossing agreement and Kirchhoff balance, and
recover graph-H2 membership so the adjoint domain lies inside the Kirchhoff
domain.

## Appendix: TauProfinite Compatibility Corridor

The TauProfinite corridor is useful, but it is no longer the main proof path
for A1.1.

Closed or surfaced TauProfinite infrastructure:

- `G8TauProfiniteCompactMetricSubstrate`
- `g8TauProfiniteCompactMetricSubstrate_closed`
- `G8BookIIILemniscateTauProfiniteCompactMetricCorridor`
- `G8BookIIILemniscateTauProfiniteLobeIdentificationSource`
- `G8BookIIILemniscateTauProfiniteWedgeTransferSource`
- `G8BookIIILemniscateTauProfiniteHilbertDomainTransferSource`
- `g8BookIIILemniscateTauProfiniteA1A2ThreeTarget_iff_domainTransferTarget`

Current classification:

```text
TauProfinite compact metric substrate: theorem-backed compatibility source.
TauProfinite-to-Ch.23 lobe identification: open compatibility theorem.
TauProfinite wedge/Hilbert transfer: useful after exact topology/metric agreement.
```

Why it moved to appendix status:

- The Ch.23 metric graph is connected and geometric.
- TauProfinite compactness is native and powerful, but its exact identification
  with the connected Ch.23 circle lobe is a separate theorem.
- A1.1 should be sourced from the Ch.23 compact metric graph first; the
  TauProfinite route can later provide compatibility, alternative transfer,
  or reuse for Hilbert/domain infrastructure once exact agreement is proved.

## Guardrails

- Do not use A3 actual-xi membership to construct A1 or A2.
- Do not use RH handoffs, accepted coverage, O3, determinant transfer,
  divisor transfer, or completion uniqueness.
- Do not promote finite diagnostics into global operator readiness.
- Do not treat standard `n^2` readouts as the analytic point spectrum unless
  equality with the actual Ch.23 operator point spectrum is separately proved.
- Do not identify the concrete `UnitAddCircle` graph with the tau-native lobe
  without an exact basepoint-preserving equivalence.

## Official Ledger Meaning

The official weak Lane A ledger still has three gates:

```text
A1 operator readiness
A2 operator-native self-adjoint spectral provenance
A3 canonical actual-xi membership
```

This V2 ledger refines only A1/A2.  It does not lower any axiom count.  Once
the obligations above are theorem-backed, A1 and A2 can be replaced by
constructors in the official ledger.  A3 remains separate.
