# G8 Lane A A1 Tau-Circle Infrastructure Research

Private working note for the A1.1 compact metric graph route.

## Question

Can the current TauLib circle, topology, geometry, and trigonometric
infrastructure directly construct the compact metric graph package for the
two-lobe lemniscate carrier?

## Reusable Theorem-Backed Infrastructure

The strongest existing topology/metric substrate is the `TauProfinite` stack:

- `TauLib.BookI.Boundary.Bridge.TauProfiniteMetricSpace` constructs the
  canonical ultrametric distance and the `MetricSpace TauProfinite` instance.
- `TauLib.BookI.Boundary.Bridge.TauProfiniteMetricSpaceTopologyAgreement`
  proves cylinder topology equals metric topology.
- `TauLib.BookI.Boundary.Bridge.TauProfiniteMetricSpaceCanonical` installs the
  canonical `MetricSpace.replaceTopology` wrapper.
- `TauLib.BookI.Boundary.Bridge.TauProfiniteCompactSpace` constructs
  `CompactSpace TauProfinite`.

This is now reflected in Lean by
`G8TauProfiniteCompactMetricSubstrate` and
`g8TauProfiniteCompactMetricSubstrate_closed`.

## Useful Circle/Trig Infrastructure

`TauLib.BookIII.Bridge.TauCircleParam` gives the current tau-circle point
carrier:

- `TauCirclePoint`
- `TauCirclePoint.base`
- `TauCirclePoint.unit_magnitude`
- `TauCirclePoint.negate_equiv_conj`
- `TauCirclePoint.ofRat`

`TauLib.BookI.Boundary.TauRealSinCos` provides theorem-backed trigonometric
and unit-magnitude algebra:

- `TauComplex.cisTauReal_add`
- `TauComplex.cisTauReal_neg_self_equiv_one`
- `TauComplex.cisTauReal_negate_equiv_conj`
- `TauComplex.cisTauReal_magSq_equiv_one`

These are real algebraic/geometric facts, but they do not currently provide a
`TopologicalSpace`, `MetricSpace`, `CompactSpace`, quotient topology, or
shortest-path graph metric for `TauCirclePoint`.

## Diagnostic-Only Sources

`TauLib.BookII.Transcendentals.Circles` records the intended solenoidal/profinite
circle interpretation with finite checks:

- `circle_profinite_b_check`
- `circle_profinite_c_check`
- `geo_topo_check`
- `bc_independence_check`

These are useful source anchors, but they are finite diagnostics and do not by
themselves construct the compact metric graph carrier.

`TauLib.BookI.Polarity.Lemniscate` and
`TauLib.BookI.Polarity.WedgeLoop` provide algebraic/wedge-loop provenance.
They are not compact metric graph constructions.

## Current A1.1 Verdict

The raw two-lobe quotient is theorem-backed in
`G8BookIIILemniscateTwoLobeWedgeCore`, and the compact metric substrate exists
for `TauProfinite`.

Red-team comparison with the Ch.23 proof map sharpened the source order:
the primary A1.1 source truth is the Ch.23 compact metric graph
`L = S^1_B vee S^1_C`, not the TauProfinite compatibility corridor. This is
now reflected in Lean by:

```text
G8BookIIICh23CompactLoopConstructor
G8BookIIICh23CompactLoopConstructorTarget
G8BookIIICh23TwoLobeLoopConstructorTarget
G8BookIIICh23ConcreteCompactMetricGraphTarget
G8BookIIICh23UnitAddCircleTauNativeQuotientBridgeTarget
G8BookIIICh23UnitAddCircleTauNativeMetricTransferTarget
G8BookIIILemniscateCh23CompactMetricGraphSource
G8BookIIILemniscateCh23CompactMetricGraphTarget
```

The one-loop constructor adapts into `G8BookIIICh23CircleLobeModel`; two copies
provide the plus/minus lobe models consumed by the Ch.23 graph source. The
`UnitAddCircle` loop theorem and concrete quotient-core wedge are now
theorem-backed in Lean. The next bridge is split so that a basepoint-preserving
lobe equivalence induces the quotient equivalence before any metric transfer
is claimed. The Ch.23 graph source then adapts into
`G8BookIIILemniscateCompactMetricGraphPackage` and
`G8BookIIILemniscateMetricGraphSource`. The full concrete compact graph and
tau-native metric transfer still remain proof-carrying targets: quotient
topology, shortest-path graph metric, compactness, topology/metric agreement,
and graph-distance realization are not constructed from finite diagnostics.

The TauProfinite route is now classified as compatibility scaffolding. What is
missing there is the transfer theorem:

```text
TauCirclePoint lobe
  = profinite circle substrate
  -> two profinite lobes glued at the basepoint
  -> compact quotient wedge topology
  -> graph shortest-path metric
  -> current LemniscateCarrier context
```

This compatibility transfer is isolated in two layers:

- `G8BookIIILemniscateTauProfiniteLobeIdentificationSource`
- `G8BookIIILemniscateTauProfiniteWedgeTransferSource`

Those refine and feed the existing
`G8BookIIILemniscateTauProfiniteCompactMetricCorridor`.

## Next Constructor Target

The one-loop and two-loop targets are now discharged by `UnitAddCircle`:

```text
g8BookIIICh23CompactLoopConstructorTarget_unitAddCircle
G8BookIIICh23TwoLobeLoopConstructorTarget
g8BookIIICh23UnitAddCircleWedgeCore_closed
```

The next non-circular A1.1 targets are now:

```text
G8BookIIICh23ConcreteCompactMetricGraphTarget
G8BookIIICh23UnitAddCircleTauNativeA11ClosureTarget
G8BookIIICh23UnitAddCircleTauNativeMetricTransferTarget
G8BookIIILemniscateCh23CompactMetricGraphTarget
```

The concrete graph target must supply:

- quotient gluing at the crossing point;
- compactness of the wedge;
- topology/metric agreement for the graph topology and graph metric;
- shortest-path realization for the concrete `UnitAddCircle` wedge.

The tau-native transfer target must supply:

- a basepoint-preserving `UnitAddCircle ≃ TauCirclePoint` lobe equivalence;
- the induced quotient equivalence
  `G8Ch23UnitAddCircleWedgeCarrier ≃ LemniscateCarrier`;
- topology, metric, compactness, topology/metric agreement, and
  shortest-path realization transferred to the selected
  `LemniscateCarrierContext`;
- exact `status = .theoremBacked` for the carrier context.

The assembly target
`G8BookIIICh23UnitAddCircleTauNativeA11ClosureTarget` now packages the
concrete graph source, lobe equivalence, and exact transfer fields into one
load-bearing A1.1 closure object.  It forwards to
`G8BookIIICh23UnitAddCircleTauNativeMetricTransferTarget` and then to the
tau-native compact metric graph package.  This is an adapter closure, not an
unconditional construction of the missing graph metric or tau-circle
equivalence.

After this Ch.23 source is theorem-backed, the TauProfinite compatibility
route can be attacked through inhabitants of:

```text
G8BookIIILemniscateTauProfiniteLobeIdentificationSource
G8BookIIILemniscateTauProfiniteWedgeTransferSource
```

Those compatibility constructors must supply:

- tau-circle/profinite lobe identification;
- two-lobe wedge quotient agreement with `LemniscateCarrier`;
- compactness transfer from the two compact profinite lobes through the wedge
  quotient;
- topology/metric agreement on the wedge;
- graph distance as the shortest-path metric rather than the current zero
  scaffold.

## A1.2 Transfer Follow-Up

The Hilbert/domain layer has now also been refined as
`G8BookIIILemniscateTauProfiniteHilbertDomainTransferSource`.  This is the
proof-carrying target for:

- graph measure transfer from the two compact lobes;
- finite total graph measure and B/C lobe measure agreement;
- graph L2 inner-product readiness;
- value and derivative trace continuity;
- closed crossing agreement and Kirchhoff balance conditions.

It adapts into the existing `G8BookIIILemniscateKirchhoffDomainReadinessData`
and `G8BookIIILemniscateHilbertDomainSource` surfaces once supplied.

## Three-Target Compression

The Lean target economy is now:

```text
G8BookIIILemniscateTauProfiniteHilbertDomainTransferTarget
  <-> G8BookIIILemniscateTauProfiniteA1A2ThreeTarget
```

This is proved by
`g8BookIIILemniscateTauProfiniteA1A2ThreeTarget_iff_domainTransferTarget`.
The reason is structural: a Hilbert/domain transfer source contains a
`graphTransfer`, and that graph transfer contains the exact lobe-identification
source.  Thus target 3 coherently carries targets 1 and 2; it does not erase
them.

No actual-xi membership, final RH handoff, accepted tower coverage, determinant
transfer, O3, completion uniqueness, or finite spectral diagnostics are part of
these A1.1/A1.2 constructors.
