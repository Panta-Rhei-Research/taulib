# G8 Lane A A2 Proof-Step Ledger V3

Private working ledger for the now-discharged Lane A A2 operator-native
self-adjoint spectral provenance route.

This V3 supersedes the active-planning role of
`docs/g8-lane-a-a1-a2-proof-step-ledger-v2.md`.  V2 remains the historical
record of the A1/A2 climb.  V3 starts from the new official state:

```text
A1 operator readiness                         closed / theorem-backed
A2 operator-native self-adjoint provenance    closed / theorem-backed
A3 canonical actual-xi membership             open / official axiom
```

The official weak Lane A ledger now has expected temporary axioms `1`.
This file records the A2 retirement.  It does not use A3 canonical actual-xi
membership, final live hinge, accepted coverage, determinant transfer, O3,
divisor transfer, completion uniqueness, or the Mathlib RH discharge.

## Current Official State

The official Lane A ledger is:

```lean
g8LaneA_operatorReadyGate_axiom
```

This historical name is now a `noncomputable def`, not an axiom.  It is backed
by the selected Ch.23 floor-normalized A1.1-A1.6 route:

```text
compact metric graph
  -> Hilbert/Sobolev/Kirchhoff domain
  -> edgewise Kirchhoff Laplacian
  -> boundary-form cancellation
  -> maximal Kirchhoff self-adjoint extension
  -> compact resolvent
  -> discrete point-spectrum consequence
  -> LemniscateOperatorReady
```

The former A2 ledger gate is:

```lean
g8LaneA_operatorNativeSelfAdjointGate_axiom :
  G8LaneAOperatorNativeSelfAdjointGate g8LaneA_operatorReadyGate_axiom
```

Despite the historical name, this is now a `noncomputable def`, not an axiom.
It is backed by a theorem-backed constructor whose load-bearing content is a
strict `G8OperatorNativeSpectralProvenance` over the A1-ready operator context.

## Existing Lean Surfaces

The strict A2 target is already shaped in:

- `TauLib.BookIII.Bridge.G8LaneAOperatorNativeSelfAdjointSource`
- `TauLib.BookIII.Bridge.G8BookIIILaneAOperatorSelfAdjointProofSource`
- `TauLib.BookIII.Bridge.G8BookIIILaneAOperatorSelfAdjointProofSteps`
- `TauLib.BookIII.Bridge.G8BookIIICh23FloorNormalizedA2SelectedOperatorReadySource`
- `TauLib.BookIII.Bridge.G8BookIIICh23FloorNormalizedA2EigenpairPointSpectrumSource`
- `TauLib.BookIII.Bridge.G8ActualXiCanonicalAbstractSpectralMembershipSource`

The core strict provenance object is:

```lean
G8OperatorNativeSpectralProvenance
  (operatorCtx : LemniscateOperatorContext)
  (operatorReady : LemniscateOperatorReady operatorCtx)
```

Its load-bearing fields are:

```lean
spectralMembership : G8LemniscateSpectrumMembership operatorCtx operatorReady
nativeMembership : C -> Prop
kind : G8OperatorNativeSpectralProvenanceKind
spectralMembership_iff_native :
  forall spectralValue, spectralMembership spectralValue <-> nativeMembership spectralValue
selfAdjointReality_native :
  forall spectralValue, nativeMembership spectralValue -> spectralValue.im = 0
```

The preferred A2 route uses the existing eigenpair surface:

```lean
G8BookIIILemniscateEigenpairData
G8BookIIILemniscateEigenpairPointSpectrumMembership
G8BookIIILemniscateEigenpairRealitySource
G8BookIIILemniscateEigenpairPointSpectrumProvenance
```

The generic eigenpair carrier has now been sharpened: native eigenpair data
must carry the selected domain/eigen-equation evidence, a nonzero norm-square,
and the self-adjoint scalar-pairing identity

```text
lambda * normSq = conjugate(lambda) * normSq
normSq != 0
```

This is the exact A2.3/A2.4 hinge.  Once a value is a native eigenpair member,
the reality proof is pure cancellation and `Complex.conj_eq_iff_im`.

The important adapter is already closed:

```lean
G8BookIIILemniscateEigenpairPointSpectrumProvenance.toAnalyticPointSpectrumSource
```

It makes `exportedMembership` and `nativeMembership` the same eigenpair
predicate, so exported/native agreement is definitional once the eigenpair
provenance source is built.

## A1 Infrastructure To Reuse

A2 should build on the selected A1 route, not rebuild it.

Closed A1 anchors:

- `g8BookIIICh23FloorNormalizedA11CompactMetricGraphTarget_closed`
- `g8BookIIICh23FloorNormalizedA12HilbertReadinessTarget_closed`
- `g8BookIIICh23FloorNormalizedA12TraceReadinessTarget_closed`
- `g8BookIIICh23FloorNormalizedA12KirchhoffDomainTarget_closed`
- `g8BookIIICh23FloorNormalizedA15MaximalKirchhoffSelfAdjointExtensionTarget_closed`
- `g8BookIIICh23FloorNormalizedA16ResolventCompactnessTarget_closed`
- `g8BookIIICh23FloorNormalizedA16DiscretePointSpectrumTarget_closed`
- `g8BookIIICh23FloorNormalizedA16SelectedDiscreteSpectrumNoStandardModeEqualityClaim_closed`

The private official-ledger A1 projection now has a public A2.0 counterpart:

```lean
g8BookIIICh23FloorNormalizedA2SelectedOperatorReadySource :
  G8BookIIILemniscateOperatorReadySource
```

A2 should consume this public Book III source module rather than depending on
the quarantined ledger helper.

## A2 Proof-Step Ledger

| Step | Obligation | Status | Next Lean target |
| --- | --- | --- | --- |
| A2.0 | Public selected A1 operator-source anchor for A2 | Closed | `G8BookIIICh23FloorNormalizedA2SelectedOperatorReadySource` exposes `g8BookIIICh23FloorNormalizedA2SelectedOperatorReadySource : G8BookIIILemniscateOperatorReadySource` without importing the quarantine ledger. |
| A2.1 | Define the operator-native point-spectrum predicate | Closed | `G8BookIIICh23FloorNormalizedA2NativePointSpectrum` is definitionally `G8BookIIILemniscateEigenpairPointSpectrumMembership g8BookIIICh23FloorNormalizedA2SelectedCompactResolventSource`, with `G8BookIIICh23FloorNormalizedA2NativePointSpectrumDefinitionTarget` closed. |
| A2.2 | Prove exported/native membership agreement | Closed | The selected eigenpair predicate is used as both exported and native membership; the adapter `toAnalyticPointSpectrumSource` closes agreement by `rfl`. |
| A2.3 | Define exact eigenpair data for the selected operator | Closed | `G8BookIIILemniscateEigenpairData` now carries domain/eigen-equation evidence, nonzero eigenfunction evidence, `pairingNormSq`, `pairingNormSq_ne_zero`, and `selfAdjointScalarPairingIdentity`. The selected alias `G8BookIIICh23FloorNormalizedA2SelectedEigenpairData` and target `G8BookIIICh23FloorNormalizedA2SelectedEigenpairDataTarget` are closed. |
| A2.4 | Prove self-adjoint eigenpair reality | Closed | `g8BookIIICh23FloorNormalizedA2SelfAdjointEigenpairRealityCalculusTarget_closed` proves the conjugate-eigenvalue equality from certified selected eigenpair data, and `g8BookIIICh23FloorNormalizedA2EigenpairRealityTarget_closed` packages the selected reality source. |
| A2.5 | Package strict operator-native provenance | Closed | `g8BookIIICh23FloorNormalizedA2EigenpairPointSpectrumProvenance_ofRealityTarget`, `g8BookIIICh23FloorNormalizedA2AnalyticPointSpectrumProvenance_ofRealityTarget`, and `g8BookIIICh23FloorNormalizedA2OperatorNativeProvenance_ofRealityTarget` are in place. |
| A2.6 | Package `G8LaneAOperatorNativeSelfAdjointSource` | Closed | `g8BookIIICh23FloorNormalizedA2LaneAOperatorNativeSelfAdjointSource_closed` builds the theorem-backed A1/A2 source. No A3 membership enters. |
| A2.7 | Retire the official A2 ledger axiom | Closed | `g8LaneA_operatorNativeSelfAdjointGate_axiom` is now a theorem-backed `noncomputable def`. Expected weak Lane A axioms are now `1`; full RH ledger axioms are now `2`; global no-sorry scan expectation is now `8`. |

## A2.4 Analytic Core

The substantial mathematical proof inside A2 is now exposed at the exact
eigenpair-data boundary: native membership itself requires the scalar
self-adjoint pairing identity and nonzero norm-square.  Therefore A2.4 is a
theorem-backed algebraic consequence of A2.3.

Selected target shape:

```lean
G8BookIIILemniscateEigenpairRealitySource
  g8BookIIICh23FloorNormalizedA2SelectedCompactResolventSource
```

The proof should split into small stones:

1. Eigenpair equation pairing:

```text
H u = lambda u
  -> <H u, u> = <lambda u, u>
```

2. Self-adjoint symmetry:

```text
<H u, u> = <u, H u>
```

3. Scalar extraction:

```text
<lambda u, u> = lambda * <u, u>
<u, lambda u> = conjugate(lambda) * <u, u>
```

4. Nonzero norm:

```text
u != 0 -> <u, u> != 0
```

5. Cancellation:

```text
lambda * <u,u> = conjugate(lambda) * <u,u>
  -> lambda = conjugate(lambda)
  -> lambda.im = 0
```

This is classical self-adjoint point-spectrum reality.  In our Lean code, the
closed split is:

```lean
g8BookIIICh23FloorNormalizedA2SelfAdjointEigenpairRealityCalculusTarget_closed
  -> g8BookIIICh23FloorNormalizedA2EigenpairRealityTarget_closed
```

The selected certified eigenpair data produces the conjugate-eigenvalue
equality:

```text
lambda = conjugate(lambda)
```

Lean then proves `lambda.im = 0` from `Complex.conj_eq_iff_im`.

## Recommended Next Wave

The next implementation wave should move to A3:

```text
canonical actual-xi membership in the selected certified eigenpair predicate
```

Suggested starting import:

```lean
import TauLib.BookIII.Bridge.G8BookIIICh23FloorNormalizedA2EigenpairPointSpectrumSource
```

Suggested contents:

1. define the selected A3 membership target against
   `g8BookIIICh23FloorNormalizedA2LaneAOperatorNativeSelfAdjointSource_closed.legitimacy`;
2. construct, for each actual nonzero-height carrier, selected certified
   eigenpair data for its canonical scaled value;
3. keep exact operator alignment and nonzero norm-square evidence explicit;
4. package the result as the remaining `G8LaneACanonicalActualXiMembershipGate`.

Do not introduce axioms or sorries.  Do not fill `operatorNativeSource` with a
bare `True`.

## What A2 Must Not Do

- It must not mention actual `xi` carriers or canonical actual-xi membership.
  That is A3.
- It must not use finite checks, bounded numeric diagnostics, or standard
  `n^2` mode data as proof of operator-native spectral provenance.
- It must not use `RiemannHypothesis`, final live hinge, accepted coverage,
  O3, determinant transfer, divisor transfer, completion uniqueness, or legacy
  universal spectral-correspondence modules.
- It must not assert exact standard-mode equality.  A2 only needs
  operator-native self-adjoint spectral legitimacy and real-valuedness.

## Success Criteria

A2 is discharged because:

```lean
g8LaneA_operatorNativeSelfAdjointGate_axiom
```

is no longer an axiom and has been replaced by a theorem-backed constructor.

Expected audit results after A2:

```text
make lane-a-axiom-ledger        axioms=1, sorry=0
make full-rh-axiom-ledger       axioms=2, sorry=0
make fine-rh-axiom-ledger       unchanged unless separately rewired
python3 scripts/check_no_sorry.py --root TauLib --expected-axioms 8 --expected-sorry 0
make rh-mathlib-discharge-axiomfree
lake build
```

At that point Lane A has exactly one remaining weak-route gate: A3 canonical
actual-xi membership in the legitimate operator-native spectral predicate.
