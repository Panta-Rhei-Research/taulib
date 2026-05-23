# G8 Lane A Axiom Ledger Map

Private audit note, May 21, 2026.  Updated May 23, 2026 after the selected
Ch.23 A1 operator-readiness route and A2 certified eigenpair point-spectrum
route were wired into the official ledger.

## Purpose

`TauLib.BookIII.Bridge.G8LaneAAxiomLedger` is a quarantined tracking module.
It is not imported by `TauLib.BookIII` and is not part of the axiom-free final
spine. Its job is to mark the remaining Lane A gates as explicit Lean axioms so
we can audit and retire them one by one.

## Current Ledger Count

Expected temporary axioms: `1`.

Retired theorem-backed constructor:

- `g8LaneA_operatorReadyGate_axiom`
  This legacy-named object is now a `noncomputable def`, not an axiom.  It is
  backed by the selected Ch.23 floor-normalized A1.1-A1.6 operator route:
  compact metric graph, Hilbert/Kirchhoff domain, edgewise Laplacian,
  boundary-form cancellation, maximal self-adjoint extension, compact
  resolvent, and discrete point-spectrum consequence.
- `g8LaneA_operatorNativeSelfAdjointGate_axiom`
  This legacy-named object is now a `noncomputable def`, not an axiom.  It is
  backed by the selected certified eigenpair point-spectrum carrier, whose
  native members carry the nonzero norm-square and self-adjoint scalar-pairing
  identity needed to prove member real-valuedness.

Remaining explicit axioms:

1. `g8LaneA_canonicalActualXiMembershipGate_axiom`
   Canonical actual nonzero-height xi values belong to that operator-native
   spectral source.

## What The Ledger Closes

With the theorem-backed A1/A2 constructors and this explicit A3 gate, the module
derives:

- `G8ActualXiNonzeroHeightSpectralParameterReal`;
- `G8ActualXiNonzeroHeightSpectralRealityInputs`, using the theorem-backed
  paired-eta zero-height branch;
- `G8ActualXiBoundaryCharacterSigmaFixed`;
- `G8ActualXiBoundaryReadoutCrossingMediatedAll`.

The reusable non-quarantine bridge for this chain is
`TauLib.BookIII.Bridge.G8ActualXiMinimalSelfAdjointMembershipRoute`. It packages
the same weak target as
`G8ActualXiMinimalSelfAdjointMembershipTarget operatorCtx operatorReady` and
forwards it through the theorem-backed zero-height branch and final live-hinge
adapters.

## Audit Target

Run:

```bash
make lane-a-axiom-ledger
```

The expected count should drop from `1` to `0` once A3 is replaced by a
theorem-backed constructor.

## Guardrail

This ledger is an audit harness, not a proof claim. It does not import the final
RH handoff, accepted coverage, divisor transfer, completion uniqueness,
determinant transfer, or the older O3 bridge.

The strong standard-mode route remains separately tracked. Exact standard
eigenvalue alignment implies the weak minimal route, but the weak route does not
assert discrete standard `n^2` membership.
