# G8 Lane A Axiom Ledger Map

Private audit note, May 21, 2026.

## Purpose

`TauLib.BookIII.Bridge.G8LaneAAxiomLedger` is a quarantined tracking module.
It is not imported by `TauLib.BookIII` and is not part of the axiom-free final
spine. Its job is to mark the remaining Lane A gates as explicit Lean axioms so
we can audit and retire them one by one.

## Current Ledger Count

Expected temporary axioms: `3`.

1. `g8LaneA_operatorReadyGate_axiom`
   Independent readiness of the Book III lemniscate operator package.

2. `g8LaneA_operatorNativeSelfAdjointGate_axiom`
   Operator-native self-adjoint spectral-membership legitimacy and member
   real-valuedness.

3. `g8LaneA_canonicalActualXiMembershipGate_axiom`
   Canonical actual nonzero-height xi values belong to that operator-native
   spectral source.

## What The Ledger Closes

With those three explicit gates, the module derives:

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

The expected count should drop from `3` to `2`, then `1`, then `0` as each gate
is replaced by a theorem-backed constructor.

## Guardrail

This ledger is an audit harness, not a proof claim. It does not import the final
RH handoff, accepted coverage, divisor transfer, completion uniqueness,
determinant transfer, or the older O3 bridge.

The strong standard-mode route remains separately tracked. Exact standard
eigenvalue alignment implies the weak minimal route, but the weak route does not
assert discrete standard `n^2` membership.
