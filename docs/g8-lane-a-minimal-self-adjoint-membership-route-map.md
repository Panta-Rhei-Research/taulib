# G8 Lane A Minimal Self-Adjoint Membership Route Map

Private audit note, May 21, 2026.

## Purpose

`TauLib.BookIII.Bridge.G8ActualXiMinimalSelfAdjointMembershipRoute` records the
weaker Lane A route now preferred for the nonzero-height branch.

The strong standard-mode route remains useful as an optional strengthening, but
Lane A itself only needs an operator-native self-adjoint spectral predicate that
contains the canonical actual-`xi` scaled values.

## Minimal Chain

```text
operator readiness
  + operator-native self-adjoint spectral legitimacy
  + canonical actual-xi membership
  -> nonzero-height spectral-parameter reality
  -> zero-height/paired-eta height split
  -> actual sigma-fixedness
  -> final live hinge once accepted tower realization is supplied
```

In Lean, the minimal target is:

```lean
G8ActualXiMinimalSelfAdjointMembershipTarget operatorCtx operatorReady
```

It is just `Nonempty (G8ActualXiCanonicalAbstractSelfAdjointRouteSource
operatorCtx operatorReady)`.

## What The Module Proves

- The minimal target implies `G8ActualXiNonzeroHeightSpectralParameterReal`.
- The minimal target implies `G8ActualXiNonzeroHeightSpectralRealityInputs`
  using the theorem-backed paired-eta zero-height branch.
- The minimal target implies `G8ActualXiBoundaryCharacterSigmaFixed`.
- The minimal target plus `G8BookIIIAcceptedTowerRealizationFromSigmaFixed`
  builds `G8FinalLiveHinge`.
- Exact standard-mode alignment implies the minimal weak target.

## What It Does Not Prove

- It does not instantiate operator readiness.
- It does not instantiate operator-native self-adjoint legitimacy.
- It does not instantiate canonical actual-`xi` membership in the legitimate
  spectral predicate.
- It does not claim the weak route implies discrete standard eigenvalue
  membership.

## Relationship To Ledgers

The quarantined weak ledger remains:

```text
G8LaneAAxiomLedger -> G8FullRHSpineAxiomLedger
```

The current Lane A ledger still has three temporary gates:

1. operator readiness;
2. operator-native self-adjoint spectral legitimacy;
3. canonical actual-`xi` membership.

The full-spine ledger adds the accepted tower realization gate. This wave
does not reduce those counts; it only makes the minimal route reusable outside
the quarantine ledger.

## Guardrails

Finite diagnostics are support evidence, not operator-native legitimacy.
Canonical-values-only predicates are also insufficient unless the source is
operator-native and carries self-adjoint real-valuedness.

The strong L3b-E standard-mode route remains tracked separately. It implies the
minimal weak route, but the reverse direction is intentionally absent.
