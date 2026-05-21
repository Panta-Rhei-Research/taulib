# G8 Lane A Abstract Spectral Membership Source Map

Private implementation note, May 21, 2026.

## What Landed

`TauLib.BookIII.Bridge.G8ActualXiCanonicalAbstractSpectralMembershipSource`
formalizes the weak Lane A route from the red-team memo:

```text
operator-native spectral membership
  + self-adjoint real-valuedness for members
  + canonical actual-xi membership
  -> nonzero-height spectral-parameter reality
```

The module adds `G8LemniscateSpectralMembershipLegitimacy`, which keeps the
operator-native provenance explicit, and
`G8ActualXiCanonicalAbstractSpectralMembershipSource`, which carries the
pointwise canonical actual-xi membership theorem.

## Closed Adapters

- abstract source to `G8LemniscateSelfAdjointSpectrumRealitySource`;
- abstract source to `G8ActualXiIotaTauCanonicalSelfAdjointRealitySource`;
- abstract source to `G8ActualXiIotaTauBookIIIOperatorSpectralImageSource`;
- abstract source to `G8ActualXiNonzeroHeightSpectralParameterReal`;
- abstract source to the existing nonzero-height operator readout context.

## Live Payload

The remaining theorem is still mathematical:

```text
each canonical scaled actual nonzero-height xi value is a genuine member
of an operator-native self-adjoint lemniscate spectral source
```

The source must not be a predicate defined only to contain the canonical values.
It should come from the Book III operator spectrum/readout machinery.

## Guardrails

Finite checks remain diagnostic unless they provide exact global membership and
exact real-valuedness. The route does not use the final live hinge, accepted
coverage, divisor transfer, completion uniqueness, determinant transfer, O3, or
any downstream critical-axis conclusion.
