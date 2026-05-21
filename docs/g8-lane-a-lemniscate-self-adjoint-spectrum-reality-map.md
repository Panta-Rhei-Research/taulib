# G8 Lane A Lemniscate Self-Adjoint Spectrum Reality Map

This note records the new generic operator-theory split for the nonzero-height
Lane A route.

## New Split

The remaining canonical self-adjoint reality source is factored into:

```text
ready lemniscate operator package
  -> spectral-membership predicate on complex values
  -> self-adjoint spectrum-reality selector
  -> canonical xi scaled value is a member
```

The generic operator theorem is:

```text
if lambda is a spectral member, then Im(lambda) = 0
```

The actual xi theorem is now only:

```text
for every nonzero-height actual xi carrier z,
g8ActualXiIotaTauCanonicalScaledOperatorSpectralValue z
is a member of that lemniscate spectral predicate.
```

## Closed By This Layer

The new Lean surface proves that:

```text
generic self-adjoint spectrum reality
  + canonical xi spectral membership
  -> G8ActualXiIotaTauCanonicalSelfAdjointRealitySource
  -> G8ActualXiNonzeroHeightSpectralParameterReal
```

So the proof spine no longer needs a custom pointwise real-valuedness theorem for
actual xi values. It can consume the generic spectral theorem plus membership.

## Guardrails

Finite self-adjoint, K5, and finite correspondence checks remain diagnostics.
They do not imply either generic spectral reality or canonical xi membership.

The route remains upstream of final RH handoff, accepted coverage, determinant
transfer, full divisor transfer, completion uniqueness, and the legacy O3
module.

## Next Payload

Instantiate the generic source from a genuine Book III lemniscate operator
theorem, then separately prove canonical actual xi membership in that spectrum.

This is now the clean nonzero-height Lane A source target.
