# G8 Lane A Nonzero-Height Operator Readout Source Map

## Current State

The zero-height branch is already discharged through the paired eta/open-unit
route.  The remaining nonzero-height Lane A payload is now isolated in the
clean core theorem target:

```lean
G8ActualXiNonzeroHeightSpectralParameterReal
```

This target says that every actual nonzero-height orthodox `xi` carrier has
real centered quadratic parameter.

## New Source Contract

`G8ActualXiNonzeroHeightOperatorSpectralReadoutContext` is the operator-facing
contract for the next Book III theorem.  It requires:

- a `LemniscateOperatorContext`;
- proof that `LemniscateOperatorReady` holds for that context;
- a declared spectral value for each actual nonzero-height carrier;
- exact equality with `orthodoxXiCarrierCenteredQuadratic`;
- exact real-valuedness of the declared spectral value.

Those last two fields are load-bearing.  They are the only facts consumed to
prove the nonzero-height spectral payload.

## Diagnostics

Finite self-adjointness, K5 diagonal, and finite spectral-correspondence checks
remain diagnostic support.  They may guide the future Book III/operator proof,
but they do not by themselves prove the global real-valued readout.

## Remaining Mathematical Theorem

The next real theorem is to instantiate the operator readout context from
independent Book III spectral machinery:

```text
self-adjoint lemniscate operator readout
  -> real spectral value
  -> exact centered-quadratic alignment
```

This must not be derived from downstream RH-facing modules, accepted coverage,
the final live hinge, O3, full divisor transfer, or analytic-completion
uniqueness.
