# G8 Lane A Spectral Reality Core Map

Private bridge-engineering note for the Lane-A spectral-reality route.

## What Closed

The centered quadratic readout is pure algebra:

```text
Im (s * (1 - s) - 1/4) = Im(s) * (1 - 2 * Re(s)).
```

Lean records this as `orthodoxXiCarrierCenteredQuadratic_im` in the low-level
spectral-reality core.  The old `centeredQuadratic_readout` field is therefore
bookkeeping, not a mathematical bottleneck.

## What Remains Open

Lane A now has exactly two live inputs:

- `spectralParameterReal`: the centered quadratic parameter of each actual
  orthodox `xi` carrier is real.
- `nontrivialHeight`: each actual carrier in this lane has nonzero imaginary
  height.

Together with the algebraic readout, these inputs force the critical axis and
therefore crossing-mediated centered-address balance.

## Guardrail

The two live inputs must not be proved from actual sigma-fixedness, accepted
tower coverage, the final live hinge, O3 as an ambient assumption, full divisor
transfer, or Mathlib's `RiemannHypothesis` target.  They need an independent
spectral/determinant/self-adjoint readout theorem or a restricted carrier with
explicit nonzero-height evidence.
