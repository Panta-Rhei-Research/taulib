# G8 Lane A Height-Split Spectral Reality Map

Private bridge-engineering note for the refined Lane-A spectral-reality route.

## What Changed

The earlier Lane-A input package asked for nonzero imaginary height for every
actual orthodox `xi` carrier.  The height-split corridor weakens that:

```text
zero-height carrier      -> explicit zero-height axis guard
nonzero-height carrier   -> real centered quadratic + algebra forces axis
```

Lean records this in `G8ActualXiHeightSplitSpectralRealityInputs`.

## What Closed

The nonzero-height branch is now pure assembly:

- `orthodoxXiCarrierCenteredQuadratic_im` gives the imaginary readout.
- `g8CenteredQuadraticReality_forces_re_eq_half` gives the algebraic forcing.
- The existing centered-address reduction turns carrier off-critical exclusion
  into B/C balance and actual sigma-fixedness.

The previous stronger `G8ActualXiSpectralRealityInputs` still derives the new
height-split package by making the zero-height branch impossible.

## What Remains Open

The two live mathematical targets are now sharper:

- `spectralParameterReal`: the centered quadratic parameter is real from an
  independent self-adjoint/spectral readout.
- `zeroHeightAxis`: zero-height actual `xi` carriers are on the receiving
  critical axis, or are excluded from the relevant carrier stream.

## Guardrail

Neither target may be proved from actual sigma-fixedness, accepted tower
coverage, the final live hinge, O3 as an ambient assumption, full divisor
transfer, or Mathlib's `RiemannHypothesis` target.  Those are downstream
handoffs, not sources for Lane-A spectral inputs.
