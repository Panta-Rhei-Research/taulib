# G8 Lane A Iota-Tau Operator Spectral Image Source Map

## Current Closed Pieces

- The certified 500-digit `iota_tau` tower value is available through
  `TauReal.iota_tau_bbp_certified_500d`.
- `g8IotaTau500dSquaredSpectralScale` supplies a theorem-backed nonzero real
  scale for the intended `iota_tau^2` operator image.
- `G8ActualXiNonzeroHeightScaledOperatorSpectralImageContext` proves the safe
  algebraic adapter: if a nonzero real scale times the centered quadratic is
  real, then the unscaled centered quadratic is real.

## Exact Remaining Source Theorem

The nonzero-height Lane-A source theorem is now:

```text
for every actual nonzero-height xi carrier z,
  operatorSpectralValue z =
    iota_tau^2 * orthodoxXiCarrierCenteredQuadratic z
and
  Im (operatorSpectralValue z) = 0.
```

In Lean this is packaged by
`G8ActualXiIotaTauOperatorSpectralImageSourceContext`.

## What Counts As Evidence

- Load-bearing evidence:
  - exact `iota_tau^2` scaled centered-quadratic alignment;
  - exact real-valuedness of the selected operator spectral value.
- Diagnostic evidence only:
  - finite self-adjoint checks;
  - finite K5 diagonal checks;
  - finite spectral-correspondence checks;
  - the numerical scale certificate by itself.

## Guardrail

This source layer must not be discharged from `RiemannHypothesis`, accepted
coverage, the final live hinge, O3, full divisor transfer, determinant transfer,
or analytic-completion uniqueness.  The remaining mathematical work is to
instantiate the source context from independent Book III operator/spectral
machinery.
