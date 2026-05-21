# G8 Lane A Book III Operator Spectral Image Source Map

Private bridge-engineering note for the sharpened nonzero-height Lane A source.

## Closed In Lean

- The certified `iota_tau^2` scale is nonzero.
- A real nonzero scaled image forces the unscaled centered quadratic to be real.
- The zero-height branch is already discharged through the eta/open-unit path.
- The new source split separates two exact obligations:
  - Book III scaled-image law;
  - self-adjoint spectral-reality readout.

## Current Lean Surface

`G8ActualXiIotaTauBookIIIOperatorSpectralImageSource` is the combined source
package.  It contains:

- `operatorCtx` and `operatorReady`;
- `operatorSpectralValue`;
- `imageLaw`, whose load-bearing field is exact equality
  `operatorSpectralValue z = iota_tau^2 * centeredQuadratic z`;
- `selfAdjointReality`, whose load-bearing field is exact real-valuedness for
  selected values known to be in the operator spectrum.

The adapter
`G8ActualXiIotaTauBookIIIOperatorSpectralImageSource.toSpectralParameterReal`
forwards this package into the existing nonzero-height Lane A route.

## Still Open

The remaining mathematical implementation target is to instantiate the two
source pieces from independent Book III machinery:

```text
actual nonzero-height xi carrier
  -> Book III scaled spectral image law
  -> selected image belongs to the self-adjoint spectral readout
  -> selected image is real-valued
```

Finite self-adjoint, K5, and spectral-correspondence checks remain diagnostic
support.  They are not promoted to global real-valuedness, and this route does
not use RH-facing downstream modules, O3, determinant transfer, full divisor
transfer, accepted coverage, or analytic-completion uniqueness.
