# G8 Lane A Scaled Operator Spectral Image Source Map

Private source map for the nonzero-height Lane A operator readout.

## What This Wave Adds

- Book III Ch. 24 reads the spectral parameter as a scaled centered quadratic:
  `iota_tau^2 * (s * (1 - s) - 1/4)`.
- The existing Lean Lane A spine consumes real-valuedness of the unscaled
  centered quadratic.
- The new scaled source layer proves the safe algebraic adapter: if a nonzero
  real scale times the centered quadratic is real, then the centered quadratic
  itself is real.

## Source Anchors

- Book III Ch. 23: the lemniscate operator package is the intended
  self-adjoint spectral carrier.
- Book III Ch. 24: the spectral correspondence uses the scaled parameter
  `iota_tau^2 * (s * (1 - s) - 1/4)`.
- Book III Ch. 25: real spectral values plus nonzero height force the critical
  line through the centered quadratic imaginary-part calculation.

## Guardrails

- The scale remains abstract in this wave.  The intended `iota_tau^2`
  instantiation belongs in a later compatibility layer.
- Finite self-adjoint, K5, spectral-correspondence, and determinant diagnostics
  remain evidence markers only.  They do not prove global spectral
  real-valuedness.
- The load-bearing input is still exact real-valuedness of the selected scaled
  operator spectral value, plus exact equality to the scaled centered
  quadratic.
- This module does not use downstream final-spine handoffs, accepted coverage,
  divisor transfer, pullback machinery, or determinant closure to prove the
  readout.

## Remaining Theorem

Instantiate the scaled source context from independent Book III
operator/spectral machinery:

```text
actual nonzero-height xi carrier
  -> Book III scaled operator spectral image
  -> exact scaled centered-quadratic alignment
  -> exact real-valuedness from the accepted self-adjoint spectral readout
```

Once supplied, the existing Lane A spine removes the nonzero real scale and
forwards to centered-address balance, sigma-fixedness, and the conditional final
handoff.
