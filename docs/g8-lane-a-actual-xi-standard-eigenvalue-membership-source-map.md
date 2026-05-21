# G8 Lane A Actual Xi Standard Eigenvalue Membership Source Map

This note records the current Lane A payload after the spectral-coordinate
readout split.

## Closed

- The canonical `iota_tau^2` scaled actual-xi value has a fixed Lean readout.
- Standard lemniscate eigenvalues are theorem-backed as real complex readouts.
- Finite Book III coordinates add no extra strength: `spectral_parameter n n`
  represents mode `n`, so coordinate realization is equivalent to standard
  eigenvalue membership.

## New Source Layer

`G8ActualXiStandardEigenvalueMembershipSource` packages the exact payload as:

```text
actual nonzero-height xi carrier
  -> mode : Nat
  -> canonical scaled value = lemniscate_eigenvalue mode
```

The finite projector, spectral-resolution, finite-correspondence, and
self-adjoint checks are recorded only as diagnostics.

## Remaining Mathematical Payload

The next theorem is exact actual-xi spectral membership in the standard
lemniscate eigenvalue spectrum.  Finite diagnostics, bounded coordinate modes,
or approximate numerical agreement do not prove this theorem.

Forbidden proof sources remain: RH handoff, final live hinge, accepted carrier
coverage, O3, full divisor transfer, determinant transfer, completion
uniqueness, and legacy universal spectral correspondence.
