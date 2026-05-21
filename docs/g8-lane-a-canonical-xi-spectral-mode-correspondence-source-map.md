# G8 Lane A Canonical Xi Spectral Mode Correspondence Source Map

## Purpose

This note records the next proof-facing split after canonical xi spectral mode
membership.

The Lean module
`TauLib.BookIII.Bridge.G8CanonicalXiSpectralModeCorrespondenceSource` expresses
the mode theorem through the finite Book III coordinate readout:

```text
spectralIndex, stage
  -> mode = spectral_parameter spectralIndex stage
  -> canonical iota_tau^2-scaled xi value = lemniscate_eigenvalue mode.
```

The coordinate data explains where the mode comes from. The equality with the
lemniscate eigenvalue remains the load-bearing theorem.

## Closed In Lean

- Coordinate diagnostics for `spectral_param_check`,
  `spectral_correspondence_finite`, and `eigenvalue_nesting_check`.
- Coordinate mode selector:
  `g8CanonicalXiSpectralCoordinateMode`.
- Theorem-backed finite algebra: the coordinate mode is bounded by the stage,
  and the selected eigenvalue is definitionally `mode^2`.
- Pointwise correspondence certificate to canonical spectral mode certificate.
- Global correspondence source to:
  - `G8CanonicalXiSpectralModeMembershipSource`;
  - `G8CanonicalXiSpectralModeMembershipAll`;
  - standard eigenvalue index source;
  - nonzero-height spectral-parameter reality.
- Falsifiers for diagnostics-only evidence, wrong extracted mode, missing exact
  coordinate equality, and boundedness-only data.

## Still Open

The mathematical payload is now:

```text
for each actual nonzero-height xi carrier,
construct spectralIndex and stage from independent Book III spectral machinery
and prove the exact eigenvalue equality.
```

Finite checks support the coordinate story but do not construct the global
actual-xi correspondence theorem.

## Guardrails

Do not replace exact equality with:

- finite-stage booleans;
- mode boundedness;
- approximate numerical agreement;
- axis-offset or BoundaryNF data;
- accepted-tower coverage;
- final live hinge or RH handoff;
- divisor transfer, determinant transfer, O3, or completion uniqueness.

The next implementation target should instantiate the correspondence source
from a genuine Book III operator/spectral-coordinate construction.
