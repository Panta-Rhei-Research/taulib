# G8 Lane A Canonical Xi Spectral Mode Membership Map

## Purpose

This note records the next Lane A nonzero-height hinge after the standard
lemniscate eigenvalue source.

The Lean module
`TauLib.BookIII.Bridge.G8CanonicalXiSpectralModeMembership` packages the exact
remaining theorem as pointwise mode membership:

```text
for every actual nonzero-height xi carrier z,
there is a mode n such that
canonical iota_tau^2-scaled xi value at z = lemniscate_eigenvalue n.
```

This is the source theorem needed to feed the standard eigenvalue spectrum
route. Once this mode certificate is supplied, the existing adapters recover the
standard index source, nonzero-height spectral-parameter reality, and the
downstream Lane A assembly.

## Closed In Lean

- Pointwise certificate shape:
  `G8CanonicalXiSpectralModeCertificate`.
- Pointwise membership:
  `G8CanonicalXiSpectralModeMembership`.
- Global membership:
  `G8CanonicalXiSpectralModeMembershipAll`.
- Equivalence with standard eigenvalue-spectrum membership.
- Equivalence with the existing
  `G8ActualXiIotaTauCanonicalStandardEigenvalueIndexSource`.
- Adapter from mode membership to nonzero-height spectral-parameter reality.
- Falsifiers for missing modes, wrong exact image equality, and
  diagnostics-only evidence.

## Still Open

The remaining mathematical theorem is not that standard lemniscate eigenvalues
are real; that is already closed. The remaining theorem is exact mode
construction:

```text
actual canonical scaled xi spectral value
  -> standard lemniscate mode n
  -> exact equality with n^2.
```

This must come from independent Book III spectral correspondence or operator
image machinery.

## Guardrails

Finite self-adjoint, K5, or correspondence checks are useful diagnostics, but
they do not construct the mode certificate.

The mode equality must be exact. It must not be replaced by axis-offset data,
approximate numerical agreement, finite-stage evidence, accepted-tower coverage,
the final live hinge, divisor transfer, determinant transfer, O3, or any
downstream RH-facing handoff.

## Next Stone

The next plausible module should instantiate or further decompose:

```text
G8CanonicalXiSpectralModeMembershipAll
```

from a Book III spectral correspondence source. A good name would be:

```text
G8CanonicalXiSpectralModeCorrespondenceSource
```

Its honest payload should be the exact bridge from the canonical scaled
operator image to the standard lemniscate eigenvalue ladder.
