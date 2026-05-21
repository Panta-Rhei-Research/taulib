# G8 Lane A Standard Lemniscate Eigenvalue Spectrum Source Map

This note records the next nonzero-height Lane A split.

## Closed By This Layer

The standard Book III lemniscate spectrum is now represented as:

```text
lambda is spectral
  iff
lambda = lemniscate_eigenvalue n for some n
```

Since `lemniscate_eigenvalue n = n^2`, every such complex readout has imaginary
part zero.  This instantiates the generic self-adjoint spectrum-reality source
without using final RH handoff, accepted coverage, determinant transfer, O3, or
full divisor transfer.

## Remaining Actual Xi Payload

The actual `xi` side is not closed by finite checks.  The next theorem is the
exact mode-index target:

```text
for every nonzero-height actual xi carrier z,
g8ActualXiIotaTauCanonicalScaledOperatorSpectralValue z
  = lemniscate_eigenvalue (modeOf z)
```

This exact equality supplies canonical membership in the standard spectrum and
then feeds the existing nonzero-height spectral-parameter reality corridor.

## Guardrails

Finite self-adjoint, K5, and finite spectral-parameter checks remain
diagnostics.  They support the intended operator picture, but they do not supply
the global actual-`xi` mode index.

The remaining theorem is an operator/spectral correspondence theorem for the
canonical actual-`xi` scaled image, not a statement about downstream RH-facing
coverage.
