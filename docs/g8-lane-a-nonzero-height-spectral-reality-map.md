# G8 Lane A Nonzero-Height Spectral Reality Map

Private bridge-engineering note for the next Lane-A climb.

## What Closed Before This Wave

- The zero-height branch is theorem-backed by the paired eta/open-unit route:
  `g8ActualXiZeroHeightAxisGuardDischarge_from_pairedPositiveHalfPlane`.
- Therefore zero-height actual `xi` carriers no longer need to be handled by
  the spectral-parameter reality theorem.

## New Minimal Payload

The remaining Lane-A spectral input is now:

```text
for every nonzero-height OrthodoxXiZeroCarrier z,
Im (orthodoxXiCarrierCenteredQuadratic z) = 0.
```

Lean records this as:

```text
G8ActualXiNonzeroHeightSpectralParameterReal
```

and packages it with the already-closed zero-height guard as:

```text
G8ActualXiNonzeroHeightSpectralRealityInputs
```

## What This Wave Adds

- `G8ActualXiNonzeroHeightSpectralParameterReal` is equivalent to excluding
  off-critical carriers on the nonzero-height subtype.
- The sharpened package still supplies:
  - no carrier off-criticality;
  - actual centered-address balance;
  - actual sigma-fixedness;
  - crossing-mediated evidence;
  - the existing final live hinge when paired with accepted tower realization.
- The older global height-split package maps into the new package, but not
  conversely.  This preserves the strictly weaker proof burden.

## Next Sprint Stack

1. Build a concrete spectral-readout interface for the nonzero-height centered
   quadratic parameter.
2. Isolate the self-adjoint/operator-theoretic field that makes that parameter
   real.
3. Prove or reduce the nonzero-height spectral reality theorem from that
   field, without using actual sigma-fixedness, accepted coverage, final RH
   handoff, O3, full divisor transfer, or analytic-completion uniqueness.
4. In parallel, continue the Book III tower lane:
   `G8BookIIIAcceptedTowerRealizationFromSigmaFixed`.

## Guardrail

This wave does not prove the nonzero-height spectral theorem.  It makes the
theorem smaller and exact.  The remaining mathematical payload is now the
operator/spectral reason why the centered quadratic parameter attached to an
actual nonzero-height `xi` carrier is real.
