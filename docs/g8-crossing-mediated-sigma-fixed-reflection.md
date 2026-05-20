# G8 Crossing-Mediated Sigma-Fixed Reflection

Private mathematical reflection on the current final G8 hinge.

## Central Question

The current proof spine has reduced the remaining RH-strength hinge to one
precise question:

```text
Does every actual orthodox xi boundary readout land in the tau
crossing-mediated / sigma-fixed scalar fibre?
```

If that landing theorem is supplied, the existing Lean spine forwards it:

```text
crossing-mediated xi readout
  -> centered boundary address is B/C-balanced
  -> actual xi boundary character is sigma-fixed
  -> accepted Book III tower realization
  -> accepted centered-address coverage
  -> Mathlib RiemannHypothesis
```

This is not full zero-divisor equivalence.  It is an off-axis localization
route: an orthodox off-critical candidate would read as B/C imbalance in the
centered tau boundary address, while crossing-mediated / accepted tau readouts
are B/C-balanced.

## Objects

- **Prime polarity.**  Primes split into B/C channels by the Legendre `(2/p)`
  classifier.  Multiplicative arithmetic data accumulates through prime
  factorization into a B/C polarity profile.
- **Primorial ladder.**  `M_k = product of first k primes` is the canonical
  global test system.  It is not merely a finite cutoff; it is the coherent
  CRT/profinite address ladder through which boundary data is read.
- **Tau boundary normal form.**  `BoundaryNF` carries the B and C components.
  In the current Lean bridge, the critical balance predicate is exactly
  `BCBalanced nf`, i.e. equality of the B and C parts.
- **Crossing mediator `iota_tau`.**  The source papers characterize it as the
  unique non-polar, sigma-fixed, tail-stable crossing germ between the two
  lobes.  It is the canonical balanced mediator, not a B or C eigenstate.
- **Orthodox `xi` chart.**  Classical zero candidates are read through a
  centered chart around `Re(s) = 1/2`.  Lean now has theorem-backed binary
  hygiene: off-criticality is equivalent to the centered shadow being off-axis,
  and off-axis centered addresses normalize to B/C imbalance.

## What Is Theorem-Backed Now

- No-rogue / two-channel structure is necessary but not sufficient: a character
  can be two-channel and still fail to be sigma-fixed unless B and C agree.
- Pointwise sigma-fixedness of the canonical `xi` boundary character is
  equivalent to B/C balance of the normalized centered boundary address.
- Actual sigma-fixedness rejects carrier-level off-criticality pointwise.
- Accepted Book III tower witnesses are balanced, so an off-axis centered
  address cannot be an accepted centered address.
- The active final hinge is not O3, full divisor transfer, multiplicity
  transfer, or analytic completion uniqueness.  Those are stronger lanes.  The
  live lane is the actual `xi` readout landing in the crossing-mediated fixed
  fibre.

## Mathematical Proof Shape

1. Define the actual orthodox readout as a boundary character extracted from
   the centered `xi` carrier.
2. Prove this readout is not merely two-channel, but sigma-equivariant in the
   strong localization-bearing sense: the lobe-swap symmetry leaves its scalar
   fibre fixed.
3. Translate sigma-fixedness into B/C balance of the normalized centered
   boundary address.
4. Use the existing Lean reduction: B/C balance of every actual centered
   address is equivalent to `G8ActualXiBoundaryCharacterSigmaFixed`.
5. Combine actual sigma-fixedness with
   `G8BookIIIAcceptedTowerRealizationFromSigmaFixed` to obtain accepted
   centered-address coverage.
6. Forward through the existing zero-local-postulate final spine to Mathlib's
   `RiemannHypothesis` target.

## Core Remaining Theorem

The real theorem target is:

```text
For every OrthodoxXiZeroCarrier z,
orthodoxXiCarrierCenteredBoundaryPointAddress z
lands in the crossing-mediated / sigma-fixed scalar fibre.
```

Equivalently in the current Lean reduction:

```text
forall z,
  BCBalanced (orthodoxXiCarrierCenteredBoundaryPointAddress z).normalize.nf
```

That theorem must come from upstream chart geometry, not from the final RH
handoff.  The plausible proof sources are:

- centered `xi` functional symmetry plus the critical-axis fold;
- spectral reality forcing for the associated centered quadratic parameter;
- a tau boundary-transformer theorem saying the actual `xi` chart is
  sigma-equivariant and therefore factors through the unique crossing mediator.

## Euler Product / Primorial Interpretation

The Euler product intuition is relevant because the orthodox `zeta`/`xi`
readout is prime-generated, while tau reads prime generation through the
primorial CRT ladder.  In tau language, the issue is not whether a complex
analytic function becomes zero.  It is whether the global prime-generated
boundary readout balances the B and C channels.

The primorial ladder supplies the canonical tests.  A finite stage can expose
or approximate a polarity profile, but finite-stage balance is not enough to
settle the orthodox object.  The missing theorem is global: the actual
orthodox centered `xi` boundary readout must be shown to respect the
crossing-mediated B/C balance in the tau boundary algebra.

## Guardrail

Do not claim:

```text
finite primorial balance proves RH
```

or:

```text
two-channel / no-rogue factorization proves sigma-fixedness
```

The correct load-bearing statement is sharper:

```text
actual centered xi readout is crossing-mediated
```

Only after that statement is proved does the existing final spine turn the
localization result into the Mathlib `RiemannHypothesis` target.
