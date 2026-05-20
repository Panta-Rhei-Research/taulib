# G8 Actual Sigma-Fixed Last-Hinge Audit

Private bridge audit for the final live hinge:

```text
G8ActualXiBoundaryCharacterSigmaFixed
  + G8BookIIIAcceptedTowerRealizationFromSigmaFixed
  -> G8BookIIIPointwiseAcceptedCenteredAddressCoverage
  -> RiemannHypothesis
```

## Current Lean Verdict

`G8ActualXiBoundaryCharacterSigmaFixed` is the last live theorem target.  It is
not plumbing.  In the current centered-address model it is equivalent to saying
that every actual canonical `xi` boundary address normalizes to the B/C balance
hyperplane.

Current theorem-backed facts:

- pointwise sigma-fixedness is equivalent to B/C balance of the normalized
  centered boundary address;
- carrier off-criticality is equivalent to off-axis readability of the centered
  shadow;
- off-axis actual centered addresses normalize to B/C imbalance;
- therefore actual sigma-fixedness refutes every carrier-level off-critical
  witness.

This makes the hinge RH-strength.  It must not be proved from accepted coverage,
tau purity, the final live hinge, Mathlib `RiemannHypothesis`, full divisor
transfer, O3, or legacy ambient bridge axioms.

## First-Edition Part III Archaeology

Source path:

```text
First-edition Book III, Part III source folder.
```

This material is quarantined archaeology from a pre-final kernel.  It is useful
for proof patterns, not as final-kernel source truth.

Reusable patterns:

- Chapter 35 constructs the lemniscate as a wedge of two branch circles and
  records the branch-swap involution.
- Chapter 35 identifies the critical line as the fixed locus of the model
  coordinate involution `s -> 1 - s`.
- Chapter 37 isolates the central quadratic parameter
  `s(1-s)-1/4 = -(s-1/2)^2`.
- Chapter 38 proves the conditional forcing pattern: if a zero yields a real
  spectral parameter and the height is nonzero, then the real coordinate is
  `1/2`.
- Chapter 36 supplies the intended operator-theoretic reason for real spectral
  parameters: self-adjointness of the lemniscate operator.

Unsafe or obsolete as final claims:

- first-edition phrasing that the RH proof is complete;
- finite cutoff or certified finite windows as full classical zero coverage;
- treating functional equation symmetry alone as proving individual zeros lie
  on the fixed locus;
- treating the old determinant/spectral correspondence as an unconditional
  theorem in the final kernel.

## Implementation Consequence

The active O3-free route should keep actual sigma-fixedness as the final live
target.  A separate conditional spectral-reality lane may be useful, but it must
make the determinant/spectral input explicit:

```text
real central quadratic parameter
  + nonzero height
  -> real coordinate = 1/2
  -> centered address is B/C balanced
  -> actual sigma-fixed
```

The live mathematical work is to prove one of those explicit upstream premises
without importing the downstream RH conclusion.
