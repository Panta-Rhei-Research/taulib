# G8 Crossing-Mediated Sigma-Fixed Source Audit

Private bridge-engineering note for the actual `xi` sigma-fixed hinge.

## Source Verdict

The current Lean spine has reduced the live hinge to:

```text
actual xi boundary readout is crossing-mediated
  -> centered address is B/C-balanced
  -> actual xi boundary character is sigma-fixed
```

The source papers support the algebraic route, but they do not by themselves
prove that every actual orthodox `xi` readout lands in the crossing-mediated
fibre.  That remains the RH-strength mathematical target.

## Paper Anchors

- `iota-tau`: the master constant is the scalar readout of the unique
  sigma-fixed, non-polar crossing-point germ.  The reusable pattern is
  crossing-mediator universality under sigma-equivariant boundary
  transformers, not a direct proof of actual `xi` sigma-fixedness.
- `boundary-algebra`: the split boundary algebra has two idempotent sectors
  swapped by sigma.  Sigma-fixed scalar-fibre membership is the algebraic
  form of B/C balance.
- `prime-polarity`: no-rogue two-channel factorization is necessary but not
  sufficient.  A two-channel character can still fail to be sigma-fixed unless
  its B and C coordinates agree.

## Lean Consequence

`G8ActualXiBoundaryReadoutCrossingMediated` is intentionally proof-carrying:
it records the exact B/C balance fact for the normalized centered boundary
address.  The new corridor may forward that evidence to
`G8ActualXiBoundaryCharacterSigmaFixed` and then to the existing final live
hinge, but it must not construct the evidence from accepted coverage, tau
purity, O3, full divisor transfer, or the final RH handoff.

## Red-Team Boundary

Do not claim that the actual `xi` landing theorem is discharged here.  The next
mathematical target is to prove that the actual centered `xi` boundary readout
is crossing-mediated from chart symmetry, spectral reality, or a sharper
boundary-transformer theorem.
