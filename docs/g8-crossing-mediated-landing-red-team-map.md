# G8 Crossing-Mediated Landing Red-Team Map

Private bridge-engineering note for the final actual-`xi` landing hinge.

## Verdict

The current Lean spine has a clean conditional handoff:

```text
actual xi readout lands in the crossing/sigma-fixed fibre
  + sigma-fixed Book III accepted tower realization
  -> final live hinge
  -> conditional Mathlib RiemannHypothesis handoff
```

The first clause remains the hard theorem.  It must not be inferred from the
final handoff, accepted tower coverage, O3, full divisor transfer, or finite
primorial checks alone.

## Source Roles

- `prime-polarity` supplies the B/C channel split and the no-rogue
  two-channel vocabulary.  This is necessary but not sufficient for
  sigma-fixedness.
- `boundary-algebra` supplies the split idempotent boundary algebra, the sigma
  swap, and the scalar fixed fibre.  In normalized coordinates, scalar-fibre
  membership is B/C balance.
- `iota-tau` supplies the unique crossing mediator under explicit hypotheses:
  sigma-fixedness, non-polar two-lobe crossing, and omega/tail-stable
  mediator behavior.
- The actual `xi` theorem still has to prove that the centered orthodox readout
  lands in that crossing fibre.  The current binary centered-address model
  makes this RH-strength, so it stays proof-carrying.

## Lean Landing Surface

`G8ActualXiCrossingMediatedLandingEvidence z` records the source-paper route
pointwise and exposes only the localization-bearing conclusion:

```text
BCBalanced (orthodoxXiCarrierCenteredBoundaryPointAddress z).normalize.nf
```

From there, Lean forwards through the existing chain:

```text
G8ActualXiBoundaryReadoutCrossingMediated
  -> G8ActualXiBoundaryCharacterSigmaFixed
  -> G8FinalLiveHinge
```

The spectral-reality lane remains conditional but theorem-backed once its
fields are supplied:

```text
G8ActualXiSpectralRealityContext
  -> crossing-mediated all
  -> final live hinge with accepted realization
```

## Red-Team Boundaries

- No-rogue/two-channel evidence alone does not imply B/C balance.
- Axis-offset equality is not enough for accepted tower realization; exact
  `BoundaryNF` equality remains required.
- Off-critical carriers refute crossing-mediated landing through the existing
  binary address construction.
- Accepted tower realization from sigma-fixedness remains a second live input
  unless Book III tower addressability supplies it theorem-backed.
