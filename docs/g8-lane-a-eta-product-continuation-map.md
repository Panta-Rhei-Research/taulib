# G8 Lane A Eta Product And Continuation Map

Private proof-engineering note for the Lane-A zero-height branch.

## Theorem-Backed In This Wave

- The mod-two eta coefficient splits as `1 - 2 * evenIndicator` on positive
  indices: odd terms contribute `+1`, even terms contribute `-1`.
- The even-indicator ordinary `LSeries` is theorem-backed on `1 < Re(s)` by
  Mathlib's `ZMod.LFunction_eq_LSeries` and the finite residue-class
  computation of `ZMod.LFunction`.
- The safe-half-plane ordinary product identity now holds:
  `LSeries g8EtaModTwoNatCoeff s =
  (1 - 2^(1-s)) * riemannZeta s` for `1 < s.re`.
- The corresponding mod-two `LFunction` product identity follows on the same
  half-plane by the existing `ZMod.LFunction = LSeries` bridge.

## Still Analytic

- Continue the product identity from the right half-plane to real
  `0 < x < 1`.
- Identify Mathlib's mod-two `LFunction` with the concrete conditional eta
  value on the real open unit interval.

These two fields are now packaged as `G8EtaModTwoOpenUnitContinuationData`.
Supplying them gives the eta-zeta identity on `0 < x < 1`, zeta
nonvanishing on that interval, the zero-height axis guard, and then the
height-split Lane-A inputs.

## Guardrails

- No RH handoff, accepted coverage, final live hinge, O3, full divisor
  transfer, or analytic-completion uniqueness is used to prove the product
  theorem.
- The continuation and concrete-series identification are proof-carrying
  targets, not axioms and not hidden assumptions.
- The exact denominator convention remains `1 - 2^(1-x)`.
