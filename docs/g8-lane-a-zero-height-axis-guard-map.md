# G8 Lane A Zero-Height Axis Guard Map

Private proof-engineering note.

## Closed in Lean

- The zero-height branch is now a real-axis `orthodoxXi` nonvanishing problem.
- Outside the open unit interval, nonvanishing is theorem-backed:
  - `x > 1` follows from Mathlib zeta nonvanishing on `Re(s) >= 1` and the completed-zeta product form of `orthodoxXi`.
  - `x < 0` reflects to `1 - x > 1` by `orthodoxXi_one_sub`.
  - `x = 0` and `x = 1` are direct normalization checks.
- Full real-axis nonvanishing implies `G8ActualXiZeroHeightAxisGuard`.
- A residual open-unit theorem plus the outside-zone theorem supplies the current height-split Lane-A inputs.

## Remaining Target

The only remaining zero-height payload is:

```lean
G8OrthodoxXiOpenUnitIntervalNonvanishing
```

Equivalently, the current zero-height guard is discharged once we prove that
`orthodoxXi (x : Complex)` does not vanish for real `0 < x < 1`.

## Guardrails

This reduction does not use `RiemannHypothesis`, accepted coverage, the final
live hinge, O3, full divisor transfer, or analytic-completion uniqueness.
The open-unit interval theorem remains a receiving-side real-axis theorem, not
a tau spectral-purity conclusion.
