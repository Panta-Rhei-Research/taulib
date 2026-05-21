# G8 Lane A L3b-E Exact Alignment Map

This is a private red-team map for
`TauLib.BookIII.Bridge.G8ActualXiStandardEigenvalueExactAlignment`.

## What Closed

The new Lean layer makes L3b-E a first-class proof surface:

```text
selected standard mode
  + exact canonical-value equality at that mode
  -> standard eigenvalue membership
  -> pointwise imaginary-part zero
  -> nonzero-height spectral-parameter reality
```

The theorem-backed adapters show that this L3b-E surface is equivalent to the
previous standard-eigenvalue membership target, and that it forwards through
the existing Lane-A nonzero-height corridor.

## What Did Not Close

No current TauLib theorem constructs the exact selected-mode equality:

```text
g8ActualXiIotaTauCanonicalScaledOperatorSpectralValue z
  = lemniscate_eigenvalue (selectedMode z)
```

Finite self-adjoint, K5, spectral-resolution, and finite correspondence checks
remain diagnostic evidence only. They do not select a global standard mode and
do not prove exact equality.

## Red-Team Guardrail

L3b-E is stronger than bare self-adjoint reality. It forces the canonical
scaled value to be the complex readout of a selected natural-square standard
eigenvalue:

```text
g8ActualXiIotaTauCanonicalScaledOperatorSpectralValue z
  = (selectedMode z * selectedMode z : Nat)
```

The weaker abstract self-adjoint route can still be the better Lane-A route:
it only needs canonical membership in an operator-native self-adjoint spectral
predicate, not discreteness in the standard `n^2` readout. The exact-alignment
module therefore records both directions cleanly:

- if L3b-E is supplied, Lane A receives the needed real-valuedness;
- if only abstract self-adjoint membership is supplied, exact standard-mode
  alignment remains a separate theorem and must not be inferred silently.

## Next Mathematical Target

Either:

1. prove a non-circular Book III standard-mode theorem that really gives the
   selected `lemniscate_eigenvalue` equality for every actual nonzero-height
   carrier; or
2. continue the weaker abstract self-adjoint membership route and avoid the
   discrete standard-mode claim unless the operator model justifies it.

Both routes must avoid RH-facing downstream modules, O3, determinant transfer,
completion uniqueness, full divisor transfer, and finite-check-only arguments.
