# G8 Full RH Spine Axiom Ledger Map

This is a private audit map for the quarantined module
`TauLib.BookIII.Bridge.G8FullRHSpineAxiomLedger`.

The purpose is narrow: count the exact temporary proof gates which, if supplied
as axioms, close the current formal chain all the way to Mathlib's
`RiemannHypothesis` statement.

## Current Count

The full-spine ledger imports the Lane A ledger and adds one final accepted
tower realization gate.

Retired theorem-backed Lane A constructors:

- `g8LaneA_operatorReadyGate_axiom`
  Despite the historical name, this is now a `def`, not an axiom.  It is backed
  by the selected Ch.23 A1.1-A1.6 operator-readiness route.
- `g8LaneA_operatorNativeSelfAdjointGate_axiom`
  Despite the historical name, this is now a `def`, not an axiom.  It is backed
  by the selected certified eigenpair point-spectrum carrier and its
  self-adjoint scalar-pairing reality proof.

Remaining full-spine temporary axioms:

1. `g8LaneA_canonicalActualXiMembershipGate_axiom`
   Canonical actual-`xi` membership in that legitimate spectral source.

2. `g8FullRHSpine_acceptedTowerRealizationGate_axiom`
   Accepted Book III tower realization from sigma-fixed canonical characters,
   with exact centered-address normal form.

Together these produce:

```text
Lane A actual sigma-fixedness
  + accepted tower realization from sigma-fixedness
  -> final live hinge
  -> pointwise accepted centered-address coverage
  -> accepted-realization proof package
  -> Mathlib RiemannHypothesis
```

The non-quarantine bridge
`TauLib.BookIII.Bridge.G8ActualXiMinimalSelfAdjointMembershipRoute` now records
the weak Lane A target directly. It proves that the minimal abstract
self-adjoint route is sufficient for actual sigma-fixedness and for the final
live hinge once the accepted tower realization gate is supplied.

## Audit Targets

```bash
make lane-a-axiom-ledger
make full-rh-axiom-ledger
make rh-mathlib-discharge-axiomfree
```

The first target should report exactly one temporary Lane A axiom.
The second target should report exactly two temporary full-spine axioms.
The third target must remain axiom-free; it checks that the official RH handoff
still requires explicit proof inputs and is not contaminated by this ledger.

## Retirement Order

The remaining preferred retirement order is:

1. Replace canonical actual-`xi` membership with the actual spectral-membership
   theorem.
2. Replace accepted tower realization from sigma-fixedness with the Book III
   NF-addressable accepted tower witness theorem.

Each retirement should lower the expected axiom count in the ledger target.

The strong standard eigenvalue route remains an optional refinement. The full
ledger uses only the weaker operator-native self-adjoint membership route, so it
does not require exact discrete `n^2` mode membership unless that stronger
theorem is chosen as the proof source for one of the Lane A gates.

## Guardrails

This ledger is quarantine-only. It is not imported by `TauLib.BookIII`, the
axiom-free final-spine target, or the axiom-free Mathlib discharge target.

The ledger does not assert an unconditional published result. It records the
remaining formal obligations and proves that those obligations are exactly
sufficient for the present Lean spine.
