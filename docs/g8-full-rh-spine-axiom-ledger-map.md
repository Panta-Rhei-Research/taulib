# G8 Full RH Spine Axiom Ledger Map

This is a private audit map for the quarantined module
`TauLib.BookIII.Bridge.G8FullRHSpineAxiomLedger`.

The purpose is narrow: count the exact temporary proof gates which, if supplied
as axioms, close the current formal chain all the way to Mathlib's
`RiemannHypothesis` statement.

## Current Count

The full-spine ledger imports the Lane A ledger and adds one final accepted
tower realization gate.

1. `g8LaneA_operatorReadyGate_axiom`
   Book III lemniscate operator readiness.

2. `g8LaneA_operatorNativeSelfAdjointGate_axiom`
   Operator-native self-adjoint spectral-membership legitimacy.

3. `g8LaneA_canonicalActualXiMembershipGate_axiom`
   Canonical actual-`xi` membership in that legitimate spectral source.

4. `g8FullRHSpine_acceptedTowerRealizationGate_axiom`
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

The first target should report exactly three temporary Lane A axioms.
The second target should report exactly four temporary full-spine axioms.
The third target must remain axiom-free; it checks that the official RH handoff
still requires explicit proof inputs and is not contaminated by this ledger.

## Retirement Order

The preferred retirement order is:

1. Replace the operator readiness axiom with the Book III readiness theorem.
2. Replace the self-adjoint spectral legitimacy axiom with the operator-native
   spectral reality theorem.
3. Replace canonical actual-`xi` membership with the actual spectral-membership
   theorem.
4. Replace accepted tower realization from sigma-fixedness with the Book III
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
