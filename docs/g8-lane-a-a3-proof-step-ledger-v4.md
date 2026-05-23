# G8 Lane A A3 Proof-Step Ledger V4

Private working ledger for the remaining Lane A gate:

```text
A3 canonical actual-xi membership in the selected operator-native
self-adjoint spectral predicate
```

This V4 ledger supersedes the active-planning role of
`docs/g8-lane-a-a2-proof-step-ledger-v3.md`.  V3 records the A2 retirement.
V4 starts from the new official state:

```text
A1 operator readiness                         closed / theorem-backed
A2 operator-native self-adjoint provenance    closed / theorem-backed
A3 canonical actual-xi membership             open / official axiom
```

The official weak Lane A ledger now has expected temporary axioms `1`.
This file is not a formal axiom file.  It is a proof-step ledger for retiring
that last Lane A axiom without using final/RH-facing machinery.

## Exact A3 Target

The official remaining gate is:

```lean
g8LaneA_canonicalActualXiMembershipGate_axiom :
  G8LaneACanonicalActualXiMembershipGate
    g8LaneA_operatorReadyGate_axiom
    g8LaneA_operatorNativeSelfAdjointGate_axiom
```

Its load-bearing field is:

```lean
membershipSource :
  G8ActualXiCanonicalAbstractSpectralMembershipSource
    g8LaneA_operatorNativeSelfAdjointGate_axiom.legitimacy
```

After A2, the selected legitimacy is backed by:

```lean
g8BookIIICh23FloorNormalizedA2LaneAOperatorNativeSelfAdjointSource_closed
```

and its spectral predicate is the selected native eigenpair predicate:

```lean
G8BookIIICh23FloorNormalizedA2NativePointSpectrum
```

So the smallest concrete A3 target is:

```lean
forall z : G8ActualXiNonzeroHeightCarrier,
  G8BookIIICh23FloorNormalizedA2NativePointSpectrum
    (g8ActualXiIotaTauCanonicalScaledOperatorSpectralValue z)
```

Unfolding A2.3, this is equivalently:

```lean
forall z : G8ActualXiNonzeroHeightCarrier,
  Nonempty
    (G8BookIIICh23FloorNormalizedA2SelectedEigenpairData
      (g8ActualXiIotaTauCanonicalScaledOperatorSpectralValue z))
```

That is the bare-metal A3 theorem: every actual nonzero-height canonical
scaled `xi` value must produce selected certified eigenpair data for the
Ch.23 floor-normalized lemniscate operator.

## Red-Team Verdict

The scouting pass agreed on the target split:

- The smallest load-bearing A3 theorem is selected native point-spectrum
  membership of the canonical scaled value.
- Since A2 fixed the selected predicate as certified eigenpair membership,
  A3 must construct actual selected eigenpair data.
- Standard-mode equality is sufficient but stronger than necessary.
- Finite diagnostics, approximate matching, or a predicate chosen only to
  contain the canonical values cannot discharge A3.
- A3 source modules should stay upstream of final/RH handoffs, accepted tower
  coverage, O3, determinant transfer, divisor transfer, completion uniqueness,
  and the quarantined ledger itself.

## Already Closed Downstream

Once A3 supplies the membership source, the existing code already carries:

```text
A1/A2 source + A3 membership
  -> G8ActualXiMinimalSelfAdjointMembershipTarget
  -> G8ActualXiNonzeroHeightSpectralParameterReal
  -> height-split Lane A inputs, using the closed zero-height eta route
  -> G8ActualXiBoundaryCharacterSigmaFixed
  -> crossing-mediated evidence
```

The key adapters are:

- `G8LaneAOperatorNativeSelfAdjointSource.toMinimalTarget`
- `G8ActualXiMinimalSelfAdjointMembershipTarget.toSpectralParameterReal`
- `G8ActualXiMinimalSelfAdjointMembershipTarget.actualSigmaFixed`
- `G8ActualXiMinimalSelfAdjointMembershipTarget.toCrossingMediatedAll`

The accepted Book III tower realization remains a separate full-spine gate.
A3 closes Lane A; it does not by itself close the accepted-tower side.

## Current Lean Anchors

- A1/A2 official source:
  `TauLib.BookIII.Bridge.G8BookIIICh23FloorNormalizedA2EigenpairPointSpectrumSource`
- strict A1/A2 provenance:
  `TauLib.BookIII.Bridge.G8LaneAOperatorNativeSelfAdjointSource`
- abstract A3 membership source:
  `TauLib.BookIII.Bridge.G8ActualXiCanonicalAbstractSpectralMembershipSource`
- minimal Lane A route:
  `TauLib.BookIII.Bridge.G8ActualXiMinimalSelfAdjointMembershipRoute`
- canonical scaled value:
  `TauLib.BookIII.Bridge.G8ActualXiIotaTauScaledImageLawConstruction`
- stronger optional standard-mode route:
  `TauLib.BookIII.Bridge.G8ActualXiStandardEigenvalueExactAlignment`

## A3 Proof-Step Ledger

| Step | Obligation | Lean surface to add/use | Status | What remains |
| --- | --- | --- | --- | --- |
| A3.0 | Freeze the selected A1/A2 source for A3. | Use `g8BookIIICh23FloorNormalizedA2LaneAOperatorNativeSelfAdjointSource_closed` and its `.legitimacy`. | Closed source available. | Add an A3 module that imports the selected A2 source, not the quarantined ledger. |
| A3.1 | Define the selected A3 membership target. | Add `G8BookIIICh23FloorNormalizedA3SelectedCanonicalMembershipTarget`. | Next small adapter. | Prove it is equivalent to the `G8LaneACanonicalActualXiMembershipGate` field for the selected source. |
| A3.2 | Re-express A3 as selected certified eigenpair data. | Use `G8BookIIICh23FloorNormalizedA2SelectedEigenpairDataTarget_closed`. | Adapter should be theorem-backed. | Show the target is exactly pointwise nonempty selected eigenpair data at `g8ActualXiIotaTauCanonicalScaledOperatorSpectralValue z`. |
| A3.3 | Construct the actual spectral/eigenfunction carrier for each nonzero-height actual `xi` carrier. | New source target, e.g. `G8ActualXiCanonicalEigenfunctionCandidateSource`. | Open mathematical payload. | Supply the Book III operator-native eigenfunction/readout attached to each actual carrier. |
| A3.4 | Prove selected domain membership and nonzero eigenfunction evidence. | New target, e.g. `G8ActualXiCanonicalEigenfunctionDomainNonzeroSource`. | Open mathematical payload. | Show the candidate lies in the selected Kirchhoff domain and is not the zero vector. |
| A3.5 | Prove the exact selected eigen-equation. | New target, e.g. `G8ActualXiCanonicalSelectedEigenEquationSource`. | Core open payload. | Prove `H_L psi_z = V(z) psi_z`, where `V(z)` is the canonical `iota_tau^2` scaled centered quadratic. |
| A3.6 | Produce certified eigenpair scalar-pairing data. | New constructor from A3.3-A3.5 plus selected A2 self-adjoint calculus. | Open, but should be local once A3.3-A3.5 are in place. | Provide `pairingNormSq`, `pairingNormSq_ne_zero`, and `selfAdjointScalarPairingIdentity` required by `G8BookIIILemniscateEigenpairData`. |
| A3.7 | Package pointwise selected eigenpair data into the abstract membership source. | New theorem, e.g. `g8BookIIICh23FloorNormalizedA3CanonicalMembershipSource_closed`. | Adapter. | Build `G8ActualXiCanonicalAbstractSpectralMembershipSource selectedLegitimacy`. |
| A3.8 | Retire the official A3 ledger axiom. | Replace `g8LaneA_canonicalActualXiMembershipGate_axiom` with a `def`. | Final A3 bookkeeping. | Lower `make lane-a-axiom-ledger` to `0`, full RH ledger to `1`, and global no-sorry expected axioms by one. |

## Recommended First Lean Wave

Add:

```lean
TauLib.BookIII.Bridge.G8BookIIICh23FloorNormalizedA3SelectedCanonicalMembership
```

The first wave should be adapter-only and no-sorry:

1. import `G8BookIIICh23FloorNormalizedA2EigenpairPointSpectrumSource`;
2. define the selected A3 target:

```lean
def G8BookIIICh23FloorNormalizedA3SelectedCanonicalMembershipTarget : Prop :=
  forall z : G8ActualXiNonzeroHeightCarrier,
    G8BookIIICh23FloorNormalizedA2NativePointSpectrum
      (g8ActualXiIotaTauCanonicalScaledOperatorSpectralValue z)
```

3. prove equivalence to pointwise selected eigenpair-data nonemptiness;
4. prove selected A3 target -> `G8ActualXiCanonicalAbstractSpectralMembershipSource`;
5. prove selected A3 target -> `G8LaneACanonicalActualXiMembershipGate`
   over the theorem-backed A1/A2 selected gates;
6. do not replace the official ledger axiom until a theorem-backed constructor
   for the selected A3 target exists.

This keeps the first A3 step small and gives the next mathematical payload a
precise Lean landing pad.

The preferred target theorem for later ledger retirement is:

```lean
theorem g8BookIIICh23FloorNormalizedA3SelectedCanonicalMembership_closed :
  G8BookIIICh23FloorNormalizedA3SelectedCanonicalMembershipTarget
```

and the preferred official adapter is:

```lean
def g8LaneA_canonicalActualXiMembershipGate_ofSelectedNativeMembership :
  G8LaneACanonicalActualXiMembershipGate
    g8LaneA_operatorReadyGate_axiom
    g8LaneA_operatorNativeSelfAdjointGate_axiom
```

The adapter may live near the ledger only after the source theorem is closed;
the source theorem itself should not import the ledger.

## Mathematical Core

The core theorem is not merely that the canonical value is real.  It is the
operator-native membership theorem:

```text
for every actual nonzero-height xi carrier z,
the selected Ch.23 lemniscate operator has a genuine eigenpair with
eigenvalue V(z) = g8ActualXiIotaTauCanonicalScaledOperatorSpectralValue z.
```

The selected A2 predicate is a point-spectrum/eigenpair predicate.  Therefore
A3 must supply actual eigenpair data, not only a real-valued scalar, finite
diagnostics, approximate matching, or standard-mode numerology.

## Optional Stronger Route

The strong standard-mode path remains available:

```text
for every z, exists n,
  V(z) = lemniscate_eigenvalue n
```

The relevant surfaces are:

- `G8ActualXiCanonicalStandardEigenvalueMembershipSource`
- `G8ActualXiCanonicalStandardModeSelectionSource`
- `G8ActualXiCanonicalSelectedModeExactAlignmentSource`

This path implies the weak route, but it is stronger than needed.  The V4
preferred path is the minimal selected-eigenpair membership route, because A1
and A2 have already made the native point-spectrum predicate theorem-backed.

## Guardrails

- Do not import or use `G8LaneAAxiomLedger` to prove A3.
- Do not use `RiemannHypothesis`, `RHMathlibDischarge`, `G8FinalLiveHinge`,
  accepted coverage, O3, determinant transfer, divisor transfer, completion
  uniqueness, or legacy universal spectral correspondence modules.
- Do not define the spectral predicate to contain the canonical values.  A2
  has already fixed the selected operator-native predicate.
- Do not treat finite diagnostics, approximate agreement, or bounded checks as
  selected eigenpair data.
- Do not prove only real-valuedness.  A3 must prove membership; A2 then
  supplies real-valuedness.
- Do not require standard `n^2` mode equality unless we explicitly choose the
  stronger optional route.

## Success Criteria

The A3 discharge is complete only when:

```text
make lane-a-axiom-ledger        axioms=0, sorry=0
make full-rh-axiom-ledger       axioms=1, sorry=0
python3 scripts/check_no_sorry.py --root TauLib --expected-axioms 7 --expected-sorry 0
make rh-mathlib-discharge-axiomfree
lake build
git diff --check
```

At that point Lane A is fully theorem-backed.  The full RH spine will still
have the accepted-tower realization gate unless that has also been retired.
