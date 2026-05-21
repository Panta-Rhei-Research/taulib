# G8 Fine RH Spine Axiom Ledger Map

This is a private audit map for
`TauLib.BookIII.Bridge.G8FineRHSpineAxiomLedger`.

The coarse full-spine ledger counts four temporary gates. This fine ledger
keeps the same final target but splits the two load-bearing gates into smaller
proof obligations so the last-mile work is harder to hide inside broad names.

## Fine Gate Count

The fine ledger now has three temporary axioms. Six formerly temporary gates
are theorem-backed, with L3 split into a closed standard-spectrum reality side
and an actual canonical-membership side, and with T3/T5 fused into one sharper
aligned-certificate selection target:

- L2 is discharged by the canonical `ιτ²` scaled-image construction.
- L3a is discharged by the theorem-backed standard lemniscate eigenvalue
  spectrum: standard eigenvalue members are real-valued.
- T1 is discharged by the certificate-carrier accepted tower model:
  accepted witnesses are already-formed Book III tower balance certificates.
- T2 is discharged by pointwise sigma-fixed centered-address NF
  addressability.
- T4 is discharged for the certificate-carrier model because acceptedness is
  built into the witness carrier.
- T5 is discharged as a projection from the aligned certificate selected by
  the remaining T3* target.

### Lane A

1. `g8FineLaneA_operatorReadyGate_axiom`
   Book III lemniscate operator readiness.

2. `g8FineLaneA_scaledImageLawGate`
   The selected Book III operator spectral value is exactly the certified
   `ιτ²`-scaled centered quadratic of the actual nonzero-height `xi` carrier.
   This gate is closed by `g8ActualXiIotaTauCanonicalScaledImageLawSource`.

3a. `g8FineLaneA_standardSpectrumRealityGate`
   The standard Book III lemniscate eigenvalue spectrum is real-valued. This is
   theorem-backed by `g8StandardLemniscateSelfAdjointSpectrumRealitySource`.

3b. `g8FineLaneA_canonicalStandardEigenvalueMembershipGate_axiom`
   Every actual nonzero-height canonical scaled `xi` value is exactly a
   standard lemniscate eigenvalue. This is now the remaining Lane-A L3 payload.

   The L3b payload has a theorem-backed reduction layer in
   `G8ActualXiStandardEigenvalueMembershipReduction` and a first-class
   L3b-E surface in `G8ActualXiStandardEigenvalueExactAlignment`:

   - `g8FineLaneA_canonicalStandardModeSelection` selects the candidate
     standard mode for each actual nonzero-height canonical value.
   - `g8FineLaneA_canonicalStandardModeSelectionTarget` records that this
     selected-mode handle exists.  As a standalone L3b-M target this is
     non-load-bearing: a mode handle is not spectral membership.
   - `g8FineLaneA_canonicalSelectedModeExactAlignment` is the load-bearing
     equality with `lemniscate_eigenvalue` at that selected mode.

   Mode selection without exact alignment is intentionally non-load-bearing;
   the reduction proves that the split package is equivalent to the existence
   of a selected mode together with exact selected-mode alignment, and this is
   equivalent to the old standard-eigenvalue membership target. The exact
   alignment module records the downstream payoff directly: L3b-E gives
   standard-spectrum membership, pointwise imaginary-part zero, and the
   nonzero-height spectral-parameter reality route.

   The next Lane-A proof target is therefore the L3b-E equality for the
   selected Book III standard mode:

   ```text
   g8ActualXiIotaTauCanonicalScaledOperatorSpectralValue z
     = lemniscate_eigenvalue (selectedMode z)
   ```

   A future proof may replace the current L3b axiom by a non-circular Book III
   selector plus this exact equality. It may not weaken equality to finite
   diagnostics, approximation, boundedness, or coordinate existence alone. The
   exact-alignment surface also makes the red-team warning explicit: the
   weaker abstract self-adjoint route is enough for real-valuedness once
   supplied, but it does not manufacture membership in the discrete standard
   eigenvalue readout.

Together these replace the coarse Lane-A abstract membership payload with the
more concrete operator-image route:

```text
operator readiness
  + exact scaled image law
  + standard eigenvalue spectral reality
  + actual canonical standard-eigenvalue membership
  -> nonzero-height spectral-parameter reality
  -> actual sigma-fixedness
```

The zero-height branch remains theorem-backed by the paired-eta/open-unit lane.

### Accepted Tower

4. `g8FineAcceptedTower_modelGate`
   The accepted Book III tower witness model. This gate is closed by
   `g8BookIIITowerCertificateAcceptedSpectralWitnessModel`; it supplies the
   carrier/model layer only, not pointwise witness realization for actual
   `xi` addresses.

5. `g8FineAcceptedTower_nfAddressabilityGate`
   Sigma-fixed canonical characters are NF-addressable. This gate is closed by
   `G8XiBoundaryCharacterSigmaFixed.toNFAddressability`.

6. `g8FineAcceptedTower_alignedCertificateSelectionGate_axiom`
   Sigma-fixed canonical characters select tower balance certificates whose
   stage normal form is exactly the normalized centered boundary address. This
   is the remaining fused T3/T5 accepted-tower payload.

7. `g8FineAcceptedTower_witnessAcceptedGate`
   The selected tower witnesses are accepted. This gate is closed by the
   certificate-carrier model: any selected witness is already an accepted
   tower balance certificate.

8. `g8FineAcceptedTower_normalFormGate`
   The selected accepted witnesses have exactly the normalized centered
   boundary normal form. This gate is closed by projecting the normal-form
   field of `g8FineAcceptedTower_alignedCertificateSelectionGate_axiom`.

Together these replace the coarse accepted-realization payload:

```text
sigma-fixed canonical character
  -> NF-addressability
  -> selected tower witness
  -> acceptedness
  -> exact normal-form alignment
  -> accepted centered-address coverage
```

## Audit Targets

```bash
make lane-a-axiom-ledger
make full-rh-axiom-ledger
make fine-rh-axiom-ledger
make rh-mathlib-discharge-axiomfree
```

Expected local axiom counts:

```text
Lane A coarse ledger: 3
Full RH coarse ledger: 4
Fine RH ledger: 3
Official RH discharge: 0
```

## Guardrails

The fine ledger is quarantine-only. It must not be imported by `TauLib.BookIII`,
the axiom-free final-spine target, or the axiom-free Mathlib discharge target.

The fine ledger does not say the remaining three axioms are minor. Gate 3b is
mathematically load-bearing: it is the exact actual-`xi` membership theorem for
the standard lemniscate eigenvalue spectrum. Gate 1 remains serious operator
infrastructure, and gate 6 remains the fused accepted-tower construction plus
exact normal-form alignment obligation.
The point is to name them precisely enough that each can be discharged, audited,
or rejected independently.
