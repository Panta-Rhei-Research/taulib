import TauLib.BookIII.Bridge.G8BookIIITowerSpectralBalance

/-!
# TauLib.BookIII.Bridge.G8BookIIITowerAdmissionConflict

D4 accepted tower admission conflict discharge.

The D3 layer made accepted Book III tower witnesses B/C-balanced by their
tower spectral-balance certificate.  The actual centered `xi` address layer
shows that an off-axis receiving shadow normalizes to a tau
critical-imbalance normal form.  This module isolates the resulting local
contradiction:

```text
actual off-axis xi shadow
  + accepted tower admission aligned to its normalized address
  -> False
```

This is a contradiction surface, not a total admission constructor.  It does
not prove O3, full zero-divisor transfer, analytic-completion uniqueness, or
any new receiving-side theorem.
-/

set_option autoImplicit false

noncomputable section

namespace Tau.BookIII.Bridge

open Tau.BookIII.Spectral

-- ============================================================
-- DIRECT ACCEPTED-TOWER / OFF-AXIS CONFLICT
-- ============================================================

/-- Accepted tower witnesses exclude tau critical imbalance by their tower
    balance certificate. -/
theorem g8BookIIITowerAcceptedWitness_noCriticalImbalance
    (model : G8BookIIITowerAcceptedSpectralWitnessModel)
    (w : model.spectralWitness)
    (hAccepted : model.IsAccepted w) :
    ¬ TauCriticalImbalance (model.normalForm w) :=
  model.acceptedPurity w hAccepted

/-- Actual thin off-axis chart shadows normalize to tau critical imbalance at
    the explicit centered boundary address. -/
theorem g8ActualXiZetaThinOffAxis_centeredAddress_criticalImbalance
    (source : G8ActualXiZetaThinSourceContext)
    (z : OrthodoxXiZeroCarrier)
    (hOffAxis : G8ActualXiZetaThinChartOffAxis source z) :
    TauCriticalImbalance
      (orthodoxXiCarrierCenteredBoundaryPointAddress z).normalize.nf :=
  orthodoxXiCarrierCenteredBoundaryPointAddress_criticalImbalance z
    (by
      simpa [
        G8ActualXiZetaThinChartOffAxis,
        g8ActualXiZetaThinCenteredShadow
      ] using hOffAxis)

/-- A pointwise accepted tower admission aligned to the actual centered
    boundary address contradicts off-axis critical imbalance. -/
theorem g8BookIIITowerAcceptedWitness_refutesAlignedOffAxis
    (model : G8BookIIITowerAcceptedSpectralWitnessModel)
    {transfer : G8dZeroDivisorTransferContext}
    {readout : G8FinalRHTransferChartReadout transfer}
    (z : OrthodoxXiZeroCarrier)
    (hOffAxis :
      G8ActualXiZetaThinChartOffAxis
        (model.toAcceptedDomain.thinSource readout) z)
    (w : model.spectralWitness)
    (hAccepted : model.IsAccepted w)
    (hAligned :
      model.normalForm w =
        (orthodoxXiCarrierCenteredBoundaryPointAddress z).normalize.nf) :
    False := by
  have hNo :
      ¬ TauCriticalImbalance (model.normalForm w) :=
    g8BookIIITowerAcceptedWitness_noCriticalImbalance
      model w hAccepted
  have hImbalance :
      TauCriticalImbalance
        (orthodoxXiCarrierCenteredBoundaryPointAddress z).normalize.nf :=
    g8ActualXiZetaThinOffAxis_centeredAddress_criticalImbalance
      (model.toAcceptedDomain.thinSource readout) z hOffAxis
  exact hNo (by simpa [hAligned] using hImbalance)

/-- A tower admission map refutes every thin off-axis actual `xi` chart
    shadow, because its admitted witness would be both accepted-balanced and
    aligned with an off-axis imbalanced address. -/
theorem G8BoundaryToBookIIITowerSpectralAdmission.refutesThinOffAxis
    {model : G8BookIIITowerAcceptedSpectralWitnessModel}
    {transfer : G8dZeroDivisorTransferContext}
    {readout : G8FinalRHTransferChartReadout transfer}
    (admission :
      G8BoundaryToBookIIITowerSpectralAdmission model readout)
    (z : OrthodoxXiZeroCarrier)
    (hOffAxis :
      G8ActualXiZetaThinChartOffAxis
        (model.toAcceptedDomain.thinSource readout) z) :
    False :=
  g8BookIIITowerAcceptedWitness_refutesAlignedOffAxis
    model z hOffAxis
    (admission.admitRaw z hOffAxis)
    (admission.admitAccepted z hOffAxis)
    (admission.admitNormalForm z hOffAxis)

/-- Tower admission excludes thin off-axis chart shadows by the direct D4
    accepted-admission conflict. -/
theorem G8BoundaryToBookIIITowerSpectralAdmission.noThinChartOffAxis_direct
    {model : G8BookIIITowerAcceptedSpectralWitnessModel}
    {transfer : G8dZeroDivisorTransferContext}
    {readout : G8FinalRHTransferChartReadout transfer}
    (admission :
      G8BoundaryToBookIIITowerSpectralAdmission model readout) :
    ∀ z : OrthodoxXiZeroCarrier,
      ¬ G8ActualXiZetaThinChartOffAxis
          (model.toAcceptedDomain.thinSource readout) z := by
  intro z hOffAxis
  exact admission.refutesThinOffAxis z hOffAxis

-- ============================================================
-- POINTWISE CONFLICT WITNESS
-- ============================================================

/-- Pointwise witness of the fatal D4 configuration.

It packages an actual off-axis `xi` shadow together with an accepted tower
witness whose normal form is aligned to the normalized centered boundary
address.  Such a package is impossible. -/
structure G8BookIIITowerAdmittedOffAxisWitness
    (model : G8BookIIITowerAcceptedSpectralWitnessModel)
    {transfer : G8dZeroDivisorTransferContext}
    (readout : G8FinalRHTransferChartReadout transfer) where
  z : OrthodoxXiZeroCarrier
  hOffAxis :
    G8ActualXiZetaThinChartOffAxis
      (model.toAcceptedDomain.thinSource readout) z
  admitted : model.spectralWitness
  admittedAccepted : model.IsAccepted admitted
  normalForm_aligned :
    model.normalForm admitted =
      (orthodoxXiCarrierCenteredBoundaryPointAddress z).normalize.nf

/-- A pointwise admitted off-axis tower witness refutes itself. -/
theorem G8BookIIITowerAdmittedOffAxisWitness.refutes
    {model : G8BookIIITowerAcceptedSpectralWitnessModel}
    {transfer : G8dZeroDivisorTransferContext}
    {readout : G8FinalRHTransferChartReadout transfer}
    (witness :
      G8BookIIITowerAdmittedOffAxisWitness model readout) :
    False :=
  g8BookIIITowerAcceptedWitness_refutesAlignedOffAxis
    model witness.z witness.hOffAxis witness.admitted
    witness.admittedAccepted witness.normalForm_aligned

/-- Every tower admission would produce the impossible pointwise conflict
    witness at any off-axis point. -/
def G8BoundaryToBookIIITowerSpectralAdmission.toAdmittedOffAxisWitness
    {model : G8BookIIITowerAcceptedSpectralWitnessModel}
    {transfer : G8dZeroDivisorTransferContext}
    {readout : G8FinalRHTransferChartReadout transfer}
    (admission :
      G8BoundaryToBookIIITowerSpectralAdmission model readout)
    (z : OrthodoxXiZeroCarrier)
    (hOffAxis :
      G8ActualXiZetaThinChartOffAxis
        (model.toAcceptedDomain.thinSource readout) z) :
    G8BookIIITowerAdmittedOffAxisWitness model readout where
  z := z
  hOffAxis := hOffAxis
  admitted := admission.admitRaw z hOffAxis
  admittedAccepted := admission.admitAccepted z hOffAxis
  normalForm_aligned := admission.admitNormalForm z hOffAxis

/-- The pointwise witness extracted from a tower admission is impossible. -/
theorem G8BoundaryToBookIIITowerSpectralAdmission.admittedOffAxisWitness_refutes
    {model : G8BookIIITowerAcceptedSpectralWitnessModel}
    {transfer : G8dZeroDivisorTransferContext}
    {readout : G8FinalRHTransferChartReadout transfer}
    (admission :
      G8BoundaryToBookIIITowerSpectralAdmission model readout)
    (z : OrthodoxXiZeroCarrier)
    (hOffAxis :
      G8ActualXiZetaThinChartOffAxis
        (model.toAcceptedDomain.thinSource readout) z) :
    False :=
  (admission.toAdmittedOffAxisWitness z hOffAxis).refutes

-- ============================================================
-- COMPACT TOWER-ADMISSION SPINE
-- ============================================================

/-- Compact D4 tower-admission spine.

The fields intentionally keep tower admission explicit.  This object does not
construct admission from the broad boundary carrier; it only records the
consequences if such an accepted tower admission is supplied. -/
structure G8BookIIITowerAdmissionConflictSpine where
  transfer : G8dZeroDivisorTransferContext
  readout : G8FinalRHTransferChartReadout transfer
  model : G8BookIIITowerAcceptedSpectralWitnessModel
  admission :
    G8BoundaryToBookIIITowerSpectralAdmission model readout

/-- Accepted domain selected by the D4 tower-admission spine. -/
def G8BookIIITowerAdmissionConflictSpine.domain
    (spine : G8BookIIITowerAdmissionConflictSpine) :
    G8AcceptedTauSpectralWitnessDomain :=
  spine.model.toAcceptedDomain

/-- Thin actual source selected by the D4 tower-admission spine. -/
def G8BookIIITowerAdmissionConflictSpine.thinSource
    (spine : G8BookIIITowerAdmissionConflictSpine) :
    G8ActualXiZetaThinSourceContext :=
  spine.domain.thinSource spine.readout

/-- Full actual source selected by the D4 tower-admission spine. -/
def G8BookIIITowerAdmissionConflictSpine.source
    (spine : G8BookIIITowerAdmissionConflictSpine) :
    G8ActualXiZetaSourceContext :=
  spine.domain.source spine.readout

/-- The D4 tower-admission spine as the accepted-balance admission spine. -/
def G8BookIIITowerAdmissionConflictSpine.toAcceptedBalanceSpine
    (spine : G8BookIIITowerAdmissionConflictSpine) :
    G8BookIIIAcceptedBalanceAdmissionSpine :=
  spine.admission.toAcceptedBalanceSpine

/-- The D4 tower-admission spine refutes a pointwise thin off-axis shadow. -/
theorem G8BookIIITowerAdmissionConflictSpine.refutesThinOffAxis
    (spine : G8BookIIITowerAdmissionConflictSpine)
    (z : OrthodoxXiZeroCarrier)
    (hOffAxis :
      G8ActualXiZetaThinChartOffAxis spine.thinSource z) :
    False :=
  spine.admission.refutesThinOffAxis z hOffAxis

/-- The D4 tower-admission spine excludes all thin off-axis chart shadows. -/
theorem G8BookIIITowerAdmissionConflictSpine.noThinChartOffAxis
    (spine : G8BookIIITowerAdmissionConflictSpine) :
    ∀ z : OrthodoxXiZeroCarrier,
      ¬ G8ActualXiZetaThinChartOffAxis spine.thinSource z :=
  spine.admission.noThinChartOffAxis_direct

/-- The D4 tower-admission spine yields local off-critical exclusion through
    the accepted-balance spine. -/
theorem G8BookIIITowerAdmissionConflictSpine.noOffCriticalXiZeros
    (spine : G8BookIIITowerAdmissionConflictSpine) :
    G8eNoOrthodoxOffCriticalZeros
      (g8ActualXiZeta_base
        (G8BookIIISpectralPurityAdmissionSpine.toAcceptedSpine
          (G8BookIIIAcceptedBalanceAdmissionSpine.toSpectralPurityAdmissionSpine
            spine.toAcceptedBalanceSpine)).source) :=
  spine.toAcceptedBalanceSpine.noOffCriticalXiZeros

/-- Conditional final handoff through the existing coverage theorem, using
    only the fields supplied by the D4 tower-admission spine. -/
theorem G8BookIIITowerAdmissionConflictSpine.mathlibRiemannHypothesis
    (spine : G8BookIIITowerAdmissionConflictSpine) :
    RiemannHypothesis :=
  spine.toAcceptedBalanceSpine.mathlibRiemannHypothesis

-- ============================================================
-- INTERFACE CHECKS
-- ============================================================

#check g8BookIIITowerAcceptedWitness_refutesAlignedOffAxis
#check G8BoundaryToBookIIITowerSpectralAdmission.refutesThinOffAxis
#check G8BookIIITowerAdmittedOffAxisWitness.refutes
#check G8BookIIITowerAdmissionConflictSpine.noThinChartOffAxis
#check G8BookIIITowerAdmissionConflictSpine.mathlibRiemannHypothesis

end Tau.BookIII.Bridge
