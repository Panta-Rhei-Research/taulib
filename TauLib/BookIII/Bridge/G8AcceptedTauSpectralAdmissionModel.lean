import TauLib.BookIII.Bridge.G8AcceptedSpectralStageCertificate

/-!
# TauLib.BookIII.Bridge.G8AcceptedTauSpectralAdmissionModel

Raw-to-accepted admission model for the final G8f tau-purity hinge.

The broad boundary-address carrier is an address-resolution surface.  It is
not the carrier governed by Book III spectral purity.  This module therefore
keeps accepted tau witnesses as a filtered subtype of a raw spectral-witness
model, and factors admission into:

* selecting a raw witness for an actual off-axis `xi` shadow;
* proving that raw witness is accepted;
* proving its normal form is the normalized centered boundary address.

The local contradiction theorem below is a proof-shape test: once such an
accepted admission exists, any off-axis actual `xi` shadow contradicts the
accepted-domain purity field.  The theorem does not construct the admission,
does not prove global tau spectral purity, does not prove O3, and does not
prove an analytic zero-divisor transfer theorem.
-/

set_option autoImplicit false

noncomputable section

namespace Tau.BookIII.Bridge

open Tau.BookIII.Spectral
open Tau.BookIII.Doors

-- ============================================================
-- RAW-TO-ACCEPTED SPECTRAL WITNESS MODEL
-- ============================================================

/-- Raw spectral-witness model before filtering to the accepted tau carrier.

The accepted carrier is the subtype of raw witnesses satisfying `IsAccepted`.
This prevents the final spine from treating every boundary-address candidate
as governed by Book III spectral purity. -/
structure G8RawTauSpectralWitnessModel where
  rawWitness : Type 2
  rawNormalForm : rawWitness → BoundaryNF
  IsAccepted : rawWitness → Prop
  acceptedPurity :
    ∀ w : rawWitness, IsAccepted w →
      ¬ TauCriticalImbalance (rawNormalForm w)
  status : G8OffCriticalExclusionStatus := .openObligation

/-- The accepted tau spectral domain obtained by filtering raw witnesses. -/
def G8RawTauSpectralWitnessModel.toAcceptedDomain
    (model : G8RawTauSpectralWitnessModel) :
    G8AcceptedTauSpectralWitnessDomain where
  tauWitness := { w : model.rawWitness // model.IsAccepted w }
  tauNormalForm := fun w => model.rawNormalForm w.1
  spectralPurity := by
    intro w hImbalance
    exact model.acceptedPurity w.1 w.2 hImbalance
  status := model.status

-- ============================================================
-- RAW ADMISSION INTO THE ACCEPTED SUBTYPE
-- ============================================================

/-- Raw admission data for actual off-axis `xi` shadows.

This is the proof-facing place where a future tau-geometry theorem should
select a raw witness, prove it accepted, and align its normal form with the
normalized centered boundary address. -/
structure G8RawBoundaryToAcceptedTauSpectralAdmission
    (model : G8RawTauSpectralWitnessModel)
    {transfer : G8dZeroDivisorTransferContext}
    (readout : G8FinalRHTransferChartReadout transfer) where
  admitRaw :
    ∀ z : OrthodoxXiZeroCarrier,
      G8ActualXiZetaThinChartOffAxis
        (model.toAcceptedDomain.thinSource readout) z →
        model.rawWitness
  admitAccepted :
    ∀ (z : OrthodoxXiZeroCarrier)
      (hOffAxis :
        G8ActualXiZetaThinChartOffAxis
          (model.toAcceptedDomain.thinSource readout) z),
      model.IsAccepted (admitRaw z hOffAxis)
  admitNormalForm :
    ∀ (z : OrthodoxXiZeroCarrier)
      (hOffAxis :
        G8ActualXiZetaThinChartOffAxis
          (model.toAcceptedDomain.thinSource readout) z),
      model.rawNormalForm (admitRaw z hOffAxis) =
        (orthodoxXiCarrierCenteredBoundaryPointAddress z).normalize.nf

/-- Convert raw admission data into the existing accepted-domain admission
    interface. -/
def G8RawBoundaryToAcceptedTauSpectralAdmission.toAdmission
    {model : G8RawTauSpectralWitnessModel}
    {transfer : G8dZeroDivisorTransferContext}
    {readout : G8FinalRHTransferChartReadout transfer}
    (rawAdmission :
      G8RawBoundaryToAcceptedTauSpectralAdmission model readout) :
    G8BoundaryToAcceptedTauSpectralAdmission
      model.toAcceptedDomain readout where
  admit := fun z hOffAxis =>
    ⟨rawAdmission.admitRaw z hOffAxis,
      rawAdmission.admitAccepted z hOffAxis⟩
  admit_normalForm := by
    intro z hOffAxis
    exact rawAdmission.admitNormalForm z hOffAxis

-- ============================================================
-- LOCAL CONTRADICTION SURFACE
-- ============================================================

/-- Accepted-domain admission excludes thin off-axis chart shadows.

The proof is intentionally local: the admitted witness has the normalized
centered boundary-address normal form, that normal form is critically
imbalanced for an off-axis actual `xi` shadow, and the accepted spectral
domain excludes critical imbalance. -/
theorem G8BoundaryToAcceptedTauSpectralAdmission.noThinChartOffAxis
    {transfer : G8dZeroDivisorTransferContext}
    {domain : G8AcceptedTauSpectralWitnessDomain}
    {readout : G8FinalRHTransferChartReadout transfer}
    (admission :
      G8BoundaryToAcceptedTauSpectralAdmission domain readout) :
    ∀ z : OrthodoxXiZeroCarrier,
      ¬ G8ActualXiZetaThinChartOffAxis
          (domain.thinSource readout) z := by
  intro z hOffAxis
  have hShadow :
      ShadowOffAxis (orthodoxXiCarrierCenteredShadow z) := by
    simpa [
      G8ActualXiZetaThinChartOffAxis,
      g8ActualXiZetaThinCenteredShadow
    ] using hOffAxis
  have hAddressImbalance :
      TauCriticalImbalance
        (orthodoxXiCarrierCenteredBoundaryPointAddress z).normalize.nf :=
    orthodoxXiCarrierCenteredBoundaryPointAddress_criticalImbalance
      z hShadow
  have hAdmittedImbalance :
      TauCriticalImbalance
        (domain.tauNormalForm (admission.admit z hOffAxis)) := by
    rw [admission.admit_normalForm z hOffAxis]
    exact hAddressImbalance
  exact domain.spectralPurity (admission.admit z hOffAxis) hAdmittedImbalance

/-- Raw admission excludes thin off-axis chart shadows after conversion to the
    accepted subtype. -/
theorem G8RawBoundaryToAcceptedTauSpectralAdmission.noThinChartOffAxis
    {model : G8RawTauSpectralWitnessModel}
    {transfer : G8dZeroDivisorTransferContext}
    {readout : G8FinalRHTransferChartReadout transfer}
    (rawAdmission :
      G8RawBoundaryToAcceptedTauSpectralAdmission model readout) :
    ∀ z : OrthodoxXiZeroCarrier,
      ¬ G8ActualXiZetaThinChartOffAxis
          (model.toAcceptedDomain.thinSource readout) z :=
  rawAdmission.toAdmission.noThinChartOffAxis

-- ============================================================
-- FIXED STAGE-3 FINITE CERTIFICATE EXAMPLES
-- ============================================================

/-- Finite stage certificate for the first theorem-backed point-sensitive
    off-axis address.  This is check-level evidence only. -/
def g8AcceptedStageCertificate_offAxisAddressA :
    G8AcceptedSpectralStageCertificate where
  stage := 3
  mode := 1
  nf := g8PointSensitiveOffAxisAddressA.normalize.nf
  nf_depth := by native_decide
  mode_visible := by native_decide
  self_adjoint_stage := by native_decide
  k5_diagonal_stage := by native_decide
  finite_correspondence_stage := by native_decide
  critical_line_stage := by native_decide
  projector_stage := by native_decide
  measure_stage := by native_decide
  parseval_stage := by native_decide
  spectral_resolution_stage := by native_decide

/-- Finite stage certificate for the second theorem-backed point-sensitive
    off-axis address.  This is check-level evidence only. -/
def g8AcceptedStageCertificate_offAxisAddressB :
    G8AcceptedSpectralStageCertificate where
  stage := 3
  mode := 1
  nf := g8PointSensitiveOffAxisAddressB.normalize.nf
  nf_depth := by native_decide
  mode_visible := by native_decide
  self_adjoint_stage := by native_decide
  k5_diagonal_stage := by native_decide
  finite_correspondence_stage := by native_decide
  critical_line_stage := by native_decide
  projector_stage := by native_decide
  measure_stage := by native_decide
  parseval_stage := by native_decide
  spectral_resolution_stage := by native_decide

/-- The first fixed certificate carries the first normalized off-axis address. -/
theorem g8AcceptedStageCertificate_offAxisAddressA_nf :
    g8AcceptedStageCertificate_offAxisAddressA.nf =
      g8PointSensitiveOffAxisAddressA.normalize.nf :=
  rfl

/-- The second fixed certificate carries the second normalized off-axis
    address. -/
theorem g8AcceptedStageCertificate_offAxisAddressB_nf :
    g8AcceptedStageCertificate_offAxisAddressB.nf =
      g8PointSensitiveOffAxisAddressB.normalize.nf :=
  rfl

-- ============================================================
-- INTERFACE CHECKS
-- ============================================================

#check G8RawTauSpectralWitnessModel.toAcceptedDomain
#check G8RawBoundaryToAcceptedTauSpectralAdmission.toAdmission
#check G8BoundaryToAcceptedTauSpectralAdmission.noThinChartOffAxis
#check G8CertifiedAcceptedTauSpectralAlmostFinalSpine.mathlibRiemannHypothesis

end Tau.BookIII.Bridge
