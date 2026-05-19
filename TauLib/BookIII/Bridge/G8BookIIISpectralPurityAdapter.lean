import TauLib.BookIII.Bridge.G8AcceptedTauSpectralAdmissionModel

/-!
# TauLib.BookIII.Bridge.G8BookIIISpectralPurityAdapter

Book III spectral-purity adapter for the accepted G8f tau witness domain.

Book III's purity mechanism is an accepted spectral-domain statement: K5
diagonal discipline, the lemniscate operator, and finite primorial stage
certificates support accepted B/C balance.  The broad boundary-address carrier
remains an address-resolution surface.  This module therefore derives the
accepted-domain purity field from an explicit Book III balance invariant while
keeping actual off-axis `xi` admission as a separate load-bearing map.

The adapter does not establish O3, analytic-completion uniqueness, full
zero-divisor transfer, or a global theorem that every boundary address is
accepted by the spectral domain.
-/

set_option autoImplicit false

noncomputable section

namespace Tau.BookIII.Bridge

open Tau.BookIII.Spectral
open Tau.BookIII.Doors

-- ============================================================
-- BOOK III ACCEPTED SPECTRAL PURITY MODEL
-- ============================================================

/-- B/C balance excludes tau critical imbalance. -/
theorem bcBalanced_noTauCriticalImbalance
    (nf : BoundaryNF)
    (hBalanced : BCBalanced nf) :
    ¬ TauCriticalImbalance nf := by
  intro hImbalance
  exact hImbalance ((tauCriticalLocus_iff_bcBalanced nf).mpr hBalanced)

/-- Book III accepted spectral-purity model.

The field `acceptedBalanced` is the precise load-bearing Book III target:
accepted spectral witnesses must have B/C-balanced normal form.  Finite stage
certificates record the reusable lemniscate/K5/critical-line checks supporting
the accepted witness, but do not by themselves assert global purity. -/
structure G8BookIIISpectralPurityModel where
  spectralWitness : Type 2
  normalForm : spectralWitness → BoundaryNF
  IsAccepted : spectralWitness → Prop
  stageCertificate :
    ∀ w : spectralWitness,
      IsAccepted w →
        G8AcceptedSpectralStageCertificate
  stageCertificate_normalForm :
    ∀ (w : spectralWitness) (hAccepted : IsAccepted w),
      (stageCertificate w hAccepted).nf = normalForm w
  acceptedBalanced :
    ∀ w : spectralWitness,
      IsAccepted w →
        BCBalanced (normalForm w)
  status : G8OffCriticalExclusionStatus := .openObligation

/-- Accepted Book III balance supplies accepted-domain purity. -/
theorem G8BookIIISpectralPurityModel.acceptedPurity
    (model : G8BookIIISpectralPurityModel)
    (w : model.spectralWitness)
    (hAccepted : model.IsAccepted w) :
    ¬ TauCriticalImbalance (model.normalForm w) :=
  bcBalanced_noTauCriticalImbalance
    (model.normalForm w)
    (model.acceptedBalanced w hAccepted)

/-- Convert the Book III model into the raw-to-accepted model used by the
    final G8f admission layer. -/
def G8BookIIISpectralPurityModel.toRawTauSpectralWitnessModel
    (model : G8BookIIISpectralPurityModel) :
    G8RawTauSpectralWitnessModel where
  rawWitness := model.spectralWitness
  rawNormalForm := model.normalForm
  IsAccepted := model.IsAccepted
  acceptedPurity := by
    intro w hAccepted
    exact model.acceptedPurity w hAccepted
  status := model.status

/-- Accepted spectral domain induced by the Book III model. -/
def G8BookIIISpectralPurityModel.toAcceptedDomain
    (model : G8BookIIISpectralPurityModel) :
    G8AcceptedTauSpectralWitnessDomain :=
  model.toRawTauSpectralWitnessModel.toAcceptedDomain

-- ============================================================
-- STAGE-CERTIFICATE SELECTORS
-- ============================================================

/-- Book III model exposes the finite stage certificate for an accepted
    witness. -/
def G8BookIIISpectralPurityModel.stageCert
    (model : G8BookIIISpectralPurityModel)
    (w : model.spectralWitness)
    (hAccepted : model.IsAccepted w) :
    G8AcceptedSpectralStageCertificate :=
  model.stageCertificate w hAccepted

/-- The finite certificate normal form is the accepted witness normal form. -/
theorem G8BookIIISpectralPurityModel.stageCert_normalForm
    (model : G8BookIIISpectralPurityModel)
    (w : model.spectralWitness)
    (hAccepted : model.IsAccepted w) :
    (model.stageCert w hAccepted).nf = model.normalForm w :=
  model.stageCertificate_normalForm w hAccepted

/-- Book III finite self-adjointness check carried by the accepted witness. -/
theorem G8BookIIISpectralPurityModel.stage_selfAdjoint
    (model : G8BookIIISpectralPurityModel)
    (w : model.spectralWitness)
    (hAccepted : model.IsAccepted w) :
    self_adjoint_check (model.stageCert w hAccepted).stage = true :=
  (model.stageCert w hAccepted).selfAdjoint

/-- Book III finite K5 diagonal-discipline check carried by the accepted
    witness. -/
theorem G8BookIIISpectralPurityModel.stage_k5Diagonal
    (model : G8BookIIISpectralPurityModel)
    (w : model.spectralWitness)
    (hAccepted : model.IsAccepted w) :
    k5_diagonal_check (model.stageCert w hAccepted).stage = true :=
  (model.stageCert w hAccepted).k5Diagonal

/-- Book III finite spectral-correspondence check carried by the accepted
    witness. -/
theorem G8BookIIISpectralPurityModel.stage_finiteCorrespondence
    (model : G8BookIIISpectralPurityModel)
    (w : model.spectralWitness)
    (hAccepted : model.IsAccepted w) :
    spectral_correspondence_finite
      (model.stageCert w hAccepted).stage = true :=
  (model.stageCert w hAccepted).finiteCorrespondence

/-- Book III finite critical-line check carried by the accepted witness. -/
theorem G8BookIIISpectralPurityModel.stage_criticalLine
    (model : G8BookIIISpectralPurityModel)
    (w : model.spectralWitness)
    (hAccepted : model.IsAccepted w) :
    critical_line_check (model.stageCert w hAccepted).stage = true :=
  (model.stageCert w hAccepted).criticalLine

/-- Book III finite spectral-resolution check carried by the accepted
    witness. -/
theorem G8BookIIISpectralPurityModel.stage_spectralResolution
    (model : G8BookIIISpectralPurityModel)
    (w : model.spectralWitness)
    (hAccepted : model.IsAccepted w) :
    spectral_resolution_check
      ((model.stageCert w hAccepted).stage + 1) = true :=
  (model.stageCert w hAccepted).spectralResolution

-- ============================================================
-- BOOK III PURITY ADMISSION SPINE
-- ============================================================

/-- Compact admission spine using the Book III accepted-purity model.

The raw admission map is still explicit: it selects a raw spectral witness for
an actual off-axis `xi` shadow, proves acceptance, and aligns the normal form
with the normalized centered boundary address. -/
structure G8BookIIISpectralPurityAdmissionSpine where
  transfer : G8dZeroDivisorTransferContext
  readout : G8FinalRHTransferChartReadout transfer
  model : G8BookIIISpectralPurityModel
  rawAdmission :
    G8RawBoundaryToAcceptedTauSpectralAdmission
      model.toRawTauSpectralWitnessModel readout

/-- Raw model selected by the Book III admission spine. -/
def G8BookIIISpectralPurityAdmissionSpine.rawModel
    (spine : G8BookIIISpectralPurityAdmissionSpine) :
    G8RawTauSpectralWitnessModel :=
  spine.model.toRawTauSpectralWitnessModel

/-- Accepted domain selected by the Book III admission spine. -/
def G8BookIIISpectralPurityAdmissionSpine.domain
    (spine : G8BookIIISpectralPurityAdmissionSpine) :
    G8AcceptedTauSpectralWitnessDomain :=
  spine.model.toAcceptedDomain

/-- Accepted-domain admission obtained from the raw admission map. -/
def G8BookIIISpectralPurityAdmissionSpine.admission
    (spine : G8BookIIISpectralPurityAdmissionSpine) :
    G8BoundaryToAcceptedTauSpectralAdmission
      spine.domain spine.readout :=
  spine.rawAdmission.toAdmission

/-- Accepted almost-final spine induced by the Book III model and raw
    admission. -/
def G8BookIIISpectralPurityAdmissionSpine.toAcceptedSpine
    (spine : G8BookIIISpectralPurityAdmissionSpine) :
    G8AcceptedTauSpectralAlmostFinalSpine where
  transfer := spine.transfer
  readout := spine.readout
  domain := spine.domain
  admission := spine.admission

/-- Pointwise finite stage support induced by the Book III model. -/
def G8BookIIISpectralPurityAdmissionSpine.admissionSupport
    (spine : G8BookIIISpectralPurityAdmissionSpine) :
    G8BoundaryToAcceptedTauSpectralAdmissionSupport spine.admission where
  certificateOf := by
    intro z hOffAxis
    let raw := spine.rawAdmission.admitRaw z hOffAxis
    let hAccepted := spine.rawAdmission.admitAccepted z hOffAxis
    exact
      { witness := spine.admission.admit z hOffAxis
        stageCert := spine.model.stageCert raw hAccepted
        witness_normalForm := by
          exact
            (spine.model.stageCert_normalForm raw hAccepted).symm }
  certificate_witness := by
    intro z hOffAxis
    rfl
  certificate_normalForm := by
    intro z hOffAxis
    exact
      (spine.model.stageCert_normalForm
        (spine.rawAdmission.admitRaw z hOffAxis)
        (spine.rawAdmission.admitAccepted z hOffAxis)).trans
        (spine.rawAdmission.admitNormalForm z hOffAxis)

/-- Certified accepted spine induced by the Book III admission spine. -/
def G8BookIIISpectralPurityAdmissionSpine.toCertifiedAcceptedSpine
    (spine : G8BookIIISpectralPurityAdmissionSpine) :
    G8CertifiedAcceptedTauSpectralAlmostFinalSpine where
  transfer := spine.transfer
  readout := spine.readout
  domain := spine.domain
  admission := spine.admission
  admissionSupport := spine.admissionSupport

/-- The Book III admission spine exposes the G3 readout. -/
theorem G8BookIIISpectralPurityAdmissionSpine.requires_g3ZetaBridge
    (spine : G8BookIIISpectralPurityAdmissionSpine) :
    spine.transfer.completion.chart.g3ZetaBridge :=
  spine.readout.g3ZetaChartReadout

/-- The Book III admission spine exposes the G4 readout. -/
theorem G8BookIIISpectralPurityAdmissionSpine.requires_g4AnalyticContinuation
    (spine : G8BookIIISpectralPurityAdmissionSpine) :
    spine.transfer.completion.chart.g4AnalyticContinuation :=
  spine.readout.g4CompletedXiReadout

/-- The Book III admission spine exposes pointwise finite stage certificates. -/
def G8BookIIISpectralPurityAdmissionSpine.stageCertificate
    (spine : G8BookIIISpectralPurityAdmissionSpine)
    (z : OrthodoxXiZeroCarrier)
    (hOffAxis :
      G8ActualXiZetaThinChartOffAxis
        (spine.domain.thinSource spine.readout) z) :
    G8AcceptedSpectralStageCertificate :=
  spine.admissionSupport.stageCertificate z hOffAxis

/-- The Book III admission spine exposes finite self-adjointness pointwise. -/
theorem G8BookIIISpectralPurityAdmissionSpine.pointwiseSelfAdjoint
    (spine : G8BookIIISpectralPurityAdmissionSpine)
    (z : OrthodoxXiZeroCarrier)
    (hOffAxis :
      G8ActualXiZetaThinChartOffAxis
        (spine.domain.thinSource spine.readout) z) :
    self_adjoint_check (spine.stageCertificate z hOffAxis).stage = true :=
  spine.admissionSupport.selfAdjoint z hOffAxis

/-- The Book III admission spine exposes finite K5 discipline pointwise. -/
theorem G8BookIIISpectralPurityAdmissionSpine.pointwiseK5Diagonal
    (spine : G8BookIIISpectralPurityAdmissionSpine)
    (z : OrthodoxXiZeroCarrier)
    (hOffAxis :
      G8ActualXiZetaThinChartOffAxis
        (spine.domain.thinSource spine.readout) z) :
    k5_diagonal_check (spine.stageCertificate z hOffAxis).stage = true :=
  (spine.stageCertificate z hOffAxis).k5Diagonal

/-- The Book III admission spine exposes finite critical-line checks
    pointwise. -/
theorem G8BookIIISpectralPurityAdmissionSpine.pointwiseCriticalLine
    (spine : G8BookIIISpectralPurityAdmissionSpine)
    (z : OrthodoxXiZeroCarrier)
    (hOffAxis :
      G8ActualXiZetaThinChartOffAxis
        (spine.domain.thinSource spine.readout) z) :
    critical_line_check (spine.stageCertificate z hOffAxis).stage = true :=
  (spine.stageCertificate z hOffAxis).criticalLine

/-- The Book III admission spine exposes finite spectral resolution
    pointwise. -/
theorem G8BookIIISpectralPurityAdmissionSpine.pointwiseSpectralResolution
    (spine : G8BookIIISpectralPurityAdmissionSpine)
    (z : OrthodoxXiZeroCarrier)
    (hOffAxis :
      G8ActualXiZetaThinChartOffAxis
        (spine.domain.thinSource spine.readout) z) :
    spectral_resolution_check
        ((spine.stageCertificate z hOffAxis).stage + 1) = true :=
  spine.admissionSupport.spectralResolution z hOffAxis

/-- Book III accepted balance and admission exclude thin off-axis chart
    shadows. -/
theorem G8BookIIISpectralPurityAdmissionSpine.noThinChartOffAxis
    (spine : G8BookIIISpectralPurityAdmissionSpine) :
    ∀ z : OrthodoxXiZeroCarrier,
      ¬ G8ActualXiZetaThinChartOffAxis
          (spine.domain.thinSource spine.readout) z :=
  spine.admission.noThinChartOffAxis

/-- Book III accepted-purity admission yields the local off-critical
    exclusion theorem through the existing accepted-domain corridor. -/
theorem G8BookIIISpectralPurityAdmissionSpine.noOffCriticalXiZeros
    (spine : G8BookIIISpectralPurityAdmissionSpine) :
    G8eNoOrthodoxOffCriticalZeros
      (g8ActualXiZeta_base spine.toAcceptedSpine.source) :=
  spine.toAcceptedSpine.noOffCriticalXiZeros

/-- Conditional final handoff through the existing coverage theorem, from the
    fields carried by the Book III admission spine. -/
theorem G8BookIIISpectralPurityAdmissionSpine.mathlibRiemannHypothesis
    (spine : G8BookIIISpectralPurityAdmissionSpine) :
    RiemannHypothesis :=
  spine.toAcceptedSpine.mathlibRiemannHypothesis

-- ============================================================
-- INTERFACE CHECKS
-- ============================================================

#check G8BookIIISpectralPurityModel.toRawTauSpectralWitnessModel
#check G8BookIIISpectralPurityModel.toAcceptedDomain
#check G8BookIIISpectralPurityAdmissionSpine.noThinChartOffAxis
#check G8BookIIISpectralPurityAdmissionSpine.mathlibRiemannHypothesis

end Tau.BookIII.Bridge
