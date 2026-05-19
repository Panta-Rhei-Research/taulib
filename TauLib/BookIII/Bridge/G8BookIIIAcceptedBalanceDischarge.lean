import TauLib.BookIII.Bridge.G8BookIIISpectralPurityAdapter

/-!
# TauLib.BookIII.Bridge.G8BookIIIAcceptedBalanceDischarge

Accepted B/C-balance discharge for the Book III spectral-purity adapter.

The preceding adapter named `acceptedBalanced` as the precise Book III
load-bearing target.  This module removes it as an independent model field:
an accepted spectral witness now carries a Book III balance-hyperplane
certificate, and B/C balance is extracted from that certificate.

The certificate remains deliberately scoped.  It packages finite
self-adjointness, K5 diagonal discipline, finite correspondence,
critical-line, and spectral-resolution checks together with the balance
hyperplane datum for the accepted witness normal form.  It does not assert
that every boundary-address candidate is accepted, and it does not discharge
O3, analytic-completion uniqueness, or full divisor transfer.
-/

set_option autoImplicit false

noncomputable section

namespace Tau.BookIII.Bridge

open Tau.BookIII.Spectral
open Tau.BookIII.Doors

-- ============================================================
-- BOOK III BALANCE-HYPERPLANE CERTIFICATES
-- ============================================================

/-- Book III balance-hyperplane invariant for a finite spectral-stage
    certificate. -/
def G8BookIIIBalanceHyperplaneInvariant
    (cert : G8AcceptedSpectralStageCertificate) : Prop :=
  BCBalanced cert.nf

/-- Accepted Book III spectral-stage certificate with its balance-hyperplane
    datum.

The finite stage checks record the operator/spectral discipline; the
hyperplane datum records the accepted witness's B/C balance. -/
structure G8BookIIIBalanceHyperplaneCertificate where
  stageCert : G8AcceptedSpectralStageCertificate
  balanceHyperplane :
    G8BookIIIBalanceHyperplaneInvariant stageCert

/-- The balance-hyperplane certificate exposes B/C balance. -/
theorem G8BookIIIBalanceHyperplaneCertificate.bcBalanced
    (cert : G8BookIIIBalanceHyperplaneCertificate) :
    BCBalanced cert.stageCert.nf :=
  cert.balanceHyperplane

/-- The balance-hyperplane certificate excludes tau critical imbalance. -/
theorem G8BookIIIBalanceHyperplaneCertificate.noCriticalImbalance
    (cert : G8BookIIIBalanceHyperplaneCertificate) :
    ¬ TauCriticalImbalance cert.stageCert.nf :=
  bcBalanced_noTauCriticalImbalance
    cert.stageCert.nf cert.bcBalanced

/-- Balance-hyperplane certificates still expose finite self-adjointness. -/
theorem G8BookIIIBalanceHyperplaneCertificate.selfAdjoint
    (cert : G8BookIIIBalanceHyperplaneCertificate) :
    self_adjoint_check cert.stageCert.stage = true :=
  cert.stageCert.selfAdjoint

/-- Balance-hyperplane certificates still expose finite K5 discipline. -/
theorem G8BookIIIBalanceHyperplaneCertificate.k5Diagonal
    (cert : G8BookIIIBalanceHyperplaneCertificate) :
    k5_diagonal_check cert.stageCert.stage = true :=
  cert.stageCert.k5Diagonal

/-- Balance-hyperplane certificates still expose finite correspondence. -/
theorem G8BookIIIBalanceHyperplaneCertificate.finiteCorrespondence
    (cert : G8BookIIIBalanceHyperplaneCertificate) :
    spectral_correspondence_finite cert.stageCert.stage = true :=
  cert.stageCert.finiteCorrespondence

/-- Balance-hyperplane certificates still expose finite critical-line
    discipline. -/
theorem G8BookIIIBalanceHyperplaneCertificate.criticalLine
    (cert : G8BookIIIBalanceHyperplaneCertificate) :
    critical_line_check cert.stageCert.stage = true :=
  cert.stageCert.criticalLine

/-- Balance-hyperplane certificates still expose finite spectral resolution. -/
theorem G8BookIIIBalanceHyperplaneCertificate.spectralResolution
    (cert : G8BookIIIBalanceHyperplaneCertificate) :
    spectral_resolution_check (cert.stageCert.stage + 1) = true :=
  cert.stageCert.spectralResolution

-- ============================================================
-- ACCEPTED BALANCE MODEL WITHOUT A FREE BALANCE FIELD
-- ============================================================

/-- Book III accepted-balance model.

Compared with `G8BookIIISpectralPurityModel`, this structure has no
standalone `acceptedBalanced` field.  Accepted balance is discharged by the
pointwise Book III balance-hyperplane certificate. -/
structure G8BookIIIAcceptedBalanceModel where
  spectralWitness : Type 2
  normalForm : spectralWitness → BoundaryNF
  IsAccepted : spectralWitness → Prop
  balanceCertificate :
    ∀ w : spectralWitness,
      IsAccepted w →
        G8BookIIIBalanceHyperplaneCertificate
  balanceCertificate_normalForm :
    ∀ (w : spectralWitness) (hAccepted : IsAccepted w),
      (balanceCertificate w hAccepted).stageCert.nf = normalForm w
  status : G8OffCriticalExclusionStatus := .openObligation

/-- Accepted balance is discharged from the Book III balance certificate. -/
theorem G8BookIIIAcceptedBalanceModel.acceptedBalanced
    (model : G8BookIIIAcceptedBalanceModel)
    (w : model.spectralWitness)
    (hAccepted : model.IsAccepted w) :
    BCBalanced (model.normalForm w) := by
  have hBalanced :
      BCBalanced
        (model.balanceCertificate w hAccepted).stageCert.nf :=
    (model.balanceCertificate w hAccepted).bcBalanced
  simpa [model.balanceCertificate_normalForm w hAccepted] using hBalanced

/-- Accepted balance supplies accepted-domain purity. -/
theorem G8BookIIIAcceptedBalanceModel.acceptedPurity
    (model : G8BookIIIAcceptedBalanceModel)
    (w : model.spectralWitness)
    (hAccepted : model.IsAccepted w) :
    ¬ TauCriticalImbalance (model.normalForm w) :=
  bcBalanced_noTauCriticalImbalance
    (model.normalForm w)
    (model.acceptedBalanced w hAccepted)

/-- The accepted-balance model exposes the underlying finite stage
    certificate. -/
def G8BookIIIAcceptedBalanceModel.stageCertificate
    (model : G8BookIIIAcceptedBalanceModel)
    (w : model.spectralWitness)
    (hAccepted : model.IsAccepted w) :
    G8AcceptedSpectralStageCertificate :=
  (model.balanceCertificate w hAccepted).stageCert

/-- The stage-certificate normal form is the accepted witness normal form. -/
theorem G8BookIIIAcceptedBalanceModel.stageCertificate_normalForm
    (model : G8BookIIIAcceptedBalanceModel)
    (w : model.spectralWitness)
    (hAccepted : model.IsAccepted w) :
    (model.stageCertificate w hAccepted).nf = model.normalForm w :=
  model.balanceCertificate_normalForm w hAccepted

/-- Convert the accepted-balance model into the earlier Book III purity
    adapter surface. -/
def G8BookIIIAcceptedBalanceModel.toSpectralPurityModel
    (model : G8BookIIIAcceptedBalanceModel) :
    G8BookIIISpectralPurityModel where
  spectralWitness := model.spectralWitness
  normalForm := model.normalForm
  IsAccepted := model.IsAccepted
  stageCertificate := model.stageCertificate
  stageCertificate_normalForm := model.stageCertificate_normalForm
  acceptedBalanced := model.acceptedBalanced
  status := model.status

/-- Convert the accepted-balance model into the raw spectral-witness model. -/
def G8BookIIIAcceptedBalanceModel.toRawTauSpectralWitnessModel
    (model : G8BookIIIAcceptedBalanceModel) :
    G8RawTauSpectralWitnessModel :=
  model.toSpectralPurityModel.toRawTauSpectralWitnessModel

/-- Accepted spectral domain induced by the accepted-balance model. -/
def G8BookIIIAcceptedBalanceModel.toAcceptedDomain
    (model : G8BookIIIAcceptedBalanceModel) :
    G8AcceptedTauSpectralWitnessDomain :=
  model.toRawTauSpectralWitnessModel.toAcceptedDomain

/-- The accepted-balance model exposes finite self-adjointness pointwise. -/
theorem G8BookIIIAcceptedBalanceModel.stage_selfAdjoint
    (model : G8BookIIIAcceptedBalanceModel)
    (w : model.spectralWitness)
    (hAccepted : model.IsAccepted w) :
    self_adjoint_check (model.stageCertificate w hAccepted).stage = true :=
  (model.balanceCertificate w hAccepted).selfAdjoint

/-- The accepted-balance model exposes finite K5 discipline pointwise. -/
theorem G8BookIIIAcceptedBalanceModel.stage_k5Diagonal
    (model : G8BookIIIAcceptedBalanceModel)
    (w : model.spectralWitness)
    (hAccepted : model.IsAccepted w) :
    k5_diagonal_check (model.stageCertificate w hAccepted).stage = true :=
  (model.balanceCertificate w hAccepted).k5Diagonal

/-- The accepted-balance model exposes finite critical-line checks
    pointwise. -/
theorem G8BookIIIAcceptedBalanceModel.stage_criticalLine
    (model : G8BookIIIAcceptedBalanceModel)
    (w : model.spectralWitness)
    (hAccepted : model.IsAccepted w) :
    critical_line_check (model.stageCertificate w hAccepted).stage = true :=
  (model.balanceCertificate w hAccepted).criticalLine

/-- The accepted-balance model exposes finite spectral resolution pointwise. -/
theorem G8BookIIIAcceptedBalanceModel.stage_spectralResolution
    (model : G8BookIIIAcceptedBalanceModel)
    (w : model.spectralWitness)
    (hAccepted : model.IsAccepted w) :
    spectral_resolution_check
        ((model.stageCertificate w hAccepted).stage + 1) = true :=
  (model.balanceCertificate w hAccepted).spectralResolution

-- ============================================================
-- ACCEPTED-BALANCE ADMISSION SPINE
-- ============================================================

/-- Admission spine whose accepted purity is discharged by Book III
    balance-hyperplane certificates. -/
structure G8BookIIIAcceptedBalanceAdmissionSpine where
  transfer : G8dZeroDivisorTransferContext
  readout : G8FinalRHTransferChartReadout transfer
  model : G8BookIIIAcceptedBalanceModel
  rawAdmission :
    G8RawBoundaryToAcceptedTauSpectralAdmission
      model.toRawTauSpectralWitnessModel readout

/-- The accepted-balance admission spine as the previous Book III spectral
    purity admission spine. -/
def G8BookIIIAcceptedBalanceAdmissionSpine.toSpectralPurityAdmissionSpine
    (spine : G8BookIIIAcceptedBalanceAdmissionSpine) :
    G8BookIIISpectralPurityAdmissionSpine where
  transfer := spine.transfer
  readout := spine.readout
  model := spine.model.toSpectralPurityModel
  rawAdmission := spine.rawAdmission

/-- Accepted domain selected by the accepted-balance admission spine. -/
def G8BookIIIAcceptedBalanceAdmissionSpine.domain
    (spine : G8BookIIIAcceptedBalanceAdmissionSpine) :
    G8AcceptedTauSpectralWitnessDomain :=
  spine.model.toAcceptedDomain

/-- Accepted-domain admission selected by the accepted-balance spine. -/
def G8BookIIIAcceptedBalanceAdmissionSpine.admission
    (spine : G8BookIIIAcceptedBalanceAdmissionSpine) :
    G8BoundaryToAcceptedTauSpectralAdmission
      spine.domain spine.readout :=
  spine.rawAdmission.toAdmission

/-- Pointwise Book III balance certificate for an admitted off-axis shadow. -/
def G8BookIIIAcceptedBalanceAdmissionSpine.balanceCertificate
    (spine : G8BookIIIAcceptedBalanceAdmissionSpine)
    (z : OrthodoxXiZeroCarrier)
    (hOffAxis :
      G8ActualXiZetaThinChartOffAxis
        (spine.domain.thinSource spine.readout) z) :
    G8BookIIIBalanceHyperplaneCertificate :=
  spine.model.balanceCertificate
    (spine.rawAdmission.admitRaw z hOffAxis)
    (spine.rawAdmission.admitAccepted z hOffAxis)

/-- Pointwise accepted B/C balance for the admitted spectral witness. -/
theorem G8BookIIIAcceptedBalanceAdmissionSpine.pointwiseAcceptedBalanced
    (spine : G8BookIIIAcceptedBalanceAdmissionSpine)
    (z : OrthodoxXiZeroCarrier)
    (hOffAxis :
      G8ActualXiZetaThinChartOffAxis
        (spine.domain.thinSource spine.readout) z) :
    BCBalanced
      (spine.model.normalForm
        (spine.rawAdmission.admitRaw z hOffAxis)) :=
  spine.model.acceptedBalanced
    (spine.rawAdmission.admitRaw z hOffAxis)
    (spine.rawAdmission.admitAccepted z hOffAxis)

/-- The admitted witness normal form is pure in the accepted Book III sense. -/
theorem G8BookIIIAcceptedBalanceAdmissionSpine.pointwiseNoCriticalImbalance
    (spine : G8BookIIIAcceptedBalanceAdmissionSpine)
    (z : OrthodoxXiZeroCarrier)
    (hOffAxis :
      G8ActualXiZetaThinChartOffAxis
        (spine.domain.thinSource spine.readout) z) :
    ¬ TauCriticalImbalance
        (spine.model.normalForm
          (spine.rawAdmission.admitRaw z hOffAxis)) :=
  spine.model.acceptedPurity
    (spine.rawAdmission.admitRaw z hOffAxis)
    (spine.rawAdmission.admitAccepted z hOffAxis)

/-- Accepted-balance admission excludes thin off-axis chart shadows through
    the existing local contradiction surface. -/
theorem G8BookIIIAcceptedBalanceAdmissionSpine.noThinChartOffAxis
    (spine : G8BookIIIAcceptedBalanceAdmissionSpine) :
    ∀ z : OrthodoxXiZeroCarrier,
      ¬ G8ActualXiZetaThinChartOffAxis
          (spine.domain.thinSource spine.readout) z :=
  spine.admission.noThinChartOffAxis

/-- Accepted-balance admission yields the local off-critical exclusion
    through the accepted-domain corridor. -/
theorem G8BookIIIAcceptedBalanceAdmissionSpine.noOffCriticalXiZeros
    (spine : G8BookIIIAcceptedBalanceAdmissionSpine) :
    G8eNoOrthodoxOffCriticalZeros
      (g8ActualXiZeta_base
        spine.toSpectralPurityAdmissionSpine.toAcceptedSpine.source) :=
  spine.toSpectralPurityAdmissionSpine.noOffCriticalXiZeros

/-- Conditional final handoff through the existing coverage theorem, from the
    fields carried by the accepted-balance admission spine. -/
theorem G8BookIIIAcceptedBalanceAdmissionSpine.mathlibRiemannHypothesis
    (spine : G8BookIIIAcceptedBalanceAdmissionSpine) :
    RiemannHypothesis :=
  spine.toSpectralPurityAdmissionSpine.mathlibRiemannHypothesis

-- ============================================================
-- INTERFACE CHECKS
-- ============================================================

#check G8BookIIIAcceptedBalanceModel.acceptedBalanced
#check G8BookIIIAcceptedBalanceModel.toSpectralPurityModel
#check G8BookIIIAcceptedBalanceAdmissionSpine.noThinChartOffAxis
#check G8BookIIIAcceptedBalanceAdmissionSpine.mathlibRiemannHypothesis

end Tau.BookIII.Bridge
