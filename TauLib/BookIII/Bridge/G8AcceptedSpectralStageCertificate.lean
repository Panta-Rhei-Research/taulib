import TauLib.BookIII.Bridge.G8AcceptedTauSpectralPurityDomain
import TauLib.BookIII.Doors.CriticalLine
import TauLib.BookIII.Doors.SpectralDecomp

/-!
# TauLib.BookIII.Bridge.G8AcceptedSpectralStageCertificate

Finite stage certificates for accepted tau spectral witnesses.

This module records the Book III machinery that can be reused when an actual
centered `xi` shadow is admitted into the accepted tau spectral domain:

* primorial stage / boundary normal form substrate;
* lemniscate eigenvalue and self-adjointness checks;
* finite spectral correspondence and critical-line checks;
* finite projector, measure, Parseval, and spectral-resolution checks.

The certificate is deliberately finite and staged.  It does not supply the
global accepted-domain purity theorem, the O3 correspondence theorem, or an
analytic zero-divisor transfer theorem.  It is a reusable discipline surface
for future admission proofs.
-/

set_option autoImplicit false

noncomputable section

namespace Tau.BookIII.Bridge

open Tau.BookIII.Spectral
open Tau.BookIII.Doors

-- ============================================================
-- FINITE ACCEPTED-SPECTRAL STAGE CERTIFICATE
-- ============================================================

/-- Finite certificate that a boundary normal form is being treated through
    the existing Book III spectral-stage machinery.

The fields are intentionally check-level: they record exactly which current
TauLib finite surfaces support an admitted witness.  Infinite correspondence
and global purity stay outside this structure. -/
structure G8AcceptedSpectralStageCertificate where
  stage : Nat
  mode : Nat
  nf : BoundaryNF
  nf_depth : nf.depth = stage
  mode_visible : mode ≤ stage
  primorial_stage :
    PrimorialStage :=
      primorial_stage (nf.b_part + nf.c_part + nf.x_part) stage
  primorial_depth :
    primorial_stage.depth = stage := by
      rfl
  primorial_value :
    primorial_stage.value =
      Tau.Polarity.reduce (nf.b_part + nf.c_part + nf.x_part) stage := by
      rfl
  lemniscate_mode :
    lemniscate_eigenvalue mode = mode * mode := by
      rfl
  self_adjoint_stage :
    self_adjoint_check stage = true
  k5_diagonal_stage :
    k5_diagonal_check stage = true
  finite_correspondence_stage :
    spectral_correspondence_finite stage = true
  critical_line_stage :
    critical_line_check stage = true
  projector_stage :
    projector_check (stage + 1) = true
  measure_stage :
    measure_total_check (stage + 1) = true
  parseval_stage :
    parseval_check (stage + 1) = true
  spectral_resolution_stage :
    spectral_resolution_check (stage + 1) = true

/-- The stage certificate exposes its finite lemniscate eigenvalue law. -/
theorem G8AcceptedSpectralStageCertificate.lemniscateEigenvalue
    (cert : G8AcceptedSpectralStageCertificate) :
    lemniscate_eigenvalue cert.mode = cert.mode * cert.mode :=
  cert.lemniscate_mode

/-- The stage certificate exposes finite self-adjointness. -/
theorem G8AcceptedSpectralStageCertificate.selfAdjoint
    (cert : G8AcceptedSpectralStageCertificate) :
    self_adjoint_check cert.stage = true :=
  cert.self_adjoint_stage

/-- The stage certificate exposes finite K5 diagonal discipline. -/
theorem G8AcceptedSpectralStageCertificate.k5Diagonal
    (cert : G8AcceptedSpectralStageCertificate) :
    k5_diagonal_check cert.stage = true :=
  cert.k5_diagonal_stage

/-- The stage certificate exposes finite spectral correspondence. -/
theorem G8AcceptedSpectralStageCertificate.finiteCorrespondence
    (cert : G8AcceptedSpectralStageCertificate) :
    spectral_correspondence_finite cert.stage = true :=
  cert.finite_correspondence_stage

/-- The stage certificate exposes finite critical-line localization. -/
theorem G8AcceptedSpectralStageCertificate.criticalLine
    (cert : G8AcceptedSpectralStageCertificate) :
    critical_line_check cert.stage = true :=
  cert.critical_line_stage

/-- The stage certificate exposes finite spectral resolution. -/
theorem G8AcceptedSpectralStageCertificate.spectralResolution
    (cert : G8AcceptedSpectralStageCertificate) :
    spectral_resolution_check (cert.stage + 1) = true :=
  cert.spectral_resolution_stage

-- ============================================================
-- CERTIFIED ACCEPTED WITNESSES
-- ============================================================

/-- A witness of an accepted tau spectral domain together with its finite
    spectral-stage certificate. -/
structure G8AcceptedTauSpectralWitnessCertificate
    (domain : G8AcceptedTauSpectralWitnessDomain) where
  witness : domain.tauWitness
  stageCert : G8AcceptedSpectralStageCertificate
  witness_normalForm :
    domain.tauNormalForm witness = stageCert.nf

/-- Accepted-domain purity excludes critical imbalance of the certified
    normal form. -/
theorem G8AcceptedTauSpectralWitnessCertificate.noCriticalImbalance
    {domain : G8AcceptedTauSpectralWitnessDomain}
    (cert : G8AcceptedTauSpectralWitnessCertificate domain) :
    ¬ TauCriticalImbalance cert.stageCert.nf := by
  intro hImbalance
  exact
    domain.spectralPurity cert.witness
      (by
        rw [cert.witness_normalForm]
        exact hImbalance)

/-- A certified accepted witness exposes its finite stage. -/
def G8AcceptedTauSpectralWitnessCertificate.stage
    {domain : G8AcceptedTauSpectralWitnessDomain}
    (cert : G8AcceptedTauSpectralWitnessCertificate domain) : Nat :=
  cert.stageCert.stage

/-- A certified accepted witness exposes its finite mode. -/
def G8AcceptedTauSpectralWitnessCertificate.mode
    {domain : G8AcceptedTauSpectralWitnessDomain}
    (cert : G8AcceptedTauSpectralWitnessCertificate domain) : Nat :=
  cert.stageCert.mode

/-- A certified accepted witness exposes the finite spectral-resolution
    check carried by its stage certificate. -/
theorem G8AcceptedTauSpectralWitnessCertificate.spectralResolution
    {domain : G8AcceptedTauSpectralWitnessDomain}
    (cert : G8AcceptedTauSpectralWitnessCertificate domain) :
    spectral_resolution_check (cert.stage + 1) = true :=
  cert.stageCert.spectralResolution

-- ============================================================
-- ADMISSION SUPPORT CERTIFICATES
-- ============================================================

/-- Certificate support for an admission map into an accepted tau spectral
    domain.

This packages the reusable Book III finite-stage evidence pointwise over the
actual off-axis `xi` carrier.  It is not the admission theorem itself; it is
the evidence layer that future admission proofs can populate. -/
structure G8BoundaryToAcceptedTauSpectralAdmissionSupport
    {transfer : G8dZeroDivisorTransferContext}
    {domain : G8AcceptedTauSpectralWitnessDomain}
    {readout : G8FinalRHTransferChartReadout transfer}
    (admission :
      G8BoundaryToAcceptedTauSpectralAdmission domain readout) where
  certificateOf :
    ∀ (z : OrthodoxXiZeroCarrier)
      (_hOffAxis :
        G8ActualXiZetaThinChartOffAxis
          (domain.thinSource readout) z),
      G8AcceptedTauSpectralWitnessCertificate domain
  certificate_witness :
    ∀ (z : OrthodoxXiZeroCarrier)
      (hOffAxis :
        G8ActualXiZetaThinChartOffAxis
          (domain.thinSource readout) z),
      (certificateOf z hOffAxis).witness =
        admission.admit z hOffAxis
  certificate_normalForm :
    ∀ (z : OrthodoxXiZeroCarrier)
      (hOffAxis :
        G8ActualXiZetaThinChartOffAxis
          (domain.thinSource readout) z),
      (certificateOf z hOffAxis).stageCert.nf =
        (orthodoxXiCarrierCenteredBoundaryPointAddress z).normalize.nf

/-- Admission support exposes the staged certificate for a point. -/
def G8BoundaryToAcceptedTauSpectralAdmissionSupport.stageCertificate
    {transfer : G8dZeroDivisorTransferContext}
    {domain : G8AcceptedTauSpectralWitnessDomain}
    {readout : G8FinalRHTransferChartReadout transfer}
    {admission :
      G8BoundaryToAcceptedTauSpectralAdmission domain readout}
    (support :
      G8BoundaryToAcceptedTauSpectralAdmissionSupport admission)
    (z : OrthodoxXiZeroCarrier)
    (hOffAxis :
      G8ActualXiZetaThinChartOffAxis
        (domain.thinSource readout) z) :
    G8AcceptedSpectralStageCertificate :=
  (support.certificateOf z hOffAxis).stageCert

/-- Admission support exposes finite self-adjointness for a point. -/
theorem G8BoundaryToAcceptedTauSpectralAdmissionSupport.selfAdjoint
    {transfer : G8dZeroDivisorTransferContext}
    {domain : G8AcceptedTauSpectralWitnessDomain}
    {readout : G8FinalRHTransferChartReadout transfer}
    {admission :
      G8BoundaryToAcceptedTauSpectralAdmission domain readout}
    (support :
      G8BoundaryToAcceptedTauSpectralAdmissionSupport admission)
    (z : OrthodoxXiZeroCarrier)
    (hOffAxis :
      G8ActualXiZetaThinChartOffAxis
        (domain.thinSource readout) z) :
    self_adjoint_check (support.stageCertificate z hOffAxis).stage = true :=
  (support.stageCertificate z hOffAxis).selfAdjoint

/-- Admission support exposes finite spectral resolution for a point. -/
theorem G8BoundaryToAcceptedTauSpectralAdmissionSupport.spectralResolution
    {transfer : G8dZeroDivisorTransferContext}
    {domain : G8AcceptedTauSpectralWitnessDomain}
    {readout : G8FinalRHTransferChartReadout transfer}
    {admission :
      G8BoundaryToAcceptedTauSpectralAdmission domain readout}
    (support :
      G8BoundaryToAcceptedTauSpectralAdmissionSupport admission)
    (z : OrthodoxXiZeroCarrier)
    (hOffAxis :
      G8ActualXiZetaThinChartOffAxis
        (domain.thinSource readout) z) :
    spectral_resolution_check
        ((support.stageCertificate z hOffAxis).stage + 1) = true :=
  (support.stageCertificate z hOffAxis).spectralResolution

/-- Admission support keeps the admitted witness aligned with the normalized
    centered address normal form. -/
theorem G8BoundaryToAcceptedTauSpectralAdmissionSupport.admitted_normalForm
    {transfer : G8dZeroDivisorTransferContext}
    {domain : G8AcceptedTauSpectralWitnessDomain}
    {readout : G8FinalRHTransferChartReadout transfer}
    {admission :
      G8BoundaryToAcceptedTauSpectralAdmission domain readout}
    (support :
      G8BoundaryToAcceptedTauSpectralAdmissionSupport admission)
    (z : OrthodoxXiZeroCarrier)
    (hOffAxis :
      G8ActualXiZetaThinChartOffAxis
        (domain.thinSource readout) z) :
    domain.tauNormalForm (admission.admit z hOffAxis) =
      (orthodoxXiCarrierCenteredBoundaryPointAddress z).normalize.nf := by
  rw [← support.certificate_witness z hOffAxis]
  exact
    (support.certificateOf z hOffAxis).witness_normalForm.trans
      (support.certificate_normalForm z hOffAxis)

-- ============================================================
-- CERTIFIED ACCEPTED SPINE
-- ============================================================

/-- Accepted almost-final spine with pointwise finite spectral-stage support.

This is the compact “reuse ledger” for the final spine: it keeps the proof
route committed to the accepted-domain architecture while recording exactly
which Book III finite spectral checks can be carried pointwise by admitted
witnesses. -/
structure G8CertifiedAcceptedTauSpectralAlmostFinalSpine extends
    G8AcceptedTauSpectralAlmostFinalSpine where
  admissionSupport :
    G8BoundaryToAcceptedTauSpectralAdmissionSupport toG8AcceptedTauSpectralAlmostFinalSpine.admission

/-- The certified accepted spine still yields the existing accepted
    almost-final spine. -/
def G8CertifiedAcceptedTauSpectralAlmostFinalSpine.toAcceptedSpine
    (spine : G8CertifiedAcceptedTauSpectralAlmostFinalSpine) :
    G8AcceptedTauSpectralAlmostFinalSpine :=
  spine.toG8AcceptedTauSpectralAlmostFinalSpine

/-- Certified accepted spine exposes pointwise finite spectral-stage support. -/
def G8CertifiedAcceptedTauSpectralAlmostFinalSpine.stageCertificate
    (spine : G8CertifiedAcceptedTauSpectralAlmostFinalSpine)
    (z : OrthodoxXiZeroCarrier)
    (hOffAxis :
      G8ActualXiZetaThinChartOffAxis spine.thinSource z) :
    G8AcceptedSpectralStageCertificate :=
  spine.admissionSupport.stageCertificate z hOffAxis

/-- Certified accepted spine exposes its local exclusion theorem through the
    existing accepted-domain route. -/
theorem G8CertifiedAcceptedTauSpectralAlmostFinalSpine.noOffCriticalXiZeros
    (spine : G8CertifiedAcceptedTauSpectralAlmostFinalSpine) :
    G8eNoOrthodoxOffCriticalZeros
      (g8ActualXiZeta_base spine.source) :=
  spine.toAcceptedSpine.noOffCriticalXiZeros

/-- Certified accepted spine exposes Mathlib's `RiemannHypothesis` target
    through the existing accepted-domain route. -/
theorem G8CertifiedAcceptedTauSpectralAlmostFinalSpine.mathlibRiemannHypothesis
    (spine : G8CertifiedAcceptedTauSpectralAlmostFinalSpine) :
    RiemannHypothesis :=
  spine.toAcceptedSpine.mathlibRiemannHypothesis

end Tau.BookIII.Bridge
