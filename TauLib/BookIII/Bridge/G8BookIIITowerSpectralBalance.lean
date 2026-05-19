import TauLib.BookIII.Bridge.G8BookIIIAcceptedBalanceDischarge

/-!
# TauLib.BookIII.Bridge.G8BookIIITowerSpectralBalance

D3 tower spectral-balance discharge for the accepted Book III witness carrier.

The previous layer made `acceptedBalanced` follow from a Book III
balance-hyperplane certificate.  This module tightens the intended source of
that certificate: an accepted tower spectral witness carries both finite
Book III stage support and a balance-hyperplane proof for the same normal form.

Finite checks are recorded as tower support; they are not used to infer
B/C balance by themselves.  The load-bearing balance claim remains the explicit
hyperplane proof on the tower certificate.
-/

set_option autoImplicit false

noncomputable section

namespace Tau.BookIII.Bridge

open Tau.BookIII.Spectral
open Tau.BookIII.Doors

-- ============================================================
-- TOWER SUPPORT FOR FINITE BOOK III STAGES
-- ============================================================

/-- Finite tower support attached to a Book III spectral stage.

These fields record existing Book III tower and protocol checks.  They are
evidence that the stage is being treated through the intended primorial
spectral machinery; they do not by themselves imply B/C balance. -/
structure G8BookIIITowerStageSupport (stage : Nat) where
  primorialLadder :
    primorial_ladder_check stage = true
  primorialCofinal :
    primorial_cofinal_check stage = true
  eigenvalueNesting :
    eigenvalue_nesting_check stage = true
  tauEffectiveRH :
    tau_effective_rh_check stage = true
  rhProtocol :
    rh_protocol_check stage = true

/-- Tower support exposes primorial ladder coherence. -/
theorem G8BookIIITowerStageSupport.primorial_ladder
    {stage : Nat}
    (support : G8BookIIITowerStageSupport stage) :
    primorial_ladder_check stage = true :=
  support.primorialLadder

/-- Tower support exposes finite eigenvalue nesting. -/
theorem G8BookIIITowerStageSupport.eigenvalue_nesting
    {stage : Nat}
    (support : G8BookIIITowerStageSupport stage) :
    eigenvalue_nesting_check stage = true :=
  support.eigenvalueNesting

/-- Tower support exposes the tau-effective RH check at the stage. -/
theorem G8BookIIITowerStageSupport.tau_effective_rh
    {stage : Nat}
    (support : G8BookIIITowerStageSupport stage) :
    tau_effective_rh_check stage = true :=
  support.tauEffectiveRH

/-- Tower support exposes the finite RH protocol at the stage. -/
theorem G8BookIIITowerStageSupport.rh_protocol
    {stage : Nat}
    (support : G8BookIIITowerStageSupport stage) :
    rh_protocol_check stage = true :=
  support.rhProtocol

-- ============================================================
-- TOWER SPECTRAL-BALANCE CERTIFICATES
-- ============================================================

/-- Tower spectral-balance certificate for an accepted Book III witness.

The finite stage checks and tower support identify the Book III machinery.
The final field is the decisive balance-hyperplane proof for the certificate
normal form. -/
structure G8BookIIITowerSpectralBalanceCertificate where
  stageCert : G8AcceptedSpectralStageCertificate
  towerSupport : G8BookIIITowerStageSupport stageCert.stage
  balanceHyperplane :
    BCBalanced stageCert.nf

/-- Tower balance certificates expose the underlying balance-hyperplane
    certificate consumed by the previous D3 layer. -/
def G8BookIIITowerSpectralBalanceCertificate.toBalanceHyperplaneCertificate
    (cert : G8BookIIITowerSpectralBalanceCertificate) :
    G8BookIIIBalanceHyperplaneCertificate where
  stageCert := cert.stageCert
  balanceHyperplane := cert.balanceHyperplane

/-- Tower balance certificates expose B/C balance. -/
theorem G8BookIIITowerSpectralBalanceCertificate.bcBalanced
    (cert : G8BookIIITowerSpectralBalanceCertificate) :
    BCBalanced cert.stageCert.nf :=
  cert.balanceHyperplane

/-- Tower balance certificates exclude tau critical imbalance. -/
theorem G8BookIIITowerSpectralBalanceCertificate.noCriticalImbalance
    (cert : G8BookIIITowerSpectralBalanceCertificate) :
    ¬ TauCriticalImbalance cert.stageCert.nf :=
  cert.toBalanceHyperplaneCertificate.noCriticalImbalance

/-- Tower balance certificates expose finite self-adjointness. -/
theorem G8BookIIITowerSpectralBalanceCertificate.selfAdjoint
    (cert : G8BookIIITowerSpectralBalanceCertificate) :
    self_adjoint_check cert.stageCert.stage = true :=
  cert.stageCert.selfAdjoint

/-- Tower balance certificates expose finite K5 diagonal discipline. -/
theorem G8BookIIITowerSpectralBalanceCertificate.k5Diagonal
    (cert : G8BookIIITowerSpectralBalanceCertificate) :
    k5_diagonal_check cert.stageCert.stage = true :=
  cert.stageCert.k5Diagonal

/-- Tower balance certificates expose tower eigenvalue nesting. -/
theorem G8BookIIITowerSpectralBalanceCertificate.eigenvalueNesting
    (cert : G8BookIIITowerSpectralBalanceCertificate) :
    eigenvalue_nesting_check cert.stageCert.stage = true :=
  cert.towerSupport.eigenvalue_nesting

/-- Tower balance certificates expose the tau-effective RH stage check. -/
theorem G8BookIIITowerSpectralBalanceCertificate.tauEffectiveRH
    (cert : G8BookIIITowerSpectralBalanceCertificate) :
    tau_effective_rh_check cert.stageCert.stage = true :=
  cert.towerSupport.tau_effective_rh

-- ============================================================
-- ACCEPTED TOWER WITNESS MODEL
-- ============================================================

/-- Accepted Book III tower spectral-witness model.

Acceptedness now means more than having finite check-level support: every
accepted witness carries a tower spectral-balance certificate whose normal
form is the witness normal form. -/
structure G8BookIIITowerAcceptedSpectralWitnessModel where
  spectralWitness : Type 2
  normalForm : spectralWitness → BoundaryNF
  IsAccepted : spectralWitness → Prop
  towerCertificate :
    ∀ w : spectralWitness,
      IsAccepted w →
        G8BookIIITowerSpectralBalanceCertificate
  towerCertificate_normalForm :
    ∀ (w : spectralWitness) (hAccepted : IsAccepted w),
      (towerCertificate w hAccepted).stageCert.nf = normalForm w
  status : G8OffCriticalExclusionStatus := .openObligation

/-- Accepted tower witnesses are B/C-balanced by their tower certificate. -/
theorem G8BookIIITowerAcceptedSpectralWitnessModel.acceptedBalanced
    (model : G8BookIIITowerAcceptedSpectralWitnessModel)
    (w : model.spectralWitness)
    (hAccepted : model.IsAccepted w) :
    BCBalanced (model.normalForm w) := by
  have hBalanced :
      BCBalanced (model.towerCertificate w hAccepted).stageCert.nf :=
    (model.towerCertificate w hAccepted).bcBalanced
  simpa [model.towerCertificate_normalForm w hAccepted] using hBalanced

/-- Accepted tower witnesses exclude tau critical imbalance. -/
theorem G8BookIIITowerAcceptedSpectralWitnessModel.acceptedPurity
    (model : G8BookIIITowerAcceptedSpectralWitnessModel)
    (w : model.spectralWitness)
    (hAccepted : model.IsAccepted w) :
    ¬ TauCriticalImbalance (model.normalForm w) :=
  bcBalanced_noTauCriticalImbalance
    (model.normalForm w)
    (model.acceptedBalanced w hAccepted)

/-- Convert the tower witness model into the accepted-balance model. -/
def G8BookIIITowerAcceptedSpectralWitnessModel.toAcceptedBalanceModel
    (model : G8BookIIITowerAcceptedSpectralWitnessModel) :
    G8BookIIIAcceptedBalanceModel where
  spectralWitness := model.spectralWitness
  normalForm := model.normalForm
  IsAccepted := model.IsAccepted
  balanceCertificate := by
    intro w hAccepted
    exact
      (model.towerCertificate w hAccepted).toBalanceHyperplaneCertificate
  balanceCertificate_normalForm := model.towerCertificate_normalForm
  status := model.status

/-- Convert the tower witness model into the raw spectral-witness model. -/
def G8BookIIITowerAcceptedSpectralWitnessModel.toRawTauSpectralWitnessModel
    (model : G8BookIIITowerAcceptedSpectralWitnessModel) :
    G8RawTauSpectralWitnessModel :=
  model.toAcceptedBalanceModel.toRawTauSpectralWitnessModel

/-- Accepted spectral domain induced by the tower witness model. -/
def G8BookIIITowerAcceptedSpectralWitnessModel.toAcceptedDomain
    (model : G8BookIIITowerAcceptedSpectralWitnessModel) :
    G8AcceptedTauSpectralWitnessDomain :=
  model.toRawTauSpectralWitnessModel.toAcceptedDomain

-- ============================================================
-- ADMISSION INTO THE ACCEPTED TOWER CARRIER
-- ============================================================

/-- Explicit admission map from actual off-axis centered `xi` shadows into
    the accepted Book III tower witness carrier.

This is the remaining load-bearing admission interface: it selects a tower
spectral witness, proves acceptedness, and aligns the witness normal form with
the normalized centered boundary address. -/
structure G8BoundaryToBookIIITowerSpectralAdmission
    (model : G8BookIIITowerAcceptedSpectralWitnessModel)
    {transfer : G8dZeroDivisorTransferContext}
    (readout : G8FinalRHTransferChartReadout transfer) where
  admitRaw :
    ∀ z : OrthodoxXiZeroCarrier,
      G8ActualXiZetaThinChartOffAxis
        (model.toAcceptedDomain.thinSource readout) z →
        model.spectralWitness
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
      model.normalForm (admitRaw z hOffAxis) =
        (orthodoxXiCarrierCenteredBoundaryPointAddress z).normalize.nf

/-- Convert tower admission into the raw admission interface used by the
    accepted-domain corridor. -/
def G8BoundaryToBookIIITowerSpectralAdmission.toRawAdmission
    {model : G8BookIIITowerAcceptedSpectralWitnessModel}
    {transfer : G8dZeroDivisorTransferContext}
    {readout : G8FinalRHTransferChartReadout transfer}
    (admission :
      G8BoundaryToBookIIITowerSpectralAdmission model readout) :
    G8RawBoundaryToAcceptedTauSpectralAdmission
      model.toRawTauSpectralWitnessModel readout where
  admitRaw := admission.admitRaw
  admitAccepted := admission.admitAccepted
  admitNormalForm := admission.admitNormalForm

/-- Convert tower admission into the accepted-domain admission interface. -/
def G8BoundaryToBookIIITowerSpectralAdmission.toAcceptedAdmission
    {model : G8BookIIITowerAcceptedSpectralWitnessModel}
    {transfer : G8dZeroDivisorTransferContext}
    {readout : G8FinalRHTransferChartReadout transfer}
    (admission :
      G8BoundaryToBookIIITowerSpectralAdmission model readout) :
    G8BoundaryToAcceptedTauSpectralAdmission
      model.toAcceptedDomain readout :=
  admission.toRawAdmission.toAdmission

/-- Tower admission as an accepted-balance admission spine. -/
def G8BoundaryToBookIIITowerSpectralAdmission.toAcceptedBalanceSpine
    {model : G8BookIIITowerAcceptedSpectralWitnessModel}
    {transfer : G8dZeroDivisorTransferContext}
    {readout : G8FinalRHTransferChartReadout transfer}
    (admission :
      G8BoundaryToBookIIITowerSpectralAdmission model readout) :
    G8BookIIIAcceptedBalanceAdmissionSpine where
  transfer := transfer
  readout := readout
  model := model.toAcceptedBalanceModel
  rawAdmission := admission.toRawAdmission

/-- Tower admission excludes thin off-axis chart shadows through the accepted
    Book III balance corridor. -/
theorem G8BoundaryToBookIIITowerSpectralAdmission.noThinChartOffAxis
    {model : G8BookIIITowerAcceptedSpectralWitnessModel}
    {transfer : G8dZeroDivisorTransferContext}
    {readout : G8FinalRHTransferChartReadout transfer}
    (admission :
      G8BoundaryToBookIIITowerSpectralAdmission model readout) :
    ∀ z : OrthodoxXiZeroCarrier,
      ¬ G8ActualXiZetaThinChartOffAxis
          (model.toAcceptedDomain.thinSource readout) z :=
  admission.toAcceptedAdmission.noThinChartOffAxis

-- ============================================================
-- STAGE-3 CALIBRATION AND GUARDRAILS
-- ============================================================

/-- Stage-3 tower support for calibration examples. -/
def g8BookIIITowerStageSupport_3 :
    G8BookIIITowerStageSupport 3 where
  primorialLadder := by native_decide
  primorialCofinal := by native_decide
  eigenvalueNesting := by native_decide
  tauEffectiveRH := by native_decide
  rhProtocol := by native_decide

/-- Finite stage certificate for the theorem-backed on-axis sample normal
    form. -/
def g8AcceptedStageCertificate_onAxisStage3 :
    G8AcceptedSpectralStageCertificate where
  stage := 3
  mode := 1
  nf := g8TauSampleOnAxisBoundaryNF
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

/-- The on-axis stage-3 certificate carries the on-axis normal form. -/
theorem g8AcceptedStageCertificate_onAxisStage3_nf :
    g8AcceptedStageCertificate_onAxisStage3.nf =
      g8TauSampleOnAxisBoundaryNF :=
  rfl

/-- The on-axis stage-3 certificate is a tower spectral-balance certificate. -/
def g8BookIIITowerBalanceCertificate_onAxisStage3 :
    G8BookIIITowerSpectralBalanceCertificate where
  stageCert := g8AcceptedStageCertificate_onAxisStage3
  towerSupport := g8BookIIITowerStageSupport_3
  balanceHyperplane := g8TauSampleOnAxisBoundaryNF_bcBalanced

/-- The first off-axis finite certificate is not on the B/C balance
    hyperplane. -/
theorem g8AcceptedStageCertificate_offAxisAddressA_notBalanced :
    ¬ G8BookIIIBalanceHyperplaneInvariant
        g8AcceptedStageCertificate_offAxisAddressA := by
  unfold G8BookIIIBalanceHyperplaneInvariant
  rw [g8AcceptedStageCertificate_offAxisAddressA_nf]
  exact g8PointSensitiveOffAxisAddressA_bcImbalance

/-- The second off-axis finite certificate is not on the B/C balance
    hyperplane. -/
theorem g8AcceptedStageCertificate_offAxisAddressB_notBalanced :
    ¬ G8BookIIIBalanceHyperplaneInvariant
        g8AcceptedStageCertificate_offAxisAddressB := by
  unfold G8BookIIIBalanceHyperplaneInvariant
  rw [g8AcceptedStageCertificate_offAxisAddressB_nf]
  exact g8PointSensitiveOffAxisAddressB_bcImbalance

/-- No tower spectral-balance certificate can have the first off-axis sample
    certificate as its underlying stage certificate. -/
theorem g8OffAxisAddressA_notTowerBalanced
    (cert : G8BookIIITowerSpectralBalanceCertificate) :
    cert.stageCert ≠ g8AcceptedStageCertificate_offAxisAddressA := by
  intro h
  have hBalanced : BCBalanced g8AcceptedStageCertificate_offAxisAddressA.nf := by
    rw [← h]
    exact cert.bcBalanced
  exact g8AcceptedStageCertificate_offAxisAddressA_notBalanced hBalanced

/-- No tower spectral-balance certificate can have the second off-axis sample
    certificate as its underlying stage certificate. -/
theorem g8OffAxisAddressB_notTowerBalanced
    (cert : G8BookIIITowerSpectralBalanceCertificate) :
    cert.stageCert ≠ g8AcceptedStageCertificate_offAxisAddressB := by
  intro h
  have hBalanced : BCBalanced g8AcceptedStageCertificate_offAxisAddressB.nf := by
    rw [← h]
    exact cert.bcBalanced
  exact g8AcceptedStageCertificate_offAxisAddressB_notBalanced hBalanced

-- ============================================================
-- INTERFACE CHECKS
-- ============================================================

#check G8BookIIITowerSpectralBalanceCertificate.toBalanceHyperplaneCertificate
#check G8BookIIITowerAcceptedSpectralWitnessModel.toAcceptedBalanceModel
#check G8BoundaryToBookIIITowerSpectralAdmission.toRawAdmission
#check G8BoundaryToBookIIITowerSpectralAdmission.noThinChartOffAxis

end Tau.BookIII.Bridge
