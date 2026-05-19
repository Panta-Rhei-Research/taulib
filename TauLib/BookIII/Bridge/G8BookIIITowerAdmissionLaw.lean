import TauLib.BookIII.Bridge.G8BookIIITowerAdmissionConflict

/-!
# TauLib.BookIII.Bridge.G8BookIIITowerAdmissionLaw

D5 accepted tower admission law.

The D4 layer showed that an actual off-axis `xi` shadow plus an accepted tower
admission aligned to its centered boundary address is contradictory.  This
module turns the same fact into the positive admission-law surface:

```text
accepted Book III tower address -> B/C balanced
actual off-axis xi address       -> B/C imbalanced
```

Thus the remaining global hinge is accepted-carrier coverage, not a total
constructor that admits off-axis shadows into the accepted tower carrier.  This
module does not prove O3, analytic-completion uniqueness, full divisor
transfer, or any new receiving-side theorem.
-/

set_option autoImplicit false

noncomputable section

namespace Tau.BookIII.Bridge

open Tau.BookIII.Spectral

-- ============================================================
-- POINTWISE ACCEPTED CENTERED-ADDRESS ADMISSION
-- ============================================================

/-- A centered actual `xi` carrier address is accepted by the Book III tower
    model when some accepted tower witness has exactly the same normal form as
    the normalized centered boundary address. -/
def G8BookIIITowerAdmitsCenteredAddress
    (model : G8BookIIITowerAcceptedSpectralWitnessModel)
    (z : OrthodoxXiZeroCarrier) : Prop :=
  ∃ w : model.spectralWitness,
    model.IsAccepted w ∧
      model.normalForm w =
        (orthodoxXiCarrierCenteredBoundaryPointAddress z).normalize.nf

/-- Accepted centered addresses are B/C-balanced because accepted Book III
    tower witnesses are balanced by their tower certificate. -/
theorem g8BookIIITowerAdmitsCenteredAddress_bcBalanced
    (model : G8BookIIITowerAcceptedSpectralWitnessModel)
    (z : OrthodoxXiZeroCarrier)
    (hAdmits : G8BookIIITowerAdmitsCenteredAddress model z) :
    BCBalanced
      (orthodoxXiCarrierCenteredBoundaryPointAddress z).normalize.nf := by
  rcases hAdmits with ⟨w, hAccepted, hAligned⟩
  have hBalanced : BCBalanced (model.normalForm w) :=
    model.acceptedBalanced w hAccepted
  simpa [hAligned] using hBalanced

/-- Accepted centered addresses exclude tau critical imbalance. -/
theorem g8BookIIITowerAdmitsCenteredAddress_noCriticalImbalance
    (model : G8BookIIITowerAcceptedSpectralWitnessModel)
    (z : OrthodoxXiZeroCarrier)
    (hAdmits : G8BookIIITowerAdmitsCenteredAddress model z) :
    ¬ TauCriticalImbalance
        (orthodoxXiCarrierCenteredBoundaryPointAddress z).normalize.nf :=
  bcBalanced_noTauCriticalImbalance
    (orthodoxXiCarrierCenteredBoundaryPointAddress z).normalize.nf
    (g8BookIIITowerAdmitsCenteredAddress_bcBalanced
      model z hAdmits)

/-- A centered address accepted by the Book III tower model cannot also be an
    actual thin off-axis chart shadow. -/
theorem g8BookIIITowerAdmitsCenteredAddress_refutesThinOffAxis
    (model : G8BookIIITowerAcceptedSpectralWitnessModel)
    (source : G8ActualXiZetaThinSourceContext)
    (z : OrthodoxXiZeroCarrier)
    (hAdmits : G8BookIIITowerAdmitsCenteredAddress model z)
    (hOffAxis : G8ActualXiZetaThinChartOffAxis source z) :
    False :=
  (g8BookIIITowerAdmitsCenteredAddress_noCriticalImbalance
    model z hAdmits)
    (g8ActualXiZetaThinOffAxis_centeredAddress_criticalImbalance
      source z hOffAxis)

/-- Accepted centered addresses reject actual thin off-axis classification. -/
theorem g8BookIIITowerAdmitsCenteredAddress_notThinOffAxis
    (model : G8BookIIITowerAcceptedSpectralWitnessModel)
    (source : G8ActualXiZetaThinSourceContext)
    (z : OrthodoxXiZeroCarrier)
    (hAdmits : G8BookIIITowerAdmitsCenteredAddress model z) :
    ¬ G8ActualXiZetaThinChartOffAxis source z := by
  intro hOffAxis
  exact
    g8BookIIITowerAdmitsCenteredAddress_refutesThinOffAxis
      model source z hAdmits hOffAxis

/-- Accepted centered addresses reject carrier-level off-criticality. -/
theorem g8BookIIITowerAdmitsCenteredAddress_notCarrierOffCritical
    (model : G8BookIIITowerAcceptedSpectralWitnessModel)
    (z : OrthodoxXiZeroCarrier)
    (hAdmits : G8BookIIITowerAdmitsCenteredAddress model z) :
    ¬ OrthodoxXiCarrierOffCritical z := by
  intro hOffCritical
  have hOffAxis :
      ShadowOffAxis (orthodoxXiCarrierCenteredShadow z) :=
    (orthodoxXiCarrierOffCritical_iff_shadowOffAxis z).mp
      hOffCritical
  have hImbalance :
      TauCriticalImbalance
        (orthodoxXiCarrierCenteredBoundaryPointAddress z).normalize.nf :=
    orthodoxXiCarrierCenteredBoundaryPointAddress_criticalImbalance
      z hOffAxis
  exact
    (g8BookIIITowerAdmitsCenteredAddress_noCriticalImbalance
      model z hAdmits) hImbalance

-- ============================================================
-- ACCEPTED ORTHODOX XI CARRIER
-- ============================================================

/-- Orthodox `xi` carrier restricted to addresses accepted by the Book III
    tower model. -/
def G8BookIIIAcceptedXiZeroCarrier
    (model : G8BookIIITowerAcceptedSpectralWitnessModel) : Type 2 :=
  { z : OrthodoxXiZeroCarrier //
    G8BookIIITowerAdmitsCenteredAddress model z }

/-- Accepted `xi` carrier elements cannot be carrier-off-critical. -/
theorem G8BookIIIAcceptedXiZeroCarrier.notCarrierOffCritical
    {model : G8BookIIITowerAcceptedSpectralWitnessModel}
    (z : G8BookIIIAcceptedXiZeroCarrier model) :
    ¬ OrthodoxXiCarrierOffCritical z.val :=
  g8BookIIITowerAdmitsCenteredAddress_notCarrierOffCritical
    model z.val z.property

/-- Accepted `xi` carrier elements cannot be off the centered chart axis. -/
theorem G8BookIIIAcceptedXiZeroCarrier.notShadowOffAxis
    {model : G8BookIIITowerAcceptedSpectralWitnessModel}
    (z : G8BookIIIAcceptedXiZeroCarrier model) :
    ¬ ShadowOffAxis (orthodoxXiCarrierCenteredShadow z.val) := by
  intro hOffAxis
  exact
    (G8BookIIIAcceptedXiZeroCarrier.notCarrierOffCritical z)
      ((orthodoxXiCarrierOffCritical_iff_shadowOffAxis z.val).mpr
        hOffAxis)

/-- Accepted `xi` carrier elements are not off-critical after projecting back
    to the orthodox zero record. -/
theorem G8BookIIIAcceptedXiZeroCarrier.notOffCritical
    {model : G8BookIIITowerAcceptedSpectralWitnessModel}
    (z : G8BookIIIAcceptedXiZeroCarrier model) :
    ¬ OrthodoxXiOffCritical z.val.toZero :=
  G8BookIIIAcceptedXiZeroCarrier.notCarrierOffCritical z

-- ============================================================
-- ACCEPTED-CARRIER COVERAGE TARGET AND CONDITIONAL HANDOFF
-- ============================================================

/-- Future load-bearing coverage theorem for the D5 admission-law route.

Every Mathlib nontrivial zeta zero must be represented by an orthodox `xi`
zero whose centered boundary address is accepted by the Book III tower
carrier.  This module records the target; it does not prove the coverage
theorem. -/
def G8BookIIIAcceptedXiCoversMathlibNontrivialZetaZeros
    (model : G8BookIIITowerAcceptedSpectralWitnessModel) : Prop :=
  ∀ (s : ℂ),
    riemannZeta s = 0 →
    (¬ ∃ n : ℕ, s = -2 * (n + 1)) →
    s ≠ 1 →
      ∃ z : G8BookIIIAcceptedXiZeroCarrier model,
        z.val.toZero.point = s

/-- Accepted-carrier coverage supplies covered nontrivial zeros together with
    their no-off-critical law. -/
theorem g8BookIIIAcceptedXiCoverage_noOffCritical
    {model : G8BookIIITowerAcceptedSpectralWitnessModel}
    (coverage :
      G8BookIIIAcceptedXiCoversMathlibNontrivialZetaZeros model)
    (s : ℂ)
    (hz : riemannZeta s = 0)
    (hNotTrivial : ¬ ∃ n : ℕ, s = -2 * (n + 1))
    (hNotPole : s ≠ 1) :
    ∃ z : G8BookIIIAcceptedXiZeroCarrier model,
      z.val.toZero.point = s ∧
        ¬ OrthodoxXiOffCritical z.val.toZero := by
  obtain ⟨z, hPoint⟩ := coverage s hz hNotTrivial hNotPole
  exact
    ⟨z, hPoint,
      G8BookIIIAcceptedXiZeroCarrier.notOffCritical z⟩

/-- Conditional final handoff for the D5 admission-law route.

The proof consumes only accepted-carrier coverage plus the accepted-address
restriction theorem above. -/
theorem mathlibRiemannHypothesis_from_acceptedXiCoverage
    {model : G8BookIIITowerAcceptedSpectralWitnessModel}
    (coverage :
      G8BookIIIAcceptedXiCoversMathlibNontrivialZetaZeros model) :
    RiemannHypothesis := by
  intro s hz hNotTrivial hNotPole
  obtain ⟨z, hPoint, hNoOffCritical⟩ :=
    g8BookIIIAcceptedXiCoverage_noOffCritical
      coverage s hz hNotTrivial hNotPole
  have hAxis : z.val.toZero.point.re = (1 / 2 : ℝ) := by
    by_contra hOffCritical
    exact hNoOffCritical hOffCritical
  simpa [hPoint] using hAxis

-- ============================================================
-- INTERFACE CHECKS
-- ============================================================

#check G8BookIIITowerAdmitsCenteredAddress
#check g8BookIIITowerAdmitsCenteredAddress_refutesThinOffAxis
#check G8BookIIIAcceptedXiZeroCarrier.notCarrierOffCritical
#check G8BookIIIAcceptedXiCoversMathlibNontrivialZetaZeros
#check mathlibRiemannHypothesis_from_acceptedXiCoverage

end Tau.BookIII.Bridge
