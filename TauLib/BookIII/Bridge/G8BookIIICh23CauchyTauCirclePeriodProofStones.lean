import TauLib.BookIII.Bridge.G8BookIIICh23CauchyTauCirclePeriodMilestone

/-!
# TauLib.BookIII.Bridge.G8BookIIICh23CauchyTauCirclePeriodProofStones

Theorem-backed proof stones for the A1.1 Cauchy tau-circle period corridor.

The floor-grid lift now gives a bounded Cauchy tau angle for every
`UnitAddCircle` point.  This module closes the one inverse law that follows
purely from the quotient-real readout: if we read the floor lift back through
`TauRealQ ≃ ℝ` and then into `UnitAddCircle`, we recover the original period.

The remaining period theorem is consequently isolated as the right-inverse
law saying that every Cauchy-parametrized canonical tau-circle point is
presented by the floor lift of its readout.  Bounded-angle Cauchy replacement
is kept exactly equivalent to parametrized Cauchy completeness; boundedness
alone is not treated as a Cauchy theorem.
-/

set_option autoImplicit false

namespace Tau.BookIII.Bridge

open Tau.Boundary

-- ============================================================
-- THEOREM-BACKED UNIT-PERIOD READOUT FOR CAUCHY TAU ANGLES
-- ============================================================

/-- Read the unit-period of a bounded Cauchy tau angle through the established
    `TauRealQ ≃ ℝ` bridge and then through the additive-circle quotient. -/
noncomputable def g8BookIIICh23CauchyBoundedAngleUnitAddCirclePeriod
    (a : BoundedTauAngle)
    (ha : BoundedTauAngle.IsCauchy a) : UnitAddCircle :=
  (tauRealQRingEquivReal
    (G8BookIIICh23CauchyBoundedAngle.toTauRealQ a ha) : ℝ)

/-- The theorem-backed floor-grid lift is a left inverse after reading its
    bounded Cauchy angle back to a unit additive-circle period. -/
theorem g8BookIIICh23RealIcoFloorLift_unitPeriod_left_inv
    (p : UnitAddCircle) :
    g8BookIIICh23CauchyBoundedAngleUnitAddCirclePeriod
        (g8BookIIICh23RealIcoFloorLiftSource
          |>.toBoundedAngleOfUnitAddCircle p)
        (g8BookIIICh23RealIcoFloorLiftSource
          |>.toBoundedAngleOfUnitAddCircle_cauchy p) =
      p := by
  dsimp [g8BookIIICh23CauchyBoundedAngleUnitAddCirclePeriod]
  have hreal :
      tauRealQRingEquivReal
          (G8BookIIICh23CauchyBoundedAngle.toTauRealQ
            (g8BookIIICh23RealIcoFloorLiftSource
              |>.toBoundedAngleOfUnitAddCircle p)
            (g8BookIIICh23RealIcoFloorLiftSource
              |>.toBoundedAngleOfUnitAddCircle_cauchy p)) =
        (g8BookIIICh23UnitAddCircleRealIcoAngle p).1 :=
    g8BookIIICh23RealIcoFloorLiftSource
      |>.toBoundedAngleOfUnitAddCircle_representsReal p
  rw [hreal]
  change
    (AddCircle.equivIco (1 : ℝ) (0 : ℝ)).symm
        (g8BookIIICh23UnitAddCircleRealIcoAngle p) =
      p
  exact g8BookIIICh23UnitAddCircleRealIcoAngle_symm_apply p

-- ============================================================
-- EXACT RIGHT-INVERSE SURFACE
-- ============================================================

/-- Right-inverse law for a chosen readout from the Cauchy-parametrized
    canonical tau-circle lobe to `UnitAddCircle`.

This is the remaining period law after the theorem-backed floor-left-inverse
above. -/
def G8BookIIICh23FloorLiftCanonicalRightInverseFor
    (fromCauchyParametrized :
      TauCircleCauchyParametrizedCanonicalPoint → UnitAddCircle) :
    Prop :=
  ∀ p : TauCircleCauchyParametrizedCanonicalPoint,
    TauCircleCauchyParametrizedCanonicalPoint.ofBoundedAngle
        (g8BookIIICh23RealIcoFloorLiftSource
          |>.toBoundedAngleOfUnitAddCircle
            (fromCauchyParametrized p))
        (g8BookIIICh23RealIcoFloorLiftSource
          |>.toBoundedAngleOfUnitAddCircle_cauchy
            (fromCauchyParametrized p)) =
      p

/-- Readout-form period source.

The load-bearing new field is `right_inv`.  The left inverse is now derived
from `agreesWithUnitPeriod` and the theorem-backed floor-left-inverse above. -/
structure G8BookIIICh23FloorLiftCauchyPeriodReadoutSource where
  fromCauchyParametrized :
    TauCircleCauchyParametrizedCanonicalPoint → UnitAddCircle
  agreesWithUnitPeriod :
    ∀ (a : BoundedTauAngle) (ha : BoundedTauAngle.IsCauchy a),
      fromCauchyParametrized
          (TauCircleCauchyParametrizedCanonicalPoint.ofBoundedAngle a ha) =
        g8BookIIICh23CauchyBoundedAngleUnitAddCirclePeriod a ha
  right_inv :
    G8BookIIICh23FloorLiftCanonicalRightInverseFor
      fromCauchyParametrized
  tauCisPeriodSoundness : Prop
  tauCisPeriodSoundnessEvidence : tauCisPeriodSoundness
  periodInjectivity : Prop
  periodInjectivityEvidence : periodInjectivity
  periodSurjectivity : Prop
  periodSurjectivityEvidence : periodSurjectivity
  lobeTopologyAgreement : Prop
  lobeTopologyAgreementEvidence : lobeTopologyAgreement
  lobeMetricAgreement : Prop
  lobeMetricAgreementEvidence : lobeMetricAgreement
  lobeCompactnessAgreement : Prop
  lobeCompactnessAgreementEvidence : lobeCompactnessAgreement
  anglePeriodBridge : Prop
  anglePeriodBridgeEvidence : anglePeriodBridge
  cauchyParametrizedComplete : Prop
  cauchyParametrizedCompleteEvidence :
    cauchyParametrizedComplete
  status : SpineStatus := .conditional_interface

namespace G8BookIIICh23FloorLiftCauchyPeriodReadoutSource

/-- The readout source supplies the clean floor-lift period equivalence. -/
noncomputable def toEquivalenceSource
    (source :
      G8BookIIICh23FloorLiftCauchyPeriodReadoutSource) :
    G8BookIIICh23FloorLiftCauchyPeriodEquivalenceSource where
  periodEquiv :=
    { toFun := fun p =>
        TauCircleCauchyParametrizedCanonicalPoint.ofBoundedAngle
          (g8BookIIICh23RealIcoFloorLiftSource
            |>.toBoundedAngleOfUnitAddCircle p)
          (g8BookIIICh23RealIcoFloorLiftSource
            |>.toBoundedAngleOfUnitAddCircle_cauchy p)
      invFun := source.fromCauchyParametrized
      left_inv := by
        intro p
        rw [source.agreesWithUnitPeriod]
        exact g8BookIIICh23RealIcoFloorLift_unitPeriod_left_inv p
      right_inv := source.right_inv }
  forward_eq := by
    intro p
    rfl
  tauCisPeriodSoundness := source.tauCisPeriodSoundness
  tauCisPeriodSoundnessEvidence :=
    source.tauCisPeriodSoundnessEvidence
  periodInjectivity := source.periodInjectivity
  periodInjectivityEvidence := source.periodInjectivityEvidence
  periodSurjectivity := source.periodSurjectivity
  periodSurjectivityEvidence := source.periodSurjectivityEvidence
  lobeTopologyAgreement := source.lobeTopologyAgreement
  lobeTopologyAgreementEvidence := source.lobeTopologyAgreementEvidence
  lobeMetricAgreement := source.lobeMetricAgreement
  lobeMetricAgreementEvidence := source.lobeMetricAgreementEvidence
  lobeCompactnessAgreement := source.lobeCompactnessAgreement
  lobeCompactnessAgreementEvidence :=
    source.lobeCompactnessAgreementEvidence
  anglePeriodBridge := source.anglePeriodBridge
  anglePeriodBridgeEvidence := source.anglePeriodBridgeEvidence
  cauchyParametrizedComplete := source.cauchyParametrizedComplete
  cauchyParametrizedCompleteEvidence :=
    source.cauchyParametrizedCompleteEvidence
  status := source.status

/-- The readout source closes the existing floor-lift soundness target. -/
theorem toSoundnessTarget
    (source :
      G8BookIIICh23FloorLiftCauchyPeriodReadoutSource) :
    G8BookIIICh23FloorLiftCauchyTauCirclePeriodSoundnessTarget :=
  source.toEquivalenceSource.toSoundnessTarget

end G8BookIIICh23FloorLiftCauchyPeriodReadoutSource

/-- A readout source plus bounded-angle Cauchy replacement supplies the
    combined floor-lift Cauchy period milestone. -/
theorem g8BookIIICh23FloorLiftCauchyPeriodMilestone_of_readout
    (readout :
      G8BookIIICh23FloorLiftCauchyPeriodReadoutSource)
    (replacement : G8BookIIICh23BoundedAngleCauchyReplacement) :
    G8BookIIICh23FloorLiftCauchyPeriodMilestone :=
  g8BookIIICh23FloorLiftCauchyPeriodMilestone_of_sources
    readout.toEquivalenceSource
    replacement

-- ============================================================
-- PARAMETRIZED COMPLETENESS ALIAS IN THE PROOF-STONE DIRECTION
-- ============================================================

/-- Bounded-angle replacement is exactly parametrized Cauchy completeness,
    stated in the replacement-first orientation used by this proof-stone
    corridor. -/
theorem g8BookIIICh23BoundedAngleCauchyReplacement_iff_parametrizedComplete :
    G8BookIIICh23BoundedAngleCauchyReplacement ↔
      G8BookIIICh23TauCircleParametrizedCauchyComplete :=
  g8BookIIICh23TauCircleParametrizedCauchyComplete_iff_replacement.symm

-- ============================================================
-- GUARDRAILS AND FALSIFIERS
-- ============================================================

/-- Falsifier surface: a readout that disagrees with the quotient-real
    unit-period readout cannot instantiate the readout source. -/
structure G8BookIIICh23CauchyPeriodReadoutMismatch
    (source :
      G8BookIIICh23FloorLiftCauchyPeriodReadoutSource) where
  angle : BoundedTauAngle
  cauchy : BoundedTauAngle.IsCauchy angle
  mismatch :
    source.fromCauchyParametrized
        (TauCircleCauchyParametrizedCanonicalPoint.ofBoundedAngle
          angle cauchy) ≠
      g8BookIIICh23CauchyBoundedAngleUnitAddCirclePeriod
        angle cauchy

/-- Readout mismatch refutes the source's exact agreement field. -/
theorem
    G8BookIIICh23CauchyPeriodReadoutMismatch.refutesSource
    {source :
      G8BookIIICh23FloorLiftCauchyPeriodReadoutSource}
    (gap :
      G8BookIIICh23CauchyPeriodReadoutMismatch source) :
    False :=
  gap.mismatch
    (source.agreesWithUnitPeriod gap.angle gap.cauchy)

/-- Falsifier surface: a failed right inverse is precisely the remaining
    floor-lift period gap. -/
structure G8BookIIICh23FloorLiftRightInverseGap
    (source :
      G8BookIIICh23FloorLiftCauchyPeriodReadoutSource) where
  point : TauCircleCauchyParametrizedCanonicalPoint
  mismatch :
    TauCircleCauchyParametrizedCanonicalPoint.ofBoundedAngle
        (g8BookIIICh23RealIcoFloorLiftSource
          |>.toBoundedAngleOfUnitAddCircle
            (source.fromCauchyParametrized point))
        (g8BookIIICh23RealIcoFloorLiftSource
          |>.toBoundedAngleOfUnitAddCircle_cauchy
            (source.fromCauchyParametrized point)) ≠
      point

/-- A right-inverse mismatch refutes the corresponding readout source. -/
theorem G8BookIIICh23FloorLiftRightInverseGap.refutesSource
    {source :
      G8BookIIICh23FloorLiftCauchyPeriodReadoutSource}
    (gap : G8BookIIICh23FloorLiftRightInverseGap source) :
    False :=
  gap.mismatch (source.right_inv gap.point)

/-- Guardrail target: boundedness by itself is not used as Cauchy evidence.
    Any proof of this proposition must provide the replacement theorem
    explicitly. -/
def G8BookIIICh23BoundednessAloneDoesNotSupplyReplacement : Prop :=
  G8BookIIICh23BoundedAngleCauchyReplacement →
    G8BookIIICh23TauCircleParametrizedCauchyComplete

/-- The guardrail is only the theorem-backed replacement adapter, not a claim
    that arbitrary bounded tau angles are already Cauchy. -/
theorem g8BookIIICh23BoundednessAlone_guardrail :
    G8BookIIICh23BoundednessAloneDoesNotSupplyReplacement :=
  g8BookIIICh23TauCircleParametrizedCauchyComplete_of_replacement

end Tau.BookIII.Bridge
