import TauLib.BookIII.Bridge.G8BookIIICh23RealIcoFloorBoundedTauRepresentative

/-!
# TauLib.BookIII.Bridge.G8BookIIICh23CauchyTauCirclePeriodMilestone

Milestone surface for the A1.1 Cauchy tau-circle period corridor.

The floor-grid construction has closed the controlled lift from real half-open
periods to bounded Cauchy tau angles.  The next two live facts are the exact
period inverse law for that lift and the fact that every parametrized
canonical tau-circle point admits a Cauchy bounded-angle representative.

This module does not pretend those inverse laws are already proved.  It pins
the concrete floor lift, proves theorem-backed adapters from clean equivalence
and replacement sources, and shows that the existing
`G8BookIIICh23TauCircleParametrizedCauchyComplete` target is equivalent to a
bounded-angle Cauchy replacement theorem.
-/

set_option autoImplicit false

namespace Tau.BookIII.Bridge

-- ============================================================
-- THE CONCRETE FLOOR-GRID LIFT
-- ============================================================

/-- The concrete real-Ico to bounded-Cauchy-tau-angle lift supplied by the
    theorem-backed floor-grid representative construction. -/
noncomputable def g8BookIIICh23RealIcoFloorLiftSource :
    G8BookIIICh23RealIcoCauchyBoundedTauAngleLiftSource :=
  g8BookIIICh23RealIcoBoundedCauchyTauRepresentativeSource
    |>.toRealIcoCauchyBoundedTauAngleLiftSource

/-- The closed lift target, restated with the concrete floor-grid lift as the
    selected source. -/
theorem g8BookIIICh23RealIcoFloorLiftTarget_closed :
    G8BookIIICh23RealIcoCauchyBoundedTauAngleLiftTarget :=
  ⟨g8BookIIICh23RealIcoFloorLiftSource⟩

/-- The period-soundness target specialized to the theorem-backed floor-grid
    lift. -/
def G8BookIIICh23FloorLiftCauchyTauCirclePeriodSoundnessTarget :
    Prop :=
  G8BookIIICh23CauchyTauCirclePeriodSoundnessTarget
    g8BookIIICh23RealIcoFloorLiftSource

-- ============================================================
-- PERIOD SOUNDNESS AS AN EXPLICIT EQUIVALENCE SOURCE
-- ============================================================

/-- Clean equivalence form of period soundness for the floor-grid lift.

This is intentionally just the load-bearing bijective period law plus the
same lobe-agreement evidence fields expected by the downstream source. -/
structure G8BookIIICh23FloorLiftCauchyPeriodEquivalenceSource where
  periodEquiv :
    UnitAddCircle ≃ TauCircleCauchyParametrizedCanonicalPoint
  forward_eq :
    ∀ p : UnitAddCircle,
      periodEquiv p =
        TauCircleCauchyParametrizedCanonicalPoint.ofBoundedAngle
          (g8BookIIICh23RealIcoFloorLiftSource
            |>.toBoundedAngleOfUnitAddCircle p)
          (g8BookIIICh23RealIcoFloorLiftSource
            |>.toBoundedAngleOfUnitAddCircle_cauchy p)
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

namespace G8BookIIICh23FloorLiftCauchyPeriodEquivalenceSource

/-- A floor-lift period equivalence supplies the existing soundness source. -/
noncomputable def toSoundnessSource
    (source :
      G8BookIIICh23FloorLiftCauchyPeriodEquivalenceSource) :
    G8BookIIICh23CauchyTauCirclePeriodSoundnessSource
      g8BookIIICh23RealIcoFloorLiftSource where
  fromCauchyParametrized := source.periodEquiv.symm
  left_inv := by
    intro p
    rw [← source.forward_eq p]
    exact source.periodEquiv.left_inv p
  right_inv := by
    intro p
    rw [← source.forward_eq (source.periodEquiv.symm p)]
    exact source.periodEquiv.right_inv p
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

/-- The clean equivalence source closes the floor-lift soundness target. -/
theorem toSoundnessTarget
    (source :
      G8BookIIICh23FloorLiftCauchyPeriodEquivalenceSource) :
    G8BookIIICh23FloorLiftCauchyTauCirclePeriodSoundnessTarget :=
  ⟨source.toSoundnessSource⟩

end G8BookIIICh23FloorLiftCauchyPeriodEquivalenceSource

/-- The existing soundness source is equivalent to the clean equivalence
    presentation. -/
noncomputable def
    g8BookIIICh23FloorLiftCauchyPeriodEquivalenceSource_ofSoundness
    (sound :
      G8BookIIICh23CauchyTauCirclePeriodSoundnessSource
        g8BookIIICh23RealIcoFloorLiftSource) :
    G8BookIIICh23FloorLiftCauchyPeriodEquivalenceSource where
  periodEquiv := sound.toCauchyAnglePeriodSource.toCauchyParametrizedEquiv
  forward_eq := by
    intro p
    rfl
  tauCisPeriodSoundness := sound.tauCisPeriodSoundness
  tauCisPeriodSoundnessEvidence := sound.tauCisPeriodSoundnessEvidence
  periodInjectivity := sound.periodInjectivity
  periodInjectivityEvidence := sound.periodInjectivityEvidence
  periodSurjectivity := sound.periodSurjectivity
  periodSurjectivityEvidence := sound.periodSurjectivityEvidence
  lobeTopologyAgreement := sound.lobeTopologyAgreement
  lobeTopologyAgreementEvidence := sound.lobeTopologyAgreementEvidence
  lobeMetricAgreement := sound.lobeMetricAgreement
  lobeMetricAgreementEvidence := sound.lobeMetricAgreementEvidence
  lobeCompactnessAgreement := sound.lobeCompactnessAgreement
  lobeCompactnessAgreementEvidence :=
    sound.lobeCompactnessAgreementEvidence
  anglePeriodBridge := sound.anglePeriodBridge
  anglePeriodBridgeEvidence := sound.anglePeriodBridgeEvidence
  cauchyParametrizedComplete := sound.cauchyParametrizedComplete
  cauchyParametrizedCompleteEvidence :=
    sound.cauchyParametrizedCompleteEvidence
  status := sound.status

-- ============================================================
-- PARAMETRIZED CAUCHY COMPLETENESS AS REPLACEMENT
-- ============================================================

/-- Bounded-angle Cauchy replacement theorem.

Every bounded tau angle has a Cauchy bounded tau angle representing the same
canonical tau-circle point.  This is the exact mathematical content hidden
inside `G8BookIIICh23TauCircleParametrizedCauchyComplete`. -/
def G8BookIIICh23BoundedAngleCauchyReplacement : Prop :=
  ∀ a : BoundedTauAngle,
    ∃ b : BoundedTauAngle,
      BoundedTauAngle.IsCauchy b ∧
        TauCircleCanonicalPoint.ofBoundedAngle b =
          TauCircleCanonicalPoint.ofBoundedAngle a

/-- Cauchy replacement closes parametrized Cauchy completeness. -/
theorem
    g8BookIIICh23TauCircleParametrizedCauchyComplete_of_replacement
    (replacement : G8BookIIICh23BoundedAngleCauchyReplacement) :
    G8BookIIICh23TauCircleParametrizedCauchyComplete := by
  intro p
  rcases p.2 with ⟨a, ha⟩
  rcases replacement a with ⟨b, hbCauchy, hbEq⟩
  exact ⟨b, hbCauchy, hbEq.trans ha⟩

/-- Parametrized Cauchy completeness gives the bounded-angle replacement
    theorem by applying completeness to the point represented by a given
    bounded angle. -/
theorem
    g8BookIIICh23BoundedAngleCauchyReplacement_of_parametrizedComplete
    (complete : G8BookIIICh23TauCircleParametrizedCauchyComplete) :
    G8BookIIICh23BoundedAngleCauchyReplacement := by
  intro a
  exact complete (TauCircleParametrizedCanonicalPoint.ofBoundedAngle a)

/-- The advertised parametrized Cauchy completeness target is exactly the
    bounded-angle Cauchy replacement theorem. -/
theorem g8BookIIICh23TauCircleParametrizedCauchyComplete_iff_replacement :
    G8BookIIICh23TauCircleParametrizedCauchyComplete ↔
      G8BookIIICh23BoundedAngleCauchyReplacement :=
  ⟨g8BookIIICh23BoundedAngleCauchyReplacement_of_parametrizedComplete,
    g8BookIIICh23TauCircleParametrizedCauchyComplete_of_replacement⟩

-- ============================================================
-- COMBINED MILESTONE AND DOWNSTREAM ADAPTERS
-- ============================================================

/-- The exact combined milestone needed after the floor lift:
    period soundness for that lift and Cauchy completeness of the
    parametrized canonical lobe. -/
def G8BookIIICh23FloorLiftCauchyPeriodMilestone : Prop :=
  G8BookIIICh23FloorLiftCauchyTauCirclePeriodSoundnessTarget ∧
    G8BookIIICh23TauCircleParametrizedCauchyComplete

/-- A period equivalence plus bounded-angle Cauchy replacement supplies the
    combined milestone. -/
theorem g8BookIIICh23FloorLiftCauchyPeriodMilestone_of_sources
    (period :
      G8BookIIICh23FloorLiftCauchyPeriodEquivalenceSource)
    (replacement : G8BookIIICh23BoundedAngleCauchyReplacement) :
    G8BookIIICh23FloorLiftCauchyPeriodMilestone :=
  ⟨period.toSoundnessTarget,
    g8BookIIICh23TauCircleParametrizedCauchyComplete_of_replacement
      replacement⟩

/-- The combined milestone supplies the Cauchy angle-period source target. -/
theorem
    g8BookIIICh23FloorLiftCauchyPeriodMilestone_toCauchyTarget
    (milestone : G8BookIIICh23FloorLiftCauchyPeriodMilestone) :
    G8BookIIICh23UnitAddCircleCauchyAnglePeriodSourceTarget := by
  rcases milestone.1 with ⟨sound⟩
  exact ⟨sound.toCauchyAnglePeriodSource⟩

/-- The combined milestone supplies the parametrized canonical angle-period
    source target. -/
theorem
    g8BookIIICh23FloorLiftCauchyPeriodMilestone_toParametrizedTarget
    (milestone : G8BookIIICh23FloorLiftCauchyPeriodMilestone) :
    G8BookIIICh23UnitAddCircleParametrizedCanonicalAnglePeriodSourceTarget :=
  g8BookIIICh23UnitAddCircleCauchyAnglePeriodSourceTarget_toParametrizedTarget
    (g8BookIIICh23FloorLiftCauchyPeriodMilestone_toCauchyTarget
      milestone)
    milestone.2

-- ============================================================
-- GUARDRAILS
-- ============================================================

/-- Falsifier surface: a bounded angle with no Cauchy replacement refutes the
    advertised parametrized Cauchy completeness target. -/
structure G8BookIIICh23BoundedAngleWithoutCauchyReplacement where
  angle : BoundedTauAngle
  noReplacement :
    ¬ ∃ b : BoundedTauAngle,
      BoundedTauAngle.IsCauchy b ∧
        TauCircleCanonicalPoint.ofBoundedAngle b =
          TauCircleCanonicalPoint.ofBoundedAngle angle

/-- A missing replacement refutes parametrized Cauchy completeness. -/
theorem
    G8BookIIICh23BoundedAngleWithoutCauchyReplacement.refutesComplete
    (gap : G8BookIIICh23BoundedAngleWithoutCauchyReplacement) :
    ¬ G8BookIIICh23TauCircleParametrizedCauchyComplete := by
  intro complete
  exact gap.noReplacement
    (g8BookIIICh23BoundedAngleCauchyReplacement_of_parametrizedComplete
      complete gap.angle)

/-- Falsifier surface: a period equivalence whose forward map is not the
    floor-grid lift cannot close the floor-lift soundness target through the
    clean equivalence adapter. -/
structure G8BookIIICh23WrongFloorLiftPeriodForwardMap where
  source : G8BookIIICh23FloorLiftCauchyPeriodEquivalenceSource
  point : UnitAddCircle
  mismatch :
    source.periodEquiv point ≠
      TauCircleCauchyParametrizedCanonicalPoint.ofBoundedAngle
        (g8BookIIICh23RealIcoFloorLiftSource
          |>.toBoundedAngleOfUnitAddCircle point)
        (g8BookIIICh23RealIcoFloorLiftSource
          |>.toBoundedAngleOfUnitAddCircle_cauchy point)

/-- Wrong forward-map evidence refutes the source's exact alignment field. -/
theorem
    G8BookIIICh23WrongFloorLiftPeriodForwardMap.refutesSource
    (gap : G8BookIIICh23WrongFloorLiftPeriodForwardMap) :
    False :=
  gap.mismatch (gap.source.forward_eq gap.point)

end Tau.BookIII.Bridge
