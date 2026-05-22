import TauLib.BookIII.Bridge.G8BookIIICh23CauchyTauCircleRightInverseReduction

/-!
# TauLib.BookIII.Bridge.G8BookIIICh23FloorNormalizedCauchyLobe

The floor-normalized Cauchy tau-circle lobe.

The unrestricted Cauchy-parametrized lobe still requires the period-canonical
compatibility theorem isolated in
`G8BookIIICh23CauchyTauCircleRightInverseReduction`.  This module closes the
next theorem-backed object: the witness-carrying image of the floor lift.

On this normalized lobe the additive-circle coordinate is part of the point,
so the right inverse is theorem-backed without weakening the full-lobe target
or changing the current exact-angle canonical quotient.
-/

set_option autoImplicit false

namespace Tau.BookIII.Bridge

open Tau.Boundary

-- ============================================================
-- FLOOR-NORMALIZED CAUCHY LOBE
-- ============================================================

/-- A floor-normalized Cauchy lobe point is a unit additive-circle period
    together with the Cauchy-parametrized canonical tau-circle point generated
    by the theorem-backed floor lift of that period. -/
structure G8BookIIICh23FloorNormalizedCauchyLobePoint where
  period : UnitAddCircle
  cauchyPoint : TauCircleCauchyParametrizedCanonicalPoint
  cauchyPoint_eq :
    cauchyPoint = g8BookIIICh23FloorLiftCauchyPoint period

namespace G8BookIIICh23FloorNormalizedCauchyLobePoint

/-- Constructor from a unit additive-circle period. -/
noncomputable def ofUnitAddCircle
    (u : UnitAddCircle) :
    G8BookIIICh23FloorNormalizedCauchyLobePoint where
  period := u
  cauchyPoint := g8BookIIICh23FloorLiftCauchyPoint u
  cauchyPoint_eq := rfl

/-- Forget the normalized coordinate and view the point in the wider
    Cauchy-parametrized canonical lobe. -/
def toCauchyParametrized
    (p : G8BookIIICh23FloorNormalizedCauchyLobePoint) :
    TauCircleCauchyParametrizedCanonicalPoint :=
  p.cauchyPoint

@[simp] theorem ofUnitAddCircle_period
    (u : UnitAddCircle) :
    (ofUnitAddCircle u).period = u :=
  rfl

@[simp] theorem ofUnitAddCircle_toCauchyParametrized
    (u : UnitAddCircle) :
    (ofUnitAddCircle u).toCauchyParametrized =
      g8BookIIICh23FloorLiftCauchyPoint u :=
  rfl

@[simp] theorem toCauchyParametrized_eq_floor
    (p : G8BookIIICh23FloorNormalizedCauchyLobePoint) :
    p.toCauchyParametrized =
      g8BookIIICh23FloorLiftCauchyPoint p.period :=
  p.cauchyPoint_eq

/-- Extensionality by the normalized period coordinate. -/
theorem ext_period
    {p q : G8BookIIICh23FloorNormalizedCauchyLobePoint}
    (h : p.period = q.period) : p = q := by
  rcases p with ⟨up, pp, hp⟩
  rcases q with ⟨uq, pq, hq⟩
  dsimp at h
  subst uq
  subst pp
  subst pq
  rfl

end G8BookIIICh23FloorNormalizedCauchyLobePoint

-- ============================================================
-- UNITADDCIRCLE EQUIVALENCE
-- ============================================================

/-- The floor-normalized Cauchy lobe is theorem-backed equivalent to
    `UnitAddCircle`: its coordinate is exactly the additive-circle period. -/
noncomputable def g8BookIIICh23UnitAddCircleEquivFloorNormalizedCauchyLobe :
    UnitAddCircle ≃ G8BookIIICh23FloorNormalizedCauchyLobePoint where
  toFun :=
    G8BookIIICh23FloorNormalizedCauchyLobePoint.ofUnitAddCircle
  invFun := fun p => p.period
  left_inv := by
    intro u
    rfl
  right_inv := by
    intro p
    exact
      G8BookIIICh23FloorNormalizedCauchyLobePoint.ext_period
        rfl

/-- The equivalence sends a unit period to the corresponding floor-lift point
    in the wider Cauchy-parametrized lobe. -/
@[simp] theorem
    g8BookIIICh23UnitAddCircleEquivFloorNormalizedCauchyLobe_apply_cauchy
    (u : UnitAddCircle) :
    (g8BookIIICh23UnitAddCircleEquivFloorNormalizedCauchyLobe u).toCauchyParametrized =
      g8BookIIICh23FloorLiftCauchyPoint u :=
  rfl

/-- The normalized lobe readout is a right inverse on normalized points. -/
theorem g8BookIIICh23FloorNormalizedCauchyLobe_right_inv
    (p : G8BookIIICh23FloorNormalizedCauchyLobePoint) :
    G8BookIIICh23FloorNormalizedCauchyLobePoint.ofUnitAddCircle
        p.period =
      p :=
  g8BookIIICh23UnitAddCircleEquivFloorNormalizedCauchyLobe.right_inv p

/-- The normalized lobe readout is a left inverse on `UnitAddCircle`. -/
theorem g8BookIIICh23FloorNormalizedCauchyLobe_left_inv
    (u : UnitAddCircle) :
    (G8BookIIICh23FloorNormalizedCauchyLobePoint.ofUnitAddCircle u).period =
      u :=
  rfl

/-- The theorem-backed unit-period readout agrees with the normalized period
    coordinate. -/
theorem g8BookIIICh23FloorNormalizedCauchyLobe_unitPeriod
    (p : G8BookIIICh23FloorNormalizedCauchyLobePoint) :
    g8BookIIICh23CauchyBoundedAngleUnitAddCirclePeriod
        (g8BookIIICh23RealIcoFloorLiftSource.toBoundedAngleOfUnitAddCircle
          p.period)
        (g8BookIIICh23RealIcoFloorLiftSource.toBoundedAngleOfUnitAddCircle_cauchy
          p.period) =
      p.period :=
  g8BookIIICh23FloorLiftCauchyPoint_unitPeriod p.period

/-- Target form of the closed floor-normalized lobe equivalence. -/
def G8BookIIICh23FloorNormalizedCauchyLobeEquivalenceTarget :
    Prop :=
  Nonempty (UnitAddCircle ≃ G8BookIIICh23FloorNormalizedCauchyLobePoint)

/-- The floor-normalized lobe equivalence is closed theorem-backed. -/
theorem g8BookIIICh23FloorNormalizedCauchyLobeEquivalence_closed :
    G8BookIIICh23FloorNormalizedCauchyLobeEquivalenceTarget :=
  ⟨g8BookIIICh23UnitAddCircleEquivFloorNormalizedCauchyLobe⟩

-- ============================================================
-- COVERAGE OF THE FULL CAUCHY-PARAMETRIZED LOBE
-- ============================================================

/-- Coverage of the full Cauchy-parametrized lobe by the floor-normalized
    image.  This is the exact remaining bridge if we want the normalized lobe
    equivalence to become the unrestricted Cauchy period source. -/
def G8BookIIICh23FloorNormalizedCauchyLobeCoversFullCauchyLobe :
    Prop :=
  ∀ p : TauCircleCauchyParametrizedCanonicalPoint,
    ∃ q : G8BookIIICh23FloorNormalizedCauchyLobePoint,
      q.toCauchyParametrized = p

/-- Full-lobe coverage implies the image-surjectivity target from the previous
    reduction module. -/
theorem g8BookIIICh23FloorLift_imageSurjective_of_normalizedCoverage
    (h :
      G8BookIIICh23FloorNormalizedCauchyLobeCoversFullCauchyLobe) :
    G8BookIIICh23FloorLiftCauchyImageSurjectivity := by
  intro p
  rcases h p with ⟨q, hq⟩
  refine ⟨q.period, ?_⟩
  exact q.cauchyPoint_eq.symm.trans hq

/-- Image-surjectivity is enough to cover the full lobe by normalized points,
    using the witness-carrying normalized constructor. -/
theorem g8BookIIICh23FloorNormalizedCoverage_of_imageSurjectivity
    (h : G8BookIIICh23FloorLiftCauchyImageSurjectivity) :
    G8BookIIICh23FloorNormalizedCauchyLobeCoversFullCauchyLobe := by
  intro p
  rcases h p with ⟨u, hu⟩
  refine
    ⟨G8BookIIICh23FloorNormalizedCauchyLobePoint.ofUnitAddCircle u,
      ?_⟩
  simpa using hu

/-- Coverage of the full lobe is equivalent to the image-surjectivity target
    already identified as the unrestricted right-inverse content. -/
theorem
    g8BookIIICh23FloorNormalizedCoverage_iff_imageSurjectivity :
    G8BookIIICh23FloorNormalizedCauchyLobeCoversFullCauchyLobe ↔
      G8BookIIICh23FloorLiftCauchyImageSurjectivity :=
  ⟨g8BookIIICh23FloorLift_imageSurjective_of_normalizedCoverage,
    g8BookIIICh23FloorNormalizedCoverage_of_imageSurjectivity⟩

/-- Period-canonical compatibility makes the floor-normalized lobe cover the
    full Cauchy-parametrized lobe. -/
theorem
    g8BookIIICh23FloorNormalizedCoverage_of_periodCanonicalCompatibility
    (hcompat : G8BookIIICh23FloorLiftPeriodCanonicalCompatibility) :
    G8BookIIICh23FloorNormalizedCauchyLobeCoversFullCauchyLobe :=
  g8BookIIICh23FloorNormalizedCoverage_of_imageSurjectivity
    (g8BookIIICh23FloorLift_imageSurjective_of_periodCanonicalCompatibility
      hcompat)

-- ============================================================
-- GUARDRAILS
-- ============================================================

/-- Falsifier surface: a full Cauchy-parametrized point not covered by the
    normalized lobe blocks upgrading the normalized equivalence to the
    unrestricted right inverse. -/
structure G8BookIIICh23FloorNormalizedCauchyLobeCoverageGap where
  point : TauCircleCauchyParametrizedCanonicalPoint
  notCovered :
    ¬ ∃ q : G8BookIIICh23FloorNormalizedCauchyLobePoint,
      q.toCauchyParametrized = point

/-- A coverage gap refutes full-lobe coverage. -/
theorem G8BookIIICh23FloorNormalizedCauchyLobeCoverageGap.refutesCoverage
    (gap : G8BookIIICh23FloorNormalizedCauchyLobeCoverageGap) :
    ¬ G8BookIIICh23FloorNormalizedCauchyLobeCoversFullCauchyLobe := by
  intro h
  exact gap.notCovered (h gap.point)

/-- A coverage gap refutes the unrestricted right inverse through the exact
    image-surjectivity equivalence. -/
theorem G8BookIIICh23FloorNormalizedCauchyLobeCoverageGap.refutesUnrestrictedRightInverse
    (gap : G8BookIIICh23FloorNormalizedCauchyLobeCoverageGap) :
    ¬ ∃ fromCauchyParametrized :
        TauCircleCauchyParametrizedCanonicalPoint → UnitAddCircle,
        G8BookIIICh23FloorLiftCanonicalRightInverseFor
          fromCauchyParametrized := by
  intro hright
  exact
    gap.refutesCoverage
      (g8BookIIICh23FloorNormalizedCoverage_iff_imageSurjectivity.mpr
        (g8BookIIICh23FloorLift_rightInverse_iff_imageSurjectivity.mp
          hright))

end Tau.BookIII.Bridge
