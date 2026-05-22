import TauLib.BookIII.Bridge.G8BookIIICh23FloorNormalizedCauchyLobe

/-!
# G8 Book III Ch.23 Period-Canonical Compatibility Split

This module isolates the exact quotient-theoretic payload behind the
floor-normalized Cauchy lobe upgrade.  A period-normalized representative is
enough to recover a Cauchy point precisely when its bounded angle and tau value
are equivalent to the original bounded Cauchy angle in the canonical tau-circle
quotient.

No full-lobe coverage is asserted here.  The result is a no-sorry split of the
remaining compatibility target into the exact angle/value relations required by
`TauCircleCanonicalPoint`.
-/

namespace Tau.BookIII.Bridge

open Tau.Boundary

/-- The floor-normalized bounded angle associated to a Cauchy bounded tau angle. -/
noncomputable def g8BookIIICh23FloorNormalizedAngleOfCauchyAngle
    (a : BoundedTauAngle) (ha : BoundedTauAngle.IsCauchy a) :
    BoundedTauAngle :=
  g8BookIIICh23RealIcoFloorLiftSource.toBoundedAngleOfUnitAddCircle
    (g8BookIIICh23CauchyBoundedAngleUnitAddCirclePeriod a ha)

/-- The floor-normalized angle is Cauchy by construction. -/
theorem g8BookIIICh23FloorNormalizedAngleOfCauchyAngle_cauchy
    (a : BoundedTauAngle) (ha : BoundedTauAngle.IsCauchy a) :
    BoundedTauAngle.IsCauchy
      (g8BookIIICh23FloorNormalizedAngleOfCauchyAngle a ha) :=
  g8BookIIICh23RealIcoFloorLiftSource.toBoundedAngleOfUnitAddCircle_cauchy
    (g8BookIIICh23CauchyBoundedAngleUnitAddCirclePeriod a ha)

/--
Pointwise exact compatibility between a bounded Cauchy angle and its
floor-normalized period representative.  These are exactly the two fields of
the canonical tau-circle quotient relation.
-/
structure G8BookIIICh23PointwiseFloorPeriodCanonicalCompatibility
    (a : BoundedTauAngle) (ha : BoundedTauAngle.IsCauchy a) : Prop where
  angle_equiv :
    TauReal.equiv
      (g8BookIIICh23FloorNormalizedAngleOfCauchyAngle a ha).angle
      a.angle
  value_equiv :
    TauComplex.equiv
      (TauComplex.cisTauReal
        (g8BookIIICh23FloorNormalizedAngleOfCauchyAngle a ha).angle)
      (TauComplex.cisTauReal a.angle)

/--
Global exact angle/value compatibility.  This is the quotient-level form of
the remaining period-canonical compatibility theorem.
-/
def G8BookIIICh23FloorPeriodExactAngleValueCompatibility : Prop :=
  ∀ (a : BoundedTauAngle) (ha : BoundedTauAngle.IsCauchy a),
    G8BookIIICh23PointwiseFloorPeriodCanonicalCompatibility a ha

/-- Pointwise exact compatibility gives equality in the canonical tau-circle quotient. -/
theorem G8BookIIICh23PointwiseFloorPeriodCanonicalCompatibility.toCanonicalEq
    {a : BoundedTauAngle} {ha : BoundedTauAngle.IsCauchy a}
    (h : G8BookIIICh23PointwiseFloorPeriodCanonicalCompatibility a ha) :
    TauCircleCanonicalPoint.ofBoundedAngle
        (g8BookIIICh23FloorNormalizedAngleOfCauchyAngle a ha) =
      TauCircleCanonicalPoint.ofBoundedAngle a :=
  TauCircleCanonicalPoint.eq_of_param_value h.angle_equiv h.value_equiv

/-- Pointwise exact compatibility gives equality of Cauchy-parametrized points. -/
theorem G8BookIIICh23PointwiseFloorPeriodCanonicalCompatibility.toCauchyPointEq
    {a : BoundedTauAngle} {ha : BoundedTauAngle.IsCauchy a}
    (h : G8BookIIICh23PointwiseFloorPeriodCanonicalCompatibility a ha) :
    TauCircleCauchyParametrizedCanonicalPoint.ofBoundedAngle
        (g8BookIIICh23FloorNormalizedAngleOfCauchyAngle a ha)
        (g8BookIIICh23FloorNormalizedAngleOfCauchyAngle_cauchy a ha) =
      TauCircleCauchyParametrizedCanonicalPoint.ofBoundedAngle a ha := by
  apply Subtype.ext
  exact h.toCanonicalEq

/-- Exact angle/value compatibility implies the period-canonical compatibility target. -/
theorem g8BookIIICh23FloorLiftPeriodCanonicalCompatibility_of_exactAngleValue
    (h : G8BookIIICh23FloorPeriodExactAngleValueCompatibility) :
    G8BookIIICh23FloorLiftPeriodCanonicalCompatibility := by
  intro a ha
  exact (h a ha).toCauchyPointEq

/--
Conversely, equality of the Cauchy-parametrized quotient points exposes exactly
the canonical quotient relation, hence the two angle/value compatibility fields.
-/
theorem g8BookIIICh23ExactAngleValue_of_floorLiftPeriodCanonicalCompatibility
    (h : G8BookIIICh23FloorLiftPeriodCanonicalCompatibility) :
    G8BookIIICh23FloorPeriodExactAngleValueCompatibility := by
  intro a ha
  have hcauchy := h a ha
  have hcanon :
      TauCircleCanonicalPoint.ofBoundedAngle
          (g8BookIIICh23FloorNormalizedAngleOfCauchyAngle a ha) =
        TauCircleCanonicalPoint.ofBoundedAngle a := by
    simpa [g8BookIIICh23FloorNormalizedAngleOfCauchyAngle]
      using congrArg
        (fun p : TauCircleCauchyParametrizedCanonicalPoint =>
          (p : TauCircleCanonicalPoint))
        hcauchy
  have hrel :
      TauCirclePoint.CanonicalEquivalent
        (TauCirclePoint.ofBoundedAngle
          (g8BookIIICh23FloorNormalizedAngleOfCauchyAngle a ha))
        (TauCirclePoint.ofBoundedAngle a) := by
    exact Quotient.exact hcanon
  exact ⟨hrel.1, hrel.2⟩

/--
The floor-lift period-canonical compatibility theorem is exactly the exact
angle/value compatibility theorem.
-/
theorem g8BookIIICh23FloorLiftPeriodCanonicalCompatibility_iff_exactAngleValue :
    G8BookIIICh23FloorLiftPeriodCanonicalCompatibility ↔
      G8BookIIICh23FloorPeriodExactAngleValueCompatibility :=
  ⟨g8BookIIICh23ExactAngleValue_of_floorLiftPeriodCanonicalCompatibility,
    g8BookIIICh23FloorLiftPeriodCanonicalCompatibility_of_exactAngleValue⟩

/-- Exact angle/value compatibility is sufficient for normalized full-lobe coverage. -/
theorem g8BookIIICh23FloorNormalizedCoverage_of_exactAngleValue
    (h : G8BookIIICh23FloorPeriodExactAngleValueCompatibility) :
    G8BookIIICh23FloorNormalizedCauchyLobeCoversFullCauchyLobe :=
  g8BookIIICh23FloorNormalizedCoverage_of_periodCanonicalCompatibility
    (g8BookIIICh23FloorLiftPeriodCanonicalCompatibility_of_exactAngleValue h)

/-- Exact angle/value compatibility is sufficient for floor-lift image surjectivity. -/
theorem g8BookIIICh23FloorLift_imageSurjective_of_exactAngleValue
    (h : G8BookIIICh23FloorPeriodExactAngleValueCompatibility) :
    G8BookIIICh23FloorLiftCauchyImageSurjectivity :=
  g8BookIIICh23FloorLift_imageSurjective_of_normalizedCoverage
    (g8BookIIICh23FloorNormalizedCoverage_of_exactAngleValue h)

/-- A pointwise angle mismatch blocks the exact compatibility theorem. -/
structure G8BookIIICh23FloorPeriodAngleMismatch where
  angle : BoundedTauAngle
  cauchy : BoundedTauAngle.IsCauchy angle
  not_angle_equiv :
    ¬ TauReal.equiv
      (g8BookIIICh23FloorNormalizedAngleOfCauchyAngle angle cauchy).angle
      angle.angle

/-- A pointwise value mismatch blocks the exact compatibility theorem. -/
structure G8BookIIICh23FloorPeriodValueMismatch where
  angle : BoundedTauAngle
  cauchy : BoundedTauAngle.IsCauchy angle
  not_value_equiv :
    ¬ TauComplex.equiv
      (TauComplex.cisTauReal
        (g8BookIIICh23FloorNormalizedAngleOfCauchyAngle angle cauchy).angle)
      (TauComplex.cisTauReal angle.angle)

namespace G8BookIIICh23FloorPeriodAngleMismatch

theorem refutesExactAngleValue
    (gap : G8BookIIICh23FloorPeriodAngleMismatch) :
    ¬ G8BookIIICh23FloorPeriodExactAngleValueCompatibility := by
  intro h
  exact gap.not_angle_equiv (h gap.angle gap.cauchy).angle_equiv

theorem refutesFloorLiftPeriodCanonicalCompatibility
    (gap : G8BookIIICh23FloorPeriodAngleMismatch) :
    ¬ G8BookIIICh23FloorLiftPeriodCanonicalCompatibility := by
  intro h
  exact gap.refutesExactAngleValue
    (g8BookIIICh23ExactAngleValue_of_floorLiftPeriodCanonicalCompatibility h)

end G8BookIIICh23FloorPeriodAngleMismatch

namespace G8BookIIICh23FloorPeriodValueMismatch

theorem refutesExactAngleValue
    (gap : G8BookIIICh23FloorPeriodValueMismatch) :
    ¬ G8BookIIICh23FloorPeriodExactAngleValueCompatibility := by
  intro h
  exact gap.not_value_equiv (h gap.angle gap.cauchy).value_equiv

theorem refutesFloorLiftPeriodCanonicalCompatibility
    (gap : G8BookIIICh23FloorPeriodValueMismatch) :
    ¬ G8BookIIICh23FloorLiftPeriodCanonicalCompatibility := by
  intro h
  exact gap.refutesExactAngleValue
    (g8BookIIICh23ExactAngleValue_of_floorLiftPeriodCanonicalCompatibility h)

end G8BookIIICh23FloorPeriodValueMismatch

end Tau.BookIII.Bridge
