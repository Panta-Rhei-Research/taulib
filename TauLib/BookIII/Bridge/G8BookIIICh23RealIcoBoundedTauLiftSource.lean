import TauLib.BookIII.Bridge.G8BookIIICh23UnitAddCircleRealIcoCauchyAngleReadout

/-!
# TauLib.BookIII.Bridge.G8BookIIICh23RealIcoBoundedTauLiftSource

Bounded tau-angle representative source for the Ch.23 real-Ico period lift.

The previous readout module closed the orthodox side: every `UnitAddCircle`
point has a canonical real period in `[0,1)`.  This module closes the quotient
bookkeeping around that period: the canonical real period has a theorem-backed
`TauRealQ` value through `tauRealQRingEquivReal.symm`, and a bounded Cauchy
tau-angle representative with that quotient value is exactly sufficient to
build the controlled lift needed downstream.

The hard tau-native theorem is not hidden here.  It is the explicit
basepoint-preserving bounded-representative source:

```text
∀ x : [0,1), choose a bounded Cauchy tau angle representing
  tauRealQRingEquivReal.symm x.
```

No final-spine, RH, O3, determinant-transfer, accepted-realization, or
completion-uniqueness machinery enters this A1.1 period-lift corridor.
-/

set_option autoImplicit false

namespace Tau.BookIII.Bridge

open Tau.Boundary

-- ============================================================
-- QUOTIENT-LEVEL REAL-ICO LIFT
-- ============================================================

/-- The theorem-backed `TauRealQ` value of a real half-open unit period. -/
noncomputable def g8BookIIICh23UnitRealIcoTauRealQ
    (x : G8BookIIICh23UnitRealIco) : TauRealQ :=
  tauRealQRingEquivReal.symm x.1

/-- The quotient-level real-Ico lift has exact real agreement. -/
theorem g8BookIIICh23UnitRealIcoTauRealQ_representsReal
    (x : G8BookIIICh23UnitRealIco) :
    tauRealQRingEquivReal
        (g8BookIIICh23UnitRealIcoTauRealQ x) =
      x.1 :=
  tauRealQRingEquivReal.apply_symm_apply x.1

/-- The zero bounded tau angle is Cauchy. -/
theorem g8BookIIICh23BoundedTauAngle_zero_isCauchy :
    BoundedTauAngle.IsCauchy BoundedTauAngle.zero :=
  TauReal.zero_isCauchy

/-- The zero bounded tau angle represents the zero `TauRealQ` value. -/
theorem g8BookIIICh23BoundedTauAngleZero_toTauRealQ :
    G8BookIIICh23CauchyBoundedAngle.toTauRealQ
        BoundedTauAngle.zero
        g8BookIIICh23BoundedTauAngle_zero_isCauchy =
      (0 : TauRealQ) := by
  change
    CauchyTauReal.toQ
        ⟨TauReal.zero,
          g8BookIIICh23BoundedTauAngle_zero_isCauchy⟩ =
      CauchyTauReal.zero.toQ
  exact Quotient.sound (TauReal.equiv_refl TauReal.zero)

/-- The canonical real-Ico zero period has zero `TauRealQ` value. -/
theorem g8BookIIICh23UnitRealIcoTauRealQ_zero :
    g8BookIIICh23UnitRealIcoTauRealQ
        g8BookIIICh23UnitRealIcoZero =
      (0 : TauRealQ) := by
  dsimp [g8BookIIICh23UnitRealIcoTauRealQ,
    g8BookIIICh23UnitRealIcoZero]
  exact map_zero tauRealQRingEquivReal.symm

-- ============================================================
-- BOUNDED REPRESENTATIVE SOURCE
-- ============================================================

/-- A bounded Cauchy tau angle represents the canonical quotient value of a
    real-Ico period. -/
def G8BookIIICh23BoundedCauchyAngleRepresentsTauRealQ
    (x : G8BookIIICh23UnitRealIco)
    (a : BoundedTauAngle)
    (ha : BoundedTauAngle.IsCauchy a) : Prop :=
  G8BookIIICh23CauchyBoundedAngle.toTauRealQ a ha =
    g8BookIIICh23UnitRealIcoTauRealQ x

/-- Pointwise bounded Cauchy representative for a real-Ico period. -/
structure G8BookIIICh23BoundedCauchyTauRepresentative
    (x : G8BookIIICh23UnitRealIco) where
  angle : BoundedTauAngle
  cauchy : BoundedTauAngle.IsCauchy angle
  quotient_eq :
    G8BookIIICh23BoundedCauchyAngleRepresentsTauRealQ
      x angle cauchy

/-- The theorem-backed zero representative. -/
def g8BookIIICh23UnitRealIcoZeroBoundedTauRepresentative :
    G8BookIIICh23BoundedCauchyTauRepresentative
      g8BookIIICh23UnitRealIcoZero where
  angle := BoundedTauAngle.zero
  cauchy := g8BookIIICh23BoundedTauAngle_zero_isCauchy
  quotient_eq := by
    dsimp [G8BookIIICh23BoundedCauchyAngleRepresentsTauRealQ]
    rw [g8BookIIICh23BoundedTauAngleZero_toTauRealQ,
      g8BookIIICh23UnitRealIcoTauRealQ_zero]

/-- Source form of the remaining tau-native bounded representative theorem.

This is stronger than a bare pointwise existence statement because it records
the basepoint-preserving choice needed by the additive-circle lobe bridge. -/
structure G8BookIIICh23RealIcoBoundedCauchyTauRepresentativeSource where
  representative :
    ∀ x : G8BookIIICh23UnitRealIco,
      G8BookIIICh23BoundedCauchyTauRepresentative x
  zero_preserving :
    (representative g8BookIIICh23UnitRealIcoZero).angle =
      BoundedTauAngle.zero
  boundedRepresentativeConstruction : Prop
  boundedRepresentativeConstructionEvidence :
    boundedRepresentativeConstruction
  quotientRepresentativeAgreement : Prop
  quotientRepresentativeAgreementEvidence :
    quotientRepresentativeAgreement
  status : SpineStatus := .conditional_interface

/-- Target form of the bounded Cauchy representative source. -/
def G8BookIIICh23RealIcoBoundedCauchyTauRepresentativeSourceTarget :
    Prop :=
  Nonempty
    G8BookIIICh23RealIcoBoundedCauchyTauRepresentativeSource

namespace G8BookIIICh23RealIcoBoundedCauchyTauRepresentativeSource

/-- A bounded representative source supplies the controlled real-Ico lift. -/
noncomputable def toRealIcoCauchyBoundedTauAngleLiftSource
    (source :
      G8BookIIICh23RealIcoBoundedCauchyTauRepresentativeSource) :
    G8BookIIICh23RealIcoCauchyBoundedTauAngleLiftSource where
  toBoundedAngle := fun x => (source.representative x).angle
  toBoundedAngle_cauchy := fun x => (source.representative x).cauchy
  representsReal := by
    intro x
    dsimp [G8BookIIICh23CauchyBoundedAngleRepresentsReal]
    rw [(source.representative x).quotient_eq]
    exact g8BookIIICh23UnitRealIcoTauRealQ_representsReal x
  basepoint_preserving := source.zero_preserving
  boundedLiftConstruction := source.boundedRepresentativeConstruction
  boundedLiftConstructionEvidence :=
    source.boundedRepresentativeConstructionEvidence
  quotientRealAgreement :=
    ∀ x : G8BookIIICh23UnitRealIco,
      G8BookIIICh23BoundedCauchyAngleRepresentsTauRealQ
        x
        (source.representative x).angle
        (source.representative x).cauchy
  quotientRealAgreementEvidence := by
    intro x
    exact (source.representative x).quotient_eq
  status := source.status

end G8BookIIICh23RealIcoBoundedCauchyTauRepresentativeSource

/-- The bounded representative target is exactly sufficient for the older
    controlled real-Ico lift target. -/
theorem
    g8BookIIICh23RealIcoBoundedCauchyTauRepresentativeSourceTarget_toLiftTarget
    (target :
      G8BookIIICh23RealIcoBoundedCauchyTauRepresentativeSourceTarget) :
    G8BookIIICh23RealIcoCauchyBoundedTauAngleLiftTarget := by
  rcases target with ⟨source⟩
  exact ⟨source.toRealIcoCauchyBoundedTauAngleLiftSource⟩

-- ============================================================
-- GUARDRAILS
-- ============================================================

/-- Falsifier surface: a pointwise representative with the wrong quotient
    value cannot instantiate the representative source. -/
structure G8BookIIICh23BoundedTauRepresentativeQuotientMismatch
    (source :
      G8BookIIICh23RealIcoBoundedCauchyTauRepresentativeSource) where
  point : G8BookIIICh23UnitRealIco
  mismatch :
    ¬ G8BookIIICh23BoundedCauchyAngleRepresentsTauRealQ
        point
        (source.representative point).angle
        (source.representative point).cauchy

/-- Quotient mismatch refutes the corresponding representative field. -/
theorem
    G8BookIIICh23BoundedTauRepresentativeQuotientMismatch.refutesSource
    {source :
      G8BookIIICh23RealIcoBoundedCauchyTauRepresentativeSource}
    (failure :
      G8BookIIICh23BoundedTauRepresentativeQuotientMismatch source) :
    False :=
  failure.mismatch
    (source.representative failure.point).quotient_eq

/-- Falsifier surface: a source that fails to preserve the zero representative
    cannot supply the basepoint-preserving lobe bridge. -/
structure G8BookIIICh23BoundedTauRepresentativeBasepointMismatch
    (source :
      G8BookIIICh23RealIcoBoundedCauchyTauRepresentativeSource) where
  mismatch :
    (source.representative g8BookIIICh23UnitRealIcoZero).angle ≠
      BoundedTauAngle.zero

/-- Basepoint mismatch refutes the source's zero-preserving field. -/
theorem
    G8BookIIICh23BoundedTauRepresentativeBasepointMismatch.refutesSource
    {source :
      G8BookIIICh23RealIcoBoundedCauchyTauRepresentativeSource}
    (failure :
      G8BookIIICh23BoundedTauRepresentativeBasepointMismatch source) :
    False :=
  failure.mismatch source.zero_preserving

/-- Guardrail: the theorem-backed zero representative is available, but it
    does not by itself construct representatives for all real-Ico periods. -/
def G8BookIIICh23ZeroRepresentativeOnlyDoesNotCloseAllPeriods : Prop :=
  ¬ G8BookIIICh23RealIcoBoundedCauchyTauRepresentativeSourceTarget

end Tau.BookIII.Bridge
