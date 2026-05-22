import TauLib.BookIII.Bridge.G8BookIIICh23TauCircleParametrizationCompletenessRealityCheck

/-!
# TauLib.BookIII.Bridge.G8BookIIICh23UnitAddCircleTauCircleCanonicalEquivalence

Canonical lobe-equivalence target for A1.1.

The raw tau-circle target

```text
UnitAddCircle ≃ TauCirclePoint
```

is too strong for the current carrier: `TauCirclePoint` includes source-status
and proof-presentation fibers.  `TauCircleCanonicalPoint` removes those fibers.
This module installs the exact replacement target

```text
UnitAddCircle ≃ TauCircleCanonicalPoint
```

and proves the adapters around it.  It does not manufacture the equivalence:
the remaining mathematical payload is the real/periodic angle bridge between
Mathlib's additive circle and the tau-native bounded-angle quotient.
-/

set_option autoImplicit false

namespace Tau.BookIII.Bridge

-- ============================================================
-- CANONICAL LOBE-LEVEL EQUIVALENCE
-- ============================================================

/-- Exact lobe-level identification between Mathlib's additive circle and the
    semantic tau-circle quotient.

The equivalence is the load-bearing field.  The topology/metric/compactness
fields are kept explicit so that future A1.1 transfer does not silently turn a
set-level bijection into a compact metric graph theorem. -/
structure G8BookIIICh23UnitAddCircleTauCircleCanonicalLobeEquivalence where
  lobeEquiv : UnitAddCircle ≃ TauCircleCanonicalPoint
  basepoint_preserving :
    lobeEquiv G8Ch23UnitAddCircleWedgePoint.basepoint =
      TauCircleCanonicalPoint.base
  lobeTopologyAgreement : Prop
  lobeTopologyAgreementEvidence : lobeTopologyAgreement
  lobeMetricAgreement : Prop
  lobeMetricAgreementEvidence : lobeMetricAgreement
  lobeCompactnessAgreement : Prop
  lobeCompactnessAgreementEvidence : lobeCompactnessAgreement
  anglePeriodBridge : Prop
  anglePeriodBridgeEvidence : anglePeriodBridge
  canonicalParametrizationComplete : Prop
  canonicalParametrizationCompleteEvidence :
    canonicalParametrizationComplete
  status : SpineStatus := .conditional_interface

namespace G8BookIIICh23UnitAddCircleTauCircleCanonicalLobeEquivalence

/-- The inverse lobe map also preserves the distinguished basepoint. -/
theorem symm_basepoint_preserving
    (source :
      G8BookIIICh23UnitAddCircleTauCircleCanonicalLobeEquivalence) :
    source.lobeEquiv.symm TauCircleCanonicalPoint.base =
      G8Ch23UnitAddCircleWedgePoint.basepoint := by
  apply source.lobeEquiv.injective
  rw [Equiv.apply_symm_apply]
  exact source.basepoint_preserving.symm

/-- The forward map from the canonical equivalence. -/
def toCanonical
    (source :
      G8BookIIICh23UnitAddCircleTauCircleCanonicalLobeEquivalence) :
    UnitAddCircle → TauCircleCanonicalPoint :=
  source.lobeEquiv

/-- The inverse map from the canonical equivalence. -/
def fromCanonical
    (source :
      G8BookIIICh23UnitAddCircleTauCircleCanonicalLobeEquivalence) :
    TauCircleCanonicalPoint → UnitAddCircle :=
  source.lobeEquiv.symm

@[simp] theorem from_to
    (source :
      G8BookIIICh23UnitAddCircleTauCircleCanonicalLobeEquivalence)
    (p : UnitAddCircle) :
    source.fromCanonical (source.toCanonical p) = p :=
  source.lobeEquiv.left_inv p

@[simp] theorem to_from
    (source :
      G8BookIIICh23UnitAddCircleTauCircleCanonicalLobeEquivalence)
    (p : TauCircleCanonicalPoint) :
    source.toCanonical (source.fromCanonical p) = p :=
  source.lobeEquiv.right_inv p

end G8BookIIICh23UnitAddCircleTauCircleCanonicalLobeEquivalence

/-- Target form of the canonical tau-circle lobe equivalence. -/
def G8BookIIICh23UnitAddCircleTauCircleCanonicalLobeEquivalenceTarget :
    Prop :=
  Nonempty G8BookIIICh23UnitAddCircleTauCircleCanonicalLobeEquivalence

-- ============================================================
-- PARAMETRIZATION SOURCE FORM
-- ============================================================

/-- Source form for a complete canonical tau-circle parametrization.

This is the map/inverse presentation of the equivalence target.  It is often
more convenient while building the real-angle and tau-angle bridge because the
two maps can be constructed and audited separately. -/
structure G8BookIIICh23TauCircleCanonicalParametrizationCompletenessSource where
  toCanonical : UnitAddCircle → TauCircleCanonicalPoint
  fromCanonical : TauCircleCanonicalPoint → UnitAddCircle
  left_inv :
    ∀ p : UnitAddCircle, fromCanonical (toCanonical p) = p
  right_inv :
    ∀ p : TauCircleCanonicalPoint, toCanonical (fromCanonical p) = p
  basepoint_preserving :
    toCanonical G8Ch23UnitAddCircleWedgePoint.basepoint =
      TauCircleCanonicalPoint.base
  lobeTopologyAgreement : Prop
  lobeTopologyAgreementEvidence : lobeTopologyAgreement
  lobeMetricAgreement : Prop
  lobeMetricAgreementEvidence : lobeMetricAgreement
  lobeCompactnessAgreement : Prop
  lobeCompactnessAgreementEvidence : lobeCompactnessAgreement
  anglePeriodBridge : Prop
  anglePeriodBridgeEvidence : anglePeriodBridge
  canonicalParametrizationComplete : Prop
  canonicalParametrizationCompleteEvidence :
    canonicalParametrizationComplete
  status : SpineStatus := .conditional_interface

namespace G8BookIIICh23TauCircleCanonicalParametrizationCompletenessSource

/-- A complete canonical parametrization supplies the canonical lobe
    equivalence target. -/
def toCanonicalLobeEquivalence
    (source :
      G8BookIIICh23TauCircleCanonicalParametrizationCompletenessSource) :
    G8BookIIICh23UnitAddCircleTauCircleCanonicalLobeEquivalence where
  lobeEquiv :=
    { toFun := source.toCanonical
      invFun := source.fromCanonical
      left_inv := source.left_inv
      right_inv := source.right_inv }
  basepoint_preserving := source.basepoint_preserving
  lobeTopologyAgreement := source.lobeTopologyAgreement
  lobeTopologyAgreementEvidence := source.lobeTopologyAgreementEvidence
  lobeMetricAgreement := source.lobeMetricAgreement
  lobeMetricAgreementEvidence := source.lobeMetricAgreementEvidence
  lobeCompactnessAgreement := source.lobeCompactnessAgreement
  lobeCompactnessAgreementEvidence :=
    source.lobeCompactnessAgreementEvidence
  anglePeriodBridge := source.anglePeriodBridge
  anglePeriodBridgeEvidence := source.anglePeriodBridgeEvidence
  canonicalParametrizationComplete :=
    source.canonicalParametrizationComplete
  canonicalParametrizationCompleteEvidence :=
    source.canonicalParametrizationCompleteEvidence
  status := source.status

/-- A complete canonical parametrization discharges the canonical lobe
    equivalence target. -/
theorem toCanonicalLobeEquivalenceTarget
    (source :
      G8BookIIICh23TauCircleCanonicalParametrizationCompletenessSource) :
    G8BookIIICh23UnitAddCircleTauCircleCanonicalLobeEquivalenceTarget :=
  ⟨source.toCanonicalLobeEquivalence⟩

end G8BookIIICh23TauCircleCanonicalParametrizationCompletenessSource

/-- Target form of canonical tau-circle parametrization completeness. -/
def G8BookIIICh23TauCircleCanonicalParametrizationCompletenessTarget :
    Prop :=
  Nonempty G8BookIIICh23TauCircleCanonicalParametrizationCompletenessSource

/-- Canonical parametrization completeness is equivalent to the canonical
    lobe-equivalence target. -/
theorem
    g8BookIIICh23TauCircleCanonicalParametrizationCompletenessTarget_toLobeTarget
    (target :
      G8BookIIICh23TauCircleCanonicalParametrizationCompletenessTarget) :
    G8BookIIICh23UnitAddCircleTauCircleCanonicalLobeEquivalenceTarget := by
  rcases target with ⟨source⟩
  exact source.toCanonicalLobeEquivalenceTarget

-- ============================================================
-- ANGLE-PERIOD CONSTRUCTOR FORM
-- ============================================================

/-- Exact angle-period constructor for the canonical tau-circle lobe.

The forward map lands first in bounded tau angles and then in the canonical
tau-circle through the theorem-backed `cisTauReal` point constructor.  The
load-bearing fields are the inverse laws against this canonical cis image.
This is the narrow constructor needed before topology/metric transfer can be
closed. -/
structure G8BookIIICh23TauCircleCanonicalAnglePeriodConstructor where
  toBoundedAngle : UnitAddCircle → BoundedTauAngle
  fromCanonical : TauCircleCanonicalPoint → UnitAddCircle
  left_inv :
    ∀ p : UnitAddCircle,
      fromCanonical
          (TauCircleCanonicalPoint.ofBoundedAngle (toBoundedAngle p)) =
        p
  right_inv :
    ∀ p : TauCircleCanonicalPoint,
      TauCircleCanonicalPoint.ofBoundedAngle
          (toBoundedAngle (fromCanonical p)) =
        p
  basepoint_angle_preserving :
    toBoundedAngle G8Ch23UnitAddCircleWedgePoint.basepoint =
      BoundedTauAngle.zero
  lobeTopologyAgreement : Prop
  lobeTopologyAgreementEvidence : lobeTopologyAgreement
  lobeMetricAgreement : Prop
  lobeMetricAgreementEvidence : lobeMetricAgreement
  lobeCompactnessAgreement : Prop
  lobeCompactnessAgreementEvidence : lobeCompactnessAgreement
  anglePeriodBridge : Prop
  anglePeriodBridgeEvidence : anglePeriodBridge
  canonicalParametrizationComplete : Prop
  canonicalParametrizationCompleteEvidence :
    canonicalParametrizationComplete
  status : SpineStatus := .conditional_interface

namespace G8BookIIICh23TauCircleCanonicalAnglePeriodConstructor

/-- The canonical map induced by an angle-period constructor. -/
def toCanonical
    (source : G8BookIIICh23TauCircleCanonicalAnglePeriodConstructor) :
    UnitAddCircle → TauCircleCanonicalPoint :=
  fun p => TauCircleCanonicalPoint.ofBoundedAngle (source.toBoundedAngle p)

/-- An angle-period constructor supplies the canonical parametrization
    completeness source. -/
def toParametrizationCompletenessSource
    (source : G8BookIIICh23TauCircleCanonicalAnglePeriodConstructor) :
    G8BookIIICh23TauCircleCanonicalParametrizationCompletenessSource where
  toCanonical := source.toCanonical
  fromCanonical := source.fromCanonical
  left_inv := source.left_inv
  right_inv := source.right_inv
  basepoint_preserving := by
    rw [G8BookIIICh23TauCircleCanonicalAnglePeriodConstructor.toCanonical,
      source.basepoint_angle_preserving]
    exact TauCircleCanonicalPoint.ofBoundedAngle_zero
  lobeTopologyAgreement := source.lobeTopologyAgreement
  lobeTopologyAgreementEvidence := source.lobeTopologyAgreementEvidence
  lobeMetricAgreement := source.lobeMetricAgreement
  lobeMetricAgreementEvidence := source.lobeMetricAgreementEvidence
  lobeCompactnessAgreement := source.lobeCompactnessAgreement
  lobeCompactnessAgreementEvidence :=
    source.lobeCompactnessAgreementEvidence
  anglePeriodBridge := source.anglePeriodBridge
  anglePeriodBridgeEvidence := source.anglePeriodBridgeEvidence
  canonicalParametrizationComplete :=
    source.canonicalParametrizationComplete
  canonicalParametrizationCompleteEvidence :=
    source.canonicalParametrizationCompleteEvidence
  status := source.status

/-- An angle-period constructor supplies the canonical lobe equivalence. -/
def toCanonicalLobeEquivalence
    (source : G8BookIIICh23TauCircleCanonicalAnglePeriodConstructor) :
    G8BookIIICh23UnitAddCircleTauCircleCanonicalLobeEquivalence :=
  source.toParametrizationCompletenessSource.toCanonicalLobeEquivalence

/-- An angle-period constructor discharges the canonical lobe target. -/
theorem toCanonicalLobeEquivalenceTarget
    (source : G8BookIIICh23TauCircleCanonicalAnglePeriodConstructor) :
    G8BookIIICh23UnitAddCircleTauCircleCanonicalLobeEquivalenceTarget :=
  source.toParametrizationCompletenessSource.toCanonicalLobeEquivalenceTarget

end G8BookIIICh23TauCircleCanonicalAnglePeriodConstructor

/-- Target form of the exact angle-period constructor. -/
def G8BookIIICh23TauCircleCanonicalAnglePeriodConstructorTarget : Prop :=
  Nonempty G8BookIIICh23TauCircleCanonicalAnglePeriodConstructor

/-- The angle-period constructor is exactly sufficient for canonical
    parametrization completeness. -/
theorem
    g8BookIIICh23TauCircleCanonicalAnglePeriodConstructorTarget_toParametrization
    (target : G8BookIIICh23TauCircleCanonicalAnglePeriodConstructorTarget) :
    G8BookIIICh23TauCircleCanonicalParametrizationCompletenessTarget := by
  rcases target with ⟨source⟩
  exact ⟨source.toParametrizationCompletenessSource⟩

/-- The angle-period constructor is exactly sufficient for the canonical lobe
    equivalence target. -/
theorem
    g8BookIIICh23TauCircleCanonicalAnglePeriodConstructorTarget_toLobeTarget
    (target : G8BookIIICh23TauCircleCanonicalAnglePeriodConstructorTarget) :
    G8BookIIICh23UnitAddCircleTauCircleCanonicalLobeEquivalenceTarget :=
  g8BookIIICh23TauCircleCanonicalParametrizationCompletenessTarget_toLobeTarget
    (g8BookIIICh23TauCircleCanonicalAnglePeriodConstructorTarget_toParametrization
      target)

-- ============================================================
-- GUARDRAIL: STATUS FIBERS ARE CLOSED, ANGLE BRIDGE REMAINS
-- ============================================================

/-- Status-normalization is theorem-backed for canonical points.  This is the
    part that the raw `TauCirclePoint` carrier could not provide. -/
theorem g8TauCircleCanonicalPoint_hasTauNativeStatusRepresentative
    (c : TauCircleCanonicalPoint) :
    ∃ p : TauCirclePoint,
      p.sourceStatus = TauCircleParamStatus.tauNativeTrigInterface ∧
      TauCircleUnitMagnitude p.value ∧
      TauCircleCanonicalPoint.mk p = c :=
  TauCircleCanonicalPoint.exists_tauNativeStatus_rep c

/-- The canonical base point has no remaining source-status fiber. -/
theorem g8TauCircleCanonicalBase_receivingStatus_eq_base :
    TauCircleCanonicalPoint.mk
        (g8TauCirclePointBaseWithStatus
          TauCircleParamStatus.receivingBridge) =
      TauCircleCanonicalPoint.base :=
  g8TauCirclePointBaseWithReceivingStatus_canonical_eq_base

/-- Diagnostic surface for the remaining payload: a canonical status-normalized
    representative alone does not construct an additive-circle equivalence.

The missing fields name the actual next theorem: turn Mathlib's real
additive-circle coordinate into a tau-native bounded angle, prove period
respect, and prove the inverse/readout law on the canonical quotient. -/
structure G8BookIIICh23CanonicalStatusNormalizationWithoutAngleBridge where
  canonicalPoint : TauCircleCanonicalPoint
  statusRepresentative :
    ∃ p : TauCirclePoint,
      p.sourceStatus = TauCircleParamStatus.tauNativeTrigInterface ∧
      TauCircleUnitMagnitude p.value ∧
      TauCircleCanonicalPoint.mk p = canonicalPoint
  noCanonicalLobeEquivalence :
    ¬ G8BookIIICh23UnitAddCircleTauCircleCanonicalLobeEquivalenceTarget

theorem
    G8BookIIICh23CanonicalStatusNormalizationWithoutAngleBridge.refutesTarget
    (gap :
      G8BookIIICh23CanonicalStatusNormalizationWithoutAngleBridge) :
    ¬ G8BookIIICh23UnitAddCircleTauCircleCanonicalLobeEquivalenceTarget :=
  gap.noCanonicalLobeEquivalence

end Tau.BookIII.Bridge
