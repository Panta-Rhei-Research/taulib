import TauLib.BookIII.Bridge.G8BookIIICh23UnitAddCircleTauNativeMetricTopologyTransfer

/-!
# TauLib.BookIII.Bridge.G8BookIIICh23TauCircleParametrizationCompletenessRealityCheck

Reality check for the last A1.1 lobe-equivalence stone.

The current tau-native lobe carrier is the raw presentation type
`TauCirclePoint`.  It stores a bounded angle, a tau-complex value, a
unit-magnitude proof, and a source-status tag.  Therefore the load-bearing
target

```text
UnitAddCircle ≃ TauCirclePoint
```

is stronger than a semantic circle parametrization theorem: it must account for
every raw presentation inhabitant, not only the canonical tau-cis image.

This module proves the precise guardrail.  A parametrization whose image is
status-canonical cannot be surjective onto the current raw carrier, because the
raw carrier contains noncanonical status variants of the same base circle data.
No downstream A1.1 target is weakened or discharged here.
-/

set_option autoImplicit false

namespace Tau.BookIII.Bridge

open Tau.Boundary

-- ============================================================
-- RAW PRESENTATION FIBER
-- ============================================================

/-- The base tau-circle data with an arbitrary presentation status. -/
def g8TauCirclePointBaseWithStatus
    (status : TauCircleParamStatus) : TauCirclePoint where
  param := BoundedTauAngle.zero
  value := TauComplex.cisTauReal TauReal.zero
  unitMagnitude := by
    exact TauComplex.cisTauReal_magSq_equiv_one
      TauReal.zero
      BoundedTauAngle.zero.bounded_one
  sourceStatus := status

@[simp] theorem g8TauCirclePointBaseWithStatus_sourceStatus
    (status : TauCircleParamStatus) :
    (g8TauCirclePointBaseWithStatus status).sourceStatus = status :=
  rfl

/-- The receiving-bridge status is a genuinely different raw presentation tag
    from the canonical tau-native trigonometric status. -/
theorem g8TauCircleParamStatus_receiving_ne_tauNative :
    TauCircleParamStatus.receivingBridge ≠
      TauCircleParamStatus.tauNativeTrigInterface := by
  intro h
  cases h

/-- The current raw tau-circle carrier contains a noncanonical status variant
    of the base point. -/
theorem g8TauCirclePointBaseWithReceivingStatus_ne_base :
    g8TauCirclePointBaseWithStatus TauCircleParamStatus.receivingBridge ≠
      TauCirclePoint.base := by
  intro h
  have hStatus := congrArg TauCirclePoint.sourceStatus h
  have hStatus' :
      TauCircleParamStatus.receivingBridge =
        TauCircleParamStatus.tauNativeTrigInterface := by
    exact hStatus
  exact g8TauCircleParamStatus_receiving_ne_tauNative hStatus'

/-- The canonical tau-circle quotient removes the raw source-status fiber at
    the base point.  This is the local positive counterpart to
    `g8TauCirclePointBaseWithReceivingStatus_ne_base`: the obstruction is raw
    presentation equality, not semantic circle equality. -/
theorem g8TauCirclePointBaseWithStatus_canonical_eq_base
    (status : TauCircleParamStatus) :
    TauCircleCanonicalPoint.mk (g8TauCirclePointBaseWithStatus status) =
      TauCircleCanonicalPoint.base :=
  TauCircleCanonicalPoint.eq_of_param_value
    (TauReal.equiv_refl _)
    (TauComplex.equiv_refl _)

/-- In particular, the receiving-bridge presentation of the base point becomes
    equal to the tau-native base point in the canonical quotient. -/
theorem g8TauCirclePointBaseWithReceivingStatus_canonical_eq_base :
    TauCircleCanonicalPoint.mk
        (g8TauCirclePointBaseWithStatus
          TauCircleParamStatus.receivingBridge) =
      TauCircleCanonicalPoint.base :=
  g8TauCirclePointBaseWithStatus_canonical_eq_base _

-- ============================================================
-- SEMANTIC PARAMETRIZATION GUARDRAIL
-- ============================================================

/-- A semantic strengthening of the raw parametrization source: every point in
    the image is a canonical tau-native trigonometric presentation.

This is the natural form of a `cis`-parametrization theorem, but it is not
surjective onto the current raw `TauCirclePoint` carrier. -/
structure G8BookIIICh23TauCircleStatusCanonicalParametrizationSource where
  source : G8BookIIICh23TauCircleParametrizationCompletenessSource
  image_statusCanonical :
    ∀ p : UnitAddCircle,
      (source.toTauCircle p).sourceStatus =
        TauCircleParamStatus.tauNativeTrigInterface

/-- A status-canonical parametrization cannot satisfy the existing raw
    right-inverse field for all `TauCirclePoint`s.

This is the key discipline check for A1.1: the remaining theorem cannot be a
plain semantic `cis` parametrization unless the tau-circle lobe carrier is first
canonicalized or quotiented. -/
theorem
    g8BookIIICh23TauCircleStatusCanonicalParametrizationSource_refutesRawSurjectivity :
    ¬ Nonempty G8BookIIICh23TauCircleStatusCanonicalParametrizationSource := by
  intro h
  rcases h with ⟨source⟩
  let ghost : TauCirclePoint :=
    g8TauCirclePointBaseWithStatus TauCircleParamStatus.receivingBridge
  have hRight :
      source.source.toTauCircle (source.source.fromTauCircle ghost) = ghost :=
    source.source.right_inv ghost
  have hStatusRight :
      (source.source.toTauCircle
        (source.source.fromTauCircle ghost)).sourceStatus =
        TauCircleParamStatus.receivingBridge := by
    simpa [ghost, g8TauCirclePointBaseWithStatus] using
      congrArg TauCirclePoint.sourceStatus hRight
  have hStatusCanonical :
      (source.source.toTauCircle
        (source.source.fromTauCircle ghost)).sourceStatus =
        TauCircleParamStatus.tauNativeTrigInterface :=
    source.image_statusCanonical (source.source.fromTauCircle ghost)
  have hImpossible :
      TauCircleParamStatus.receivingBridge =
        TauCircleParamStatus.tauNativeTrigInterface :=
    hStatusRight.symm.trans hStatusCanonical
  exact g8TauCircleParamStatus_receiving_ne_tauNative hImpossible

/-- Guardrail package: a raw presentation-status fiber cannot be ignored when
    attempting to prove `G8BookIIICh23TauCircleParametrizationCompletenessTarget`.
-/
structure G8BookIIICh23TauCircleRawStatusFiberGuardrail where
  noncanonicalBase :
    g8TauCirclePointBaseWithStatus TauCircleParamStatus.receivingBridge ≠
      TauCirclePoint.base
  semanticStatusCanonicalParametrizationRefuted :
    ¬ Nonempty G8BookIIICh23TauCircleStatusCanonicalParametrizationSource

/-- The raw-status guardrail is theorem-backed from the current carrier
    definition. -/
def g8BookIIICh23TauCircleRawStatusFiberGuardrail :
    G8BookIIICh23TauCircleRawStatusFiberGuardrail where
  noncanonicalBase :=
    g8TauCirclePointBaseWithReceivingStatus_ne_base
  semanticStatusCanonicalParametrizationRefuted :=
    g8BookIIICh23TauCircleStatusCanonicalParametrizationSource_refutesRawSurjectivity

end Tau.BookIII.Bridge
