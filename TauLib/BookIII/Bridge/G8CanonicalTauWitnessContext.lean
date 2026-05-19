import TauLib.BookIII.Bridge.G8CanonicalBoundaryWitnessRealization

/-!
# TauLib.BookIII.Bridge.G8CanonicalTauWitnessContext

Canonical tau-witness carrier for the G8f off-axis corridor.

The preceding module defined canonical boundary witnesses: boundary normal
forms with finite primorial-stage provenance.  This module instantiates the
abstract tau-witness carrier of the weak pullback test with precisely those
canonical boundary witnesses.

The result is the first concrete tau-side witness carrier for the G8f route:

* `tauWitness` is `G8CanonicalBoundaryWitness`;
* `tauNormalForm` is projection to `.nf`;
* tau off-criticality is tau-critical imbalance of that normal form;
* the canonical boundary-witness model is the identity embedding.

Tau-side purity remains an external hypothesis.  This module does not prove
that all canonical boundary witnesses are excluded; it only proves that the
selected off-axis witness is represented in the canonical carrier and that the
existing corridor can consume this carrier without a raw `BoundaryNF` section.
-/

set_option autoImplicit false

namespace Tau.BookIII.Bridge

abbrev G8CanonicalTauWitnessCarrier : Type 2 :=
  ULift.{2, 0} G8CanonicalBoundaryWitness

-- ============================================================
-- CANONICAL TAU-WITNESS SOURCE DATA
-- ============================================================

/-- Source data for the canonical tau-witness carrier.

The orthodox side is still abstract: a later module must instantiate
`orthodoxZero` and the centered shadow source from the actual receiving-side
chart.  This record only fixes the tau-side carrier to provenance-backed
canonical boundary witnesses. -/
structure G8CanonicalTauWitnessSource where
  transfer : G8dZeroDivisorTransferContext
  orthodoxZero : Type 2
  isOrthodoxOffCriticalZero : orthodoxZero → Prop
  centeredShadow : orthodoxZero → CriticalAxisShadow
  offCritical_iff_notShadowAxis :
    ∀ z : orthodoxZero,
      isOrthodoxOffCriticalZero z ↔
        ¬ OnCriticalAxis (centeredShadow z)
  g3ZetaChartReadout :
    transfer.completion.chart.g3ZetaBridge
  g4CompletedXiReadout :
    transfer.completion.chart.g4AnalyticContinuation
  status : OffCriticalPullbackStatus := .conditionalInterface

-- ============================================================
-- CANONICAL CONTEXT INSTANTIATION
-- ============================================================

/-- Off-critical pullback context whose tau witnesses are canonical boundary
    witnesses. -/
def g8CanonicalTauWitness_base
    (source : G8CanonicalTauWitnessSource) :
    OffCriticalZeroPullbackContext where
  transfer := source.transfer
  orthodoxZero := source.orthodoxZero
  tauWitness := G8CanonicalTauWitnessCarrier
  isOrthodoxOffCriticalZero := source.isOrthodoxOffCriticalZero
  isTauOffCriticalWitness :=
    fun w => TauCriticalImbalance w.down.nf
  status := source.status

/-- G8e.1 test context induced by the canonical tau-witness carrier. -/
def g8CanonicalTauWitness_test
    (source : G8CanonicalTauWitnessSource) :
    OffCriticalPullbackTestContext where
  base := g8CanonicalTauWitness_base source
  orthodoxShadow := source.centeredShadow
  tauNormalForm := fun w => w.down.nf
  status := .conditionalPullbackAvailable

/-- Weak G8f pullback context induced by the canonical tau-witness carrier. -/
def g8CanonicalTauWitness_weak
    (source : G8CanonicalTauWitnessSource) :
    G8WeakOffCriticalPullbackTestContext where
  test := g8CanonicalTauWitness_test source
  finiteGuardrails := finiteG8bContext_guardrails
  status := .conditionalExclusionAvailable

/-- Orthodox shadow-axis source induced by the canonical tau-witness source. -/
def g8CanonicalTauWitness_shadowAxisSource
    (source : G8CanonicalTauWitnessSource) :
    G8OrthodoxShadowAxisSource
      (g8CanonicalTauWitness_weak source) where
  centeredShadow := source.centeredShadow
  shadowAgrees := by
    intro _z
    rfl
  offCritical_iff_notShadowAxis :=
    source.offCritical_iff_notShadowAxis
  g3ZetaChartReadout := source.g3ZetaChartReadout
  g4CompletedXiReadout := source.g4CompletedXiReadout
  finiteGuardrails := finiteG8bContext_guardrails

-- ============================================================
-- IDENTITY MODEL FOR CANONICAL BOUNDARY WITNESSES
-- ============================================================

/-- In the canonical tau-witness context, canonical boundary witnesses embed
    into the abstract carrier by identity. -/
def g8CanonicalTauWitness_boundaryModel
    (source : G8CanonicalTauWitnessSource) :
    G8CanonicalBoundaryWitnessModel
      (g8CanonicalTauWitness_weak source) where
  realizeCanonical := fun w => ULift.up w
  realizeCanonical_normalForm := by
    intro _w
    rfl

/-- The canonical context realizes the chart-selected canonical boundary
    witness in the abstract tau-witness carrier. -/
def g8CanonicalTauWitness_selectedRealization
    (source : G8CanonicalTauWitnessSource) :
    G8TauShadowSelectedNormalFormRealization
      (g8CanonicalTauWitness_shadowAxisSource source) :=
  g8CanonicalBoundaryWitnessModel_to_shadowSelectedRealization
    (g8CanonicalTauWitness_boundaryModel source)
    (g8TauShadowSelectedCanonicalBoundaryRealization
      (g8CanonicalTauWitness_shadowAxisSource source))

/-- The canonical context puts selected off-axis normal forms in the witness
    image. -/
theorem g8CanonicalTauWitness_selectedNormalFormsInImage
    (source : G8CanonicalTauWitnessSource) :
    G8TauSelectedNormalFormsInWitnessImage
      (g8CanonicalTauWitness_shadowAxisSource source) :=
  g8CanonicalBoundaryWitnessModel_selectedNormalFormsInWitnessImage
    (g8CanonicalTauWitness_boundaryModel source)
    (g8TauShadowSelectedCanonicalBoundaryRealization
      (g8CanonicalTauWitness_shadowAxisSource source))

/-- In the canonical context, tau-critical imbalance directly realizes the
    tau off-critical witness predicate. -/
theorem g8CanonicalTauWitness_tauWitnessRealization
    (source : G8CanonicalTauWitnessSource) :
    G8OffAxisTauWitnessRealization
      (g8OrthodoxShadowAxisSource_to_chart
        (g8CanonicalTauWitness_shadowAxisSource source)) := by
  intro _w hImbalance
  exact hImbalance

/-- The canonical context has no off-axis chart-only ghost: the selected
    off-axis canonical boundary witness is always available. -/
theorem g8CanonicalTauWitness_offAxisGuard
    (source : G8CanonicalTauWitnessSource) :
    G8OffAxisChartOnlyGhostGuard
      (g8OrthodoxShadowAxisSource_to_chart
        (g8CanonicalTauWitness_shadowAxisSource source)) := by
  intro hGhost
  rcases hGhost with ⟨ghost⟩
  exact
    ghost.noTauPreimage
      (ULift.up g8TauSampleOffAxisCanonicalBoundaryWitness)
      g8TauSampleOffAxisBoundaryNF_criticalImbalance

-- ============================================================
-- CORRIDOR ADAPTERS
-- ============================================================

/-- Canonical boundary-witness realization context induced by the canonical
    tau-witness carrier. -/
def g8CanonicalTauWitness_realizationContext
    (source : G8CanonicalTauWitnessSource) :
    G8CanonicalBoundaryWitnessRealizationContext
      (g8CanonicalTauWitness_weak source) where
  source := g8CanonicalTauWitness_shadowAxisSource source
  witnessModel := g8CanonicalTauWitness_boundaryModel source
  selected :=
    g8TauShadowSelectedCanonicalBoundaryRealization
      (g8CanonicalTauWitness_shadowAxisSource source)
  tauWitness := g8CanonicalTauWitness_tauWitnessRealization source
  offAxisGuard := g8CanonicalTauWitness_offAxisGuard source

/-- The canonical tau-witness carrier yields the local one-sided pullback. -/
theorem g8CanonicalTauWitness_yields_pullback
    (source : G8CanonicalTauWitnessSource) :
    G8eOffCriticalPullback
      (g8CanonicalTauWitness_base source) :=
  g8CanonicalBoundaryWitnessRealization_yields_pullback
    (g8CanonicalTauWitness_weak source)
    (g8CanonicalTauWitness_realizationContext source)

/-- The canonical tau-witness carrier plus tau-side purity yields local
    no-off-critical orthodox zeros. -/
theorem g8CanonicalTauWitness_noOffCriticalZeros
    (source : G8CanonicalTauWitnessSource)
    (tauPurity :
      G8eTauPurityExcludesOffCritical
        (g8CanonicalTauWitness_base source)) :
    G8eNoOrthodoxOffCriticalZeros
      (g8CanonicalTauWitness_base source) :=
  g8CanonicalBoundaryWitnessRealization_noOffCriticalZeros
    (g8CanonicalTauWitness_weak source)
    (g8CanonicalTauWitness_realizationContext source)
    tauPurity

/-- The canonical tau-witness carrier can be consumed as a weak exclusion
    transfer context once tau-side purity is supplied. -/
def g8CanonicalTauWitness_to_exclusionTransferContext
    (source : G8CanonicalTauWitnessSource)
    (tauPurity :
      G8eTauPurityExcludesOffCritical
        (g8CanonicalTauWitness_base source)) :
    G8OffCriticalExclusionTransferContext where
  base := g8CanonicalTauWitness_base source
  offCriticalChartAdmissible :=
    G8OffAxisChartOnlyGhostGuard
      (g8OrthodoxShadowAxisSource_to_chart
        (g8CanonicalTauWitness_shadowAxisSource source))
  offCriticalPullback :=
    g8CanonicalTauWitness_yields_pullback source
  tauPurity := tauPurity
  finiteGuardrails := finiteG8bContext_guardrails
  status := .conditionalExclusionAvailable

/-- The canonical tau-witness exclusion-transfer context is admissible by its
    theorem-backed off-axis guard. -/
theorem g8CanonicalTauWitness_exclusionTransferAdmissible
    (source : G8CanonicalTauWitnessSource)
    (tauPurity :
      G8eTauPurityExcludesOffCritical
        (g8CanonicalTauWitness_base source)) :
    G8OffCriticalExclusionTransferAdmissible
      (g8CanonicalTauWitness_to_exclusionTransferContext
        source tauPurity) :=
  g8CanonicalTauWitness_offAxisGuard source

-- ============================================================
-- FALSIFIER CLOSURE FOR THE CANONICAL CARRIER
-- ============================================================

/-- In the canonical carrier, no canonical boundary witness is outside the
    abstract tau-witness image. -/
theorem
    g8CanonicalBoundaryWitnessOutsideAbstractImage_refutes_canonicalCarrier
    (source : G8CanonicalTauWitnessSource)
    (w :
      G8CanonicalBoundaryWitnessOutsideAbstractImage
        (g8CanonicalTauWitness_weak source)) :
    False :=
  w.noAbstractWitness (ULift.up w.witness) rfl

/-- In the canonical carrier, a selected normal form cannot be unrealized. -/
theorem
    g8TauShadowSelectedNormalFormUnrealized_refutes_canonicalCarrier
    (source : G8CanonicalTauWitnessSource)
    (w :
      G8TauShadowSelectedNormalFormUnrealized
        (g8CanonicalTauWitness_shadowAxisSource source)) :
    False :=
  g8TauShadowSelectedNormalFormUnrealized_refutes_realization w
    (g8CanonicalTauWitness_selectedRealization source)

end Tau.BookIII.Bridge
