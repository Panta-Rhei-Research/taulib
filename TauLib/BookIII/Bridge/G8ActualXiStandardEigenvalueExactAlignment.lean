import TauLib.BookIII.Bridge.G8ActualXiStandardEigenvalueMembershipReduction
import TauLib.BookIII.Bridge.G8ActualXiCanonicalAbstractSpectralMembershipSource

/-!
# TauLib.BookIII.Bridge.G8ActualXiStandardEigenvalueExactAlignment

First-class L3b-E surface for exact standard-eigenvalue alignment.

The preceding reduction split the remaining standard-mode payload into:

* L3b-M: select a standard lemniscate mode for each actual nonzero-height
  canonical `xi` carrier;
* L3b-E: prove exact equality with the standard lemniscate eigenvalue at that
  selected mode.

This module isolates L3b-E as the proof-facing source needed downstream.  It
also records the key guardrail from the red-team pass: the weaker abstract
self-adjoint route proves real-valuedness once supplied, but it does not
construct exact membership in the discrete standard eigenvalue readout.
-/

set_option autoImplicit false

noncomputable section

namespace Tau.BookIII.Bridge

-- ============================================================
-- L3b-E EXACT ALIGNMENT SOURCE
-- ============================================================

/-- First-class L3b-E package: a selected standard mode together with exact
    equality between the canonical scaled value and the selected standard
    lemniscate eigenvalue. -/
structure G8ActualXiCanonicalSelectedModeExactAlignmentSource
    (operatorCtx : LemniscateOperatorContext)
    (operatorReady : LemniscateOperatorReady operatorCtx) where
  selection :
    G8ActualXiCanonicalStandardModeSelectionSource
      operatorCtx operatorReady
  exactAlignment :
    G8ActualXiCanonicalSelectedModeEigenvalueAlignment selection

/-- The L3b-E source is exactly the existing split source, viewed with the
    equality field in the foreground. -/
def G8ActualXiCanonicalSelectedModeExactAlignmentSource.toSplitSource
    {operatorCtx : LemniscateOperatorContext}
    {operatorReady : LemniscateOperatorReady operatorCtx}
    (source :
      G8ActualXiCanonicalSelectedModeExactAlignmentSource
        operatorCtx operatorReady) :
    G8ActualXiCanonicalStandardEigenvalueMembershipSplitSource
      operatorCtx operatorReady where
  selection := source.selection
  exactAlignment := source.exactAlignment

/-- Any existing split source can be re-read as the first-class L3b-E source. -/
def G8ActualXiCanonicalSelectedModeExactAlignmentSource.ofSplitSource
    {operatorCtx : LemniscateOperatorContext}
    {operatorReady : LemniscateOperatorReady operatorCtx}
    (source :
      G8ActualXiCanonicalStandardEigenvalueMembershipSplitSource
        operatorCtx operatorReady) :
    G8ActualXiCanonicalSelectedModeExactAlignmentSource
      operatorCtx operatorReady where
  selection := source.selection
  exactAlignment := source.exactAlignment

/-- The first-class L3b-E source packages the existing standard-eigenvalue
    membership source. -/
def G8ActualXiCanonicalSelectedModeExactAlignmentSource.toMembershipSource
    {operatorCtx : LemniscateOperatorContext}
    {operatorReady : LemniscateOperatorReady operatorCtx}
    (source :
      G8ActualXiCanonicalSelectedModeExactAlignmentSource
        operatorCtx operatorReady) :
    G8ActualXiCanonicalStandardEigenvalueMembershipSource
      operatorCtx operatorReady :=
  source.toSplitSource.toMembershipSource

/-- The first-class L3b-E source supplies the standard eigenvalue index source. -/
def G8ActualXiCanonicalSelectedModeExactAlignmentSource.toStandardEigenvalueIndexSource
    {operatorCtx : LemniscateOperatorContext}
    {operatorReady : LemniscateOperatorReady operatorCtx}
    (source :
      G8ActualXiCanonicalSelectedModeExactAlignmentSource
        operatorCtx operatorReady) :
    G8ActualXiIotaTauCanonicalStandardEigenvalueIndexSource
      operatorCtx operatorReady :=
  source.toSplitSource.toStandardEigenvalueIndexSource

/-- The first-class L3b-E source supplies the old standard-eigenvalue
    membership target. -/
theorem G8ActualXiCanonicalSelectedModeExactAlignmentSource.toMembershipTarget
    {operatorCtx : LemniscateOperatorContext}
    {operatorReady : LemniscateOperatorReady operatorCtx}
    (source :
      G8ActualXiCanonicalSelectedModeExactAlignmentSource
        operatorCtx operatorReady) :
    G8ActualXiIotaTauCanonicalStandardEigenvalueMembershipTarget
      operatorCtx operatorReady :=
  source.toSplitSource.toMembershipTarget

/-- The first-class L3b-E source is sufficient for nonzero-height spectral
    parameter reality through the already theorem-backed standard-spectrum
    real-valuedness corridor. -/
theorem G8ActualXiCanonicalSelectedModeExactAlignmentSource.toSpectralParameterReal
    {operatorCtx : LemniscateOperatorContext}
    {operatorReady : LemniscateOperatorReady operatorCtx}
    (source :
      G8ActualXiCanonicalSelectedModeExactAlignmentSource
        operatorCtx operatorReady) :
    G8ActualXiNonzeroHeightSpectralParameterReal :=
  source.toSplitSource.toSpectralParameterReal

/-- Prop-valued first-class L3b-E target.  This is equivalent to the previous
    standard-eigenvalue membership target, but names the exact alignment payload
    directly. -/
def G8ActualXiCanonicalSelectedModeExactAlignmentTarget
    (operatorCtx : LemniscateOperatorContext)
    (operatorReady : LemniscateOperatorReady operatorCtx) : Prop :=
  Nonempty
    (G8ActualXiCanonicalSelectedModeExactAlignmentSource
      operatorCtx operatorReady)

/-- The exact-alignment target is equivalent to the split target. -/
theorem
    g8ActualXiCanonicalSelectedModeExactAlignmentTarget_iff_splitTarget
    {operatorCtx : LemniscateOperatorContext}
    {operatorReady : LemniscateOperatorReady operatorCtx} :
    G8ActualXiCanonicalSelectedModeExactAlignmentTarget
      operatorCtx operatorReady ↔
    G8ActualXiCanonicalStandardEigenvalueMembershipSplitTarget
      operatorCtx operatorReady := by
  constructor
  · intro h
    rcases h with ⟨source⟩
    exact ⟨source.toSplitSource⟩
  · intro h
    rcases h with ⟨source⟩
    exact ⟨G8ActualXiCanonicalSelectedModeExactAlignmentSource.ofSplitSource
      source⟩

/-- The exact-alignment target is equivalent to the older standard-eigenvalue
    membership target. -/
theorem
    g8ActualXiCanonicalSelectedModeExactAlignmentTarget_iff_membershipTarget
    {operatorCtx : LemniscateOperatorContext}
    {operatorReady : LemniscateOperatorReady operatorCtx} :
    G8ActualXiCanonicalSelectedModeExactAlignmentTarget
      operatorCtx operatorReady ↔
    G8ActualXiIotaTauCanonicalStandardEigenvalueMembershipTarget
      operatorCtx operatorReady := by
  rw [g8ActualXiCanonicalSelectedModeExactAlignmentTarget_iff_splitTarget]
  exact
    (g8ActualXiCanonicalStandardEigenvalueMembershipTarget_iff_splitTarget
      (operatorCtx := operatorCtx)
      (operatorReady := operatorReady)).symm

-- ============================================================
-- POINTWISE CONSEQUENCES OF L3b-E
-- ============================================================

/-- L3b-E gives pointwise membership in the standard lemniscate spectrum. -/
theorem G8ActualXiCanonicalSelectedModeExactAlignmentSource.standardSpectrumMember
    {operatorCtx : LemniscateOperatorContext}
    {operatorReady : LemniscateOperatorReady operatorCtx}
    (source :
      G8ActualXiCanonicalSelectedModeExactAlignmentSource
        operatorCtx operatorReady)
    (z : G8ActualXiNonzeroHeightCarrier) :
    G8StandardLemniscateEigenvalueSpectrum
      operatorCtx operatorReady
      (g8ActualXiIotaTauCanonicalScaledOperatorSpectralValue z) :=
  ⟨source.selection.modeOf z, source.exactAlignment z⟩

/-- L3b-E forces the canonical scaled value to be real-valued pointwise. -/
theorem G8ActualXiCanonicalSelectedModeExactAlignmentSource.canonicalValue_im_eq_zero
    {operatorCtx : LemniscateOperatorContext}
    {operatorReady : LemniscateOperatorReady operatorCtx}
    (source :
      G8ActualXiCanonicalSelectedModeExactAlignmentSource
        operatorCtx operatorReady)
    (z : G8ActualXiNonzeroHeightCarrier) :
    (g8ActualXiIotaTauCanonicalScaledOperatorSpectralValue z).im = 0 :=
  g8StandardLemniscateEigenvalueSpectrum_real
    (g8ActualXiIotaTauCanonicalScaledOperatorSpectralValue z)
    (source.standardSpectrumMember z)

/-- L3b-E is stronger than bare reality: it forces the canonical value to be
    the complex readout of the selected natural-square eigenvalue. -/
theorem G8ActualXiCanonicalSelectedModeExactAlignmentSource.canonicalValue_eq_selectedNatSquare
    {operatorCtx : LemniscateOperatorContext}
    {operatorReady : LemniscateOperatorReady operatorCtx}
    (source :
      G8ActualXiCanonicalSelectedModeExactAlignmentSource
        operatorCtx operatorReady)
    (z : G8ActualXiNonzeroHeightCarrier) :
    g8ActualXiIotaTauCanonicalScaledOperatorSpectralValue z =
      ((source.selection.modeOf z * source.selection.modeOf z : Nat) : ℂ) := by
  simpa [Tau.BookIII.Doors.lemniscate_eigenvalue]
    using source.exactAlignment z

-- ============================================================
-- GUARDRAILS
-- ============================================================

/-- The abstract self-adjoint route plus a selected-mode handle still does not
    supply L3b-E unless exact standard-eigenvalue alignment is separately
    proved. -/
structure G8ActualXiAbstractRouteWithoutSelectedStandardAlignment
    (operatorCtx : LemniscateOperatorContext)
    (operatorReady : LemniscateOperatorReady operatorCtx) where
  abstractRoute :
    G8ActualXiCanonicalAbstractSelfAdjointRouteSource
      operatorCtx operatorReady
  selection :
    G8ActualXiCanonicalStandardModeSelectionSource
      operatorCtx operatorReady
  noExactAlignment :
    ¬ G8ActualXiCanonicalSelectedModeEigenvalueAlignment selection

/-- A claimed exact-alignment source using the same selected mode is refuted by
    an abstract-route witness that explicitly lacks selected-mode alignment. -/
theorem
    G8ActualXiAbstractRouteWithoutSelectedStandardAlignment.refutesSameSelectionExactAlignment
    {operatorCtx : LemniscateOperatorContext}
    {operatorReady : LemniscateOperatorReady operatorCtx}
    (w :
      G8ActualXiAbstractRouteWithoutSelectedStandardAlignment
        operatorCtx operatorReady)
    (source :
      G8ActualXiCanonicalSelectedModeExactAlignmentSource
        operatorCtx operatorReady)
    (hSelection : source.selection.modeOf = w.selection.modeOf) :
    False :=
  w.noExactAlignment (by
    intro z
    simpa [hSelection] using source.exactAlignment z)

/-- A pointwise non-real canonical value refutes any selected-mode exact
    alignment source. -/
structure G8ActualXiSelectedModeAlignmentNonrealFalsifier
    (operatorCtx : LemniscateOperatorContext)
    (operatorReady : LemniscateOperatorReady operatorCtx) where
  z : G8ActualXiNonzeroHeightCarrier
  nonreal :
    (g8ActualXiIotaTauCanonicalScaledOperatorSpectralValue z).im ≠ 0

/-- Non-real canonical values cannot be exactly aligned with standard
    lemniscate eigenvalues. -/
theorem G8ActualXiSelectedModeAlignmentNonrealFalsifier.refutesExactAlignment
    {operatorCtx : LemniscateOperatorContext}
    {operatorReady : LemniscateOperatorReady operatorCtx}
    (w :
      G8ActualXiSelectedModeAlignmentNonrealFalsifier
        operatorCtx operatorReady)
    (source :
      G8ActualXiCanonicalSelectedModeExactAlignmentSource
        operatorCtx operatorReady) :
    False :=
  w.nonreal (source.canonicalValue_im_eq_zero w.z)

/-- Exact alignment at a wrong selected mode is impossible. -/
structure G8ActualXiSelectedModeWrongNatSquareFalsifier
    {operatorCtx : LemniscateOperatorContext}
    {operatorReady : LemniscateOperatorReady operatorCtx}
    (selection :
      G8ActualXiCanonicalStandardModeSelectionSource
        operatorCtx operatorReady) where
  z : G8ActualXiNonzeroHeightCarrier
  notSelectedNatSquare :
    g8ActualXiIotaTauCanonicalScaledOperatorSpectralValue z ≠
      ((selection.modeOf z * selection.modeOf z : Nat) : ℂ)

/-- Failure of the selected natural-square equality refutes L3b-E for that
    selector. -/
theorem G8ActualXiSelectedModeWrongNatSquareFalsifier.refutesAlignment
    {operatorCtx : LemniscateOperatorContext}
    {operatorReady : LemniscateOperatorReady operatorCtx}
    {selection :
      G8ActualXiCanonicalStandardModeSelectionSource
        operatorCtx operatorReady}
    (w :
      G8ActualXiSelectedModeWrongNatSquareFalsifier
        selection)
    (alignment :
      G8ActualXiCanonicalSelectedModeEigenvalueAlignment selection) :
    False := by
  apply w.notSelectedNatSquare
  simpa [Tau.BookIII.Doors.lemniscate_eigenvalue] using alignment w.z

end Tau.BookIII.Bridge
