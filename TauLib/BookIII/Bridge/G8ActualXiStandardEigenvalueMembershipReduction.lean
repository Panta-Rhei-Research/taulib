import TauLib.BookIII.Bridge.G8ActualXiStandardEigenvalueMembershipSource

/-!
# TauLib.BookIII.Bridge.G8ActualXiStandardEigenvalueMembershipReduction

Reduction layer for the remaining L3b standard-eigenvalue membership payload.

The previous source module named the exact theorem:

```text
actual nonzero-height canonical scaled xi value
  = standard lemniscate eigenvalue at some mode.
```

This module splits that payload into the two proof-facing components that are
useful for the last-mile audit:

* select a standard mode for each actual nonzero-height carrier;
* prove exact equality with the lemniscate eigenvalue at that selected mode.

The first component is bookkeeping unless paired with the second.  The second
component is the mathematical load-bearing equality.
-/

set_option autoImplicit false

noncomputable section

namespace Tau.BookIII.Bridge

-- ============================================================
-- L3b SPLIT SOURCE
-- ============================================================

/-- L3b-M: selected standard lemniscate mode for each actual nonzero-height
    canonical `xi` carrier.

This is not membership by itself; it becomes meaningful only with the exact
alignment field below. -/
structure G8ActualXiCanonicalStandardModeSelectionSource
    (_operatorCtx : LemniscateOperatorContext)
    (_operatorReady : LemniscateOperatorReady _operatorCtx) where
  modeOf : G8ActualXiCanonicalModeExtractionTarget
  diagnostics : G8ActualXiCanonicalStandardEigenvalueDiagnostics := {}

/-- L3b-E: exact equality between the canonical scaled value and the selected
    standard lemniscate eigenvalue. -/
def G8ActualXiCanonicalSelectedModeEigenvalueAlignment
    {operatorCtx : LemniscateOperatorContext}
    {operatorReady : LemniscateOperatorReady operatorCtx}
    (selection :
      G8ActualXiCanonicalStandardModeSelectionSource
        operatorCtx operatorReady) : Prop :=
  G8ActualXiCanonicalModeEigenvalueAlignmentTarget selection.modeOf

/-- L3b split package: selected modes plus exact eigenvalue alignment. -/
structure G8ActualXiCanonicalStandardEigenvalueMembershipSplitSource
    (operatorCtx : LemniscateOperatorContext)
    (operatorReady : LemniscateOperatorReady operatorCtx) where
  selection :
    G8ActualXiCanonicalStandardModeSelectionSource
      operatorCtx operatorReady
  exactAlignment :
    G8ActualXiCanonicalSelectedModeEigenvalueAlignment selection

/-- Prop-valued split target equivalent to the existing standard-eigenvalue
    membership target. -/
def G8ActualXiCanonicalStandardEigenvalueMembershipSplitTarget
    (operatorCtx : LemniscateOperatorContext)
    (operatorReady : LemniscateOperatorReady operatorCtx) : Prop :=
  Nonempty
    (G8ActualXiCanonicalStandardEigenvalueMembershipSplitSource
      operatorCtx operatorReady)

/-- Standalone L3b-M target: a standard-mode selector exists for every actual
    nonzero-height canonical value.

This target is deliberately weak.  It records the mode handle only; exact
membership requires the selected-mode eigenvalue alignment below. -/
def G8ActualXiCanonicalStandardModeSelectionTarget
    (operatorCtx : LemniscateOperatorContext)
    (operatorReady : LemniscateOperatorReady operatorCtx) : Prop :=
  Nonempty
    (G8ActualXiCanonicalStandardModeSelectionSource
      operatorCtx operatorReady)

/-- L3b-M has no spectral force by itself: a selector surface can always be
    populated.  The load-bearing theorem is alignment with the selected mode. -/
def g8ActualXiCanonicalStandardModeSelectionTarget_default
    (operatorCtx : LemniscateOperatorContext)
    (operatorReady : LemniscateOperatorReady operatorCtx) :
    G8ActualXiCanonicalStandardModeSelectionTarget
      operatorCtx operatorReady :=
  ⟨{ modeOf := fun _ => 0 }⟩

/-- A concrete selection source gives the standalone L3b-M target. -/
def G8ActualXiCanonicalStandardModeSelectionSource.toSelectionTarget
    {operatorCtx : LemniscateOperatorContext}
    {operatorReady : LemniscateOperatorReady operatorCtx}
    (selection :
      G8ActualXiCanonicalStandardModeSelectionSource
        operatorCtx operatorReady) :
    G8ActualXiCanonicalStandardModeSelectionTarget
      operatorCtx operatorReady :=
  ⟨selection⟩

/-- A selected mode plus exact eigenvalue alignment is exactly the split source
    needed for standard-eigenvalue membership. -/
def G8ActualXiCanonicalStandardModeSelectionSource.toSplitSource
    {operatorCtx : LemniscateOperatorContext}
    {operatorReady : LemniscateOperatorReady operatorCtx}
    (selection :
      G8ActualXiCanonicalStandardModeSelectionSource
        operatorCtx operatorReady)
    (alignment :
      G8ActualXiCanonicalSelectedModeEigenvalueAlignment selection) :
    G8ActualXiCanonicalStandardEigenvalueMembershipSplitSource
      operatorCtx operatorReady where
  selection := selection
  exactAlignment := alignment

/-- The split target is equivalent to the existence of a selected mode together
    with exact alignment at that selected mode. -/
theorem
    g8ActualXiCanonicalStandardEigenvalueSplitTarget_iff_existsSelectedAlignment
    {operatorCtx : LemniscateOperatorContext}
    {operatorReady : LemniscateOperatorReady operatorCtx} :
    G8ActualXiCanonicalStandardEigenvalueMembershipSplitTarget
      operatorCtx operatorReady ↔
    ∃ selection :
      G8ActualXiCanonicalStandardModeSelectionSource
        operatorCtx operatorReady,
      G8ActualXiCanonicalSelectedModeEigenvalueAlignment selection := by
  constructor
  · intro hSplit
    rcases hSplit with ⟨source⟩
    exact ⟨source.selection, source.exactAlignment⟩
  · intro hExists
    rcases hExists with ⟨selection, alignment⟩
    exact ⟨selection.toSplitSource alignment⟩

-- ============================================================
-- ADAPTERS
-- ============================================================

/-- A split source packages the existing global standard-eigenvalue membership
    source. -/
def
    G8ActualXiCanonicalStandardEigenvalueMembershipSplitSource.toMembershipSource
    {operatorCtx : LemniscateOperatorContext}
    {operatorReady : LemniscateOperatorReady operatorCtx}
    (source :
      G8ActualXiCanonicalStandardEigenvalueMembershipSplitSource
        operatorCtx operatorReady) :
    G8ActualXiCanonicalStandardEigenvalueMembershipSource
      operatorCtx operatorReady where
  certificateOf := fun z =>
    { mode := source.selection.modeOf z
      canonicalValue_eq_eigenvalue := source.exactAlignment z }
  diagnostics := source.selection.diagnostics

/-- The existing global source exposes the split mode-selection/equality
    package. -/
def
    G8ActualXiCanonicalStandardEigenvalueMembershipSource.toSplitSource
    {operatorCtx : LemniscateOperatorContext}
    {operatorReady : LemniscateOperatorReady operatorCtx}
    (source :
      G8ActualXiCanonicalStandardEigenvalueMembershipSource
        operatorCtx operatorReady) :
    G8ActualXiCanonicalStandardEigenvalueMembershipSplitSource
      operatorCtx operatorReady where
  selection :=
    { modeOf := source.modeOf
      diagnostics := source.diagnostics }
  exactAlignment := source.modeAlignment

/-- A standard-eigenvalue membership target gives a split source by choosing the
    witnessing mode pointwise. -/
def
    g8ActualXiCanonicalStandardEigenvalueMembershipSplitSource_ofTarget
    (operatorCtx : LemniscateOperatorContext)
    (operatorReady : LemniscateOperatorReady operatorCtx)
    (target :
      G8ActualXiIotaTauCanonicalStandardEigenvalueMembershipTarget
        operatorCtx operatorReady) :
    G8ActualXiCanonicalStandardEigenvalueMembershipSplitSource
      operatorCtx operatorReady where
  selection :=
    { modeOf := fun z => Classical.choose (target z) }
  exactAlignment := by
    intro z
    exact Classical.choose_spec (target z)

/-- A split source proves the standard-eigenvalue membership target. -/
theorem
    G8ActualXiCanonicalStandardEigenvalueMembershipSplitSource.toMembershipTarget
    {operatorCtx : LemniscateOperatorContext}
    {operatorReady : LemniscateOperatorReady operatorCtx}
    (source :
      G8ActualXiCanonicalStandardEigenvalueMembershipSplitSource
        operatorCtx operatorReady) :
    G8ActualXiIotaTauCanonicalStandardEigenvalueMembershipTarget
      operatorCtx operatorReady :=
  source.toMembershipSource.toMembershipTarget

/-- The split target is equivalent to the existing standard-eigenvalue
    membership target. -/
theorem
    g8ActualXiCanonicalStandardEigenvalueMembershipTarget_iff_splitTarget
    {operatorCtx : LemniscateOperatorContext}
    {operatorReady : LemniscateOperatorReady operatorCtx} :
    G8ActualXiIotaTauCanonicalStandardEigenvalueMembershipTarget
      operatorCtx operatorReady ↔
    G8ActualXiCanonicalStandardEigenvalueMembershipSplitTarget
      operatorCtx operatorReady := by
  constructor
  · intro hTarget
    exact
      ⟨g8ActualXiCanonicalStandardEigenvalueMembershipSplitSource_ofTarget
        operatorCtx operatorReady hTarget⟩
  · intro hSplit
    rcases hSplit with ⟨source⟩
    exact source.toMembershipTarget

/-- A split source supplies the existing standard eigenvalue index source. -/
def
    G8ActualXiCanonicalStandardEigenvalueMembershipSplitSource.toStandardEigenvalueIndexSource
    {operatorCtx : LemniscateOperatorContext}
    {operatorReady : LemniscateOperatorReady operatorCtx}
    (source :
      G8ActualXiCanonicalStandardEigenvalueMembershipSplitSource
        operatorCtx operatorReady) :
    G8ActualXiIotaTauCanonicalStandardEigenvalueIndexSource
      operatorCtx operatorReady :=
  source.toMembershipSource.toStandardEigenvalueIndexSource

/-- A split source supplies nonzero-height spectral-parameter reality through
    the standard eigenvalue corridor. -/
theorem
    G8ActualXiCanonicalStandardEigenvalueMembershipSplitSource.toSpectralParameterReal
    {operatorCtx : LemniscateOperatorContext}
    {operatorReady : LemniscateOperatorReady operatorCtx}
    (source :
      G8ActualXiCanonicalStandardEigenvalueMembershipSplitSource
        operatorCtx operatorReady) :
    G8ActualXiNonzeroHeightSpectralParameterReal :=
  source.toMembershipSource.toSpectralParameterReal

-- ============================================================
-- RED-TEAM FALSIFIERS
-- ============================================================

/-- Mode selection alone does not prove membership when the selected mode is
    known not to align with the canonical value. -/
structure G8ActualXiCanonicalModeSelectionWithoutAlignment
    (operatorCtx : LemniscateOperatorContext)
    (operatorReady : LemniscateOperatorReady operatorCtx) where
  selection :
    G8ActualXiCanonicalStandardModeSelectionSource
      operatorCtx operatorReady
  z : G8ActualXiNonzeroHeightCarrier
  selectedMode_misaligned :
    g8ActualXiIotaTauCanonicalScaledOperatorSpectralValue z ≠
      (Tau.BookIII.Doors.lemniscate_eigenvalue
        (selection.modeOf z) : ℂ)

/-- Misalignment at the selected mode refutes a split source with the same
    selected mode at the carrier. -/
theorem
    G8ActualXiCanonicalModeSelectionWithoutAlignment.refutesSplitSource
    {operatorCtx : LemniscateOperatorContext}
    {operatorReady : LemniscateOperatorReady operatorCtx}
    (w :
      G8ActualXiCanonicalModeSelectionWithoutAlignment
        operatorCtx operatorReady)
    (source :
      G8ActualXiCanonicalStandardEigenvalueMembershipSplitSource
        operatorCtx operatorReady)
    (hSameMode : source.selection.modeOf w.z = w.selection.modeOf w.z) :
    False := by
  apply w.selectedMode_misaligned
  simpa [hSameMode] using source.exactAlignment w.z

/-- An alignment theorem cannot be weakened to mere mode extraction. -/
structure G8ActualXiCanonicalModeExtractionOnly
    (operatorCtx : LemniscateOperatorContext)
    (operatorReady : LemniscateOperatorReady operatorCtx) where
  selection :
    G8ActualXiCanonicalStandardModeSelectionSource
      operatorCtx operatorReady
  noExactAlignment :
    ¬ G8ActualXiCanonicalSelectedModeEigenvalueAlignment selection

/-- Mode extraction without exact alignment refutes a split source using the
    same selector. -/
theorem
    G8ActualXiCanonicalModeExtractionOnly.refutesSameSelectionSplitSource
    {operatorCtx : LemniscateOperatorContext}
    {operatorReady : LemniscateOperatorReady operatorCtx}
    (w :
      G8ActualXiCanonicalModeExtractionOnly
        operatorCtx operatorReady)
    (source :
      G8ActualXiCanonicalStandardEigenvalueMembershipSplitSource
        operatorCtx operatorReady)
    (hSelection : source.selection.modeOf = w.selection.modeOf) :
    False :=
  w.noExactAlignment (by
    intro z
    simpa [hSelection] using source.exactAlignment z)

/-- A split-source gap is exactly a gap in the standard-eigenvalue membership
    target. -/
structure G8ActualXiCanonicalStandardEigenvalueSplitGap
    (operatorCtx : LemniscateOperatorContext)
    (operatorReady : LemniscateOperatorReady operatorCtx) where
  noSplit :
    ¬ G8ActualXiCanonicalStandardEigenvalueMembershipSplitTarget
      operatorCtx operatorReady

/-- The split gap refutes the old membership target by equivalence. -/
theorem
    G8ActualXiCanonicalStandardEigenvalueSplitGap.refutesMembershipTarget
    {operatorCtx : LemniscateOperatorContext}
    {operatorReady : LemniscateOperatorReady operatorCtx}
    (w :
      G8ActualXiCanonicalStandardEigenvalueSplitGap
        operatorCtx operatorReady)
    (target :
      G8ActualXiIotaTauCanonicalStandardEigenvalueMembershipTarget
        operatorCtx operatorReady) :
    False :=
  w.noSplit
    ((g8ActualXiCanonicalStandardEigenvalueMembershipTarget_iff_splitTarget
      (operatorCtx := operatorCtx)
      (operatorReady := operatorReady)).mp target)

end Tau.BookIII.Bridge
