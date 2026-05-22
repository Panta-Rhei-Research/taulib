import TauLib.BookIII.Bridge.G8BookIIICh23FloorNormalizedA12FiniteLobeLengthLaw

/-!
# G8 Book III Ch.23 Floor-Normalized A1.2 Graph Measure Identification

This module closes the remaining selected-carrier graph-measure law fields
after the finite lobe-length law:

```text
crossing has zero length atom
+ canonical profile is the normalized two-lobe graph length measure
```

The result is still deliberately below Hilbert/L2 and Sobolev trace readiness.
It only constructs the selected graph-measure law needed by the A1.2 source.
-/

set_option autoImplicit false

namespace Tau.BookIII.Bridge

-- ============================================================
-- CROSSING ATOM AND TWO-LOBE GRAPH LENGTH READOUT
-- ============================================================

/-- The selected graph-length atom assigned to the glued crossing. -/
def g8BookIIICh23FloorNormalizedA12CrossingLengthAtom : ℝ :=
  0

/-- The glued crossing has zero selected graph length. -/
@[simp] theorem
    g8BookIIICh23FloorNormalizedA12CrossingLengthAtom_eq_zero :
    g8BookIIICh23FloorNormalizedA12CrossingLengthAtom = 0 :=
  rfl

/-- The canonical two-lobe graph-length readout induced by a finite lobe law. -/
def g8BookIIICh23FloorNormalizedA12TwoLobeGraphLengthMeasure
    (law : G8BookIIICh23FloorNormalizedA12FiniteLobeLengthLawSource)
    (sector : LemniscateSector) : ℝ :=
  law.budget.lobeLength sector

/-- The canonical two-lobe graph-length readout agrees with the finite lobe
    budget on each sector. -/
@[simp] theorem
    g8BookIIICh23FloorNormalizedA12TwoLobeGraphLengthMeasure_eq_budget
    (law : G8BookIIICh23FloorNormalizedA12FiniteLobeLengthLawSource)
    (sector : LemniscateSector) :
    g8BookIIICh23FloorNormalizedA12TwoLobeGraphLengthMeasure law sector =
      law.budget.lobeLength sector :=
  rfl

/-- The selected graph-measure total: crossing atom plus the two lobe lengths. -/
def g8BookIIICh23FloorNormalizedA12SelectedGraphMeasureTotal
    (law : G8BookIIICh23FloorNormalizedA12FiniteLobeLengthLawSource) : ℝ :=
  g8BookIIICh23FloorNormalizedA12CrossingLengthAtom +
    g8BookIIICh23FloorNormalizedA12TwoLobeGraphLengthMeasure law .plus +
      g8BookIIICh23FloorNormalizedA12TwoLobeGraphLengthMeasure law .minus

/-- The selected graph-measure total agrees with the finite lobe budget total. -/
theorem
    g8BookIIICh23FloorNormalizedA12SelectedGraphMeasureTotal_eq_budget
    (law : G8BookIIICh23FloorNormalizedA12FiniteLobeLengthLawSource) :
    g8BookIIICh23FloorNormalizedA12SelectedGraphMeasureTotal law =
      law.budget.totalLength := by
  rw [law.budget.totalLength_eq_sum]
  simp [g8BookIIICh23FloorNormalizedA12SelectedGraphMeasureTotal,
    g8BookIIICh23FloorNormalizedA12CrossingLengthAtom,
    g8BookIIICh23FloorNormalizedA12TwoLobeGraphLengthMeasure]

/-- The selected graph-measure total is exactly two. -/
theorem
    g8BookIIICh23FloorNormalizedA12SelectedGraphMeasureTotal_eq_two
    (law : G8BookIIICh23FloorNormalizedA12FiniteLobeLengthLawSource) :
    g8BookIIICh23FloorNormalizedA12SelectedGraphMeasureTotal law = 2 := by
  rw [g8BookIIICh23FloorNormalizedA12SelectedGraphMeasureTotal_eq_budget,
    law.totalLength_eq_two]

/-- The selected graph-measure total is nonnegative. -/
theorem
    g8BookIIICh23FloorNormalizedA12SelectedGraphMeasureTotal_nonnegative
    (law : G8BookIIICh23FloorNormalizedA12FiniteLobeLengthLawSource) :
    0 ≤ g8BookIIICh23FloorNormalizedA12SelectedGraphMeasureTotal law := by
  rw [g8BookIIICh23FloorNormalizedA12SelectedGraphMeasureTotal_eq_two]
  norm_num

-- ============================================================
-- CONCRETE GRAPH-MEASURE LAW PREDICATES
-- ============================================================

/-- Concrete crossing zero-atom predicate for the selected graph length. -/
def G8BookIIICh23FloorNormalizedA12CrossingZeroLengthAtom :
    Prop :=
  g8BookIIICh23FloorNormalizedA12CrossingLengthAtom = 0

/-- The concrete crossing zero-atom predicate is theorem-backed. -/
theorem
    g8BookIIICh23FloorNormalizedA12CrossingZeroLengthAtom_closed :
    G8BookIIICh23FloorNormalizedA12CrossingZeroLengthAtom :=
  g8BookIIICh23FloorNormalizedA12CrossingLengthAtom_eq_zero

/-- Concrete statement that the canonical selected profile is the two-lobe
    graph length measure induced by the finite lobe law. -/
def G8BookIIICh23FloorNormalizedA12CanonicalProfileIsTwoLobeGraphLength
    (law : G8BookIIICh23FloorNormalizedA12FiniteLobeLengthLawSource) :
    Prop :=
  law.budget.profile.weight =
      g8BookIIICh23FloorNormalizedA12GraphLengthWeight ∧
    G8BookIIICh23FloorNormalizedA12CrossingZeroLengthAtom ∧
    (∀ sector : LemniscateSector,
      g8BookIIICh23FloorNormalizedA12TwoLobeGraphLengthMeasure law sector =
        law.budget.lobeLength sector) ∧
    g8BookIIICh23FloorNormalizedA12SelectedGraphMeasureTotal law =
      law.budget.totalLength ∧
    g8BookIIICh23FloorNormalizedA12SelectedGraphMeasureTotal law = 2

/-- The canonical selected profile is the two-lobe graph length measure. -/
theorem
    g8BookIIICh23FloorNormalizedA12CanonicalProfileIsTwoLobeGraphLength_closed
    (law : G8BookIIICh23FloorNormalizedA12FiniteLobeLengthLawSource) :
    G8BookIIICh23FloorNormalizedA12CanonicalProfileIsTwoLobeGraphLength
      law :=
  ⟨law.budget.profile.weight_is_canonical,
    g8BookIIICh23FloorNormalizedA12CrossingZeroLengthAtom_closed,
    by intro sector; rfl,
    g8BookIIICh23FloorNormalizedA12SelectedGraphMeasureTotal_eq_budget law,
    g8BookIIICh23FloorNormalizedA12SelectedGraphMeasureTotal_eq_two law⟩

-- ============================================================
-- CLOSED GRAPH-MEASURE IDENTIFICATION SOURCE
-- ============================================================

/-- The theorem-backed crossing atom plus graph-measure identification package
    over the selected floor-normalized graph. -/
structure G8BookIIICh23FloorNormalizedA12GraphMeasureIdentificationSource where
  finiteLobeLaw :
    G8BookIIICh23FloorNormalizedA12FiniteLobeLengthLawSource
  crossingZeroLengthAtom :
    G8BookIIICh23FloorNormalizedA12CrossingZeroLengthAtom
  canonicalProfileIsTwoLobeGraphLength :
    G8BookIIICh23FloorNormalizedA12CanonicalProfileIsTwoLobeGraphLength
      finiteLobeLaw
  selectedGraphMeasureTotal_eq_two :
    g8BookIIICh23FloorNormalizedA12SelectedGraphMeasureTotal
      finiteLobeLaw = 2
  selectedGraphMeasureTotal_nonnegative :
    0 ≤
      g8BookIIICh23FloorNormalizedA12SelectedGraphMeasureTotal
        finiteLobeLaw
  status : SpineStatus := .conditional_interface

/-- Closed theorem-backed graph-measure identification source. -/
noncomputable def
    g8BookIIICh23FloorNormalizedA12GraphMeasureIdentificationSource_closed :
    G8BookIIICh23FloorNormalizedA12GraphMeasureIdentificationSource :=
  let law :=
    g8BookIIICh23FloorNormalizedA12FiniteLobeLengthLawSource_closed
  { finiteLobeLaw := law
    crossingZeroLengthAtom :=
      g8BookIIICh23FloorNormalizedA12CrossingZeroLengthAtom_closed
    canonicalProfileIsTwoLobeGraphLength :=
      g8BookIIICh23FloorNormalizedA12CanonicalProfileIsTwoLobeGraphLength_closed
        law
    selectedGraphMeasureTotal_eq_two :=
      g8BookIIICh23FloorNormalizedA12SelectedGraphMeasureTotal_eq_two law
    selectedGraphMeasureTotal_nonnegative :=
      g8BookIIICh23FloorNormalizedA12SelectedGraphMeasureTotal_nonnegative
        law
    status := .conditional_interface }

/-- Target for the selected graph-measure identification package. -/
def G8BookIIICh23FloorNormalizedA12GraphMeasureIdentificationTarget :
    Prop :=
  Nonempty G8BookIIICh23FloorNormalizedA12GraphMeasureIdentificationSource

/-- The selected graph-measure identification package is closed. -/
theorem
    g8BookIIICh23FloorNormalizedA12GraphMeasureIdentificationTarget_closed :
    G8BookIIICh23FloorNormalizedA12GraphMeasureIdentificationTarget :=
  ⟨g8BookIIICh23FloorNormalizedA12GraphMeasureIdentificationSource_closed⟩

-- ============================================================
-- ADAPTERS TO EXISTING GRAPH-MEASURE LAW SURFACES
-- ============================================================

/-- Graph-measure identification supplies the remaining crossing and
    graph-measure law source. -/
def
    G8BookIIICh23FloorNormalizedA12GraphMeasureIdentificationSource.toCrossingAndGraphMeasureLawSource
    (source :
      G8BookIIICh23FloorNormalizedA12GraphMeasureIdentificationSource) :
    G8BookIIICh23FloorNormalizedA12CrossingAndGraphMeasureLawSource where
  finiteLobeLaw := source.finiteLobeLaw
  crossingZeroLengthAtom :=
    G8BookIIICh23FloorNormalizedA12CrossingZeroLengthAtom
  crossingZeroLengthAtomEvidence :=
    source.crossingZeroLengthAtom
  graphMeasureIsTwoLobeLength :=
    G8BookIIICh23FloorNormalizedA12CanonicalProfileIsTwoLobeGraphLength
      source.finiteLobeLaw
  graphMeasureIsTwoLobeLengthEvidence :=
    source.canonicalProfileIsTwoLobeGraphLength
  status := source.status

/-- Graph-measure identification discharges the remaining crossing and graph
    measure target. -/
theorem
    G8BookIIICh23FloorNormalizedA12GraphMeasureIdentificationSource.toCrossingAndGraphMeasureLawTarget
    (source :
      G8BookIIICh23FloorNormalizedA12GraphMeasureIdentificationSource) :
    G8BookIIICh23FloorNormalizedA12CrossingAndGraphMeasureLawTarget :=
  ⟨source.toCrossingAndGraphMeasureLawSource⟩

/-- Graph-measure identification discharges the graph-length measure law
    target. -/
theorem
    G8BookIIICh23FloorNormalizedA12GraphMeasureIdentificationSource.toGraphLengthMeasureLawTarget
    (source :
      G8BookIIICh23FloorNormalizedA12GraphMeasureIdentificationSource) :
    G8BookIIICh23FloorNormalizedA12GraphLengthMeasureLawTarget :=
  source.toCrossingAndGraphMeasureLawSource.toGraphLengthMeasureLawTarget

/-- Graph-measure identification discharges the selected graph-measure target. -/
theorem
    G8BookIIICh23FloorNormalizedA12GraphMeasureIdentificationSource.toGraphMeasureTarget
    (source :
      G8BookIIICh23FloorNormalizedA12GraphMeasureIdentificationSource) :
    G8BookIIICh23FloorNormalizedA12GraphMeasureTarget :=
  source.toCrossingAndGraphMeasureLawSource.toGraphMeasureTarget

/-- Closed selected graph-measure law target. -/
theorem
    g8BookIIICh23FloorNormalizedA12GraphLengthMeasureLawTarget_closed :
    G8BookIIICh23FloorNormalizedA12GraphLengthMeasureLawTarget :=
  g8BookIIICh23FloorNormalizedA12GraphMeasureIdentificationSource_closed
    |>.toGraphLengthMeasureLawTarget

/-- Closed selected graph-measure target. -/
theorem
    g8BookIIICh23FloorNormalizedA12GraphMeasureTarget_closed :
    G8BookIIICh23FloorNormalizedA12GraphMeasureTarget :=
  g8BookIIICh23FloorNormalizedA12GraphMeasureIdentificationSource_closed
    |>.toGraphMeasureTarget

-- ============================================================
-- GUARDRAILS
-- ============================================================

/-- A nonzero crossing atom contradicts the selected graph-measure
    identification. -/
structure G8BookIIICh23FloorNormalizedA12NonzeroCrossingLengthAtom where
  nonzero :
    g8BookIIICh23FloorNormalizedA12CrossingLengthAtom ≠ 0

/-- The crossing atom is theorem-backed zero. -/
theorem
    G8BookIIICh23FloorNormalizedA12NonzeroCrossingLengthAtom.refutes
    (gap :
      G8BookIIICh23FloorNormalizedA12NonzeroCrossingLengthAtom) :
    False :=
  gap.nonzero
    g8BookIIICh23FloorNormalizedA12CrossingLengthAtom_eq_zero

/-- A mismatch between the graph-measure lobe readout and the finite lobe
    budget contradicts the canonical graph-measure identification. -/
structure G8BookIIICh23FloorNormalizedA12GraphMeasureLobeMismatch
    (source :
      G8BookIIICh23FloorNormalizedA12GraphMeasureIdentificationSource) where
  sector : LemniscateSector
  mismatch :
    g8BookIIICh23FloorNormalizedA12TwoLobeGraphLengthMeasure
        source.finiteLobeLaw sector ≠
      source.finiteLobeLaw.budget.lobeLength sector

/-- The canonical graph-measure identification carries exact lobe readout
    agreement. -/
theorem
    G8BookIIICh23FloorNormalizedA12GraphMeasureLobeMismatch.refutes
    {source :
      G8BookIIICh23FloorNormalizedA12GraphMeasureIdentificationSource}
    (gap :
      G8BookIIICh23FloorNormalizedA12GraphMeasureLobeMismatch source) :
    False :=
  gap.mismatch
    (source.canonicalProfileIsTwoLobeGraphLength.2.2.1 gap.sector)

/-- A wrong selected graph-measure total contradicts the closed
    identification. -/
structure G8BookIIICh23FloorNormalizedA12WrongSelectedGraphMeasureTotal
    (source :
      G8BookIIICh23FloorNormalizedA12GraphMeasureIdentificationSource) where
  wrongTotal :
    g8BookIIICh23FloorNormalizedA12SelectedGraphMeasureTotal
        source.finiteLobeLaw ≠ 2

/-- The selected graph-measure total is exactly two. -/
theorem
    G8BookIIICh23FloorNormalizedA12WrongSelectedGraphMeasureTotal.refutes
    {source :
      G8BookIIICh23FloorNormalizedA12GraphMeasureIdentificationSource}
    (gap :
      G8BookIIICh23FloorNormalizedA12WrongSelectedGraphMeasureTotal
        source) :
    False :=
  gap.wrongTotal source.selectedGraphMeasureTotal_eq_two

end Tau.BookIII.Bridge
