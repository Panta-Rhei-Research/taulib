import TauLib.BookIII.Bridge.G8BookIIICh23FloorNormalizedA12GraphLengthMeasure

/-!
# G8 Book III Ch.23 Floor-Normalized A1.2 Finite Lobe Length Law

This module closes the next measure-side A1.2 stone: the finite normalized
two-lobe length budget and the B/C lobe length agreement.

It still does not assert the full graph-length measure law.  The remaining
measure-theoretic payload is now exactly:

```text
crossing has zero length atom
+ canonical profile is the two-lobe graph length measure
```

Those two fields are kept explicit before constructing
`G8BookIIICh23FloorNormalizedA12GraphLengthMeasureLawSource`.
-/

set_option autoImplicit false

namespace Tau.BookIII.Bridge

-- ============================================================
-- NORMALIZED TWO-LOBE LENGTH BUDGET
-- ============================================================

/-- Normalized length assigned to each Ch.23 lobe for the selected graph
    measure layer. -/
def g8BookIIICh23FloorNormalizedA12NormalizedLobeLength
    (_ : LemniscateSector) : ℝ :=
  1

/-- The normalized plus-lobe length is one. -/
@[simp] theorem
    g8BookIIICh23FloorNormalizedA12NormalizedLobeLength_plus :
    g8BookIIICh23FloorNormalizedA12NormalizedLobeLength .plus = 1 :=
  rfl

/-- The normalized minus-lobe length is one. -/
@[simp] theorem
    g8BookIIICh23FloorNormalizedA12NormalizedLobeLength_minus :
    g8BookIIICh23FloorNormalizedA12NormalizedLobeLength .minus = 1 :=
  rfl

/-- Normalized lobe lengths are nonnegative. -/
theorem
    g8BookIIICh23FloorNormalizedA12NormalizedLobeLength_nonnegative :
    ∀ s : LemniscateSector,
      0 ≤ g8BookIIICh23FloorNormalizedA12NormalizedLobeLength s := by
  intro s
  cases s <;>
    dsimp [g8BookIIICh23FloorNormalizedA12NormalizedLobeLength] <;>
    norm_num

/-- The normalized two-lobe total length. -/
def g8BookIIICh23FloorNormalizedA12TwoLobeTotalLength : ℝ :=
  g8BookIIICh23FloorNormalizedA12NormalizedLobeLength .plus +
    g8BookIIICh23FloorNormalizedA12NormalizedLobeLength .minus

/-- The normalized two-lobe total length is two. -/
theorem g8BookIIICh23FloorNormalizedA12TwoLobeTotalLength_eq_two :
    g8BookIIICh23FloorNormalizedA12TwoLobeTotalLength = 2 := by
  dsimp [g8BookIIICh23FloorNormalizedA12TwoLobeTotalLength,
    g8BookIIICh23FloorNormalizedA12NormalizedLobeLength]
  norm_num

/-- The normalized two-lobe total length is nonnegative. -/
theorem g8BookIIICh23FloorNormalizedA12TwoLobeTotalLength_nonnegative :
    0 ≤ g8BookIIICh23FloorNormalizedA12TwoLobeTotalLength := by
  rw [g8BookIIICh23FloorNormalizedA12TwoLobeTotalLength_eq_two]
  norm_num

/-- The two normalized lobes have equal length. -/
theorem g8BookIIICh23FloorNormalizedA12NormalizedLobeLength_agreement :
    g8BookIIICh23FloorNormalizedA12NormalizedLobeLength .plus =
      g8BookIIICh23FloorNormalizedA12NormalizedLobeLength .minus :=
  rfl

/-- Closed finite normalized lobe-length budget. -/
structure G8BookIIICh23FloorNormalizedA12FiniteLobeLengthBudget where
  profile :
    G8BookIIICh23FloorNormalizedA12CanonicalGraphLengthProfileSource
  lobeLength : LemniscateSector → ℝ :=
    g8BookIIICh23FloorNormalizedA12NormalizedLobeLength
  lobeLength_is_normalized :
    lobeLength = g8BookIIICh23FloorNormalizedA12NormalizedLobeLength
  lobeLength_nonnegative : ∀ s, 0 ≤ lobeLength s
  plusLength_eq_one : lobeLength .plus = 1
  minusLength_eq_one : lobeLength .minus = 1
  totalLength : ℝ :=
    lobeLength .plus + lobeLength .minus
  totalLength_eq_sum :
    totalLength = lobeLength .plus + lobeLength .minus
  totalLength_eq_two : totalLength = 2
  totalLength_nonnegative : 0 ≤ totalLength
  lobeLengthAgreement : lobeLength .plus = lobeLength .minus
  transportedMetricEvidence :
    G8BookIIICh23FloorNormalizedGraphDistanceRealizesMetric
      profile.graph.concrete
  status : SpineStatus := .conditional_interface

/-- Closed theorem-backed normalized finite lobe-length budget. -/
noncomputable def
    g8BookIIICh23FloorNormalizedA12FiniteLobeLengthBudget_closed :
    G8BookIIICh23FloorNormalizedA12FiniteLobeLengthBudget where
  profile :=
    g8BookIIICh23FloorNormalizedA12CanonicalGraphLengthProfileSource_closed
  lobeLength :=
    g8BookIIICh23FloorNormalizedA12NormalizedLobeLength
  lobeLength_is_normalized :=
    rfl
  lobeLength_nonnegative :=
    g8BookIIICh23FloorNormalizedA12NormalizedLobeLength_nonnegative
  plusLength_eq_one :=
    g8BookIIICh23FloorNormalizedA12NormalizedLobeLength_plus
  minusLength_eq_one :=
    g8BookIIICh23FloorNormalizedA12NormalizedLobeLength_minus
  totalLength :=
    g8BookIIICh23FloorNormalizedA12TwoLobeTotalLength
  totalLength_eq_sum :=
    rfl
  totalLength_eq_two :=
    g8BookIIICh23FloorNormalizedA12TwoLobeTotalLength_eq_two
  totalLength_nonnegative :=
    g8BookIIICh23FloorNormalizedA12TwoLobeTotalLength_nonnegative
  lobeLengthAgreement :=
    g8BookIIICh23FloorNormalizedA12NormalizedLobeLength_agreement
  transportedMetricEvidence :=
    g8BookIIICh23FloorNormalizedA12CanonicalGraphLengthProfileSource_closed
      |>.transportedMetricEvidence
  status := .conditional_interface

/-- Target for the finite normalized lobe-length budget. -/
def G8BookIIICh23FloorNormalizedA12FiniteLobeLengthBudgetTarget :
    Prop :=
  Nonempty G8BookIIICh23FloorNormalizedA12FiniteLobeLengthBudget

/-- The finite normalized lobe-length budget target is closed. -/
theorem
    g8BookIIICh23FloorNormalizedA12FiniteLobeLengthBudgetTarget_closed :
    G8BookIIICh23FloorNormalizedA12FiniteLobeLengthBudgetTarget :=
  ⟨g8BookIIICh23FloorNormalizedA12FiniteLobeLengthBudget_closed⟩

-- ============================================================
-- FINITE TOTAL AND LOBE AGREEMENT LAW
-- ============================================================

/-- Finite total two-lobe length law induced by a normalized lobe budget. -/
def G8BookIIICh23FloorNormalizedA12FiniteTotalTwoLobeLength
    (budget : G8BookIIICh23FloorNormalizedA12FiniteLobeLengthBudget) :
    Prop :=
  budget.totalLength = budget.lobeLength .plus +
      budget.lobeLength .minus ∧
    budget.totalLength = 2 ∧
    0 ≤ budget.totalLength

/-- Plus/minus lobe length agreement induced by a normalized lobe budget. -/
def G8BookIIICh23FloorNormalizedA12LobeLengthAgreement
    (budget : G8BookIIICh23FloorNormalizedA12FiniteLobeLengthBudget) :
    Prop :=
  budget.lobeLength .plus = budget.lobeLength .minus

/-- A finite lobe-length budget proves finite total two-lobe length. -/
theorem
    G8BookIIICh23FloorNormalizedA12FiniteLobeLengthBudget.finiteTotalTwoLobeLength
    (budget : G8BookIIICh23FloorNormalizedA12FiniteLobeLengthBudget) :
    G8BookIIICh23FloorNormalizedA12FiniteTotalTwoLobeLength budget :=
  ⟨budget.totalLength_eq_sum,
    budget.totalLength_eq_two,
    budget.totalLength_nonnegative⟩

/-- A finite lobe-length budget proves plus/minus lobe length agreement. -/
theorem
    G8BookIIICh23FloorNormalizedA12FiniteLobeLengthBudget.lobeAgreement
    (budget : G8BookIIICh23FloorNormalizedA12FiniteLobeLengthBudget) :
    G8BookIIICh23FloorNormalizedA12LobeLengthAgreement budget :=
  budget.lobeLengthAgreement

/-- The theorem-backed finite total and lobe-agreement law package. -/
structure G8BookIIICh23FloorNormalizedA12FiniteLobeLengthLawSource where
  budget : G8BookIIICh23FloorNormalizedA12FiniteLobeLengthBudget
  finiteTotalTwoLobeLength :
    G8BookIIICh23FloorNormalizedA12FiniteTotalTwoLobeLength budget
  lobeLengthAgreement :
    G8BookIIICh23FloorNormalizedA12LobeLengthAgreement budget
  normalizedLobes :
    budget.lobeLength = g8BookIIICh23FloorNormalizedA12NormalizedLobeLength
  totalLength_eq_two : budget.totalLength = 2
  status : SpineStatus := .conditional_interface

/-- Closed finite total and lobe-agreement law package. -/
noncomputable def
    g8BookIIICh23FloorNormalizedA12FiniteLobeLengthLawSource_closed :
    G8BookIIICh23FloorNormalizedA12FiniteLobeLengthLawSource :=
  let budget :=
    g8BookIIICh23FloorNormalizedA12FiniteLobeLengthBudget_closed
  { budget := budget
    finiteTotalTwoLobeLength := budget.finiteTotalTwoLobeLength
    lobeLengthAgreement := budget.lobeAgreement
    normalizedLobes := budget.lobeLength_is_normalized
    totalLength_eq_two := budget.totalLength_eq_two
    status := .conditional_interface }

/-- Target for the finite total and lobe-agreement law package. -/
def G8BookIIICh23FloorNormalizedA12FiniteLobeLengthLawTarget : Prop :=
  Nonempty G8BookIIICh23FloorNormalizedA12FiniteLobeLengthLawSource

/-- The finite total and lobe-agreement law package is closed. -/
theorem
    g8BookIIICh23FloorNormalizedA12FiniteLobeLengthLawTarget_closed :
    G8BookIIICh23FloorNormalizedA12FiniteLobeLengthLawTarget :=
  ⟨g8BookIIICh23FloorNormalizedA12FiniteLobeLengthLawSource_closed⟩

-- ============================================================
-- ADAPTER TO THE GRAPH-LENGTH MEASURE LAW SURFACE
-- ============================================================

/-- Remaining graph-measure law fields after finite total length and lobe
    agreement have been theorem-backed. -/
structure G8BookIIICh23FloorNormalizedA12CrossingAndGraphMeasureLawSource where
  finiteLobeLaw :
    G8BookIIICh23FloorNormalizedA12FiniteLobeLengthLawSource
  crossingZeroLengthAtom : Prop
  crossingZeroLengthAtomEvidence : crossingZeroLengthAtom
  graphMeasureIsTwoLobeLength : Prop
  graphMeasureIsTwoLobeLengthEvidence :
    graphMeasureIsTwoLobeLength
  status : SpineStatus := .conditional_interface

/-- Target for the remaining crossing atom plus graph-measure identification
    laws. -/
def
    G8BookIIICh23FloorNormalizedA12CrossingAndGraphMeasureLawTarget :
    Prop :=
  Nonempty
    G8BookIIICh23FloorNormalizedA12CrossingAndGraphMeasureLawSource

/-- Finite total/lobe agreement plus the remaining crossing and graph
    identification fields produce the existing graph-length measure law
    source. -/
def
    G8BookIIICh23FloorNormalizedA12CrossingAndGraphMeasureLawSource.toGraphLengthMeasureLawSource
    (source :
      G8BookIIICh23FloorNormalizedA12CrossingAndGraphMeasureLawSource) :
    G8BookIIICh23FloorNormalizedA12GraphLengthMeasureLawSource where
  profile := source.finiteLobeLaw.budget.profile
  finiteTotalTwoLobeLength :=
    G8BookIIICh23FloorNormalizedA12FiniteTotalTwoLobeLength
      source.finiteLobeLaw.budget
  finiteTotalTwoLobeLengthEvidence :=
    source.finiteLobeLaw.finiteTotalTwoLobeLength
  lobeLengthAgreement :=
    G8BookIIICh23FloorNormalizedA12LobeLengthAgreement
      source.finiteLobeLaw.budget
  lobeLengthAgreementEvidence :=
    source.finiteLobeLaw.lobeLengthAgreement
  crossingZeroLengthAtom := source.crossingZeroLengthAtom
  crossingZeroLengthAtomEvidence :=
    source.crossingZeroLengthAtomEvidence
  graphMeasureIsTwoLobeLength := source.graphMeasureIsTwoLobeLength
  graphMeasureIsTwoLobeLengthEvidence :=
    source.graphMeasureIsTwoLobeLengthEvidence
  status := source.status

/-- The remaining crossing and graph identification package is sufficient for
    the existing graph-length measure law target. -/
theorem
    G8BookIIICh23FloorNormalizedA12CrossingAndGraphMeasureLawSource.toGraphLengthMeasureLawTarget
    (source :
      G8BookIIICh23FloorNormalizedA12CrossingAndGraphMeasureLawSource) :
    G8BookIIICh23FloorNormalizedA12GraphLengthMeasureLawTarget :=
  ⟨source.toGraphLengthMeasureLawSource⟩

/-- The remaining crossing and graph identification package is sufficient for
    the existing selected graph-measure target. -/
theorem
    G8BookIIICh23FloorNormalizedA12CrossingAndGraphMeasureLawSource.toGraphMeasureTarget
    (source :
      G8BookIIICh23FloorNormalizedA12CrossingAndGraphMeasureLawSource) :
    G8BookIIICh23FloorNormalizedA12GraphMeasureTarget :=
  source.toGraphLengthMeasureLawSource.toGraphMeasureTarget

-- ============================================================
-- GUARDRAILS
-- ============================================================

/-- A claimed finite lobe-length law with the wrong total length is refuted by
    the closed normalized budget. -/
structure G8BookIIICh23FloorNormalizedA12WrongTotalLobeLength
    (source :
      G8BookIIICh23FloorNormalizedA12FiniteLobeLengthLawSource) where
  wrongTotal : source.budget.totalLength ≠ 2

/-- The finite lobe-length law carries total length exactly two. -/
theorem G8BookIIICh23FloorNormalizedA12WrongTotalLobeLength.refutes
    {source :
      G8BookIIICh23FloorNormalizedA12FiniteLobeLengthLawSource}
    (gap :
      G8BookIIICh23FloorNormalizedA12WrongTotalLobeLength source) :
    False :=
  gap.wrongTotal source.totalLength_eq_two

/-- A claimed finite lobe-length law with unequal lobes is refuted by lobe
    agreement. -/
structure G8BookIIICh23FloorNormalizedA12UnequalLobeLength
    (source :
      G8BookIIICh23FloorNormalizedA12FiniteLobeLengthLawSource) where
  unequal :
    source.budget.lobeLength .plus ≠ source.budget.lobeLength .minus

/-- The finite lobe-length law carries exact plus/minus agreement. -/
theorem G8BookIIICh23FloorNormalizedA12UnequalLobeLength.refutes
    {source :
      G8BookIIICh23FloorNormalizedA12FiniteLobeLengthLawSource}
    (gap :
      G8BookIIICh23FloorNormalizedA12UnequalLobeLength source) :
    False :=
  gap.unequal source.lobeLengthAgreement

/-- Finite total/lobe agreement alone does not claim the crossing atom and
    graph-measure identification fields. -/
structure G8BookIIICh23FloorNormalizedA12FiniteLobeLawWithoutGraphMeasure where
  finiteLobeLaw :
    G8BookIIICh23FloorNormalizedA12FiniteLobeLengthLawSource
  missingRemainder :
    ¬ G8BookIIICh23FloorNormalizedA12CrossingAndGraphMeasureLawTarget

/-- Missing crossing/graph-measure identification still refutes the remaining
    law target after finite lobe laws are closed. -/
theorem
    G8BookIIICh23FloorNormalizedA12FiniteLobeLawWithoutGraphMeasure.refutesRemainder
    (gap :
      G8BookIIICh23FloorNormalizedA12FiniteLobeLawWithoutGraphMeasure) :
    ¬ G8BookIIICh23FloorNormalizedA12CrossingAndGraphMeasureLawTarget :=
  gap.missingRemainder

end Tau.BookIII.Bridge
