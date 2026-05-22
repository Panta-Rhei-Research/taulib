import TauLib.BookIII.Bridge.G8BookIIICh23FloorNormalizedA12HilbertDomainSource

/-!
# G8 Book III Ch.23 Floor-Normalized A1.2 Graph Length Measure

This module takes the first concrete A1.2 step after the selected compact
metric graph route.

It closes the canonical graph-length profile over the floor-normalized Ch.23
carrier and proves the adapter into the existing graph-measure source.  The
actual measure-theoretic length laws remain explicit proof fields:

```text
canonical selected graph profile
  + finite total two-lobe length
  + lobe length agreement
  + crossing has zero length atom
  + graph length is the two-lobe length measure
  -> G8BookIIICh23FloorNormalizedA12GraphMeasureSource
```

The point is deliberately narrow: this file proves the selected profile and
bookkeeping, not Sobolev trace readiness or Kirchhoff-domain closure.
-/

set_option autoImplicit false

namespace Tau.BookIII.Bridge

-- ============================================================
-- CANONICAL SELECTED GRAPH-LENGTH PROFILE
-- ============================================================

/-- Canonical pointwise density profile for the selected Ch.23 graph-length
    layer.

This is a density/profile marker, not a counting measure on points.  The
measure-theoretic content is supplied separately by
`G8BookIIICh23FloorNormalizedA12GraphLengthMeasureLawSource`. -/
noncomputable def g8BookIIICh23FloorNormalizedA12GraphLengthWeight
    (_ : G8BookIIICh23FloorNormalizedLemniscateCarrier) : ℝ :=
  1

/-- The canonical selected graph-length profile is nonnegative. -/
theorem g8BookIIICh23FloorNormalizedA12GraphLengthWeight_nonnegative :
    ∀ x : G8BookIIICh23FloorNormalizedLemniscateCarrier,
      0 ≤ g8BookIIICh23FloorNormalizedA12GraphLengthWeight x := by
  intro x
  dsimp [g8BookIIICh23FloorNormalizedA12GraphLengthWeight]
  norm_num

/-- The crossing carries the canonical density marker. -/
@[simp] theorem
    g8BookIIICh23FloorNormalizedA12GraphLengthWeight_crossing :
    g8BookIIICh23FloorNormalizedA12GraphLengthWeight
        G8BookIIICh23FloorNormalizedLemniscateCarrier.crossing = 1 :=
  rfl

/-- Every selected lobe point carries the canonical density marker. -/
@[simp] theorem
    g8BookIIICh23FloorNormalizedA12GraphLengthWeight_lobe
    (s : LemniscateSector)
    (p : G8BookIIICh23FloorNormalizedCauchyLobePoint) :
    g8BookIIICh23FloorNormalizedA12GraphLengthWeight
        (G8BookIIICh23FloorNormalizedLemniscateCarrier.lobe s p) = 1 :=
  rfl

/-- The canonical profile is lobe symmetric at the pointwise-density level. -/
theorem
    g8BookIIICh23FloorNormalizedA12GraphLengthWeight_lobe_symmetric
    (p : G8BookIIICh23FloorNormalizedCauchyLobePoint) :
    g8BookIIICh23FloorNormalizedA12GraphLengthWeight
        (G8BookIIICh23FloorNormalizedLemniscateCarrier.lobe .plus p) =
      g8BookIIICh23FloorNormalizedA12GraphLengthWeight
        (G8BookIIICh23FloorNormalizedLemniscateCarrier.lobe .minus p) :=
  rfl

/-- The selected graph profile is tied to the theorem-backed floor-normalized
    compact graph from A1.1. -/
structure G8BookIIICh23FloorNormalizedA12CanonicalGraphLengthProfileSource where
  graph : G8BookIIICh23FloorNormalizedA11CompactMetricGraphSource
  weight :
    G8BookIIICh23FloorNormalizedLemniscateCarrier → ℝ :=
      g8BookIIICh23FloorNormalizedA12GraphLengthWeight
  weight_is_canonical :
    weight = g8BookIIICh23FloorNormalizedA12GraphLengthWeight
  nonnegative : ∀ x, 0 ≤ weight x
  crossingDensity :
    weight G8BookIIICh23FloorNormalizedLemniscateCarrier.crossing = 1
  lobeDensity :
    ∀ (s : LemniscateSector)
      (p : G8BookIIICh23FloorNormalizedCauchyLobePoint),
        weight
          (G8BookIIICh23FloorNormalizedLemniscateCarrier.lobe s p) = 1
  lobeSymmetric :
    ∀ p : G8BookIIICh23FloorNormalizedCauchyLobePoint,
      weight
          (G8BookIIICh23FloorNormalizedLemniscateCarrier.lobe .plus p) =
        weight
          (G8BookIIICh23FloorNormalizedLemniscateCarrier.lobe .minus p)
  transportedMetricEvidence :
    G8BookIIICh23FloorNormalizedGraphDistanceRealizesMetric
      graph.concrete
  quotientMatchesConcrete :
    G8BookIIICh23FloorNormalizedQuotientMatchesConcrete
  status : SpineStatus := .conditional_interface

/-- Closed canonical graph-length profile over the selected floor-normalized
    Ch.23 compact graph. -/
noncomputable def
    g8BookIIICh23FloorNormalizedA12CanonicalGraphLengthProfileSource_closed :
    G8BookIIICh23FloorNormalizedA12CanonicalGraphLengthProfileSource where
  graph :=
    g8BookIIICh23FloorNormalizedA11CompactMetricGraphSource_closed
  weight :=
    g8BookIIICh23FloorNormalizedA12GraphLengthWeight
  weight_is_canonical :=
    rfl
  nonnegative :=
    g8BookIIICh23FloorNormalizedA12GraphLengthWeight_nonnegative
  crossingDensity :=
    g8BookIIICh23FloorNormalizedA12GraphLengthWeight_crossing
  lobeDensity :=
    g8BookIIICh23FloorNormalizedA12GraphLengthWeight_lobe
  lobeSymmetric :=
    g8BookIIICh23FloorNormalizedA12GraphLengthWeight_lobe_symmetric
  transportedMetricEvidence :=
    g8BookIIICh23FloorNormalizedA11CompactMetricGraphSource_closed
      |>.graphDistanceRealizesMetric
  quotientMatchesConcrete :=
    g8BookIIICh23FloorNormalizedA11CompactMetricGraphSource_closed
      |>.quotientMatchesConcrete
  status := .conditional_interface

/-- Target for the selected canonical graph-length profile. -/
def G8BookIIICh23FloorNormalizedA12CanonicalGraphLengthProfileTarget :
    Prop :=
  Nonempty G8BookIIICh23FloorNormalizedA12CanonicalGraphLengthProfileSource

/-- The selected canonical graph-length profile target is closed. -/
theorem
    g8BookIIICh23FloorNormalizedA12CanonicalGraphLengthProfileTarget_closed :
    G8BookIIICh23FloorNormalizedA12CanonicalGraphLengthProfileTarget :=
  ⟨g8BookIIICh23FloorNormalizedA12CanonicalGraphLengthProfileSource_closed⟩

-- ============================================================
-- GRAPH LENGTH MEASURE LAWS
-- ============================================================

/-- The remaining measure-theoretic length laws for A1.2 graph measure.

These fields are the actual graph-measure payload: finite total two-lobe
length, lobe agreement, zero atom at the glued crossing, and identification
with the two-lobe graph length measure. -/
structure G8BookIIICh23FloorNormalizedA12GraphLengthMeasureLawSource where
  profile :
    G8BookIIICh23FloorNormalizedA12CanonicalGraphLengthProfileSource
  finiteTotalTwoLobeLength : Prop
  finiteTotalTwoLobeLengthEvidence : finiteTotalTwoLobeLength
  lobeLengthAgreement : Prop
  lobeLengthAgreementEvidence : lobeLengthAgreement
  crossingZeroLengthAtom : Prop
  crossingZeroLengthAtomEvidence : crossingZeroLengthAtom
  graphMeasureIsTwoLobeLength : Prop
  graphMeasureIsTwoLobeLengthEvidence :
    graphMeasureIsTwoLobeLength
  status : SpineStatus := .conditional_interface

/-- Target for the selected floor-normalized graph-length measure law. -/
def G8BookIIICh23FloorNormalizedA12GraphLengthMeasureLawTarget : Prop :=
  Nonempty G8BookIIICh23FloorNormalizedA12GraphLengthMeasureLawSource

/-- A graph-length measure law supplies the existing A1.2 graph-measure
    source. -/
def G8BookIIICh23FloorNormalizedA12GraphLengthMeasureLawSource.toGraphMeasureSource
    (law :
      G8BookIIICh23FloorNormalizedA12GraphLengthMeasureLawSource) :
    G8BookIIICh23FloorNormalizedA12GraphMeasureSource where
  graph := law.profile.graph
  weight := law.profile.weight
  nonnegative := law.profile.nonnegative
  totalFinite := law.finiteTotalTwoLobeLength
  totalFiniteWitness := law.finiteTotalTwoLobeLengthEvidence
  lobeMeasureAgreement := law.lobeLengthAgreement
  lobeMeasureAgreementWitness := law.lobeLengthAgreementEvidence
  crossingAtomPolicy := law.crossingZeroLengthAtom
  crossingAtomPolicyWitness := law.crossingZeroLengthAtomEvidence
  graphMeasureFromTwoLobeLength := law.graphMeasureIsTwoLobeLength
  graphMeasureFromTwoLobeLengthEvidence :=
    law.graphMeasureIsTwoLobeLengthEvidence
  status := law.status

/-- A graph-length measure law discharges the existing selected graph-measure
    target. -/
theorem
    G8BookIIICh23FloorNormalizedA12GraphLengthMeasureLawSource.toGraphMeasureTarget
    (law :
      G8BookIIICh23FloorNormalizedA12GraphLengthMeasureLawSource) :
    G8BookIIICh23FloorNormalizedA12GraphMeasureTarget :=
  ⟨law.toGraphMeasureSource⟩

/-- The graph-length measure law target is exactly sufficient for the existing
    selected graph-measure target. -/
theorem
    g8BookIIICh23FloorNormalizedA12GraphMeasureTarget_of_lengthMeasureLaw
    (hLaw :
      G8BookIIICh23FloorNormalizedA12GraphLengthMeasureLawTarget) :
    G8BookIIICh23FloorNormalizedA12GraphMeasureTarget := by
  rcases hLaw with ⟨law⟩
  exact law.toGraphMeasureTarget

-- ============================================================
-- GUARDRAILS
-- ============================================================

/-- A wrong pointwise profile cannot be the canonical selected length profile. -/
structure G8BookIIICh23FloorNormalizedA12WrongLengthProfile
    (source :
      G8BookIIICh23FloorNormalizedA12CanonicalGraphLengthProfileSource) where
  wrongWeight :
    source.weight ≠
      g8BookIIICh23FloorNormalizedA12GraphLengthWeight

/-- The canonical profile source carries exact weight equality. -/
theorem G8BookIIICh23FloorNormalizedA12WrongLengthProfile.refutes
    {source :
      G8BookIIICh23FloorNormalizedA12CanonicalGraphLengthProfileSource}
    (gap :
      G8BookIIICh23FloorNormalizedA12WrongLengthProfile source) :
    False :=
  gap.wrongWeight source.weight_is_canonical

/-- The canonical profile alone is not the full graph-measure law. -/
structure G8BookIIICh23FloorNormalizedA12ProfileWithoutMeasureLaw where
  profile :
    G8BookIIICh23FloorNormalizedA12CanonicalGraphLengthProfileSource
  noMeasureLaw :
    ¬ G8BookIIICh23FloorNormalizedA12GraphLengthMeasureLawTarget

/-- Missing graph-length laws still refute the graph-length law target even
    when the canonical profile is closed. -/
theorem
    G8BookIIICh23FloorNormalizedA12ProfileWithoutMeasureLaw.refutesLawTarget
    (gap :
      G8BookIIICh23FloorNormalizedA12ProfileWithoutMeasureLaw) :
    ¬ G8BookIIICh23FloorNormalizedA12GraphLengthMeasureLawTarget :=
  gap.noMeasureLaw

/-- A graph-measure source built from the length law must use the canonical
    selected profile. -/
theorem
    G8BookIIICh23FloorNormalizedA12GraphLengthMeasureLawSource.graphMeasureWeight_canonical
    (law :
      G8BookIIICh23FloorNormalizedA12GraphLengthMeasureLawSource) :
    law.toGraphMeasureSource.weight =
      g8BookIIICh23FloorNormalizedA12GraphLengthWeight :=
  law.profile.weight_is_canonical

end Tau.BookIII.Bridge
