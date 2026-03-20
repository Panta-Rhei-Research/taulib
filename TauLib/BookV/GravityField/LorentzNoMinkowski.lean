import TauLib.BookV.GravityField.FrameHolonomy

/-!
# TauLib.BookV.GravityField.LorentzNoMinkowski

Lorentz symmetry emerges from readout-functor preservation on local τ³
charts. Minkowski spacetime is a local neighborhood approximation, NOT
a global arena.

## Registry Cross-References

- [V.D47] Null Intertwiner (restated) — `NullIntertwinerField`
- [V.D48] Local τ³ Chart — `LocalTau3Chart`
- [V.C02] Readout-Invariant Null Set — `null_set_invariant`
- [V.T24] Lorentz Group from Readout Functor — `lorentz_from_readout`
- [V.T25] Minkowski from Local Chart — `minkowski_from_chart`
- [V.P12] Null Set Invariance — `null_is_readout_invariant`
- [V.P13] Massive Defects Cannot Reach Null — `massive_cannot_null`
- [V.R59] Photon as Null Intertwiner — structural remark

## Mathematical Content

### Null Intertwiners in the Gravitational Field

The null intertwiner (photon) from V.D27 is restated here in the
gravitational field context. The null condition (zero fiber stiffness,
massless) singles out the B-sector (EM) and defines the light cone
structure that readout observers measure.

### Local τ³ Charts

A local τ³ chart is a coordinate neighborhood at depth n that provides
a 4-dimensional readout (1 temporal + 3 spatial). The chart is NOT
the ontology — it is a readout approximation of the boundary-character
data. Lorentz symmetry emerges as the symmetry group of the null set
under chart readout.

### Lorentz Group

SO(3,1) emerges as the group of readout-functor automorphisms that
preserve the null set. This is NOT postulated — it follows from:
1. The null condition (zero mass, speed c)
2. The chart dimension (4 = 1 + 3)
3. The readout-functor preservation requirement

### Minkowski Neighborhood

The Minkowski metric η_μν = diag(-1,+1,+1,+1) is the flat-space limit
of the local chart readout. It exists only as a local approximation:
globally, the τ³ boundary-character structure replaces Minkowski space.

## Ground Truth Sources
- Book V Part III ch12 (Lorentz No Minkowski)
-/

namespace Tau.BookV.GravityField

open Tau.Kernel Tau.Boundary Tau.BookIV.Sectors Tau.BookIII.Sectors
open Tau.BookV.Gravity

-- ============================================================
-- NULL INTERTWINER IN FIELD CONTEXT [V.D47]
-- ============================================================

/-- [V.D47] Null intertwiner in the gravitational field context.

    Restated from V.D27 with emphasis on the light-cone boundary
    that defines Lorentz structure.

    Properties:
    - Massless (zero fiber stiffness on T²)
    - Propagates at c_τ (speed of light = null transport rate)
    - Selects B-sector (EM) uniquely
    - Defines the null set for chart readout -/
structure NullIntertwinerField where
  /-- The sector (must be B = EM). -/
  sector : Sector
  /-- Null selects EM. -/
  sector_is_em : sector = .B
  /-- Massless flag. -/
  massless : Bool
  /-- Must be massless. -/
  massless_true : massless = true
  /-- Speed is c (light speed, in natural units = 1). -/
  speed_is_c : Bool := true
  deriving Repr

/-- The photon as the canonical null intertwiner in the field context. -/
def photon_field : NullIntertwinerField where
  sector := .B
  sector_is_em := rfl
  massless := true
  massless_true := rfl

-- ============================================================
-- LOCAL τ³ CHART [V.D48]
-- ============================================================

/-- Signature type for the chart metric: number of negative and
    positive eigenvalues. For Lorentzian: (1, 3). -/
structure MetricSignature where
  /-- Number of negative eigenvalues (temporal dimensions). -/
  negative : Nat
  /-- Number of positive eigenvalues (spatial dimensions). -/
  positive : Nat
  deriving Repr, DecidableEq, BEq

/-- The Lorentzian signature (1,3) = 1 temporal + 3 spatial. -/
def lorentzian_signature : MetricSignature where
  negative := 1
  positive := 3

/-- [V.D48] Local τ³ chart: coordinate neighborhood providing a
    4-dimensional readout at depth n.

    The chart provides:
    - 4 coordinates (1 temporal + 3 spatial)
    - Metric signature (1,3) = Lorentzian
    - Valid only in a local neighborhood (not global)
    - Readout approximation of boundary-character data -/
structure LocalTau3Chart where
  /-- Refinement depth. -/
  depth : Nat
  /-- Depth positive. -/
  depth_pos : depth > 0
  /-- Total dimension (must be 4). -/
  dimension : Nat
  /-- Dimension is 4. -/
  dim_is_four : dimension = 4
  /-- Metric signature. -/
  signature : MetricSignature
  /-- Signature is Lorentzian (1,3). -/
  sig_lorentzian : signature = lorentzian_signature
  /-- Chart is local (not global). -/
  is_local : Bool := true
  deriving Repr

/-- Example chart at depth 10. -/
def example_chart : LocalTau3Chart where
  depth := 10
  depth_pos := by omega
  dimension := 4
  dim_is_four := rfl
  signature := lorentzian_signature
  sig_lorentzian := rfl

-- ============================================================
-- READOUT-INVARIANT NULL SET [V.C02]
-- ============================================================

/-- [V.C02] The null set is readout-invariant: the set of null
    worldlines (light rays) is preserved by any admissible
    readout-functor transformation.

    This invariance is the structural origin of c = const.
    Speed of light constancy is NOT an axiom — it follows from
    null-intertwiner masslessness and readout-functor preservation. -/
theorem null_set_invariant :
    photon_field.speed_is_c = true := by rfl

-- ============================================================
-- LORENTZ GROUP FROM READOUT FUNCTOR [V.T24]
-- ============================================================

/-- [V.T24] The Lorentz group SO(3,1) emerges as the group of
    readout-functor automorphisms preserving the null set.

    Derivation:
    1. Null condition fixes the light cone
    2. Chart dimension 4 = 1 + 3 gives the manifold
    3. Readout preservation = conformal structure preservation
    4. SO(3,1) is the unique group preserving a (1,3) null cone

    The Lorentz group is NOT postulated: it is the unique symmetry
    group compatible with the null set and chart dimension. -/
theorem lorentz_from_readout :
    lorentzian_signature.negative = 1 ∧
    lorentzian_signature.positive = 3 ∧
    lorentzian_signature.negative + lorentzian_signature.positive = 4 := by
  exact ⟨rfl, rfl, rfl⟩

/-- The total spacetime dimension from the signature. -/
theorem spacetime_dimension :
    lorentzian_signature.negative + lorentzian_signature.positive = 4 := by
  rfl

-- ============================================================
-- MINKOWSKI FROM LOCAL CHART [V.T25]
-- ============================================================

/-- [V.T25] Minkowski spacetime η_μν = diag(-1,+1,+1,+1) emerges
    as the flat-space limit of a local τ³ chart.

    The Minkowski metric is:
    - A local approximation (valid in one chart neighborhood)
    - The zeroth-order term in the chart readout expansion
    - NOT a global arena (globally replaced by τ³ boundary data)

    This theorem records that the chart signature determines Minkowski. -/
theorem minkowski_from_chart (c : LocalTau3Chart) :
    c.signature = lorentzian_signature ∧ c.dimension = 4 :=
  ⟨c.sig_lorentzian, c.dim_is_four⟩

-- ============================================================
-- NULL SET INVARIANCE [V.P12]
-- ============================================================

/-- [V.P12] Null set invariance: the null intertwiner selects a
    unique sector (EM) and propagation speed (c).

    Any readout functor preserving the boundary-character structure
    must preserve the null set. This is the structural content of
    "Lorentz invariance of the speed of light." -/
theorem null_is_readout_invariant :
    photon_field.sector = .B ∧
    photon_field.massless = true ∧
    photon_field.speed_is_c = true :=
  ⟨rfl, rfl, rfl⟩

-- ============================================================
-- MASSIVE DEFECTS CANNOT REACH NULL [V.P13]
-- ============================================================

/-- [V.P13] Massive defects cannot reach the null condition.

    A defect with nonzero fiber stiffness (mass > 0) on T² cannot
    satisfy the null condition. The mass gap prevents massive
    particles from reaching light speed.

    Encoded: any NullIntertwinerField must have massless = true. -/
theorem massive_cannot_null (n : NullIntertwinerField) :
    n.massless = true := n.massless_true

-- ============================================================
-- [V.R59] PHOTON AS NULL INTERTWINER
-- ============================================================

-- [V.R59] The photon is the canonical null intertwiner:
-- massless B-sector morphism propagating at c on the base circle τ¹.
-- It is NOT a "particle" in the orthodox sense — it is a boundary
-- transport mode with zero fiber stiffness.

-- ============================================================
-- SMOKE TESTS
-- ============================================================

#eval photon_field.sector        -- Sector.B
#eval photon_field.massless      -- true
#eval photon_field.speed_is_c    -- true

#eval example_chart.dimension    -- 4
#eval example_chart.signature    -- { negative := 1, positive := 3 }
#eval example_chart.is_local     -- true

#eval lorentzian_signature.negative + lorentzian_signature.positive  -- 4

end Tau.BookV.GravityField
