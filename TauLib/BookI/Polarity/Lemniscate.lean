import TauLib.BookI.Polarity.BipolarAlgebra

/-!
# TauLib.BookI.Polarity.Lemniscate

The algebraic lemniscate: the pre-geometric boundary of Category τ.

## Registry Cross-References

- [I.D18] Algebraic Lemniscate — `AlgebraicLemniscate`, `algebraic_lemniscate_exists`

## Ground Truth Sources
- chunk_0123_M001424: Algebraic lemniscate as boundary of τ³, wedge structure
- chunk_0228_M002194: Split-complex extension giving H_τ = ℤ̂_τ[j]

## Mathematical Content

The algebraic lemniscate L is the triple (H_τ, ω_L, σ) where:
- H_τ is the bipolar spectral algebra (split-complex over the boundary ring)
- ω_L is the crossing-point germ (where neither polarity channel freezes)
- σ is the polarity involution (j ↦ -j, swaps B/C sectors)

This is the algebraic, pre-topological definition of the lemniscate boundary.
In Book II, when topology is earned via Global Hartogs, this becomes the
geometric lemniscate S¹ ∨ S¹.

Key properties:
- σ² = id (involution)
- σ swaps e+ ↔ e- (sector exchange)
- σ fixes the crossing point ω_L
- The two sectors e+·H_τ and e-·H_τ are the two lobes
-/

namespace Tau.Polarity

open Tau.Denotation

-- ============================================================
-- ALGEBRAIC LEMNISCATE [I.D18]
-- ============================================================

/-- [I.D18] The algebraic lemniscate: a triple (algebra, crossing point, involution).
    This is the pre-geometric boundary structure of Category τ. -/
structure AlgebraicLemniscate where
  /-- The bipolar spectral algebra H_τ, represented by its unit j. -/
  j_unit : SplitComplex
  /-- j² = 1 (split-complex identity). -/
  j_sq : SplitComplex.mul j_unit j_unit = SplitComplex.one
  /-- The crossing-point germ ω_L (sector-balanced: both components equal). -/
  crossing_point : SectorPair
  /-- The crossing point has equal sector components (balance). -/
  crossing_balanced : crossing_point.b_sector = crossing_point.c_sector
  /-- The polarity involution σ. -/
  involution : SplitComplex → SplitComplex
  /-- σ² = id. -/
  involution_sq : ∀ z, involution (involution z) = z
  /-- σ(j) = -j. -/
  involution_j : involution j_unit = SplitComplex.neg j_unit

-- ============================================================
-- CONSTRUCTION
-- ============================================================

/-- The canonical algebraic lemniscate constructed from the split-complex algebra. -/
def canonical_lemniscate : AlgebraicLemniscate :=
  { j_unit := SplitComplex.j
    j_sq := j_squared
    crossing_point := ⟨0, 0⟩
    crossing_balanced := rfl
    involution := polarity_inv
    involution_sq := polarity_inv_squared
    involution_j := polarity_inv_j }

/-- [I.D18] The algebraic lemniscate exists. -/
theorem algebraic_lemniscate_exists : Nonempty AlgebraicLemniscate :=
  ⟨canonical_lemniscate⟩

-- ============================================================
-- LEMNISCATE PROPERTIES
-- ============================================================

/-- The canonical involution swaps sectors. -/
theorem canonical_swaps_sectors (z : SplitComplex) :
    to_sectors (canonical_lemniscate.involution z) =
    ⟨(to_sectors z).c_sector, (to_sectors z).b_sector⟩ :=
  polarity_inv_swaps_sectors z

/-- The two sectors (lobes) of the lemniscate. -/
def b_lobe : SectorPair := e_plus_sector   -- (1, 0): pure B-sector
def c_lobe : SectorPair := e_minus_sector  -- (0, 1): pure C-sector

/-- The involution swaps the lobes. -/
theorem involution_swaps_lobes :
    to_sectors (polarity_inv ⟨1, 1⟩) =
    ⟨(to_sectors ⟨1, 1⟩).c_sector, (to_sectors ⟨1, 1⟩).b_sector⟩ :=
  polarity_inv_swaps_sectors ⟨1, 1⟩

-- ============================================================
-- SECTOR ANALYSIS
-- ============================================================

/-- The sector decomposition is a ring isomorphism (proved via sectors_mul). -/
theorem sector_ring_iso (a b : SplitComplex) :
    to_sectors (SplitComplex.mul a b) =
    SectorPair.mul (to_sectors a) (to_sectors b) := sectors_mul a b

/-- Every split-complex element has a unique sector decomposition. -/
theorem sector_unique (z : SplitComplex) :
    z = ⟨((to_sectors z).b_sector + (to_sectors z).c_sector) / 2,
         ((to_sectors z).b_sector - (to_sectors z).c_sector) / 2⟩ := by
  rcases z with ⟨re, im⟩
  simp only [to_sectors, SplitComplex.mk.injEq]
  constructor <;> omega

-- ============================================================
-- ZERO-DIVISOR STRUCTURE
-- ============================================================

/-- The split-complex algebra has zero divisors: (1+j)(1-j) = 0. -/
theorem split_complex_zero_divisor :
    SplitComplex.mul ⟨1, 1⟩ ⟨1, -1⟩ = SplitComplex.zero := by
  simp [SplitComplex.mul, SplitComplex.zero]

/-- The zero divisors correspond to the sector idempotents. -/
theorem zero_divisor_via_sectors :
    to_sectors ⟨1, 1⟩ = ⟨2, 0⟩ ∧ to_sectors ⟨1, -1⟩ = ⟨0, 2⟩ := by
  simp [to_sectors]

-- ============================================================
-- SMOKE TESTS
-- ============================================================

-- Lemniscate construction
#eval canonical_lemniscate.j_unit                -- (0, 1) = j
#eval canonical_lemniscate.crossing_point        -- (0, 0)
#eval canonical_lemniscate.involution ⟨3, 2⟩     -- (3, -2)

-- Sector lobes
#eval b_lobe    -- (1, 0): B-sector
#eval c_lobe    -- (0, 1): C-sector

-- Zero divisor demonstration
#eval SplitComplex.mul ⟨1, 1⟩ ⟨1, -1⟩    -- (0, 0): zero!

-- Sector decomposition of various elements
#eval to_sectors ⟨5, 3⟩     -- (8, 2)
#eval to_sectors ⟨1, 0⟩     -- (1, 1): balanced (real element)
#eval to_sectors SplitComplex.j  -- (1, -1): anti-balanced

end Tau.Polarity
