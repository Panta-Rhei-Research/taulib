import TauLib.BookI.Boundary.Characters

/-!
# TauLib.BookI.Boundary.Spectral

The spectral decomposition theorem for the bipolar spectral algebra.

## Registry Cross-References

- [I.T12] Spectral Decomposition — `spectral_decomposition`, `spectral_unique`

## Ground Truth Sources
- chunk_0228_M002194: Sector decomposition = spectral decomposition
- chunk_0310_M002679: Bipolar spectral analysis, character-based decomposition

## Mathematical Content

The spectral decomposition theorem gives a canonical decomposition of every
element z ∈ H_τ into B-sector and C-sector components via the fundamental
characters:

  to_sectors(z) = χ₊(z) + χ₋(z)

This is equivalent to the sector decomposition already proved in BipolarAlgebra.lean,
but repackaged in the language of characters and spectral theory.

Key results:
- Decomposition: every z decomposes uniquely as B-part + C-part
- Uniqueness: the decomposition is unique
- Multiplicativity: the spectral transform is a ring isomorphism
- Ring isomorphism: H_τ ≅ Z × Z via to_sectors
-/

namespace Tau.Boundary

open Tau.Polarity

-- ============================================================
-- SPECTRAL TRANSFORM [I.T12]
-- ============================================================

/-- [I.T12] The spectral transform: maps z to its (B-sector, C-sector) pair.
    This is to_sectors repackaged in spectral/character language. -/
def spectral (z : SplitComplex) : SectorPair := to_sectors z

/-- Spectral transform equals character decomposition. -/
theorem spectral_eq_chi (z : SplitComplex) :
    spectral z = ⟨chi_plus_val z, chi_minus_val z⟩ :=
  to_sectors_eq_chi z

-- ============================================================
-- SPECTRAL DECOMPOSITION THEOREM [I.T12]
-- ============================================================

/-- [I.T12] Spectral decomposition: every element decomposes as the sum of its
    B-sector projection and C-sector projection.
    to_sectors(z) = χ₊(z) + χ₋(z) -/
theorem spectral_decomposition (z : SplitComplex) :
    spectral z = SectorPair.add (chi_plus z) (chi_minus z) := by
  rw [spectral, ← chi_complete z]

/-- The B-component of the spectral decomposition. -/
def spectral_b (z : SplitComplex) : SectorPair := chi_plus z

/-- The C-component of the spectral decomposition. -/
def spectral_c (z : SplitComplex) : SectorPair := chi_minus z

/-- The B and C components are orthogonal. -/
theorem spectral_orthogonal (z : SplitComplex) :
    SectorPair.mul (spectral_b z) (spectral_c z) = SectorPair.zero :=
  chi_orthogonal z z

/-- The B and C components together reconstruct the spectral transform. -/
theorem spectral_reconstruct (z : SplitComplex) :
    SectorPair.add (spectral_b z) (spectral_c z) = spectral z :=
  (spectral_decomposition z).symm

-- ============================================================
-- UNIQUENESS
-- ============================================================

/-- [I.T12] Spectral uniqueness: if an element has the same spectral transform
    as another, they are equal. This is to_sectors injectivity in spectral language. -/
theorem spectral_unique (a b : SplitComplex) (h : spectral a = spectral b) :
    a = b :=
  to_sectors_injective a b h

/-- Two elements have equal B-sectors and C-sectors iff they are equal. -/
theorem spectral_eq_iff (a b : SplitComplex) :
    spectral a = spectral b ↔ a = b :=
  ⟨spectral_unique a b, fun h => h ▸ rfl⟩

-- ============================================================
-- MULTIPLICATIVITY (RING ISOMORPHISM)
-- ============================================================

/-- The spectral transform preserves multiplication (componentwise in sectors). -/
theorem spectral_mul (a b : SplitComplex) :
    spectral (SplitComplex.mul a b) =
    SectorPair.mul (spectral a) (spectral b) :=
  sectors_mul a b

/-- The spectral transform preserves addition. -/
theorem spectral_add (a b : SplitComplex) :
    spectral (SplitComplex.add a b) =
    SectorPair.add (spectral a) (spectral b) :=
  sectors_add a b

/-- The spectral transform preserves one. -/
theorem spectral_one : spectral SplitComplex.one = SectorPair.one :=
  to_sectors_one

/-- The spectral transform preserves zero. -/
theorem spectral_zero : spectral SplitComplex.zero = SectorPair.zero :=
  to_sectors_zero

/-- The spectral transform preserves negation. -/
theorem spectral_neg (z : SplitComplex) :
    spectral (SplitComplex.neg z) = SectorPair.neg (spectral z) :=
  to_sectors_neg z

/-- Full ring isomorphism: spectral is a ring homomorphism that is also injective. -/
theorem spectral_ring_iso :
    -- Preserves addition
    (∀ (a b : SplitComplex), spectral (SplitComplex.add a b) =
      SectorPair.add (spectral a) (spectral b)) ∧
    -- Preserves multiplication
    (∀ (a b : SplitComplex), spectral (SplitComplex.mul a b) =
      SectorPair.mul (spectral a) (spectral b)) ∧
    -- Preserves one
    (spectral SplitComplex.one = SectorPair.one) ∧
    -- Injective
    (∀ (a b : SplitComplex), spectral a = spectral b → a = b) :=
  ⟨spectral_add, spectral_mul, spectral_one, spectral_unique⟩

-- ============================================================
-- SPECTRAL PROPERTIES OF SPECIAL ELEMENTS
-- ============================================================

/-- The spectral transform of j: B-sector = 1, C-sector = -1. -/
theorem spectral_j : spectral SplitComplex.j = ⟨1, -1⟩ := by
  simp [spectral, to_sectors, SplitComplex.j]

/-- The spectral transform of 1: both sectors equal 1. -/
theorem spectral_one_val : spectral SplitComplex.one = ⟨1, 1⟩ := by
  simp [spectral, to_sectors, SplitComplex.one]

/-- A real element (im = 0) has equal sector values. -/
theorem spectral_real (a : Int) :
    spectral ⟨a, 0⟩ = ⟨a, a⟩ := by
  simp [spectral, to_sectors]

/-- A purely imaginary element (re = 0) has opposite sector values. -/
theorem spectral_imaginary (b : Int) :
    spectral ⟨0, b⟩ = ⟨b, -b⟩ := by
  simp [spectral, to_sectors]

-- ============================================================
-- POLARITY INVOLUTION IN SPECTRAL COORDINATES
-- ============================================================

/-- The polarity involution σ swaps the spectral components. -/
theorem spectral_sigma (z : SplitComplex) :
    spectral (polarity_inv z) =
    ⟨(spectral z).c_sector, (spectral z).b_sector⟩ := by
  simp [spectral]
  exact polarity_inv_swaps_sectors z

/-- σ is a spectral reflection: it exchanges B and C sectors. -/
theorem spectral_sigma_involutive (z : SplitComplex) :
    spectral (polarity_inv (polarity_inv z)) = spectral z := by
  rw [polarity_inv_squared]

-- ============================================================
-- SPECTRAL NORMS
-- ============================================================

/-- The spectral norm: product of B-sector and C-sector values.
    This is the norm form N(a+bj) = a² - b² = (a+b)(a-b). -/
def spectral_norm (z : SplitComplex) : Int :=
  (spectral z).b_sector * (spectral z).c_sector

/-- The spectral norm equals a² - b² (the split-complex norm). -/
theorem spectral_norm_eq (z : SplitComplex) :
    spectral_norm z = z.re * z.re - z.im * z.im := by
  simp only [spectral_norm, spectral, to_sectors]
  ring

/-- The spectral norm is multiplicative: N(zw) = N(z)N(w). -/
theorem spectral_norm_mul (z w : SplitComplex) :
    spectral_norm (SplitComplex.mul z w) =
    spectral_norm z * spectral_norm w := by
  simp only [spectral_norm]
  rw [spectral_mul]
  simp [SectorPair.mul]
  ring

/-- Zero divisors have zero spectral norm. -/
theorem zero_div_iff_norm_zero (z : SplitComplex) :
    spectral_norm z = 0 ↔ (z.re + z.im = 0 ∨ z.re - z.im = 0) := by
  simp only [spectral_norm, spectral, to_sectors]
  exact mul_eq_zero

-- ============================================================
-- NATIVE_DECIDE VERIFICATIONS
-- ============================================================

-- Spectral values
example : spectral ⟨3, 2⟩ = ⟨5, 1⟩ := by native_decide
example : spectral ⟨1, 0⟩ = ⟨1, 1⟩ := by native_decide
example : spectral SplitComplex.j = ⟨1, -1⟩ := by native_decide

-- Multiplicativity
example : spectral (SplitComplex.mul ⟨3, 2⟩ ⟨1, 4⟩) =
    SectorPair.mul (spectral ⟨3, 2⟩) (spectral ⟨1, 4⟩) := by native_decide

-- Spectral norm
example : spectral_norm ⟨3, 2⟩ = 5 := by native_decide
example : spectral_norm ⟨1, 1⟩ = 0 := by native_decide  -- zero divisor!

-- ============================================================
-- SMOKE TESTS
-- ============================================================

#eval spectral ⟨3, 2⟩            -- ⟨5, 1⟩
#eval spectral ⟨5, 3⟩            -- ⟨8, 2⟩
#eval spectral SplitComplex.j    -- ⟨1, -1⟩
#eval spectral_norm ⟨3, 2⟩       -- 5
#eval spectral_norm ⟨1, 1⟩       -- 0 (zero divisor)
#eval spectral_norm ⟨5, 3⟩       -- 16

-- Polarity involution swaps sectors
#eval spectral (polarity_inv ⟨3, 2⟩)   -- ⟨1, 5⟩ (swapped from ⟨5, 1⟩)

end Tau.Boundary
