import TauLib.BookI.Boundary.SplitComplex
import TauLib.BookI.Polarity.Lemniscate
import Mathlib.Tactic.Ring

/-!
# TauLib.BookI.Boundary.Characters

Lemniscate characters: ring homomorphisms from the bipolar spectral algebra
into the split-complex scalars.

## Registry Cross-References

- [I.D37] Fundamental Characters — `chi_plus`, `chi_minus`
- [I.D38] Character Group — completeness, orthogonality

## Ground Truth Sources
- chunk_0228_M002194: Split-complex algebra, sector decomposition
- chunk_0310_M002679: Bipolar partition, character theory of L

## Mathematical Content

The fundamental characters χ₊ and χ₋ are ring homomorphisms from H_τ = Z[j]
into Z (or equivalently, into the product ring Z×Z via sector embedding):

- χ₊(a + bj) = a + b   (B-sector projection)
- χ₋(a + bj) = a - b   (C-sector projection)

Viewed as SectorPair-valued maps:
- χ₊(z) = ⟨z.re + z.im, 0⟩   (pure B-sector element)
- χ₋(z) = ⟨0, z.re - z.im⟩   (pure C-sector element)

Key properties:
- Completeness: χ₊(z) + χ₋(z) = to_sectors(z) (the full sector decomposition)
- Orthogonality: χ₊(z) · χ₋(w) = 0 (sectors are mutually annihilating)
- σ swaps: χ₊(σz) = χ₋(z) and χ₋(σz) = χ₊(z)
-/

namespace Tau.Boundary

open Tau.Polarity

-- ============================================================
-- FUNDAMENTAL CHARACTERS [I.D37]
-- ============================================================

/-- [I.D37] The B-sector character χ₊: H_τ → Z, mapping a+bj ↦ a+b.
    As a SectorPair-valued map: projects to pure B-sector. -/
def chi_plus (z : SplitComplex) : SectorPair :=
  ⟨z.re + z.im, 0⟩

/-- [I.D37] The C-sector character χ₋: H_τ → Z, mapping a+bj ↦ a-b.
    As a SectorPair-valued map: projects to pure C-sector. -/
def chi_minus (z : SplitComplex) : SectorPair :=
  ⟨0, z.re - z.im⟩

/-- The B-sector value as an integer. -/
def chi_plus_val (z : SplitComplex) : Int := z.re + z.im

/-- The C-sector value as an integer. -/
def chi_minus_val (z : SplitComplex) : Int := z.re - z.im

/-- Bridge: chi_plus decomposes as sector-embedded chi_plus_val. -/
theorem chi_plus_eq (z : SplitComplex) :
    chi_plus z = ⟨chi_plus_val z, 0⟩ := rfl

/-- Bridge: chi_minus decomposes as sector-embedded chi_minus_val. -/
theorem chi_minus_eq (z : SplitComplex) :
    chi_minus z = ⟨0, chi_minus_val z⟩ := rfl

-- ============================================================
-- χ₊ IS A RING HOMOMORPHISM
-- ============================================================

/-- χ₊ preserves addition. -/
theorem chi_plus_add (a b : SplitComplex) :
    chi_plus (SplitComplex.add a b) =
    SectorPair.add (chi_plus a) (chi_plus b) := by
  simp only [chi_plus, SplitComplex.add, SectorPair.add, SectorPair.mk.injEq]
  constructor <;> ring

/-- χ₊ preserves multiplication. -/
theorem chi_plus_mul (a b : SplitComplex) :
    chi_plus (SplitComplex.mul a b) =
    SectorPair.mul (chi_plus a) (chi_plus b) := by
  simp only [chi_plus, SplitComplex.mul, SectorPair.mul, SectorPair.mk.injEq]
  constructor
  · ring
  · ring

/-- χ₊ maps the identity to ⟨1, 0⟩ (pure B-sector unit). -/
theorem chi_plus_one :
    chi_plus SplitComplex.one = ⟨1, 0⟩ := by
  simp [chi_plus, SplitComplex.one]

/-- χ₊ preserves zero. -/
theorem chi_plus_zero :
    chi_plus SplitComplex.zero = SectorPair.zero := by
  simp [chi_plus, SplitComplex.zero, SectorPair.zero]

/-- χ₊ preserves negation. -/
theorem chi_plus_neg (z : SplitComplex) :
    chi_plus (SplitComplex.neg z) = SectorPair.neg (chi_plus z) := by
  simp only [chi_plus, SplitComplex.neg, SectorPair.neg, SectorPair.mk.injEq]
  constructor <;> ring

-- ============================================================
-- χ₋ IS A RING HOMOMORPHISM
-- ============================================================

/-- χ₋ preserves addition. -/
theorem chi_minus_add (a b : SplitComplex) :
    chi_minus (SplitComplex.add a b) =
    SectorPair.add (chi_minus a) (chi_minus b) := by
  simp only [chi_minus, SplitComplex.add, SectorPair.add, SectorPair.mk.injEq]
  constructor <;> ring

/-- χ₋ preserves multiplication. -/
theorem chi_minus_mul (a b : SplitComplex) :
    chi_minus (SplitComplex.mul a b) =
    SectorPair.mul (chi_minus a) (chi_minus b) := by
  simp only [chi_minus, SplitComplex.mul, SectorPair.mul, SectorPair.mk.injEq]
  constructor
  · ring
  · ring

/-- χ₋ maps the identity to ⟨0, 1⟩ (pure C-sector unit). -/
theorem chi_minus_one :
    chi_minus SplitComplex.one = ⟨0, 1⟩ := by
  simp [chi_minus, SplitComplex.one]

/-- χ₋ preserves zero. -/
theorem chi_minus_zero :
    chi_minus SplitComplex.zero = SectorPair.zero := by
  simp [chi_minus, SplitComplex.zero, SectorPair.zero]

/-- χ₋ preserves negation. -/
theorem chi_minus_neg (z : SplitComplex) :
    chi_minus (SplitComplex.neg z) = SectorPair.neg (chi_minus z) := by
  simp only [chi_minus, SplitComplex.neg, SectorPair.neg, SectorPair.mk.injEq]
  constructor <;> ring

-- ============================================================
-- COMPLETENESS [I.D38]
-- ============================================================

/-- [I.D38] Completeness: χ₊(z) + χ₋(z) = to_sectors(z).
    The two characters together reconstruct the full sector decomposition. -/
theorem chi_complete (z : SplitComplex) :
    SectorPair.add (chi_plus z) (chi_minus z) = to_sectors z := by
  simp only [chi_plus, chi_minus, SectorPair.add, to_sectors, SectorPair.mk.injEq]
  constructor <;> omega

/-- Completeness in terms of values: the sector pair equals (χ₊ val, χ₋ val). -/
theorem to_sectors_eq_chi (z : SplitComplex) :
    to_sectors z = ⟨chi_plus_val z, chi_minus_val z⟩ := by
  simp [to_sectors, chi_plus_val, chi_minus_val]

-- ============================================================
-- ORTHOGONALITY [I.D38]
-- ============================================================

/-- [I.D38] Orthogonality: χ₊(z) · χ₋(w) = 0 for all z, w.
    The B-sector and C-sector are mutually annihilating. -/
theorem chi_orthogonal (z w : SplitComplex) :
    SectorPair.mul (chi_plus z) (chi_minus w) = SectorPair.zero := by
  simp [chi_plus, chi_minus, SectorPair.mul, SectorPair.zero]

/-- Orthogonality in the other order. -/
theorem chi_orthogonal' (z w : SplitComplex) :
    SectorPair.mul (chi_minus z) (chi_plus w) = SectorPair.zero := by
  simp [chi_plus, chi_minus, SectorPair.mul, SectorPair.zero]

-- ============================================================
-- IDEMPOTENT PROJECTIONS
-- ============================================================

/-- χ₊ is an idempotent projection: χ₊² = χ₊ (in the sector ring). -/
theorem chi_plus_idempotent (z : SplitComplex) :
    SectorPair.mul (chi_plus z) (chi_plus z) =
    ⟨(z.re + z.im) * (z.re + z.im), 0⟩ := by
  simp [chi_plus, SectorPair.mul]

/-- χ₊ of e₊ = e₊ (the character selects its own idempotent). -/
theorem chi_plus_of_e_plus :
    chi_plus ⟨1, 1⟩ = ⟨2, 0⟩ := by
  simp [chi_plus]

/-- χ₋ of e₋ = e₋ (the character selects its own idempotent). -/
theorem chi_minus_of_e_minus :
    chi_minus ⟨1, -1⟩ = ⟨0, 2⟩ := by
  simp [chi_minus]

/-- χ₊ of e₋ = 0 (the B-character annihilates the C-idempotent). -/
theorem chi_plus_of_e_minus :
    chi_plus ⟨1, -1⟩ = SectorPair.zero := by
  simp [chi_plus, SectorPair.zero]

/-- χ₋ of e₊ = 0 (the C-character annihilates the B-idempotent). -/
theorem chi_minus_of_e_plus :
    chi_minus ⟨1, 1⟩ = SectorPair.zero := by
  simp [chi_minus, SectorPair.zero]

-- ============================================================
-- POLARITY INVOLUTION AND CHARACTERS
-- ============================================================

/-- σ swaps characters: χ₊(σz) = χ₋(z) (as SectorPair values with sector swap). -/
theorem sigma_swaps_chi_plus (z : SplitComplex) :
    chi_plus_val (polarity_inv z) = chi_minus_val z := by
  simp [chi_plus_val, chi_minus_val, polarity_inv]; ring

/-- σ swaps characters: χ₋(σz) = χ₊(z). -/
theorem sigma_swaps_chi_minus (z : SplitComplex) :
    chi_minus_val (polarity_inv z) = chi_plus_val z := by
  simp [chi_minus_val, chi_plus_val, polarity_inv]; try ring

/-- σ swaps the SectorPair-valued characters (with coordinate exchange). -/
theorem sigma_swaps_chi (z : SplitComplex) :
    chi_plus (polarity_inv z) = ⟨chi_minus_val z, 0⟩ ∧
    chi_minus (polarity_inv z) = ⟨0, chi_plus_val z⟩ := by
  constructor
  · simp [chi_plus, polarity_inv, chi_minus_val]; try ring
  · simp [chi_minus, polarity_inv, chi_plus_val]; try ring

-- ============================================================
-- BRIDGE TO CHI_SPLIT [chunk_0310]
-- ============================================================

/-- Bridge: for a B-dominant prime (polarity_chi = -1), chi_split maps to
    e_plus_sector = (1,0), which is in the image of chi_plus (up to scaling). -/
theorem chi_split_b_sector (p N : Tau.Denotation.TauIdx) (h : polarity_chi p N = -1) :
    chi_split p N = e_plus_sector :=
  chi_split_of_b p N h

/-- Bridge: for a C-dominant prime (polarity_chi = +1), chi_split maps to
    e_minus_sector = (0,1), which is in the image of chi_minus (up to scaling). -/
theorem chi_split_c_sector (p N : Tau.Denotation.TauIdx) (h : polarity_chi p N = 1) :
    chi_split p N = e_minus_sector :=
  chi_split_of_c p N h

-- ============================================================
-- CHARACTER VALUES ON J
-- ============================================================

/-- χ₊(j) = 1: the split-complex unit j has B-sector value 1. -/
theorem chi_plus_j : chi_plus_val SplitComplex.j = 1 := by
  simp [chi_plus_val, SplitComplex.j]

/-- χ₋(j) = -1: the split-complex unit j has C-sector value -1. -/
theorem chi_minus_j : chi_minus_val SplitComplex.j = -1 := by
  simp [chi_minus_val, SplitComplex.j]

/-- χ₊(1) = 1 and χ₋(1) = 1. -/
theorem chi_vals_one : chi_plus_val SplitComplex.one = 1 ∧ chi_minus_val SplitComplex.one = 1 := by
  simp [chi_plus_val, chi_minus_val, SplitComplex.one]

-- ============================================================
-- NATIVE_DECIDE VERIFICATIONS
-- ============================================================

-- Character values
example : chi_plus ⟨3, 2⟩ = ⟨5, 0⟩ := by native_decide
example : chi_minus ⟨3, 2⟩ = ⟨0, 1⟩ := by native_decide
example : chi_plus ⟨1, 1⟩ = ⟨2, 0⟩ := by native_decide
example : chi_minus ⟨1, -1⟩ = ⟨0, 2⟩ := by native_decide

-- Completeness
example : SectorPair.add (chi_plus ⟨3, 2⟩) (chi_minus ⟨3, 2⟩) = to_sectors ⟨3, 2⟩ := by native_decide
example : SectorPair.add (chi_plus ⟨7, -4⟩) (chi_minus ⟨7, -4⟩) = to_sectors ⟨7, -4⟩ := by native_decide

-- Orthogonality
example : SectorPair.mul (chi_plus ⟨3, 2⟩) (chi_minus ⟨5, 1⟩) = SectorPair.zero := by native_decide
example : SectorPair.mul (chi_minus ⟨7, 3⟩) (chi_plus ⟨2, -1⟩) = SectorPair.zero := by native_decide

-- Homomorphism checks
example : chi_plus (SplitComplex.mul ⟨3, 2⟩ ⟨1, 4⟩) =
    SectorPair.mul (chi_plus ⟨3, 2⟩) (chi_plus ⟨1, 4⟩) := by native_decide
example : chi_minus (SplitComplex.add ⟨3, 2⟩ ⟨1, 4⟩) =
    SectorPair.add (chi_minus ⟨3, 2⟩) (chi_minus ⟨1, 4⟩) := by native_decide

-- ============================================================
-- SMOKE TESTS
-- ============================================================

#eval chi_plus ⟨3, 2⟩        -- ⟨5, 0⟩
#eval chi_minus ⟨3, 2⟩       -- ⟨0, 1⟩
#eval chi_plus_val ⟨3, 2⟩    -- 5
#eval chi_minus_val ⟨3, 2⟩   -- 1

-- Completeness
#eval SectorPair.add (chi_plus ⟨5, 3⟩) (chi_minus ⟨5, 3⟩)  -- ⟨8, 2⟩ = to_sectors ⟨5, 3⟩
#eval to_sectors ⟨5, 3⟩                                      -- ⟨8, 2⟩ ✓

-- Character on j
#eval chi_plus SplitComplex.j     -- ⟨1, 0⟩
#eval chi_minus SplitComplex.j    -- ⟨0, -1⟩

-- Polarity involution
#eval chi_plus (polarity_inv ⟨3, 2⟩)    -- ⟨1, 0⟩ = chi_minus value of ⟨3, 2⟩
#eval chi_minus (polarity_inv ⟨3, 2⟩)   -- ⟨0, 5⟩ = chi_plus value of ⟨3, 2⟩

end Tau.Boundary
