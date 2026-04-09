import TauLib.BookI.Boundary.Spectral

/-!
# TauLib.BookI.Boundary.Fourier

The crossing point, sector ideals, and bipolar Fourier analysis on the lemniscate.

## Registry Cross-References

- [I.D39] Crossing Point — `crossing_point`, `crossing_iff_equal_sectors`
- [I.D40] Bipolar Fourier Transform — `fourier`, `fourier_e_plus`, `fourier_e_minus`

## Ground Truth Sources
- chunk_0228_M002194: Sector decomposition, crossing locus
- chunk_0310_M002679: Bipolar Fourier, spectral harmonic analysis

## Mathematical Content

The crossing point of the lemniscate is the algebraic locus where the two
lobes (sectors) meet. In sector coordinates, the crossing point condition is
b_sector = c_sector, which for split-complex elements means im = 0 (real line).

The B-ideal and C-ideal are the kernel ideals of the characters χ₋ and χ₊
respectively. They correspond to the two lobes of the lemniscate.

The bipolar Fourier transform is the spectral decomposition viewed as
harmonic analysis on the lemniscate: every element of H_τ has a unique
expansion in terms of B-sector and C-sector harmonics.
-/

namespace Tau.Boundary

open Tau.Polarity

-- ============================================================
-- CROSSING POINT [I.D39]
-- ============================================================

/-- [I.D39] The crossing point in sector coordinates: both sectors equal.
    This is the algebraic locus where the two lobes of the lemniscate meet. -/
def crossing_point : SectorPair := ⟨1, 1⟩

/-- An element is at the crossing iff its sectors are equal. -/
def is_crossing (s : SectorPair) : Prop := s.b_sector = s.c_sector

instance (s : SectorPair) : Decidable (is_crossing s) :=
  inferInstanceAs (Decidable (s.b_sector = s.c_sector))

/-- [I.D39] Crossing characterization: a split-complex element z is at the crossing
    iff z is real (im = 0). Proof: b_sector = c_sector iff re+im = re-im iff im = 0. -/
theorem crossing_iff_real (z : SplitComplex) :
    is_crossing (spectral z) ↔ z.im = 0 := by
  simp only [is_crossing, spectral, to_sectors]
  constructor
  · intro h; omega
  · intro h; omega

/-- The crossing point condition in character language:
    z is at the crossing iff χ₊(z) = χ₋(z). -/
theorem crossing_iff_chi_equal (z : SplitComplex) :
    is_crossing (spectral z) ↔ chi_plus_val z = chi_minus_val z := by
  rw [spectral_eq_chi z]
  exact Iff.rfl

/-- The multiplicative identity is at the crossing. -/
theorem one_is_crossing : is_crossing (spectral SplitComplex.one) := by
  simp [spectral, to_sectors, SplitComplex.one, is_crossing]

/-- The split-complex unit j is NOT at the crossing (sectors differ). -/
theorem j_not_crossing : ¬is_crossing (spectral SplitComplex.j) := by
  simp [spectral, to_sectors, SplitComplex.j, is_crossing]

-- ============================================================
-- SECTOR IDEALS
-- ============================================================

/-- An element is in the B-ideal iff its C-sector vanishes.
    The B-ideal = ker(χ₋) = {z : z.re = z.im}. -/
def in_b_ideal (z : SplitComplex) : Prop :=
  (spectral z).c_sector = 0

/-- An element is in the C-ideal iff its B-sector vanishes.
    The C-ideal = ker(χ₊) = {z : z.re + z.im = 0}. -/
def in_c_ideal (z : SplitComplex) : Prop :=
  (spectral z).b_sector = 0

instance (z : SplitComplex) : Decidable (in_b_ideal z) :=
  inferInstanceAs (Decidable ((spectral z).c_sector = 0))

instance (z : SplitComplex) : Decidable (in_c_ideal z) :=
  inferInstanceAs (Decidable ((spectral z).b_sector = 0))

/-- B-ideal characterization: z is in the B-ideal iff z.re = z.im. -/
theorem b_ideal_iff (z : SplitComplex) :
    in_b_ideal z ↔ z.re = z.im := by
  simp only [in_b_ideal, spectral, to_sectors]
  constructor <;> intro h <;> omega

/-- C-ideal characterization: z is in the C-ideal iff z.re + z.im = 0. -/
theorem c_ideal_iff (z : SplitComplex) :
    in_c_ideal z ↔ z.re + z.im = 0 := by
  simp only [in_c_ideal, spectral, to_sectors]

/-- The B-ideal and C-ideal are orthogonal: their product is zero.
    If z ∈ ker(χ₋) and w ∈ ker(χ₊), then z·w = 0 in sector coordinates. -/
theorem b_times_c_zero (z w : SplitComplex)
    (hz : in_b_ideal z) (hw : in_c_ideal w) :
    spectral (SplitComplex.mul z w) = SectorPair.zero := by
  rw [spectral_mul]
  unfold in_b_ideal at hz
  unfold in_c_ideal at hw
  simp only [SectorPair.mul, SectorPair.zero, SectorPair.mk.injEq]
  exact ⟨by rw [hw]; ring, by rw [hz]; ring⟩

/-- The B-ideal is closed under addition. -/
theorem b_ideal_add (z w : SplitComplex)
    (hz : in_b_ideal z) (hw : in_b_ideal w) :
    in_b_ideal (SplitComplex.add z w) := by
  simp only [in_b_ideal, spectral, to_sectors, SplitComplex.add] at *
  omega

/-- The C-ideal is closed under addition. -/
theorem c_ideal_add (z w : SplitComplex)
    (hz : in_c_ideal z) (hw : in_c_ideal w) :
    in_c_ideal (SplitComplex.add z w) := by
  simp only [in_c_ideal, spectral, to_sectors, SplitComplex.add] at *
  omega

/-- The B-ideal is closed under multiplication. -/
theorem b_ideal_mul (z w : SplitComplex) (hz : in_b_ideal z) :
    in_b_ideal (SplitComplex.mul z w) := by
  simp only [in_b_ideal] at *
  rw [spectral_mul]
  simp [SectorPair.mul, hz]

/-- The C-ideal is closed under multiplication. -/
theorem c_ideal_mul (z w : SplitComplex) (hz : in_c_ideal z) :
    in_c_ideal (SplitComplex.mul z w) := by
  simp only [in_c_ideal] at *
  rw [spectral_mul]
  simp [SectorPair.mul, hz]

-- ============================================================
-- BIPOLAR FOURIER TRANSFORM [I.D40]
-- ============================================================

/-- [I.D40] The bipolar Fourier transform: maps z to its spectral decomposition.
    This is the spectral transform repackaged as harmonic analysis. -/
def fourier (z : SplitComplex) : SectorPair := spectral z

/-- Fourier transform of e₊ = (1,1) in split-complex: maps to pure B-sector. -/
theorem fourier_e_plus_sc :
    fourier ⟨1, 1⟩ = ⟨2, 0⟩ := by
  simp [fourier, spectral, to_sectors]

/-- Fourier transform of e₋ = (1,-1) in split-complex: maps to pure C-sector. -/
theorem fourier_e_minus_sc :
    fourier ⟨1, -1⟩ = ⟨0, 2⟩ := by
  simp [fourier, spectral, to_sectors]

/-- Fourier of the sector idempotent e₊: pure B-sector. -/
theorem fourier_e_plus_sector (z : SplitComplex) :
    SectorPair.mul e_plus_sector (spectral z) = ⟨(spectral z).b_sector, 0⟩ := by
  simp [e_plus_sector, SectorPair.mul]

/-- Fourier of the sector idempotent e₋: pure C-sector. -/
theorem fourier_e_minus_sector (z : SplitComplex) :
    SectorPair.mul e_minus_sector (spectral z) = ⟨0, (spectral z).c_sector⟩ := by
  simp [e_minus_sector, SectorPair.mul]

-- ============================================================
-- FOURIER INVERSION
-- ============================================================

/-- Fourier inversion: the spectral transform can be inverted via from_sectors. -/
theorem fourier_invertible (z : SplitComplex) :
    from_sectors (fourier z) = z :=
  from_sectors_left_inv z

/-- The Fourier transform is injective. -/
theorem fourier_injective (a b : SplitComplex) (h : fourier a = fourier b) :
    a = b :=
  spectral_unique a b h

-- ============================================================
-- σ AS FOURIER COMPONENT SWAP [I.D40]
-- ============================================================

/-- [I.D40] σ = component swap in Fourier coordinates: σ exchanges B ↔ C harmonics. -/
theorem fourier_sigma_swap (z : SplitComplex) :
    fourier (polarity_inv z) =
    ⟨(fourier z).c_sector, (fourier z).b_sector⟩ :=
  spectral_sigma z

/-- Fourier-space characterization of fixed points of σ: z is σ-fixed iff z is real. -/
theorem sigma_fixed_iff_real (z : SplitComplex) :
    polarity_inv z = z ↔ z.im = 0 := by
  constructor
  · intro h
    have := congrArg SplitComplex.im h
    simp [polarity_inv] at this
    omega
  · intro h
    ext
    · simp [polarity_inv]
    · simp [polarity_inv, h]

/-- Fourier-space characterization of anti-fixed points: polarity_inv z = -z iff z is pure imaginary. -/
theorem sigma_anti_fixed_iff_imaginary (z : SplitComplex) :
    polarity_inv z = SplitComplex.neg z ↔ z.re = 0 := by
  constructor
  · intro h
    have := congrArg SplitComplex.re h
    simp [polarity_inv, SplitComplex.neg] at this
    omega
  · intro h
    ext <;> simp [polarity_inv, SplitComplex.neg, h]

-- ============================================================
-- PARSEVAL-TYPE IDENTITY
-- ============================================================

/-- A Parseval-type identity: the spectral norm equals the product of Fourier components.
    N(z) = (Fourier B-component) · (Fourier C-component). -/
theorem fourier_parseval (z : SplitComplex) :
    spectral_norm z = (fourier z).b_sector * (fourier z).c_sector := rfl

-- ============================================================
-- NATIVE_DECIDE VERIFICATIONS
-- ============================================================

-- Fourier transform
example : fourier ⟨3, 2⟩ = ⟨5, 1⟩ := by native_decide
example : fourier ⟨1, 0⟩ = ⟨1, 1⟩ := by native_decide  -- real → crossing
example : fourier ⟨0, 3⟩ = ⟨3, -3⟩ := by native_decide  -- imaginary → anti-diagonal

-- Ideals
example : in_b_ideal ⟨2, 2⟩ = True := by native_decide
example : in_c_ideal ⟨3, -3⟩ = True := by native_decide

-- Crossing
example : is_crossing (fourier ⟨5, 0⟩) = True := by native_decide
example : is_crossing (fourier ⟨3, 2⟩) = False := by native_decide

-- ============================================================
-- SMOKE TESTS
-- ============================================================

#eval fourier ⟨3, 2⟩             -- ⟨5, 1⟩
#eval fourier ⟨1, 0⟩             -- ⟨1, 1⟩ (crossing point)
#eval fourier ⟨1, 1⟩             -- ⟨2, 0⟩ (B-ideal element)
#eval fourier ⟨1, -1⟩            -- ⟨0, 2⟩ (C-ideal element)
#eval from_sectors (fourier ⟨3, 2⟩)   -- ⟨3, 2⟩ (inversion)

-- Ideals
#eval in_b_ideal ⟨2, 2⟩          -- true
#eval in_c_ideal ⟨3, -3⟩         -- true
#eval in_b_ideal ⟨3, 2⟩          -- false

-- Crossing
#eval is_crossing (fourier ⟨5, 0⟩)    -- true (real)
#eval is_crossing (fourier ⟨3, 2⟩)    -- false

end Tau.Boundary
