import TauLib.BookI.Polarity.PolarizedGerms
import Mathlib.Tactic.Ring
import Mathlib.Tactic.LinearCombination

/-!
# TauLib.BookI.Polarity.BipolarAlgebra

The bipolar spectral algebra H_τ with split-complex scalars.

## Registry Cross-References

- [I.D28] Boundary Local Ring — `BdryRing`
- [I.T10] Split-Complex Forced — `split_complex_forced`, `no_elliptic_idempotent`
- [I.D27] Bipolar Spectral Algebra — `SplitComplex`, `e_plus`, `e_minus`

## Ground Truth Sources
- chunk_0228_M002194: Split-complex algebra, bipolar balance, τ-RH scalar structure
- chunk_0310_M002679: Bipolar partition lifts to split-complex via Chi character

## Mathematical Content

The boundary local ring ℤ̂_τ = lim Z/M_k Z inherits componentwise ring structure.
Extending by the split-complex unit j (with j² = +1) gives the bipolar spectral
algebra H_τ = ℤ̂_τ[j].

The key theorem (I.T10): split-complex scalars (j² = +1) are FORCED by the bipolar
prime partition. The elliptic alternative (i² = -1) admits no nontrivial idempotents
over Z, so it cannot encode the bipolar structure.

The canonical idempotents e± = (1±j)/2 decompose H_τ into B-sector and C-sector,
mirroring the polarity partition of the primes.
-/

namespace Tau.Polarity

open Tau.Denotation

-- ============================================================
-- BOUNDARY RING (componentwise operations on omega-tails)
-- ============================================================

/-- Boundary ring element at stage k: a pair of Z/M_kZ values (for add/mul). -/
def bdry_add (x y k : TauIdx) : TauIdx := (x + y) % primorial k
def bdry_mul (x y k : TauIdx) : TauIdx := (x * y) % primorial k
def bdry_neg (x k : TauIdx) : TauIdx := (primorial k - x % primorial k) % primorial k

-- ============================================================
-- SPLIT-COMPLEX ALGEBRA [I.D27]
-- ============================================================

/-- [I.D27] Split-complex number: a + bj where j² = +1.
    Represented as a pair of integers. -/
structure SplitComplex where
  re : Int
  im : Int
  deriving DecidableEq, Repr

instance : Inhabited SplitComplex := ⟨⟨0, 0⟩⟩

/-- Split-complex zero. -/
def SplitComplex.zero : SplitComplex := ⟨0, 0⟩

/-- Split-complex one. -/
def SplitComplex.one : SplitComplex := ⟨1, 0⟩

/-- The split-complex unit j. -/
def SplitComplex.j : SplitComplex := ⟨0, 1⟩

/-- Split-complex addition. -/
def SplitComplex.add (a b : SplitComplex) : SplitComplex :=
  ⟨a.re + b.re, a.im + b.im⟩

/-- Split-complex negation. -/
def SplitComplex.neg (a : SplitComplex) : SplitComplex :=
  ⟨-a.re, -a.im⟩

/-- Split-complex multiplication: (a + bj)(c + dj) = (ac + bd) + (ad + bc)j.
    Uses j² = +1. -/
def SplitComplex.mul (a b : SplitComplex) : SplitComplex :=
  ⟨a.re * b.re + a.im * b.im, a.re * b.im + a.im * b.re⟩

/-- Split-complex subtraction. -/
def SplitComplex.sub (a b : SplitComplex) : SplitComplex :=
  a.add b.neg

-- ============================================================
-- j² = +1 (FUNDAMENTAL IDENTITY)
-- ============================================================

/-- j² = 1: the defining property of split-complex numbers. -/
theorem j_squared : SplitComplex.mul SplitComplex.j SplitComplex.j = SplitComplex.one := by
  simp [SplitComplex.j, SplitComplex.mul, SplitComplex.one]

-- ============================================================
-- SECTOR DECOMPOSITION
-- ============================================================

/-- [I.D27] Sector pair: the isomorphic representation (u, v) = (re + im, re - im).
    In sector coordinates, multiplication is componentwise. -/
structure SectorPair where
  b_sector : Int  -- = re + im
  c_sector : Int  -- = re - im
  deriving DecidableEq, Repr

/-- Convert split-complex to sector representation. -/
def to_sectors (z : SplitComplex) : SectorPair :=
  ⟨z.re + z.im, z.re - z.im⟩

/-- Sector addition (componentwise). -/
def SectorPair.add (a b : SectorPair) : SectorPair :=
  ⟨a.b_sector + b.b_sector, a.c_sector + b.c_sector⟩

/-- Sector multiplication (componentwise). -/
def SectorPair.mul (a b : SectorPair) : SectorPair :=
  ⟨a.b_sector * b.b_sector, a.c_sector * b.c_sector⟩

/-- Homomorphism check: to_sectors preserves addition. -/
theorem sectors_add (a b : SplitComplex) :
    to_sectors (SplitComplex.add a b) =
    SectorPair.add (to_sectors a) (to_sectors b) := by
  simp [to_sectors, SplitComplex.add, SectorPair.add]
  omega

/-- Homomorphism check: to_sectors preserves multiplication. -/
theorem sectors_mul (a b : SplitComplex) :
    to_sectors (SplitComplex.mul a b) =
    SectorPair.mul (to_sectors a) (to_sectors b) := by
  simp only [to_sectors, SplitComplex.mul, SectorPair.mul, SectorPair.mk.injEq]
  constructor <;> ring

-- ============================================================
-- IDEMPOTENTS [I.D27]
-- ============================================================

/-- The B-sector idempotent e+ in sector coordinates: (1, 0).
    In split-complex coordinates: e+ = (1+j)/2 (defined over Z[1/2]). -/
def e_plus_sector : SectorPair := ⟨1, 0⟩

/-- The C-sector idempotent e- in sector coordinates: (0, 1). -/
def e_minus_sector : SectorPair := ⟨0, 1⟩

/-- e+² = e+ (idempotent). -/
theorem e_plus_idem : SectorPair.mul e_plus_sector e_plus_sector = e_plus_sector := by
  simp [e_plus_sector, SectorPair.mul]

/-- e-² = e- (idempotent). -/
theorem e_minus_idem : SectorPair.mul e_minus_sector e_minus_sector = e_minus_sector := by
  simp [e_minus_sector, SectorPair.mul]

/-- e+ · e- = 0 (orthogonal). -/
theorem e_orthogonal :
    SectorPair.mul e_plus_sector e_minus_sector = ⟨0, 0⟩ := by
  simp [e_plus_sector, e_minus_sector, SectorPair.mul]

/-- e+ + e- = 1 (partition of unity). -/
theorem e_partition :
    SectorPair.add e_plus_sector e_minus_sector = ⟨1, 1⟩ := by
  simp [e_plus_sector, e_minus_sector, SectorPair.add]

-- ============================================================
-- SPLIT-COMPLEX FORCED [I.T10]
-- ============================================================

/-- An "elliptic" number: a + bi where i² = -1.
    We represent as integer pairs (Gaussian integers). -/
structure GaussInt where
  re : Int
  im : Int
  deriving DecidableEq, Repr

/-- Gaussian integer multiplication: (a+bi)(c+di) = (ac-bd) + (ad+bc)i.
    Uses i² = -1. -/
def GaussInt.mul (a b : GaussInt) : GaussInt :=
  ⟨a.re * b.re - a.im * b.im, a.re * b.im + a.im * b.re⟩

@[ext]
theorem GaussInt.ext {a b : GaussInt} (hre : a.re = b.re) (him : a.im = b.im) : a = b := by
  cases a; cases b; simp_all

/-- Helper: Int is an integral domain (proved via natAbs). -/
private theorem int_no_zero_div {a b : Int} (h : a * b = 0) : a = 0 ∨ b = 0 := by
  rcases Nat.eq_zero_or_pos a.natAbs with ha | ha
  · left; exact Int.natAbs_eq_zero.mp ha
  · right
    have h_abs : a.natAbs * b.natAbs = 0 := by
      rw [← Int.natAbs_mul]; exact Int.natAbs_eq_zero.mpr h
    have hb : b.natAbs = 0 := by
      rcases Nat.eq_zero_or_pos b.natAbs with hb | hb
      · exact hb
      · exfalso; have := Nat.mul_pos ha hb; omega
    exact Int.natAbs_eq_zero.mp hb

/-- [I.T10] No nontrivial idempotent in the Gaussian integers:
    if (a+bi)² = (a+bi) over Z, then (a,b) = (0,0) or (a,b) = (1,0).

    Proof: From (a+bi)² = a+bi:
    - Real part: a² - b² = a
    - Imaginary part: 2ab = b
    From 2ab = b: either b = 0 or 2a = 1 (impossible in Z).
    If b = 0: a² = a, so a(a-1) = 0, hence a = 0 or a = 1. -/
theorem no_elliptic_idempotent (z : GaussInt)
    (h : GaussInt.mul z z = z) :
    z = ⟨0, 0⟩ ∨ z = ⟨1, 0⟩ := by
  -- Extract component equations
  have hR : z.re * z.re - z.im * z.im = z.re := by
    have := congrArg GaussInt.re h; simp [GaussInt.mul] at this; exact this
  have hI : z.im * z.re + z.im * z.re = z.im := by
    have := congrArg GaussInt.im h; simp [GaussInt.mul] at this
    rw [Int.mul_comm z.re z.im] at this; exact this
  -- Factor IM equation: z.im * (z.re + z.re - 1) = 0
  have him_factor : z.im * (z.re + z.re - 1) = 0 := by linear_combination hI
  -- Int integral domain: z.im = 0 or z.re + z.re = 1 (impossible)
  rcases int_no_zero_div him_factor with hb | hab
  · -- z.im = 0: then z.re² = z.re
    rw [hb] at hR; simp at hR
    -- hR: z.re * z.re = z.re
    have hre_factor : z.re * (z.re - 1) = 0 := by linear_combination hR
    rcases int_no_zero_div hre_factor with ha | ha
    · left; exact GaussInt.ext ha hb
    · right
      have hre1 : z.re = 1 := by omega
      exact GaussInt.ext hre1 hb
  · -- z.re + z.re = 1: impossible in ℤ (parity)
    exfalso; omega

/-- [I.T10] Split-complex forced: the split-complex algebra (j² = +1) admits
    nontrivial idempotents (e+, e-), while the elliptic algebra (i² = -1) does not.
    Therefore, encoding a bipolar partition requires j² = +1. -/
theorem split_complex_forced :
    -- Split-complex has nontrivial idempotent
    (∃ e : SectorPair, SectorPair.mul e e = e ∧ e ≠ ⟨0, 0⟩ ∧ e ≠ ⟨1, 1⟩) ∧
    -- Elliptic has NO nontrivial idempotent
    (∀ z : GaussInt, GaussInt.mul z z = z → z = ⟨0, 0⟩ ∨ z = ⟨1, 0⟩) := by
  constructor
  · -- Witness: e_plus_sector = (1, 0)
    exact ⟨e_plus_sector, e_plus_idem, by simp [e_plus_sector], by simp [e_plus_sector]⟩
  · exact no_elliptic_idempotent

-- ============================================================
-- POLARITY INVOLUTION
-- ============================================================

/-- The polarity involution σ: j ↦ -j, i.e., (a, b) ↦ (a, -b). -/
def polarity_inv (z : SplitComplex) : SplitComplex := ⟨z.re, -z.im⟩

/-- σ² = id. -/
theorem polarity_inv_squared (z : SplitComplex) :
    polarity_inv (polarity_inv z) = z := by
  simp [polarity_inv]

/-- σ fixes the real part. -/
theorem polarity_inv_fixes_real (a : Int) :
    polarity_inv ⟨a, 0⟩ = ⟨a, 0⟩ := by
  simp [polarity_inv]

/-- σ(j) = -j. -/
theorem polarity_inv_j :
    polarity_inv SplitComplex.j = SplitComplex.neg SplitComplex.j := by
  simp [polarity_inv, SplitComplex.j, SplitComplex.neg]

/-- σ swaps sectors: σ maps (u, v) to (v, u) in sector coordinates. -/
theorem polarity_inv_swaps_sectors (z : SplitComplex) :
    to_sectors (polarity_inv z) =
    ⟨(to_sectors z).c_sector, (to_sectors z).b_sector⟩ := by
  simp [polarity_inv, to_sectors]
  omega

-- ============================================================
-- CHI SPLIT-COMPLEX LIFT [chunk_0228, chunk_0310]
-- ============================================================

/-- [chunk_0228] Split-complex lift of the polarity character.
    Maps the Int-valued polarity_chi to sector idempotents:
    - B-dominant (chi = -1) → e_plus_sector = (1, 0)
    - C-dominant (chi = +1) → e_minus_sector = (0, 1)
    - non-prime (chi = 0)   → (0, 0)
    Ground truth: chunk_0228_M002194 — χ̃(p) ∈ {e⁻, e⁺}. -/
def chi_split (p N : TauIdx) : SectorPair :=
  if polarity_chi p N == -1 then e_plus_sector      -- B-dominant → B-sector
  else if polarity_chi p N == 1 then e_minus_sector  -- C-dominant → C-sector
  else ⟨0, 0⟩                                        -- non-prime

/-- chi_split is idempotent-valued: the output squares to itself. -/
theorem chi_split_idempotent (p N : TauIdx) :
    SectorPair.mul (chi_split p N) (chi_split p N) = chi_split p N := by
  unfold chi_split
  split
  · exact e_plus_idem
  · split
    · exact e_minus_idem
    · simp [SectorPair.mul]

/-- Bridge theorem: polarity_chi = -1 implies chi_split = e_plus_sector. -/
theorem chi_split_of_b (p N : TauIdx) (h : polarity_chi p N = -1) :
    chi_split p N = e_plus_sector := by
  simp [chi_split, h]

/-- Bridge theorem: polarity_chi = +1 implies chi_split = e_minus_sector. -/
theorem chi_split_of_c (p N : TauIdx) (h : polarity_chi p N = 1) :
    chi_split p N = e_minus_sector := by
  simp [chi_split, h]

/-- The two character representations are orthogonal:
    chi_split for B-dominant and C-dominant primes give orthogonal sectors. -/
theorem chi_split_orthogonal (p q N : TauIdx)
    (hp : polarity_chi p N = -1) (hq : polarity_chi q N = 1) :
    SectorPair.mul (chi_split p N) (chi_split q N) = ⟨0, 0⟩ := by
  rw [chi_split_of_b p N hp, chi_split_of_c q N hq]
  exact e_orthogonal

-- ============================================================
-- SMOKE TESTS
-- ============================================================

-- Split-complex arithmetic
#eval SplitComplex.mul ⟨1, 1⟩ ⟨1, 1⟩     -- (2, 2): (1+j)² = 2+2j
#eval SplitComplex.mul ⟨1, -1⟩ ⟨1, -1⟩    -- (2, -2): (1-j)² = 2-2j
#eval SplitComplex.mul ⟨1, 1⟩ ⟨1, -1⟩     -- (0, 0): (1+j)(1-j) = 0 (zero divisor!)

-- Sector decomposition
#eval to_sectors ⟨3, 2⟩    -- (5, 1): B-sector=5, C-sector=1
#eval to_sectors ⟨1, 0⟩    -- (1, 1): real element → equal sectors

-- Idempotents in sector coordinates
#eval SectorPair.mul e_plus_sector e_plus_sector    -- (1, 0) ✓
#eval SectorPair.mul e_minus_sector e_minus_sector  -- (0, 1) ✓
#eval SectorPair.mul e_plus_sector e_minus_sector   -- (0, 0) ✓
#eval SectorPair.add e_plus_sector e_minus_sector   -- (1, 1) ✓

-- Polarity involution
#eval polarity_inv ⟨3, 2⟩     -- (3, -2): swap j → -j
#eval polarity_inv (polarity_inv ⟨3, 2⟩)   -- (3, 2): σ² = id

-- Boundary ring
#eval bdry_add 100 200 3     -- (100+200) % 30 = 0
#eval bdry_mul 7 8 3         -- (7*8) % 30 = 56 % 30 = 26

-- Chi split-complex lift
#eval chi_split 2 1000    -- sector idempotent for prime 2
#eval chi_split 3 1000    -- sector idempotent for prime 3
#eval chi_split 4 1000    -- (0,0): not prime
#eval chi_split 1 1000    -- (0,0): not prime

end Tau.Polarity
