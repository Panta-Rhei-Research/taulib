import TauLib.BookI.Polarity.BipolarAlgebra
import Mathlib.Tactic.Ring
import Mathlib.Tactic.LinearCombination

/-!
# TauLib.BookI.Boundary.SplitComplex

Full ring axioms for SplitComplex and SectorPair, plus to_sectors bijectivity
and zero divisor characterization.

## Registry Cross-References

- [I.D27] Bipolar Spectral Algebra — Ring axiom suite for `SplitComplex`, `SectorPair`
- [I.T10] Split-Complex Forced — Zero divisor characterization

## Ground Truth Sources
- chunk_0228_M002194: Split-complex ring, sector decomposition ring isomorphism
- chunk_0310_M002679: Bipolar partition, zero divisors from sector coordinates

## Mathematical Content

The split-complex algebra H = Z[j] with j^2 = +1 is a commutative ring with
zero divisors. The sector decomposition phi: H -> Z x Z via (a+bj) -> (a+b, a-b)
is a ring isomorphism. Zero divisors in H are exactly elements where one sector
coordinate vanishes: z is a zero divisor iff z.re + z.im = 0 or z.re - z.im = 0.
-/

namespace Tau.Boundary

open Tau.Polarity

-- ============================================================
-- SPLITCOMPLEX EXTENSIONALITY
-- ============================================================

@[ext]
theorem SplitComplex.ext {a b : SplitComplex} (hre : a.re = b.re) (him : a.im = b.im) :
    a = b := by
  cases a; cases b; simp_all

-- ============================================================
-- SPLITCOMPLEX RING AXIOMS
-- ============================================================

/-- Additive commutativity: a + b = b + a. -/
theorem sc_add_comm (a b : SplitComplex) :
    SplitComplex.add a b = SplitComplex.add b a := by
  ext <;> simp [SplitComplex.add] <;> ring

/-- Additive associativity: (a + b) + c = a + (b + c). -/
theorem sc_add_assoc (a b c : SplitComplex) :
    SplitComplex.add (SplitComplex.add a b) c =
    SplitComplex.add a (SplitComplex.add b c) := by
  ext <;> simp [SplitComplex.add] <;> ring

/-- Additive identity: a + 0 = a. -/
theorem sc_add_zero (a : SplitComplex) :
    SplitComplex.add a SplitComplex.zero = a := by
  ext <;> simp [SplitComplex.add, SplitComplex.zero]

/-- Additive inverse: a + (-a) = 0. -/
theorem sc_add_neg (a : SplitComplex) :
    SplitComplex.add a (SplitComplex.neg a) = SplitComplex.zero := by
  ext <;> simp [SplitComplex.add, SplitComplex.neg, SplitComplex.zero]

/-- Multiplicative commutativity: a * b = b * a. -/
theorem sc_mul_comm (a b : SplitComplex) :
    SplitComplex.mul a b = SplitComplex.mul b a := by
  ext <;> simp [SplitComplex.mul] <;> ring

/-- Multiplicative associativity: (a * b) * c = a * (b * c). -/
theorem sc_mul_assoc (a b c : SplitComplex) :
    SplitComplex.mul (SplitComplex.mul a b) c =
    SplitComplex.mul a (SplitComplex.mul b c) := by
  ext <;> simp [SplitComplex.mul] <;> ring

/-- Multiplicative identity: a * 1 = a. -/
theorem sc_mul_one (a : SplitComplex) :
    SplitComplex.mul a SplitComplex.one = a := by
  ext <;> simp [SplitComplex.mul, SplitComplex.one]

/-- Left distributivity: a * (b + c) = a*b + a*c. -/
theorem sc_left_distrib (a b c : SplitComplex) :
    SplitComplex.mul a (SplitComplex.add b c) =
    SplitComplex.add (SplitComplex.mul a b) (SplitComplex.mul a c) := by
  ext <;> simp [SplitComplex.mul, SplitComplex.add] <;> ring

/-- Full SplitComplex ring axiom collection. -/
theorem sc_ring_axioms :
    (∀ (a b : SplitComplex), SplitComplex.add a b = SplitComplex.add b a) ∧
    (∀ (a b c : SplitComplex), SplitComplex.add (SplitComplex.add a b) c =
      SplitComplex.add a (SplitComplex.add b c)) ∧
    (∀ (a : SplitComplex), SplitComplex.add a SplitComplex.zero = a) ∧
    (∀ (a : SplitComplex), SplitComplex.add a (SplitComplex.neg a) = SplitComplex.zero) ∧
    (∀ (a b : SplitComplex), SplitComplex.mul a b = SplitComplex.mul b a) ∧
    (∀ (a b c : SplitComplex), SplitComplex.mul (SplitComplex.mul a b) c =
      SplitComplex.mul a (SplitComplex.mul b c)) ∧
    (∀ (a : SplitComplex), SplitComplex.mul a SplitComplex.one = a) ∧
    (∀ (a b c : SplitComplex), SplitComplex.mul a (SplitComplex.add b c) =
      SplitComplex.add (SplitComplex.mul a b) (SplitComplex.mul a c)) :=
  ⟨sc_add_comm, sc_add_assoc, sc_add_zero, sc_add_neg,
   sc_mul_comm, sc_mul_assoc, sc_mul_one, sc_left_distrib⟩

-- ============================================================
-- SECTORPAIR EXTENSIONALITY
-- ============================================================

@[ext]
theorem SectorPair.ext {a b : SectorPair}
    (hb : a.b_sector = b.b_sector) (hc : a.c_sector = b.c_sector) :
    a = b := by
  cases a; cases b; simp_all

-- ============================================================
-- SECTORPAIR RING AXIOMS
-- ============================================================

/-- SectorPair zero. -/
def SectorPair.zero : SectorPair := ⟨0, 0⟩

/-- SectorPair one (the multiplicative identity). -/
def SectorPair.one : SectorPair := ⟨1, 1⟩

/-- SectorPair negation. -/
def SectorPair.neg (a : SectorPair) : SectorPair :=
  ⟨-a.b_sector, -a.c_sector⟩

/-- Additive commutativity. -/
theorem sp_add_comm (a b : SectorPair) :
    SectorPair.add a b = SectorPair.add b a := by
  ext <;> simp [SectorPair.add] <;> ring

/-- Additive associativity. -/
theorem sp_add_assoc (a b c : SectorPair) :
    SectorPair.add (SectorPair.add a b) c =
    SectorPair.add a (SectorPair.add b c) := by
  ext <;> simp [SectorPair.add] <;> ring

/-- Additive identity. -/
theorem sp_add_zero (a : SectorPair) :
    SectorPair.add a SectorPair.zero = a := by
  ext <;> simp [SectorPair.add, SectorPair.zero]

/-- Additive inverse. -/
theorem sp_add_neg (a : SectorPair) :
    SectorPair.add a (SectorPair.neg a) = SectorPair.zero := by
  ext <;> simp [SectorPair.add, SectorPair.neg, SectorPair.zero]

/-- Multiplicative commutativity. -/
theorem sp_mul_comm (a b : SectorPair) :
    SectorPair.mul a b = SectorPair.mul b a := by
  ext <;> simp [SectorPair.mul] <;> ring

/-- Multiplicative associativity. -/
theorem sp_mul_assoc (a b c : SectorPair) :
    SectorPair.mul (SectorPair.mul a b) c =
    SectorPair.mul a (SectorPair.mul b c) := by
  ext <;> simp [SectorPair.mul] <;> ring

/-- Multiplicative identity. -/
theorem sp_mul_one (a : SectorPair) :
    SectorPair.mul a SectorPair.one = a := by
  ext <;> simp [SectorPair.mul, SectorPair.one]

/-- Left distributivity: a * (b + c) = a*b + a*c. -/
theorem sp_left_distrib (a b c : SectorPair) :
    SectorPair.mul a (SectorPair.add b c) =
    SectorPair.add (SectorPair.mul a b) (SectorPair.mul a c) := by
  ext <;> simp [SectorPair.mul, SectorPair.add] <;> ring

/-- Full SectorPair ring axiom collection. -/
theorem sp_ring_axioms :
    (∀ (a b : SectorPair), SectorPair.add a b = SectorPair.add b a) ∧
    (∀ (a b c : SectorPair), SectorPair.add (SectorPair.add a b) c =
      SectorPair.add a (SectorPair.add b c)) ∧
    (∀ (a : SectorPair), SectorPair.add a SectorPair.zero = a) ∧
    (∀ (a : SectorPair), SectorPair.add a (SectorPair.neg a) = SectorPair.zero) ∧
    (∀ (a b : SectorPair), SectorPair.mul a b = SectorPair.mul b a) ∧
    (∀ (a b c : SectorPair), SectorPair.mul (SectorPair.mul a b) c =
      SectorPair.mul a (SectorPair.mul b c)) ∧
    (∀ (a : SectorPair), SectorPair.mul a SectorPair.one = a) ∧
    (∀ (a b c : SectorPair), SectorPair.mul a (SectorPair.add b c) =
      SectorPair.add (SectorPair.mul a b) (SectorPair.mul a c)) :=
  ⟨sp_add_comm, sp_add_assoc, sp_add_zero, sp_add_neg,
   sp_mul_comm, sp_mul_assoc, sp_mul_one, sp_left_distrib⟩

-- ============================================================
-- TO_SECTORS: BIJECTIVITY
-- ============================================================

/-- Inverse of to_sectors: recover SplitComplex from SectorPair.
    Given (u, v) = (a+b, a-b), recover a = (u+v)/2, b = (u-v)/2.
    Over integers, this requires u+v and u-v to be even, which is
    always the case since u and v have the same parity. We work
    formally: from_sectors(to_sectors(z)) = z is proved directly. -/
def from_sectors (s : SectorPair) : SplitComplex :=
  ⟨(s.b_sector + s.c_sector) / 2, (s.b_sector - s.c_sector) / 2⟩

/-- to_sectors is injective: to_sectors a = to_sectors b implies a = b. -/
theorem to_sectors_injective (a b : SplitComplex)
    (h : to_sectors a = to_sectors b) : a = b := by
  simp only [to_sectors, SectorPair.mk.injEq] at h
  obtain ⟨h1, h2⟩ := h
  -- h1: a.re + a.im = b.re + b.im
  -- h2: a.re - a.im = b.re - b.im
  ext <;> omega

/-- from_sectors is a left inverse of to_sectors (over SplitComplex). -/
theorem from_sectors_left_inv (z : SplitComplex) :
    from_sectors (to_sectors z) = z := by
  simp only [to_sectors, from_sectors]
  ext <;> simp <;> omega

/-- to_sectors composed with from_sectors is identity on even-parity sector pairs.
    Note: over Z, to_sectors only reaches even-sum pairs (u+v always even). -/
theorem to_sectors_surj_on_image (s : SectorPair)
    (h : (s.b_sector + s.c_sector) % 2 = 0) :
    to_sectors (from_sectors s) = s := by
  simp only [from_sectors, to_sectors]
  ext <;> simp
  · -- b_sector: (u+v)/2 + (u-v)/2 = u
    omega
  · -- c_sector: (u+v)/2 - (u-v)/2 = v
    omega

/-- The image of to_sectors consists of pairs with equal parity. -/
theorem to_sectors_parity (z : SplitComplex) :
    ((to_sectors z).b_sector + (to_sectors z).c_sector) % 2 = 0 := by
  simp only [to_sectors]
  -- b_sector + c_sector = (re + im) + (re - im) = 2 * re
  have : z.re + z.im + (z.re - z.im) = 2 * z.re := by ring
  rw [this]
  exact Int.mul_emod_right 2 z.re

-- ============================================================
-- TO_SECTORS: RING HOMOMORPHISM (formal)
-- ============================================================

/-- to_sectors preserves zero. -/
theorem to_sectors_zero :
    to_sectors SplitComplex.zero = SectorPair.zero := by
  simp [to_sectors, SplitComplex.zero, SectorPair.zero]

/-- to_sectors preserves one. -/
theorem to_sectors_one :
    to_sectors SplitComplex.one = SectorPair.one := by
  simp [to_sectors, SplitComplex.one, SectorPair.one]

/-- to_sectors preserves negation. -/
theorem to_sectors_neg (z : SplitComplex) :
    to_sectors (SplitComplex.neg z) = SectorPair.neg (to_sectors z) := by
  simp only [to_sectors, SplitComplex.neg, SectorPair.neg]
  ext <;> simp <;> ring

-- Note: sectors_add and sectors_mul are already proved in BipolarAlgebra.lean

-- ============================================================
-- ZERO DIVISOR CHARACTERIZATION
-- ============================================================

/-- A split-complex number z is a zero divisor iff one sector coordinate vanishes.
    Forward: if z * w = 0 with w nonzero, then one sector of z is zero.
    We prove: z * w = 0 implies (z.re+z.im)*(w.re+w.im) = 0 AND
    (z.re-z.im)*(w.re-w.im) = 0. So if w has both sectors nonzero,
    both sectors of z must be zero (and z = 0). Nontrivial zero divisors
    have exactly one sector vanishing. -/
theorem zero_divisor_sector (z w : SplitComplex)
    (h : SplitComplex.mul z w = SplitComplex.zero) :
    (z.re + z.im) * (w.re + w.im) = 0 ∧
    (z.re - z.im) * (w.re - w.im) = 0 := by
  simp only [SplitComplex.mul, SplitComplex.zero, SplitComplex.mk.injEq] at h
  obtain ⟨hR, hI⟩ := h
  constructor
  · -- (z.re + z.im) * (w.re + w.im) = z.re*w.re + z.re*w.im + z.im*w.re + z.im*w.im
    -- = (z.re*w.re + z.im*w.im) + (z.re*w.im + z.im*w.re) = hR + hI = 0
    linear_combination hR + hI
  · -- (z.re - z.im) * (w.re - w.im) = (z.re*w.re + z.im*w.im) - (z.re*w.im + z.im*w.re) = hR - hI = 0
    linear_combination hR - hI

/-- Converse: if one sector of z is zero, z is a zero divisor
    (witness provided explicitly). -/
theorem zero_divisor_witness_b (z : SplitComplex) (h : z.re + z.im = 0) :
    SplitComplex.mul z ⟨1, 1⟩ = SplitComplex.zero := by
  -- z has B-sector = 0, witness ⟨1,1⟩ has C-sector = 0
  have him : z.im = -z.re := by omega
  ext <;> simp_all [SplitComplex.mul, SplitComplex.zero] <;> ring

theorem zero_divisor_witness_c (z : SplitComplex) (h : z.re - z.im = 0) :
    SplitComplex.mul z ⟨1, -1⟩ = SplitComplex.zero := by
  -- z has C-sector = 0, witness ⟨1,-1⟩ has B-sector = 0
  have hre : z.re = z.im := by omega
  ext <;> simp_all [SplitComplex.mul, SplitComplex.zero] <;> ring

/-- The zero divisors of SplitComplex are exactly the elements with a vanishing sector. -/
theorem zero_divisors_iff (z : SplitComplex) (hz : z ≠ SplitComplex.zero) :
    (∃ w : SplitComplex, w ≠ SplitComplex.zero ∧ SplitComplex.mul z w = SplitComplex.zero) ↔
    (z.re + z.im = 0 ∨ z.re - z.im = 0) := by
  constructor
  · -- Forward: z * w = 0 with w ≠ 0 implies sector vanishes
    intro ⟨w, hw_ne, hw_zero⟩
    rcases zero_divisor_sector z w hw_zero with ⟨hb, hc⟩
    -- Int integral domain: for each factor product = 0, one factor is 0
    rcases mul_eq_zero.mp hb with hzb | hwb
    · left; exact hzb
    · rcases mul_eq_zero.mp hc with hzc | hwc
      · right; exact hzc
      · -- Both w.re+w.im = 0 and w.re-w.im = 0, so w.re = 0 and w.im = 0
        exfalso; apply hw_ne
        ext <;> simp [SplitComplex.zero] <;> omega
  · -- Backward: sector vanishes implies zero divisor exists
    intro h_or
    rcases h_or with hb | hc
    · exact ⟨⟨1, 1⟩, by simp [SplitComplex.zero], zero_divisor_witness_b z hb⟩
    · exact ⟨⟨1, -1⟩, by simp [SplitComplex.zero], zero_divisor_witness_c z hc⟩

-- ============================================================
-- NATIVE_DECIDE VERIFICATIONS
-- ============================================================

-- SplitComplex ring checks
example : SplitComplex.add ⟨3, 2⟩ ⟨1, 4⟩ = ⟨4, 6⟩ := by native_decide
example : SplitComplex.mul ⟨3, 2⟩ ⟨1, 4⟩ = ⟨11, 14⟩ := by native_decide
example : SplitComplex.mul ⟨1, 1⟩ ⟨1, -1⟩ = ⟨0, 0⟩ := by native_decide
example : SplitComplex.add ⟨5, -3⟩ (SplitComplex.neg ⟨5, -3⟩) = SplitComplex.zero := by native_decide

-- SectorPair ring checks
example : SectorPair.mul ⟨2, 3⟩ ⟨4, 5⟩ = ⟨8, 15⟩ := by native_decide
example : SectorPair.add ⟨1, 2⟩ ⟨3, 4⟩ = ⟨4, 6⟩ := by native_decide

-- to_sectors checks
example : to_sectors ⟨3, 2⟩ = ⟨5, 1⟩ := by native_decide
example : to_sectors ⟨1, 0⟩ = ⟨1, 1⟩ := by native_decide
example : to_sectors (SplitComplex.mul ⟨2, 3⟩ ⟨1, 1⟩) =
    SectorPair.mul (to_sectors ⟨2, 3⟩) (to_sectors ⟨1, 1⟩) := by native_decide

-- ============================================================
-- SMOKE TESTS
-- ============================================================

#eval SplitComplex.add ⟨3, 2⟩ ⟨1, 4⟩        -- ⟨4, 6⟩
#eval SplitComplex.mul ⟨1, 1⟩ ⟨1, -1⟩        -- ⟨0, 0⟩ (zero divisor!)
#eval SplitComplex.mul ⟨2, 3⟩ ⟨1, 1⟩         -- ⟨5, 5⟩
#eval to_sectors ⟨3, 2⟩                       -- ⟨5, 1⟩
#eval from_sectors ⟨5, 1⟩                     -- ⟨3, 2⟩
#eval to_sectors (from_sectors ⟨6, 2⟩)        -- ⟨6, 2⟩ (even-parity roundtrip)
#eval SectorPair.mul ⟨2, 3⟩ ⟨4, 5⟩           -- ⟨8, 15⟩

end Tau.Boundary
