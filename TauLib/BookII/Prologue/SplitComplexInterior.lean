import TauLib.BookI.Polarity.BipolarAlgebra
import TauLib.BookI.Boundary.SplitComplex

/-!
# TauLib.BookII.Prologue.SplitComplexInterior

Split-complex codomain H_τ for Book II's τ-holomorphic functions.

## Registry Cross-References

- [II.D01] Split-Complex Codomain H_τ — `HTau`, `h_tau_sectors`

## Mathematical Content

H_τ := { a + bj : a, b ∈ Ẑ_τ } with j² = +1 (I.T10).

Three reasons the elliptic algebra (i² = -1) fails for τ:
1. Laplacian glue — symmetric diffusion erases boundary/interior asymmetry
2. No canonical propagation — isotropic, no preferred direction
3. Unipolar — single rotation phase, can't encode bipolar ℒ

Split-complex (j² = +1) is forced by prime polarity (I.T05):
bipolar partition ⇒ two orthogonal idempotents e₊, e₋ ⇒ j² = +1.
H_τ ≅ A_τ⁺ × A_τ⁻ via sector decomposition.
-/

namespace Tau.BookII.Prologue

open Tau.Polarity Tau.Boundary

-- ============================================================
-- SPLIT-COMPLEX CODOMAIN [II.D01]
-- ============================================================

/-- [II.D01] The split-complex codomain H_τ.
    Algebraically identical to Book I's SplitComplex (I.D20),
    interpreted as the codomain for τ-holomorphic functions.

    H_τ = { a + bj : a, b ∈ Ẑ_τ }, j² = +1

    Key properties:
    - Commutative ring (unlike quaternions ℍ)
    - Has zero divisors: e₊ · e₋ = 0 (unlike ℂ)
    - Bipolar: decomposes into e₊-sector and e₋-sector
    - Wave-type: split-CR equations give hyperbolic PDE -/
abbrev HTau := SplitComplex

/-- Sector form: z ↦ (z₊, z₋) where z = z₊ e₊ + z₋ e₋. -/
def h_tau_sectors (z : HTau) : SectorPair := to_sectors z

/-- B-sector projection (e₊ component): z ↦ re(z) + im(z). -/
def h_tau_b_sector (z : HTau) : Int := (to_sectors z).b_sector

/-- C-sector projection (e₋ component): z ↦ re(z) - im(z). -/
def h_tau_c_sector (z : HTau) : Int := (to_sectors z).c_sector

-- ============================================================
-- CODOMAIN RING STRUCTURE
-- ============================================================

/-- H_τ multiplication is commutative (I.T10 consequence). -/
theorem h_tau_mul_comm (z w : HTau) :
    SplitComplex.mul z w = SplitComplex.mul w z :=
  sc_mul_comm z w

/-- H_τ has zero divisors: (1+j)(1-j) = 0.
    This encodes bipolar sector orthogonality, not a pathology. -/
theorem h_tau_zero_divisors :
    SplitComplex.mul ⟨1, 1⟩ ⟨1, -1⟩ = ⟨0, 0⟩ := by
  unfold SplitComplex.mul; ext <;> simp

/-- Sector decomposition is faithful: z recoverable from sectors. -/
theorem h_tau_sector_faithful (z : HTau) :
    from_sectors (to_sectors z) = z :=
  from_sectors_left_inv z

-- ============================================================
-- BIPOLAR SECTOR STRUCTURE
-- ============================================================

/-- e₊ is idempotent in sector coordinates (I.D21). -/
theorem h_tau_e_plus_idem :
    SectorPair.mul e_plus_sector e_plus_sector = e_plus_sector :=
  e_plus_idem

/-- e₋ is idempotent in sector coordinates (I.D21). -/
theorem h_tau_e_minus_idem :
    SectorPair.mul e_minus_sector e_minus_sector = e_minus_sector :=
  e_minus_idem

/-- e₊ · e₋ = 0: sectors are orthogonal (I.D21). -/
theorem h_tau_e_orthogonal :
    SectorPair.mul e_plus_sector e_minus_sector = ⟨0, 0⟩ :=
  e_orthogonal

/-- e₊ + e₋ = 1: sectors partition the whole algebra (I.D21). -/
theorem h_tau_e_partition :
    SectorPair.add e_plus_sector e_minus_sector = ⟨1, 1⟩ :=
  e_partition

-- ============================================================
-- SPLIT-COMPLEX FORCING [I.T10]
-- ============================================================

/-- Nontrivial idempotent exists in sector coordinates.
    Witness: e₊ = ⟨1, 0⟩ is idempotent, nontrivial (≠ 0 and ≠ 1). -/
theorem h_tau_nontrivial_idempotent :
    SectorPair.mul e_plus_sector e_plus_sector = e_plus_sector ∧
    e_plus_sector ≠ ⟨0, 0⟩ ∧
    e_plus_sector ≠ ⟨1, 1⟩ := by
  refine ⟨e_plus_idem, ?_, ?_⟩
  · intro h
    have : (1 : Int) = 0 := congrArg SectorPair.b_sector h
    omega
  · intro h
    have : (0 : Int) = 1 := congrArg SectorPair.c_sector h
    omega

/-- Elliptic (Gaussian) integers have NO nontrivial idempotents.
    This is why ℂ cannot serve as codomain for τ-holomorphic functions. -/
theorem h_tau_no_elliptic_idempotent :
    ∀ z : GaussInt, GaussInt.mul z z = z →
    z = ⟨0, 0⟩ ∨ z = ⟨1, 0⟩ :=
  no_elliptic_idempotent

-- ============================================================
-- SMOKE TESTS
-- ============================================================

#eval h_tau_sectors ⟨3, 5⟩     -- expect: (8, -2)
#eval h_tau_b_sector ⟨3, 5⟩    -- expect: 8
#eval h_tau_c_sector ⟨3, 5⟩    -- expect: -2
#eval h_tau_sectors ⟨1, 0⟩     -- expect: (1, 1) = identity element
#eval h_tau_sectors ⟨0, 1⟩     -- expect: (1, -1) = j element

end Tau.BookII.Prologue
