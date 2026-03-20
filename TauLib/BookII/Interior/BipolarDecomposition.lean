import TauLib.BookII.Interior.Tau3Fibration
import TauLib.BookII.Interior.OmegaReadout
import TauLib.BookI.Polarity.BipolarAlgebra
import TauLib.BookI.Boundary.SplitComplex

/-!
# TauLib.BookII.Interior.BipolarDecomposition

Interior bipolar decomposition: every τ-admissible point inherits
sector assignment from the boundary idempotents e₊, e₋.

## Registry Cross-References

- [II.D08] Interior Bipolar Decomposition — `interior_bipolar`
- [II.P02] Sector Inheritance — `sector_orthogonal`, `sector_complete`

## Mathematical Content

For (D, A, B, C) ∈ τ³:
  Ψ_int = s₊ + s₋ = e₊ · Ψ(B,A,D) + e₋ · Ψ(C,A,D)

Two independent channels:
- B-channel (e₊): carries γ-orbit data (exponent structure)
- C-channel (e₋): carries η-orbit data (tetration height)

Orthogonality: e₊ · e₋ = 0 → channels carry independent information.

Degeneration to boundary at ω-limit:
- B-dominant → e₊-lobe of ℒ
- C-dominant → e₋-lobe of ℒ
- Balanced   → crossing point
-/

namespace Tau.BookII.Interior

open Tau.Polarity Tau.Boundary Tau.Coordinates Tau.Denotation

-- ============================================================
-- INTERIOR BIPOLAR DECOMPOSITION [II.D08]
-- ============================================================

/-- [II.D08] Interior bipolar decomposition.
    Maps a τ-admissible point to a sector pair (s₊, s₋).
    B-coordinate → e₊-sector, C-coordinate → e₋-sector.

    At finite stages, this is the integer-level shadow of the
    profinite decomposition Ψ_int = e₊ · Ψ(B) + e₋ · Ψ(C). -/
def interior_bipolar (p : TauAdmissiblePoint) : SectorPair :=
  ⟨(p.b : Int), (p.c : Int)⟩

/-- B-sector component: carries exponent (γ-orbit) data. -/
def s_plus (p : TauAdmissiblePoint) : Int := p.b

/-- C-sector component: carries tetration height (η-orbit) data. -/
def s_minus (p : TauAdmissiblePoint) : Int := p.c

/-- Full split-complex interior image via sector → split-complex conversion. -/
def interior_split_complex (p : TauAdmissiblePoint) : SplitComplex :=
  from_sectors (interior_bipolar p)

-- ============================================================
-- SECTOR INHERITANCE [II.P02]
-- ============================================================

/-- [II.P02, clause 2] Idempotent compatibility:
    The B-sector projection of the interior bipolar decomposition
    is annihilated by e₋, and vice versa.

    In sector coordinates: e₊ · s₋ = 0 and e₋ · s₊ = 0.
    This follows because e₊ = ⟨1,0⟩ projects out the C-component,
    and e₋ = ⟨0,1⟩ projects out the B-component. -/
theorem sector_orthogonal (p : TauAdmissiblePoint) :
    SectorPair.mul e_plus_sector ⟨0, s_minus p⟩ = ⟨0, 0⟩ := by
  simp [SectorPair.mul, e_plus_sector, s_minus]

theorem sector_orthogonal' (p : TauAdmissiblePoint) :
    SectorPair.mul e_minus_sector ⟨s_plus p, 0⟩ = ⟨0, 0⟩ := by
  simp [SectorPair.mul, e_minus_sector, s_plus]

/-- [II.P02, clause 2] Completeness:
    The interior bipolar decomposition recovers the full point data.
    s₊ + s₋ (in appropriate sense) gives back (B, C). -/
theorem sector_complete (p : TauAdmissiblePoint) :
    SectorPair.add
      (SectorPair.mul e_plus_sector (interior_bipolar p))
      (SectorPair.mul e_minus_sector (interior_bipolar p)) =
    interior_bipolar p := by
  simp [SectorPair.add, SectorPair.mul, e_plus_sector, e_minus_sector,
        interior_bipolar]

/-- [II.P02, clause 3] Fiber dominance recovery:
    Sector assignment determines which lobe of ℒ the point approaches. -/
def sector_lobe (p : TauAdmissiblePoint) : FiberDominance :=
  p.fiber_dominance

-- ============================================================
-- WAVE EQUATION STRUCTURE
-- ============================================================

/-- Characteristic coordinates: ξ = B + C, η' = B - C.
    Split-complex holomorphic functions decompose as f(ξ,η') = g(ξ) + h(η').
    B and C channels are the two characteristic directions. -/
def char_plus (p : TauAdmissiblePoint) : Int := p.b + p.c
def char_minus (p : TauAdmissiblePoint) : Int := (p.b : Int) - p.c

/-- Characteristic coordinates recover sector coordinates:
    b_sector = ξ = B + C (= re + im in split-complex)
    c_sector = η' = B - C (= re - im in split-complex)

    Note: this is the TRANSPOSE of the usual convention because
    interior_bipolar maps B → b_sector directly. The characteristic
    coordinate interpretation involves the full split-complex embedding. -/
def char_to_sectors (p : TauAdmissiblePoint) : SectorPair :=
  ⟨char_plus p, char_minus p⟩

-- ============================================================
-- SMOKE TESTS
-- ============================================================

-- Interior bipolar decomposition
#eval interior_bipolar (from_tau_idx 12)   -- (1, 1): B=1, C=1
#eval interior_bipolar (from_tau_idx 64)   -- (3, 2): B=3, C=2
#eval interior_bipolar (from_tau_idx 8)    -- (3, 1): B=3, C=1

-- Split-complex image
#eval interior_split_complex (from_tau_idx 64)   -- from_sectors ⟨3, 2⟩

-- Sector lobe
#eval sector_lobe (from_tau_idx 64)    -- b_dominant (B=3 > C=2)
#eval sector_lobe (from_tau_idx 30)    -- balanced (B=1 = C=1)

-- Characteristic coordinates
#eval char_plus (from_tau_idx 64)    -- 5 (= 3 + 2)
#eval char_minus (from_tau_idx 64)   -- 1 (= 3 - 2)

end Tau.BookII.Interior
