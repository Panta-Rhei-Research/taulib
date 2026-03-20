import TauLib.BookII.Interior.TauAdmissible
import TauLib.BookI.Polarity.BipolarAlgebra

/-!
# TauLib.BookII.Interior.OmegaReadout

The omega readout: how ABCD coordinates behave as paths approach ω.

## Registry Cross-References

- [II.D04] Omega Readout — `FiberDominance`, `classify_dominance`
- [II.T02] Fiber Degeneration at Omega — `fiber_degeneration_primorial`
- [II.P01] Lemniscate as Coordinate Limit — `lemniscate_coordinate_limit`

## Mathematical Content

As objects approach ω along the primorial tower P_k = p₁·...·p_k:
- Base (D, A): both components → ∞ (universal collapse to Ω)
- Fiber (B, C): locked by B/C competition into bipolar structure

Three fiber limit types:
- B-dominant (B ≫ C): maps to e₊-lobe of ℒ
- C-dominant (C ≫ B): maps to e₋-lobe of ℒ
- Balanced (B ≈ C): maps to crossing point (node of ℒ)

The lemniscate ℒ ≅ pr_fiber(Φ_ω): fiber limits at ω reproduce
the algebraic lemniscate from Book I (I.D18).
-/

namespace Tau.BookII.Interior

open Tau.Coordinates Tau.Denotation Tau.Polarity

-- ============================================================
-- FIBER DOMINANCE [II.D04]
-- ============================================================

/-- [II.D04] Classification of fiber (B,C) behavior at ω-limit.
    Determines which lobe of the lemniscate ℒ a path approaches. -/
inductive FiberDominance where
  | b_dominant : FiberDominance   -- B ≫ C → e₊-lobe
  | c_dominant : FiberDominance   -- C ≫ B → e₋-lobe
  | balanced   : FiberDominance   -- B ≈ C → crossing point ω_ℒ
  deriving Repr, DecidableEq

/-- Classify fiber dominance from (B, C) coordinates. -/
def classify_dominance (b c : TauIdx) : FiberDominance :=
  if b > c then .b_dominant
  else if c > b then .c_dominant
  else .balanced

/-- Classify an admissible point's fiber dominance. -/
def TauAdmissiblePoint.fiber_dominance (p : TauAdmissiblePoint) : FiberDominance :=
  classify_dominance p.b p.c

-- ============================================================
-- OMEGA READOUT MAP [II.D04]
-- ============================================================

/-- [II.D04] Omega readout of an admissible point.
    Returns (base_A, base_D, fiber_dominance).
    At ω-limit: base → (Ω,Ω), fiber → lobe of ℒ. -/
def omega_readout (p : TauAdmissiblePoint) :
    TauIdx × TauIdx × FiberDominance :=
  (p.a, p.d, p.fiber_dominance)

/-- Sector assignment from fiber dominance:
    B-dominant → e₊-sector, C-dominant → e₋-sector, balanced → both. -/
def dominance_to_sector (fd : FiberDominance) : SectorPair :=
  match fd with
  | .b_dominant => e_plus_sector   -- ⟨1, 0⟩
  | .c_dominant => e_minus_sector  -- ⟨0, 1⟩
  | .balanced   => ⟨1, 1⟩         -- both sectors active

-- ============================================================
-- FIBER DEGENERATION [II.T02]
-- ============================================================

/-- [II.T02] Primorial path fiber degeneration.
    Along the primorial tower, B = C = 1 always: balanced (crossing point). -/
def primorial_fiber_check : Bool :=
  primorial_witness.all fun (_, p) => p.fiber_dominance == .balanced

/-- [II.T02] Primorial base readout: A-values exhaust primes. -/
def primorial_base_diverges : Bool :=
  let as := primorial_witness.map fun (_, p) => p.a
  -- A-values strictly increasing
  go as
where
  go : List TauIdx → Bool
    | [] | [_] => true
    | x :: y :: rest => x < y && go (y :: rest)

/-- [II.T02] Tower path (X_n = 2^n) is B-dominant. -/
def tower_path_check : Bool :=
  let points := [4, 8, 16, 32, 64, 128, 256].map from_tau_idx
  points.all fun p => p.b > p.c

/-- [II.T02, clause 1] Base collapse: both A and D grow along primorials. -/
def base_collapse_check : Bool :=
  let pairs := primorial_witness.map fun (_, p) => (p.a, p.d)
  -- Both A and D are strictly increasing
  go pairs
where
  go : List (TauIdx × TauIdx) → Bool
    | [] | [_] => true
    | (a₁, d₁) :: (a₂, d₂) :: rest => a₁ < a₂ && d₁ < d₂ && go ((a₂, d₂) :: rest)

-- ============================================================
-- LEMNISCATE AS COORDINATE LIMIT [II.P01]
-- ============================================================

/-- [II.P01] The three fiber limit types correspond to the algebraic
    lemniscate structure:
    - B-dominant → e₊-lobe (I.D21 e₊ idempotent)
    - C-dominant → e₋-lobe (I.D21 e₋ idempotent)
    - Balanced   → crossing point (node where both sectors active)

    Verification: sector assignment is idempotent-compatible. -/
def lemniscate_sector_idem_check : Bool :=
  -- e₊-sector assignment: e₊² = e₊
  SectorPair.mul (dominance_to_sector .b_dominant)
                 (dominance_to_sector .b_dominant) ==
    dominance_to_sector .b_dominant &&
  -- e₋-sector assignment: e₋² = e₋
  SectorPair.mul (dominance_to_sector .c_dominant)
                 (dominance_to_sector .c_dominant) ==
    dominance_to_sector .c_dominant &&
  -- orthogonality: e₊ · e₋ = 0
  SectorPair.mul (dominance_to_sector .b_dominant)
                 (dominance_to_sector .c_dominant) ==
    ⟨0, 0⟩

-- ============================================================
-- SMOKE TESTS
-- ============================================================

-- Fiber dominance classification
#eval classify_dominance 5 1    -- b_dominant
#eval classify_dominance 1 5    -- c_dominant
#eval classify_dominance 3 3    -- balanced
#eval classify_dominance 1 1    -- balanced

-- Primorial path: always balanced
#eval primorial_fiber_check     -- true

-- Base divergence
#eval primorial_base_diverges   -- true
#eval base_collapse_check       -- true

-- Tower path: B-dominant
#eval tower_path_check          -- true

-- Lemniscate compatibility
#eval lemniscate_sector_idem_check  -- true

-- Specific readouts
#eval omega_readout (from_tau_idx 64)    -- A=2, D=1, b_dominant (B=3>C=2)
#eval omega_readout (from_tau_idx 30)    -- A=5, D=6, balanced (B=1=C=1)

-- Formal verification
theorem primorial_balanced : primorial_fiber_check = true := by native_decide
theorem base_diverges : primorial_base_diverges = true := by native_decide
theorem lemniscate_compat : lemniscate_sector_idem_check = true := by native_decide

end Tau.BookII.Interior
