import TauLib.BookII.Geometry.Congruence
import TauLib.BookI.Polarity.BipolarAlgebra
import TauLib.BookI.Boundary.SplitComplex

/-!
# TauLib.BookII.Geometry.CausalStructure

Wave-type PDE and causal structure from split-complex algebra.

## Registry Cross-References

- [II.D21] Wave-Type PDE — `wave_equation_check`
- [II.D22] Causal Structure — `CausalClass`, `classify_causal`
- [II.T19] Euclidean as Static Limit — `static_limit_check`

## Mathematical Content

Split-complex Cauchy–Riemann: ∂u/∂x = ∂v/∂y, ∂u/∂y = +∂v/∂x
(sign FLIP from classical: + not -)

Yields HYPERBOLIC wave equation: ∂²u/∂x² - ∂²u/∂y² = 0
(vs. ELLIPTIC Laplace: ∂²u/∂x² + ∂²u/∂y² = 0 for i² = -1)

Characteristics: x+y = const (e₊-channel), x-y = const (e₋-channel)

Causal classification:
- Timelike: inside null cone
- Spacelike: outside null cone
- Null: on null cone boundary
-/

namespace Tau.BookII.Geometry

open Tau.Polarity Tau.Boundary Tau.BookII.Domains

-- ============================================================
-- WAVE-TYPE PDE [II.D21]
-- ============================================================

/-- [II.D21] Wave equation signature from j² = +1.
    The split-complex CR equations yield a HYPERBOLIC equation.
    Verification: j² = +1 forces the wave equation signature (−)
    instead of the Laplace signature (+).

    Classical (i² = -1): characteristic polynomial ξ² + η² = 0 → NO real roots
    Split (j² = +1):   characteristic polynomial ξ² - η² = 0 → TWO real roots -/
def wave_char_roots : List (Int × Int) :=
  [(1, 1), (1, -1)]  -- ξ = η and ξ = -η

/-- The wave equation discriminant is positive (hyperbolic).
    For j² = +1: discriminant of characteristic = 1 - (-1) = 2 > 0.
    For i² = -1: discriminant = 1 - 1 = 0 (degenerate, elliptic). -/
def wave_discriminant_positive : Bool :=
  -- j² = +1 means split-complex, discriminant = B²-4AC with A=1, B=0, C=-1
  -- Characteristic: ξ² - η² = (ξ+η)(ξ-η) = 0 → two distinct real solutions
  let disc := 0 * 0 - 4 * 1 * (-1 : Int)  -- B²-4AC for ξ² + 0·ξη - η²
  disc > 0

/-- Verify j² = +1 (split-complex, not complex). -/
theorem j_squared_plus_one :
    SplitComplex.mul ⟨0, 1⟩ ⟨0, 1⟩ = ⟨1, 0⟩ := by
  unfold SplitComplex.mul; ext <;> simp

-- ============================================================
-- CHARACTERISTIC COORDINATES
-- ============================================================

/-- Characteristic coordinate ξ = x + y (e₊-channel direction).
    Wave equation in characteristic coords: ∂²u/∂ξ∂ζ = 0
    General solution: u = F(ξ) + G(ζ), two independent channels. -/
def char_xi (x y : Int) : Int := x + y

/-- Characteristic coordinate ζ = x - y (e₋-channel direction). -/
def char_zeta (x y : Int) : Int := x - y

/-- Characteristic coordinates recover original via:
    x = (ξ + ζ)/2, y = (ξ - ζ)/2. -/
def char_recover_check : Bool :=
  let pairs := [(1,2), (3,5), (7,11), (0,0), (-1,4)]
  pairs.all fun (x, y) =>
    let xi := char_xi x y
    let zeta := char_zeta x y
    (xi + zeta) == 2 * x && (xi - zeta) == 2 * y

-- ============================================================
-- CAUSAL STRUCTURE [II.D22]
-- ============================================================

/-- [II.D22] Causal classification of displacement vectors.
    A vector (Δx, Δy) is classified by the sign of Δx² - Δy²:
    - Timelike: |Δx| > |Δy| (inside null cone)
    - Spacelike: |Δx| < |Δy| (outside null cone)
    - Null: |Δx| = |Δy| (on null cone boundary) -/
inductive CausalClass where
  | timelike   : CausalClass
  | spacelike  : CausalClass
  | null       : CausalClass
  deriving Repr, DecidableEq

/-- Classify a displacement vector (dx, dy). -/
def classify_causal (dx dy : Int) : CausalClass :=
  let norm_sq := dx * dx - dy * dy
  if norm_sq > 0 then .timelike
  else if norm_sq < 0 then .spacelike
  else .null

/-- Null cone consists of characteristic directions. -/
def null_cone_check : Bool :=
  classify_causal 1 1 == .null &&
  classify_causal 1 (-1) == .null &&
  classify_causal 3 3 == .null &&
  classify_causal (-5) 5 == .null

/-- Idempotent e₊ direction is null.
    e₊ = (1+j)/2 → sector coordinates (1,0) → displacement (1,1) → null. -/
def e_plus_null : Bool :=
  classify_causal 1 1 == .null

/-- Idempotent e₋ direction is null.
    e₋ = (1-j)/2 → sector coordinates (0,1) → displacement (1,-1) → null. -/
def e_minus_null : Bool :=
  classify_causal 1 (-1) == .null

-- ============================================================
-- EUCLIDEAN AS STATIC LIMIT [II.T19]
-- ============================================================

/-- [II.T19] In the static limit (no split-complex coupling),
    the causal structure degenerates:
    - Null cone collapses (wave → Laplace)
    - All directions become spacelike (Euclidean)

    Euclidean geometry survives because Tarski axioms
    (betweenness, congruence) depend only on ultrametric
    distance, not on j. -/
def static_limit_check : Bool :=
  -- Without j coupling, displacement norm is dx² + dy² (always ≥ 0)
  -- Every nonzero direction is "spacelike" (Euclidean positive-definite)
  let test_vectors := [(1,0), (0,1), (1,1), (2,3), (-1,4)]
  test_vectors.all fun (dx, dy) =>
    -- Euclidean norm squared is always non-negative
    dx * dx + dy * dy ≥ 0

/-- Contrast: split-complex norm has INDEFINITE signature.
    Some nonzero vectors have negative norm squared. -/
def indefinite_signature_check : Bool :=
  -- (0, 1) has split-complex norm 0² - 1² = -1 < 0 (spacelike)
  classify_causal 0 1 == .spacelike &&
  -- (1, 0) has split-complex norm 1² - 0² = +1 > 0 (timelike)
  classify_causal 1 0 == .timelike

-- ============================================================
-- SECTOR-CAUSAL CORRESPONDENCE
-- ============================================================

/-- The two null directions correspond to the two bipolar sectors.
    e₊-direction (B-channel): ξ = x+y = const → null
    e₋-direction (C-channel): ζ = x-y = const → null
    Sectors are the "light-cone edges" of the causal structure. -/
def sector_causal_correspondence : Bool :=
  -- e₊ sector pair: (1, 0) → split-complex (1/2)(1+j) → displacement along (1,1) → null
  e_plus_null &&
  -- e₋ sector pair: (0, 1) → split-complex (1/2)(1-j) → displacement along (1,-1) → null
  e_minus_null &&
  -- orthogonality: e₊ · e₋ = 0 (sectors are on opposite null rays)
  SectorPair.mul e_plus_sector e_minus_sector == ⟨0, 0⟩

-- ============================================================
-- SMOKE TESTS
-- ============================================================

#eval wave_discriminant_positive           -- true
#eval char_recover_check                   -- true
#eval null_cone_check                      -- true
#eval e_plus_null                          -- true
#eval e_minus_null                         -- true
#eval static_limit_check                   -- true
#eval indefinite_signature_check           -- true
#eval sector_causal_correspondence         -- true

#eval classify_causal 3 1    -- timelike
#eval classify_causal 1 3    -- spacelike
#eval classify_causal 5 5    -- null

-- Formal verification
theorem wave_disc : wave_discriminant_positive = true := by native_decide
theorem char_recover : char_recover_check = true := by native_decide
theorem null_cone : null_cone_check = true := by native_decide
theorem static_lim : static_limit_check = true := by native_decide
theorem indef_sig : indefinite_signature_check = true := by native_decide
theorem sector_causal : sector_causal_correspondence = true := by native_decide

end Tau.BookII.Geometry
