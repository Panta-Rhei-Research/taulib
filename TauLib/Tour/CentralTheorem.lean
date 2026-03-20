import TauLib.BookII.CentralTheorem.CentralTheorem
import TauLib.BookII.CentralTheorem.BoundaryCharacters
import TauLib.BookII.Interior.Tau3Fibration
import TauLib.BookI.Boundary.SplitComplex

/-!
# Tour 02: The Central Theorem

A guided walk through the climax of Book II:

  **O(tau^3) = A_spec(L)**

The ring of tau-holomorphic functions on the fibered product tau^3 is
canonically isomorphic to the spectral algebra of the lemniscate L.

This tour covers:
1. The split-complex boundary ring H = Z[j] and its sector decomposition
2. The tau^3 fibered product: base tau^1, fiber T^2, and why it is NOT a product
3. Boundary characters: idempotent-supported maps from the profinite boundary
4. The Central Theorem itself: all four links of the isomorphism
5. Spectral ring and holographic principle

**Prerequisites:** Tour/Foundations.lean (generators, axioms, iota_tau).
Step through this file in VS Code with the Lean 4 extension — hover over
`#check` and `#eval` to see types and computed values.
-/

open Tau.Polarity Tau.Boundary Tau.Coordinates Tau.Denotation
open Tau.BookII.Interior Tau.BookII.CentralTheorem

-- ================================================================
-- PART 1: THE SPLIT-COMPLEX BOUNDARY RING
-- ================================================================

-- The boundary of tau^3 is the lemniscate L = S^1 v S^1.
-- Functions on L live in the split-complex algebra H = Z[j],
-- where j^2 = +1 (not -1 like the complex i).

-- SplitComplex is a pair (re, im) with j^2 = +1 multiplication:
#check SplitComplex           -- structure with fields `re` and `im`
#check SplitComplex.one       -- (1, 0)
#check SplitComplex.j         -- (0, 1), the split-imaginary unit

-- Arithmetic: addition is componentwise, multiplication uses j^2 = +1.
#eval SplitComplex.add ⟨3, 2⟩ ⟨1, 4⟩        -- (4, 6)
#eval SplitComplex.mul ⟨3, 2⟩ ⟨1, 4⟩        -- (11, 14)

-- The KEY difference from complex numbers: H has zero divisors!
-- (1+j)(1-j) = 0:
#eval SplitComplex.mul ⟨1, 1⟩ ⟨1, -1⟩       -- (0, 0)

-- This is not a bug — it is the structural origin of the B/C duality.
-- The zero divisors are exactly the elements with a vanishing sector.
#check zero_divisors_iff

-- H is a full commutative ring (all 8 axioms proved):
#check sc_ring_axioms

-- ================================================================
-- PART 2: SECTOR DECOMPOSITION — THE BIPOLAR SPLIT
-- ================================================================

-- The sector map phi : H -> Z x Z sends (a + bj) to (a+b, a-b).
-- This is a RING ISOMORPHISM to componentwise Z x Z.
-- The two components are the B-sector and C-sector.

#check to_sectors             -- SplitComplex -> SectorPair
#check from_sectors           -- SectorPair -> SplitComplex (left inverse)

#eval to_sectors ⟨3, 2⟩      -- (5, 1): B-sector = 3+2, C-sector = 3-2
#eval from_sectors ⟨5, 1⟩    -- (3, 2): recovers the original

-- Round-trip: from_sectors(to_sectors(z)) = z
#check from_sectors_left_inv
-- Injectivity: to_sectors a = to_sectors b implies a = b
#check to_sectors_injective

-- The idempotent projectors:
--   e_plus  = (1, 0) in sector coords — projects to B-channel
--   e_minus = (0, 1) in sector coords — projects to C-channel
#check e_plus_sector          -- SectorPair: (1, 0)
#check e_minus_sector         -- SectorPair: (0, 1)

-- Every sector pair decomposes: e_plus * sp + e_minus * sp = sp.
-- This is the algebraic origin of idempotent support.
#eval let sp : SectorPair := ⟨7, 3⟩
      let fp := SectorPair.mul e_plus_sector sp    -- (7, 0)
      let fm := SectorPair.mul e_minus_sector sp   -- (0, 3)
      SectorPair.add fp fm                         -- (7, 3)

-- SectorPair also forms a ring (componentwise multiplication):
#check sp_ring_axioms
#eval SectorPair.mul ⟨2, 3⟩ ⟨4, 5⟩              -- (8, 15)

-- ================================================================
-- PART 3: THE TAU^3 FIBERED PRODUCT
-- ================================================================

-- tau^3 = tau^1 x_f T^2 is NOT a Cartesian product.
-- It is a fibered product where the fiber depends on the base.

-- Base tau^1: the (D, A) coordinate space
--   D = radial depth (alpha-channel)
--   A = prime direction (pi-channel)
#check BaseTau1               -- structure with fields `d` and `a`

-- Fiber T^2: the (B, C) coordinate space
--   B = exponent (gamma-channel)
--   C = tetration height (eta-channel)
#check FiberT2                -- structure with fields `b` and `c`

-- The fibered product tau^3:
#check Tau3                   -- structure with `base : BaseTau1` and `fiber : FiberT2`

-- Conversion from the ABCD chart to fibered product form and back:
#check to_tau3                -- TauAdmissiblePoint -> Tau3
#check from_tau3              -- Tau3 -> TauAdmissiblePoint
#check tau3_round_trip        -- from_tau3(to_tau3(p)) = p
#check tau3_round_trip'       -- to_tau3(from_tau3(t)) = t

-- Example: X=12 decomposes as base=(4,3), fiber=(1,1)
#eval to_tau3 (from_tau_idx 12)

-- Projections:
#check tau3_proj              -- tau^3 -> tau^1 (project to base)
#check tau3_fiber_proj        -- tau^3 -> T^2  (project to fiber)
#eval tau3_proj (to_tau3 (from_tau_idx 12))       -- base (4, 3)
#eval tau3_fiber_proj (to_tau3 (from_tau_idx 64)) -- fiber (3, 2)

-- WHY tau^3 is not a product:
-- 1. Peel-order coupling: prime factors of D must be < A
-- 2. Base-to-fiber coupling: admissible (B,C) depends on (D,A)
-- The fibration IS surjective (every base point has a fiber) but
-- fibers vary — different A values yield different admissible ranges.
#eval proj_surjective_check 50   -- true: every base point has fiber B=1,C=0
#eval non_trivial_check          -- true: fibers genuinely vary

-- ================================================================
-- PART 4: BOUNDARY CHARACTERS
-- ================================================================

-- A boundary character is a stagewise map from the profinite boundary
-- Z-hat_tau to the split-complex algebra H. The primorial tower
-- Z/P_1 <- Z/P_2 <- Z/P_3 <- ... approximates Z-hat_tau.

-- An idempotent-supported character decomposes into B and C channels:
--   chi = e_plus * chi_plus + e_minus * chi_minus
#check IdempotentCharacter    -- structure with `b_ch` and `c_ch` stagewise functions

-- The canonical character reads B,C from the ABCD chart:
#check canonical_character
#eval canonical_character.eval 7 2    -- character at input 7, stage 2

-- The decomposition ALWAYS works (algebraic identity):
#check idemp_decomp_recovery
-- e_plus * sp + e_minus * sp = sp, for ANY SectorPair sp

-- Tower coherence: reduce(chi(x, k+1), k) = chi(x, k)
-- The character at stage k is determined by reduction from higher stages.
#check character_tower_structural
#eval character_tower_check 20 4      -- true

-- Characters form a ring under pointwise operations:
#eval character_add_check 15 3        -- true: addition preserves support
#eval character_mul_check 15 3        -- true: multiplication preserves support
#eval character_distributive_check 15 3 -- true: ring distributivity
#eval full_boundary_characters_check 15 3 -- true: all ring axioms hold

-- ================================================================
-- PART 5: THE CENTRAL THEOREM — O(tau^3) = A_spec(L)
-- ================================================================

-- The Central Theorem has 4 links, each previously verified in TauLib:
-- 1. Boundary characters <-> Hartogs extensions (II.T37)
-- 2. Hartogs extensions <-> omega-germ transformers (II.T38)
-- 3. Omega-germ transformers <-> holomorphic functions (II.T39)
-- 4. Holomorphic functions <-> idempotent-supported (II.T33)

-- The spectral algebra A_spec(L) at each stage k:
#check SpectralAlgebraElement          -- B-channel + C-channel functions on Z/P_kZ
#check SpectralAlgebraElement.eval     -- evaluate at (x, k) -> SectorPair

-- Example: a spectral algebra element with identity B-channel, shifted C-channel
#eval let sa : SpectralAlgebraElement := { b_fn := fun n => (n : Int), c_fn := fun n => (n : Int) + 1 }
      sa.eval 7 2                      -- SectorPair at input 7, stage 2

-- The spectral algebra forms a ring at each stage:
#eval spectral_algebra_stage_ring_check 3 15  -- true: ring axioms hold
-- The stages form an inverse tower:
#eval spectral_algebra_tower_check 3 15       -- true: tower compatibility

-- FORWARD direction: boundary data determines a holomorphic function.
-- Given spectral data (B-channel, C-channel), the BndLift construction
-- produces a tower-coherent holomorphic function on tau^3.
#check spectral_to_hol                -- (b_fn, c_fn, x, k) -> SectorPair
#eval central_theorem_forward_check 3 15      -- true

-- INVERSE direction: every holomorphic function restricts to boundary data.
-- Given a tower-coherent function, its restriction to the primorial lattice
-- yields a well-defined spectral algebra element.
#check hol_to_spectral                -- StageFun -> (x, k) -> SectorPair
#eval central_theorem_inverse_check 3 15      -- true

-- ROUND-TRIP: both compositions are the identity.
-- forward . inverse = id AND inverse . forward = id.
#eval central_theorem_roundtrip_check 3 15    -- true

-- Structural round-trip theorem (for identity function):
#check central_roundtrip
-- spectral_to_hol(id, id, x, k) = hol_to_spectral(id_stage, x, k)

-- THE CENTRAL THEOREM: all four links combined.
#eval central_theorem_check 3 15              -- true

-- ================================================================
-- PART 6: FORMAL PROOFS — MACHINE-CHECKED
-- ================================================================

-- Each component is not just evaluated — it is formally PROVED
-- correct by Lean's kernel via native_decide.

-- Spectral ring structure [II.D60]:
#check spectral_ring_3_15       -- spectral_algebra_stage_ring_check 3 15 = true
#check spectral_tower_3_15      -- spectral_algebra_tower_check 3 15 = true

-- Central Theorem links [II.T40]:
#check central_fwd_3_15         -- forward direction verified
#check central_inv_3_15         -- inverse direction verified
#check central_rt_3_15          -- round-trip verified

-- The combined Central Theorem:
#check central_theorem_3_15     -- central_theorem_check 3 15 = true

-- Structural theorems (proved by simp/ring, not native_decide):
#check spectral_periodic              -- evaluation is P_k-periodic
#check spectral_idempotent_supported  -- every element is idempotent-supported
#check central_forward_coherent       -- forward map is tower-coherent
#check central_inverse_periodic       -- inverse restriction is periodic

-- ================================================================
-- PART 7: THE HOLOGRAPHIC PRINCIPLE
-- ================================================================

-- The Central Theorem implies the Holographic Principle [II.C01]:
-- The 1-dimensional boundary (lemniscate data) completely encodes
-- the 3-dimensional interior (tau^3 data).
-- Nothing is lost. Nothing is added.

-- bndlift reconstructs interior from boundary:
#eval holographic_check 3 15                  -- true
#check holographic_3_15    -- holographic_check 3 15 = true (formally proved)

-- Structural: reduce(bndlift(x, k), k) = reduce(x, k)
#check holographic_roundtrip

-- The full check combines everything:
#eval full_central_theorem_check 3 15         -- true
#check full_central_3_15   -- full_central_theorem_check 3 15 = true

-- ================================================================
-- WHAT COMES NEXT
-- ================================================================

-- The Central Theorem is the bridge between pure mathematics (Books I-III)
-- and physics (Books IV-V).
--
-- O(tau^3) = A_spec(L) means:
--   - Interior data (holomorphic functions on the 3-fold) equals
--   - Boundary data (spectral algebra on the lemniscate)
--
-- In physics, this becomes:
--   - Fiber T^2 = the microcosm (quantum mechanics, particles) [Book IV]
--   - Base tau^1 = the macrocosm (gravity, cosmology) [Book V]
--   - The Central Theorem = boundary/bulk duality
--
-- Continue to Tour/Physics.lean to see how iota_tau + one anchor
-- (the neutron mass) generates all of particle physics and cosmology.
