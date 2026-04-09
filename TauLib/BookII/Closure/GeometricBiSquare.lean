import TauLib.BookII.Closure.ForwardBook3
import TauLib.BookI.Holomorphy.PresheafEssence
import TauLib.BookII.Topology.TorusDegeneration
import TauLib.BookII.Geometry.PaschParallel
import TauLib.BookII.Domains.HolImpliesCont

/-!
# TauLib.BookII.Closure.GeometricBiSquare

The Geometric Bi-Square: Book I's algebraic bi-square (I.T41)
filled with the geometric objects earned in Book II Parts I-IX.

## Registry Cross-References

- [II.D77] Geometric Bi-Square — `GeometricBiSquareData`, `compute_geometric_bisquare`
- [II.T49] Geometric Bi-Square Theorem — `geometric_bisquare_check`
- [II.R33] Algebraic-to-Geometric Audit — `algebraic_geometric_audit`
- [II.R34] Scaling Chain Forward — `ScalingLevel`, `scaling_chain_check`

## Mathematical Content

The algebraic bi-square (I.T41) is a pasted commuting diagram
on finite cyclic groups Z/M_kZ:

- Left square: tower coherence (reduce(f_l(n), k) = f_k(n))
- Right square: spectral naturality (chi_+/chi_- decomposition)
- Limit principle: agreement at one depth implies agreement below

Book II fills this algebraic skeleton with geometric content:
- Domain L becomes S^1 v S^1 via torus degeneration (II.T13)
- Interior tau^3 becomes Stone space (II.T07)
- Codomain becomes calibrated H_tau (II.D35)
- Spectral algebra becomes A_spec(L) (II.D60)
- Limit principle becomes Central Theorem (II.T40)

The Geometric Bi-Square Theorem (II.T49) asserts all eight components
are earned, all commuting squares are continuous, and the limit row
is precisely the Central Theorem.
-/

namespace Tau.BookII.Closure

open Tau.Polarity Tau.Boundary Tau.Coordinates Tau.Denotation
open Tau.BookII.Interior Tau.BookII.Domains Tau.Holomorphy
open Tau.BookII.Hartogs Tau.BookII.Regularity Tau.BookII.Enrichment
open Tau.BookII.CentralTheorem Tau.BookII.Topology Tau.BookII.Geometry

-- ============================================================
-- GEOMETRIC BI-SQUARE DATA [II.D77]
-- ============================================================

/-- [II.D77] The Geometric Bi-Square: Book I's algebraic bi-square (I.T41)
    annotated with boolean witnesses recording that each geometric
    component has been earned in Book II.

    Eight witnesses correspond to eight geometric "earnings":
    1. topology_earned: Stone space structure on tau^3 (II.T07)
    2. continuity_earned: Hol implies Continuous (II.T06)
    3. geometry_earned: Tarski axioms verified (II.T16-T20)
    4. torus_degeneration_earned: T^2 -> S^1 v S^1 (II.T13)
    5. calibration_earned: H_tau calibrated with pi, e, j (II.D35)
    6. spectral_algebra_earned: A_spec(L) ring structure (II.D60)
    7. central_theorem_earned: O(tau^3) = A_spec(L) (II.T40)
    8. hartogs_earned: Mutual determination (II.T27) -/
structure GeometricBiSquareData where
  /-- Stone space structure on tau^3 (II.T07). -/
  topology_earned : Bool
  /-- Hol implies Continuous (II.T06). -/
  continuity_earned : Bool
  /-- Tarski axioms verified (II.T16-T20). -/
  geometry_earned : Bool
  /-- T^2 -> S^1 v S^1 via pinch map (II.T13). -/
  torus_degeneration_earned : Bool
  /-- H_tau calibrated with pi, e, j (II.D35). -/
  calibration_earned : Bool
  /-- A_spec(L) ring/tower structure (II.D60). -/
  spectral_algebra_earned : Bool
  /-- Central Theorem O(tau^3) = A_spec(L) (II.T40). -/
  central_theorem_earned : Bool
  /-- Mutual determination / Hartogs (II.T27). -/
  hartogs_earned : Bool
  deriving Repr, DecidableEq

-- ============================================================
-- COMPUTE GEOMETRIC BI-SQUARE [II.D77]
-- ============================================================

/-- [II.D77] Compute the Geometric Bi-Square by evaluating all
    eight geometric check functions from Book II.
    Parameters db, bound control verification depth. -/
def compute_geometric_bisquare (db bound : TauIdx) : GeometricBiSquareData :=
  { topology_earned := stone_space_check bound db
  , continuity_earned := hol_cont_check id_stage db bound
  , geometry_earned := tarski_complete_check bound db
  , torus_degeneration_earned :=
      pinch_surjective_check && gauge_survival_check && fund_group_check
  , calibration_earned := calibration_consistency_check
  , spectral_algebra_earned := spectral_algebra_stage_ring_check db bound
  , central_theorem_earned := central_theorem_check db bound
  , hartogs_earned := hartogs_check bound db
  }

/-- [II.D77] Check that all eight components are earned. -/
def geometric_bisquare_complete (gbs : GeometricBiSquareData) : Bool :=
  gbs.topology_earned &&
  gbs.continuity_earned &&
  gbs.geometry_earned &&
  gbs.torus_degeneration_earned &&
  gbs.calibration_earned &&
  gbs.spectral_algebra_earned &&
  gbs.central_theorem_earned &&
  gbs.hartogs_earned

-- ============================================================
-- GEOMETRIC BI-SQUARE THEOREM [II.T49]
-- ============================================================

/-- [II.T49] The Geometric Bi-Square Theorem: compute and verify
    that all eight geometric components are earned. -/
def geometric_bisquare_check (db bound : TauIdx) : Bool :=
  geometric_bisquare_complete (compute_geometric_bisquare db bound)

/-- [II.T49] Count how many geometric components are verified (out of 8). -/
def geometric_component_count (gbs : GeometricBiSquareData) : Nat :=
  (if gbs.topology_earned then 1 else 0) +
  (if gbs.continuity_earned then 1 else 0) +
  (if gbs.geometry_earned then 1 else 0) +
  (if gbs.torus_degeneration_earned then 1 else 0) +
  (if gbs.calibration_earned then 1 else 0) +
  (if gbs.spectral_algebra_earned then 1 else 0) +
  (if gbs.central_theorem_earned then 1 else 0) +
  (if gbs.hartogs_earned then 1 else 0)

-- ============================================================
-- ALGEBRAIC-TO-GEOMETRIC AUDIT [II.R33]
-- ============================================================

/-- [II.R33] Algebraic-to-Geometric Audit: record which Book I
    algebraic components have received geometric content in Book II.
    The audit passes when all eight components are earned AND
    the E1 export package is complete. -/
def algebraic_geometric_audit (db bound k_max : TauIdx) : Bool :=
  geometric_bisquare_check db bound &&
  full_export_check db bound k_max

-- ============================================================
-- COMPATIBILITY WITH ALGEBRAIC BI-SQUARE
-- ============================================================

/-- The algebraic core: the Book I crown jewel is always available
    regardless of the geometric witnesses.
    This is a definitional identity: the algebraic bi-square (I.T41)
    exists independently of whether Book II's geometry is earned. -/
def algebraic_core : BookICrownJewel := book_i_crown_jewel

/-- Compatibility: the algebraic bi-square characterization is
    preserved. Forgetting geometry recovers I.T41. -/
theorem compatibility_with_algebraic (f : StageFun) :
    TowerCoherent f ↔
    (∀ n k l : TauIdx, k ≤ l → reduce (f.b_fun n l) k = f.b_fun n k) ∧
    (∀ n k l : TauIdx, k ≤ l → reduce (f.c_fun n l) k = f.c_fun n k) :=
  algebraic_core.bi_square_char f

/-- Compatibility: the limit principle survives geometrization. -/
theorem geometric_preserves_limit (f₁ f₂ : StageFun)
    (h₁ : TowerCoherent f₁) (h₂ : TowerCoherent f₂)
    (d₀ : TauIdx) (h : ∀ n, agree_at f₁ f₂ n d₀) :
    ∀ n k, k ≤ d₀ → agree_at f₁ f₂ n k :=
  algebraic_core.limit_principle f₁ f₂ h₁ h₂ d₀ h

/-- Compatibility: right-square automaticity survives geometrization. -/
theorem geometric_preserves_right_auto (f : StageFun) (htc : TowerCoherent f)
    (n k l : TauIdx) (hkl : k ≤ l) :
    spectral_of f n k =
    ⟨reduce (spectral_of f n l).b_coeff k,
     reduce (spectral_of f n l).c_coeff k⟩ :=
  algebraic_core.right_automatic f htc n k l hkl

-- ============================================================
-- SCALING CHAIN [II.R34]
-- ============================================================

/-- [II.R34] The three enrichment levels at which the bi-square lives.
    - E0_algebraic: Book I (finite cyclic groups, no topology)
    - E1_geometric: Book II (Stone space, continuity, torus degeneration)
    - E2_enriched: Book III (spectral forces, preview only) -/
inductive ScalingLevel where
  | E0_algebraic : ScalingLevel
  | E1_geometric : ScalingLevel
  | E2_enriched  : ScalingLevel
  deriving Repr, DecidableEq

/-- [II.R34] The scaling chain: algebraic < geometric < enriched.
    Each level adds geometric content to the bi-square. -/
def scaling_level_index : ScalingLevel → Nat
  | .E0_algebraic => 0
  | .E1_geometric => 1
  | .E2_enriched  => 2

/-- [II.R34] Scaling chain monotonicity: E0 < E1 < E2. -/
def scaling_chain_check : Bool :=
  scaling_level_index .E0_algebraic < scaling_level_index .E1_geometric &&
  scaling_level_index .E1_geometric < scaling_level_index .E2_enriched

/-- [II.R34] Book II lives at E1_geometric. -/
def book2_scaling_level : ScalingLevel := .E1_geometric

/-- [II.R34] The geometric bi-square is the E1 avatar of the algebraic
    bi-square. The E2 avatar (enriched bi-square) will be earned in Book III. -/
def e2_not_yet_earned : Bool :=
  scaling_level_index book2_scaling_level < scaling_level_index .E2_enriched

-- ============================================================
-- SMOKE TESTS
-- ============================================================

-- Compute geometric bi-square
#eval compute_geometric_bisquare 3 15

-- Individual components
#eval (compute_geometric_bisquare 3 15).topology_earned            -- true
#eval (compute_geometric_bisquare 3 15).continuity_earned          -- true
#eval (compute_geometric_bisquare 3 15).geometry_earned            -- true
#eval (compute_geometric_bisquare 3 15).torus_degeneration_earned  -- true
#eval (compute_geometric_bisquare 3 15).calibration_earned         -- true
#eval (compute_geometric_bisquare 3 15).spectral_algebra_earned    -- true
#eval (compute_geometric_bisquare 3 15).central_theorem_earned     -- true
#eval (compute_geometric_bisquare 3 15).hartogs_earned             -- true

-- Full check
#eval geometric_bisquare_check 3 15                                -- true

-- Component count
#eval geometric_component_count (compute_geometric_bisquare 3 15)  -- 8

-- Audit
#eval algebraic_geometric_audit 3 15 3                             -- true

-- Scaling chain
#eval scaling_chain_check                                          -- true
#eval book2_scaling_level                                          -- E1_geometric
#eval e2_not_yet_earned                                            -- true

-- Algebraic core
#check algebraic_core
#check compatibility_with_algebraic
#check geometric_preserves_limit

-- ============================================================
-- FORMAL VERIFICATION (native_decide)
-- ============================================================

-- Geometric Bi-Square Theorem [II.T49]
theorem geometric_bisquare_3_15 :
    geometric_bisquare_check 3 15 = true := by native_decide

-- All eight components [II.T49]
theorem geometric_all_eight :
    geometric_component_count (compute_geometric_bisquare 3 15) = 8 := by native_decide

-- Individual geometric components [II.D77]
theorem geo_topology :
    (compute_geometric_bisquare 3 15).topology_earned = true := by native_decide

theorem geo_continuity :
    (compute_geometric_bisquare 3 15).continuity_earned = true := by native_decide

theorem geo_geometry :
    (compute_geometric_bisquare 3 15).geometry_earned = true := by native_decide

theorem geo_torus_degeneration :
    (compute_geometric_bisquare 3 15).torus_degeneration_earned = true := by native_decide

theorem geo_calibration :
    (compute_geometric_bisquare 3 15).calibration_earned = true := by native_decide

theorem geo_spectral_algebra :
    (compute_geometric_bisquare 3 15).spectral_algebra_earned = true := by native_decide

theorem geo_central_theorem :
    (compute_geometric_bisquare 3 15).central_theorem_earned = true := by native_decide

theorem geo_hartogs :
    (compute_geometric_bisquare 3 15).hartogs_earned = true := by native_decide

-- Audit [II.R33]
theorem audit_3_15_3 :
    algebraic_geometric_audit 3 15 3 = true := by native_decide

-- Scaling chain [II.R34]
theorem scaling_chain_valid :
    scaling_chain_check = true := by native_decide

theorem e2_not_earned :
    e2_not_yet_earned = true := by native_decide

-- ============================================================
-- STRUCTURAL THEOREMS
-- ============================================================

/-- [II.T49] A complete geometric bi-square has all 8 components.
    This is the structural statement that completeness implies count = 8. -/
theorem complete_means_eight (gbs : GeometricBiSquareData) :
    geometric_bisquare_complete gbs = true →
    geometric_component_count gbs = 8 := by
  intro h
  simp only [geometric_bisquare_complete] at h
  simp only [geometric_component_count]
  revert h
  cases gbs.topology_earned <;>
  cases gbs.continuity_earned <;>
  cases gbs.geometry_earned <;>
  cases gbs.torus_degeneration_earned <;>
  cases gbs.calibration_earned <;>
  cases gbs.spectral_algebra_earned <;>
  cases gbs.central_theorem_earned <;>
  cases gbs.hartogs_earned <;>
  simp

/-- [II.T49] The geometric bi-square implies the Central Theorem is earned.
    If the full check passes, the central_theorem_earned field is true. -/
theorem geometric_implies_central (db bound : TauIdx) :
    geometric_bisquare_check db bound = true →
    central_theorem_check db bound = true := by
  intro h
  simp only [geometric_bisquare_check, geometric_bisquare_complete,
             compute_geometric_bisquare] at h
  revert h
  cases central_theorem_check db bound <;> simp

/-- [II.R34] E0 and E1 are distinct scaling levels. -/
theorem e0_ne_e1 : ScalingLevel.E0_algebraic ≠ ScalingLevel.E1_geometric := by
  intro h; cases h

/-- [II.R34] E1 and E2 are distinct scaling levels. -/
theorem e1_ne_e2 : ScalingLevel.E1_geometric ≠ ScalingLevel.E2_enriched := by
  intro h; cases h

end Tau.BookII.Closure
