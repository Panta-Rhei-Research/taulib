/-!
# TauLib.BookIV.Sectors.ModeCensus

Boundary mode census on L = S¹ ∨ S¹: the 11/15 charge fraction.

## Registry Cross-References

- [IV.D49] Boundary Mode Census — `BoundaryMode`, `emActive`, `allModes`
- [IV.T16] Active/Silent Census — `active_count`, `silent_count`
- [IV.P08] 11/15 Charge Fraction — `active_count`

## Mathematical Content

On the lemniscate boundary L = S¹ ∨ S¹, each of the 5 generators
{α, π, γ, η, ω} contributes 3 boundary modes (Lobe₊, Lobe₋, Crossing),
giving 15 total modes. The EM-activity census classifies each mode as
either electromagnetically active (nonzero U(1) holonomy) or EM-silent.

**Census result (bipolar):**

| Generator | Sector | Lobe₊ | Lobe₋ | Crossing | Active |
|-----------|--------|-------|-------|----------|--------|
| γ (EM)    | B      | yes   | yes   | yes      | 3      |
| π (Weak)  | A      | yes   | yes   | no       | 2      |
| η (Strong)| C      | yes   | yes   | yes      | 3      |
| α (Grav)  | D      | no    | no    | no       | 0      |
| ω (Higgs) | B∩C    | yes   | yes   | yes      | 3      |
|           |        |       |       | **Total**| **11** |

The 4 silent modes: 3 gravitational (α×{Lobe₊,Lobe₋,Crossing}) +
1 weak neutral (π×Crossing = Z⁰ channel).

## Ground Truth Sources
- open_questions_sprint.md Part B: bipolar census
- physics_layer_sector_instantiation.md §4: generator-sector mapping
-/

namespace Tau.BookIV.Sectors.ModeCensus

-- ============================================================
-- BOUNDARY MODE TYPES [IV.D49]
-- ============================================================

/-- The 5 generators of Category τ (local copy for census). -/
inductive Gen5 where
  | alpha  -- gravity (D-sector)
  | pi_    -- weak (A-sector)
  | gamma  -- EM (B-sector)
  | eta    -- strong (C-sector)
  | omega  -- Higgs/mass (B∩C crossing)
  deriving Repr, DecidableEq, BEq

/-- Lobe configuration on L = S¹ ∨ S¹. -/
inductive LobeConfig where
  | lobePos   -- Lobe₊ (χ₊-character)
  | lobeNeg   -- Lobe₋ (χ₋-character)
  | crossing  -- Crossing point (both lobes, through ω)
  deriving Repr, DecidableEq, BEq

/-- [IV.D49] A boundary mode is a (generator, lobe configuration) pair.
    There are 5 × 3 = 15 such modes. -/
structure BoundaryMode where
  gen : Gen5
  config : LobeConfig
  deriving Repr, DecidableEq, BEq

-- ============================================================
-- EM-ACTIVITY FUNCTION
-- ============================================================

/-- EM-activity: whether a boundary mode carries nonzero U(1) holonomy.

    Bipolar census from the Open Questions Sprint:
    - γ (EM): always active (γ IS the EM generator)
    - π (Weak): Lobe₊ = W⁺ (active), Lobe₋ = W⁻ (active), Crossing = Z⁰ (silent)
    - η (Strong): always active (quarks carry fractional EM charge)
    - α (Gravity): always silent (gravity is EM-neutral)
    - ω (Higgs): always active (Higgs couples to EM charge) -/
def BoundaryMode.emActive : BoundaryMode → Bool
  | ⟨.gamma,  _⟩          => true   -- γ always EM-active
  | ⟨.pi_,   .lobePos⟩    => true   -- W⁺ (charged)
  | ⟨.pi_,   .lobeNeg⟩    => true   -- W⁻ (charged)
  | ⟨.pi_,   .crossing⟩   => false  -- Z⁰ (neutral)
  | ⟨.eta,   _⟩           => true   -- quarks carry fractional charge
  | ⟨.alpha,  _⟩          => false  -- gravity EM-silent
  | ⟨.omega, _⟩           => true   -- Higgs couples to EM

-- ============================================================
-- EXPLICIT ENUMERATION
-- ============================================================

/-- [IV.D49] All 15 boundary modes, listed explicitly. -/
def allModes : List BoundaryMode :=
  [ ⟨.alpha, .lobePos⟩, ⟨.alpha, .lobeNeg⟩, ⟨.alpha, .crossing⟩,
    ⟨.pi_,   .lobePos⟩, ⟨.pi_,   .lobeNeg⟩, ⟨.pi_,   .crossing⟩,
    ⟨.gamma,  .lobePos⟩, ⟨.gamma,  .lobeNeg⟩, ⟨.gamma,  .crossing⟩,
    ⟨.eta,   .lobePos⟩, ⟨.eta,   .lobeNeg⟩, ⟨.eta,   .crossing⟩,
    ⟨.omega, .lobePos⟩, ⟨.omega, .lobeNeg⟩, ⟨.omega, .crossing⟩ ]

/-- Active modes (EM-active). -/
def activeModes : List BoundaryMode := allModes.filter BoundaryMode.emActive

/-- Silent modes (EM-silent). -/
def silentModes : List BoundaryMode := allModes.filter (fun m => !m.emActive)

-- ============================================================
-- CENSUS THEOREMS [IV.T16]
-- ============================================================

/-- [IV.T16] Total number of boundary modes = 15. -/
theorem mode_total : allModes.length = 15 := by native_decide

/-- [IV.T16] Number of EM-active modes = 11. -/
theorem active_count : activeModes.length = 11 := by native_decide

/-- [IV.T16] Number of EM-silent modes = 4. -/
theorem silent_count : silentModes.length = 4 := by native_decide

/-- Active + silent = total (consistency). -/
theorem active_plus_silent :
    activeModes.length + silentModes.length = allModes.length := by native_decide

-- ============================================================
-- 11/15 CHARGE FRACTION [IV.P08]
-- ============================================================

/-- [IV.P08] The charge fraction 11/15 satisfies (11/15)² = 121/225.
    This is the coefficient in the tower formula α = (121/225)·ι_τ⁴. -/
theorem charge_fraction_square : 11 * 11 = (121 : Nat) ∧ 15 * 15 = (225 : Nat) := by omega

/-- The 4 silent modes are exactly: α×3 configs + π×crossing. -/
theorem silent_modes_are_gravity_plus_Z0 :
    (⟨.alpha, .lobePos⟩ : BoundaryMode).emActive = false ∧
    (⟨.alpha, .lobeNeg⟩ : BoundaryMode).emActive = false ∧
    (⟨.alpha, .crossing⟩ : BoundaryMode).emActive = false ∧
    (⟨.pi_, .crossing⟩ : BoundaryMode).emActive = false := by
  exact ⟨rfl, rfl, rfl, rfl⟩

-- ============================================================
-- EULER SIEVE RECONCILIATION
-- ============================================================

/-- The Euler sieve identity: (1−1/3)·(1−1/5)·(1+1/120) = (11/15)².
    Cross-multiplied: 2 · 4 · 121 · 225 = 3 · 5 · 120 · 121. -/
theorem euler_sieve_identity :
    2 * 4 * 121 * 225 = 3 * 5 * 120 * (121 : Nat) := by omega

/-- The S₅ correction factor is 121/120 = 1 + 1/5!. -/
theorem s5_correction : (121 : Nat) = 120 + 1 ∧ (120 : Nat) = 1 * 2 * 3 * 4 * 5 := by omega

/-- Total modes = 5 × 3 = 15. -/
theorem mode_product : 5 * 3 = (15 : Nat) := by omega

-- ============================================================
-- SMOKE TESTS
-- ============================================================

#eval allModes.length      -- 15
#eval activeModes.length   -- 11
#eval silentModes.length   -- 4

end Tau.BookIV.Sectors.ModeCensus
