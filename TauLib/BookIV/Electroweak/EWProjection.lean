import TauLib.BookIV.Sectors.ModeCensus
import TauLib.BookIV.Sectors.BoundaryFiltration
import TauLib.BookI.CF.WindowAlgebra

/-!
# TauLib.BookIV.Electroweak.EWProjection

Structural derivation of 5/7 as an EW projection density on A_spec(L),
resolving the spectral origin of the NLO Weinberg coefficient.

## Registry Cross-References

- [IV.D335] EW-Active Mode — `isEWActive`
- [IV.D336] EW 3-Way Partition — `ewActiveModes`, `strongModes`, `ewComplement`
- [IV.T136] EW Partition Theorem — `mode_partition_EW`
- [IV.T137] EW Density = 5/7 — `ew_density_is_5_over_7`
- [IV.T138] EW–CF Bridge — `ew_density_equals_window_ratio`
- [IV.P182] Complement Characterization — `ew_complement_characterization`
- [IV.R392] OQ-B2 Status — RESOLVED (τ-EFFECTIVE)

## Mathematical Content

The 15 boundary modes on A_spec(L) admit a structural 3-way partition
under EW mixing compatibility:

| Subspace       | Modes                          | Count | Rule                          |
|----------------|--------------------------------|-------|-------------------------------|
| V_EW           | γ×{all 3} + π×{Lobe+, Lobe-}  | **5** | B-sector ∪ A-sector charged   |
| V_strong       | η×{all 3}                      | **3** | C-sector (χ₋-dominant fiber)  |
| V_complement   | α×{all 3} + π×Crossing + ω×3  | **7** | gravity + Z⁰ + Higgs         |

**Result:** 5/7 = dim(V_EW) / dim(V_complement).

This is the EW analogue of the OQ.11/OQ-A1 resolution:
- OQ.11: 11/15 = EM-active / total → α = (11/15)²·ι_τ⁴
- OQ-B2: 5/7 = EW-active / complement → NLO coefficient

The derivation uses only carrier type (Base/Fiber from τ³ = τ¹ ×_f T²),
sector assignment (5 generators → 5 sectors), and EW mixing compatibility
(B-sector + A-sector charged). No SM gauge groups or coupling constants.

## Ground Truth Sources
- OQ-B2 (06_open_questions.md): NLO coefficient 5/7
- BoundaryFiltration.lean: carrier + polarity structural rules
- WeinbergNLO.lean: CF window algebra for 5/7
-/

namespace Tau.BookIV.Electroweak.EWProjection

open Tau.BookIV.Sectors.ModeCensus
open Tau.BookIV.Sectors.BoundaryFiltration
open Tau.BookIV.Sectors
open Tau.CF

-- ============================================================
-- EW-ACTIVITY CLASSIFICATION [IV.D335]
-- ============================================================

/-- [IV.D335] EW-active: a boundary mode participates in electroweak mixing.

    **Rule:** B-sector (γ, all configs) + A-sector charged (π, lobe configs).
    Uses sector assignment and polarity, not SM physics.
    - B-sector (EM): always EW-active (EM IS electroweak)
    - A-sector (Weak): lobes = W± (charged, EW-active), crossing = Z⁰ (neutral, not EW-active)
    - All others: not EW-active (strong, gravity, Higgs) -/
def isEWActive : BoundaryMode → Bool
  | ⟨.gamma, _⟩         => true   -- B-sector: always EW-active
  | ⟨.pi_, .lobePos⟩    => true   -- A-sector, W⁺: charged, EW-active
  | ⟨.pi_, .lobeNeg⟩    => true   -- A-sector, W⁻: charged, EW-active
  | _                    => false  -- All else: not EW-active

/-- Strong-sector predicate: η × {all 3 configs}. -/
def isStrong : BoundaryMode → Bool
  | ⟨.eta, _⟩ => true
  | _          => false

/-- EW complement: modes outside both EW-active and strong. -/
def isEWComplement (m : BoundaryMode) : Bool :=
  !isEWActive m && !isStrong m

-- ============================================================
-- MODE LISTS [IV.D336]
-- ============================================================

/-- [IV.D336] EW-active modes on A_spec(L). -/
def ewActiveModes : List BoundaryMode :=
  allModes.filter isEWActive

/-- Strong modes on A_spec(L). -/
def strongModes : List BoundaryMode :=
  allModes.filter isStrong

/-- EW complement modes on A_spec(L). -/
def ewComplement : List BoundaryMode :=
  allModes.filter isEWComplement

-- ============================================================
-- CENSUS THEOREMS
-- ============================================================

/-- EW-active count = 5 (γ×3 + π×{Lobe+, Lobe-}). -/
theorem ew_active_count : ewActiveModes.length = 5 := by native_decide

/-- Strong count = 3 (η×3). -/
theorem strong_mode_count : strongModes.length = 3 := by native_decide

/-- EW complement count = 7 (α×3 + Z⁰ + ω×3). -/
theorem ew_complement_count : ewComplement.length = 7 := by native_decide

-- ============================================================
-- PARTITION THEOREM [IV.T136]
-- ============================================================

/-- [IV.T136] The 15 boundary modes partition into 5 + 3 + 7.
    This is a structural partition: EW-active ⊔ strong ⊔ complement = all. -/
theorem mode_partition_EW : 5 + 3 + 7 = 15 := by omega

/-- Census consistency: partition sums to total. -/
theorem partition_consistent :
    ewActiveModes.length + strongModes.length + ewComplement.length =
    allModes.length := by native_decide

/-- The partition is disjoint: no mode is in two subsets. -/
theorem partition_disjoint :
    (allModes.filter (fun m => isEWActive m && isStrong m)).length = 0 ∧
    (allModes.filter (fun m => isEWActive m && isEWComplement m)).length = 0 ∧
    (allModes.filter (fun m => isStrong m && isEWComplement m)).length = 0 := by
  exact ⟨by native_decide, by native_decide, by native_decide⟩

-- ============================================================
-- EW DENSITY THEOREM [IV.T137]
-- ============================================================

/-- [IV.T137] The EW projection density is 5/7.
    Cross-multiplied: |V_EW| × |V_complement_den| = |V_complement| × |V_EW_num|
    where both equal 35. -/
theorem ew_density_is_5_over_7 :
    ewActiveModes.length * 7 = ewComplement.length * 5 := by native_decide

-- ============================================================
-- COMPLEMENT CHARACTERIZATION [IV.P182]
-- ============================================================

/-- [IV.P182] The 7 complement modes are exactly α×3 + π×crossing(Z⁰) + ω×3.
    Physical interpretation: gravity (3) + neutral weak (1) + Higgs (3). -/
theorem ew_complement_characterization :
    isEWComplement ⟨.alpha, .lobePos⟩ = true ∧
    isEWComplement ⟨.alpha, .lobeNeg⟩ = true ∧
    isEWComplement ⟨.alpha, .crossing⟩ = true ∧
    isEWComplement ⟨.pi_, .crossing⟩ = true ∧
    isEWComplement ⟨.omega, .lobePos⟩ = true ∧
    isEWComplement ⟨.omega, .lobeNeg⟩ = true ∧
    isEWComplement ⟨.omega, .crossing⟩ = true := by
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- The complement has exactly 3 + 1 + 3 = 7 structure:
    3 gravity (α) + 1 neutral weak (Z⁰) + 3 Higgs (ω). -/
theorem complement_structure : 3 + 1 + 3 = 7 := by omega

-- ============================================================
-- EW–CF BRIDGE [IV.T138]
-- ============================================================

/-- [IV.T138] Bridge theorem: the EW mode density equals the CF window ratio.
    |V_EW| = W₃(4) = 5 and |V_complement| = W₃(3) − 2·W₃(4) = 7.
    This links the structural partition to the CF algebra of ι_τ. -/
theorem ew_density_equals_window_ratio :
    ewActiveModes.length = windowSum cf_head 3 4 ∧
    ewComplement.length = windowSum cf_head 3 3 - 2 * windowSum cf_head 3 4 := by
  constructor
  · -- |V_EW| = W₃(4) = 5
    native_decide
  · -- |V_complement| = W₃(3) − 2·W₃(4) = 17 − 10 = 7
    native_decide

/-- The strong sector count also matches: 3 = |solenoidal|. -/
theorem strong_equals_solenoidal :
    strongModes.length = Tau.Kernel.solenoidalGenerators.length := by native_decide

-- ============================================================
-- OQ-B2 RESOLUTION STATUS [IV.R392]
-- ============================================================

/-- [IV.R392] OQ-B2 RESOLVED (τ-EFFECTIVE).

    Derivation chain:
    1. A_spec(L) has 15 boundary modes (5 generators × 3 configs)
    2. EW partition: V_EW (5) + V_strong (3) + V_complement (7) = 15
    3. Density: 5/7 = dim(V_EW) / dim(V_complement)
    4. CF bridge: 5 = W₃(4), 7 = W₃(3) − 2·W₃(4) (numerical match)
    5. NLO: sin²θ_W = ι(1−ι) · (1 + (5/7)·ι³)  at 86 ppm

    Residual open: WHY does CF[ι_τ] match the mode census?
    (CF Compression Thesis — foundational, beyond series scope) -/
def remark_oq_b2_resolved : String :=
  "OQ-B2 RESOLVED: 5/7 = EW projection density on A_spec(L). " ++
  "V_EW (5) / V_complement (7) from carrier + polarity + mixing rules."

-- ============================================================
-- SMOKE TESTS
-- ============================================================

#eval ewActiveModes.length   -- 5
#eval strongModes.length     -- 3
#eval ewComplement.length    -- 7

-- Mode-by-mode EW activity
#eval allModes.map (fun m => (m.gen, m.config, isEWActive m, isStrong m, isEWComplement m))

end Tau.BookIV.Electroweak.EWProjection
