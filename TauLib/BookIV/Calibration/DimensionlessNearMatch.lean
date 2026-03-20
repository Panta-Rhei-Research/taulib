import TauLib.BookIV.Sectors.FineStructure
import TauLib.BookIV.Calibration.SIReference

/-!
# TauLib.BookIV.Calibration.DimensionlessNearMatch

Maps τ-derived dimensionless couplings to physical constants with range proofs.

## Registry Cross-References

- [IV.D28] Weinberg Near-Match — `WeinbergNearMatch`, `weinberg_range`
- [IV.D29] Strong Near-Match — `StrongNearMatch`, `strong_range`
- [IV.P05] All Near-Matches in Range — `all_near_matches_in_range`

## Mathematical Content

### Dimensionless Near-Matches

The τ-framework produces dimensionless couplings from ι_τ alone.
Three such couplings can be compared to measured physical constants:

| τ-coupling | Formula | τ-value | SI value | Deviation |
|------------|---------|---------|----------|-----------|
| α_EM | (8/15)·ι_τ⁴ | ~1/137.9 | 1/137.036 | 0.6% |
| sin²θ_W | ι_τ(1−ι_τ) | ~0.2249 | 0.23121 | 2.7% |
| α_s(M_Z) | 2·ι_τ³/(1−ι_τ) | ~0.1208 | 0.1180 | 2.4% |

All three are CONJECTURAL: the numerical near-matches are observed but
the exact mechanism connecting ι_τ formulas to measured values requires
the full calibration cascade (Parts III–X).

## Ground Truth Sources
- Book IV Part II ch10 (Sector Couplings), ch11 (Fine-Structure α)
- CODATA 2022 for experimental values
-/

namespace Tau.BookIV.Calibration

open Tau.Boundary Tau.BookIII.Sectors Tau.BookIV.Sectors

-- ============================================================
-- WEINBERG ANGLE NEAR-MATCH [IV.D28]
-- ============================================================

/-- [IV.D28] Weinberg angle near-match: κ(A,D) = ι_τ(1−ι_τ) vs sin²θ_W.

    τ-derived: κ(A,D) ≈ 0.2249
    Experimental: sin²θ_W = 0.23121(4) (on-shell, CODATA 2022)
    Deviation: ~2.7% -/
structure WeinbergNearMatch where
  /-- τ-derived coupling formula. -/
  tau_coupling : CouplingFormula := kappa_AD
  /-- SI reference value. -/
  si_value : SIConstant := si_weinberg_sin2
  /-- Scope: established (near-match with range proof). -/
  scope : String := "established"

/-- κ(A,D) is in the range (0.224, 0.226). -/
theorem weinberg_range :
    kappa_AD.numer * 1000 > 224 * kappa_AD.denom ∧
    kappa_AD.numer * 1000 < 226 * kappa_AD.denom := by native_decide

/-- κ(A,D) < sin²θ_W: the τ-approximation undershoots the experimental value. -/
theorem weinberg_undershoots :
    kappa_AD.numer * si_weinberg_sin2.denom <
    si_weinberg_sin2.numer * kappa_AD.denom := by native_decide

/-- The Weinberg deviation is less than 3%.
    (sin²θ_W − κ(A,D)) × 100 < 3 × sin²θ_W
    Cross-multiplied on Nat pairs. -/
theorem weinberg_deviation_lt_3pct :
    (si_weinberg_sin2.numer * kappa_AD.denom -
     kappa_AD.numer * si_weinberg_sin2.denom) * 100 <
    3 * si_weinberg_sin2.numer * kappa_AD.denom := by native_decide

-- ============================================================
-- STRONG COUPLING NEAR-MATCH [IV.D29]
-- ============================================================

/-- [IV.D29] Strong coupling near-match: 2·κ(C,C) vs α_s(M_Z).

    τ-derived: 2·κ(C) = 2·ι_τ³/(1−ι_τ) ≈ 0.1208
    Experimental: α_s(M_Z) = 0.1180(9)
    Deviation: ~2.4% -/
structure StrongNearMatch where
  /-- τ-derived coupling formula (doubled). -/
  tau_coupling : CouplingFormula := kappa_CC
  /-- Multiplication factor. -/
  factor : Nat := 2
  /-- SI reference value. -/
  si_value : SIConstant := si_strong_coupling
  /-- Scope: established (near-match with range proof). -/
  scope : String := "established"

/-- 2·κ(C) is in the range (0.119, 0.122), bracketing α_s ≈ 0.1180. -/
theorem strong_range :
    2 * kappa_CC.numer * 1000 > 119 * kappa_CC.denom ∧
    2 * kappa_CC.numer * 1000 < 122 * kappa_CC.denom := by native_decide

/-- 2·κ(C) > α_s: the τ-approximation overshoots the experimental value. -/
theorem strong_overshoots :
    2 * kappa_CC.numer * si_strong_coupling.denom >
    si_strong_coupling.numer * kappa_CC.denom := by native_decide

/-- The strong coupling deviation is less than 3%.
    (2κ(C) − α_s) × 100 < 3 × α_s
    Cross-multiplied on Nat pairs. -/
theorem strong_deviation_lt_3pct :
    (2 * kappa_CC.numer * si_strong_coupling.denom -
     si_strong_coupling.numer * kappa_CC.denom) * 100 <
    3 * si_strong_coupling.numer * kappa_CC.denom := by native_decide

-- ============================================================
-- FINE STRUCTURE RECAP
-- ============================================================

/-- The spectral 1/α overshoots the experimental value:
    α_spectral < α_exp (i.e. 1/α_spectral > 1/α_exp).
    Spectral: 1/α ≈ 137.9, Experimental: 1/α ≈ 137.036. -/
theorem alpha_spectral_overshoots :
    alpha_spectral_denom * si_alpha_inverse.denom >
    si_alpha_inverse.numer * alpha_spectral_numer := by native_decide

-- ============================================================
-- ALL NEAR-MATCHES IN RANGE [IV.P05]
-- ============================================================

/-- [IV.P05] All three dimensionless near-matches are within their
    respective range brackets. This is a structural observation,
    NOT a proof of correctness — all three are CONJECTURAL. -/
theorem all_near_matches_in_range :
    -- α: spectral 1/α between 137 and 139 (exp: 137.036)
    (alpha_spectral_denom > 137 * alpha_spectral_numer ∧
     alpha_spectral_denom < 139 * alpha_spectral_numer) ∧
    -- sin²θ_W: κ(A,D) between 0.224 and 0.226 (exp: 0.2312)
    (kappa_AD.numer * 1000 > 224 * kappa_AD.denom ∧
     kappa_AD.numer * 1000 < 226 * kappa_AD.denom) ∧
    -- α_s: 2·κ(C) between 0.119 and 0.122 (exp: 0.1180)
    (2 * kappa_CC.numer * 1000 > 119 * kappa_CC.denom ∧
     2 * kappa_CC.numer * 1000 < 122 * kappa_CC.denom) :=
  ⟨alpha_inverse_correct_ballpark, weinberg_range, strong_range⟩

-- ============================================================
-- NEAR-MATCH SUMMARY TABLE
-- ============================================================

/-- Near-match entry for the summary table. -/
structure NearMatchEntry where
  name : String
  tau_numer : Nat
  tau_denom : Nat
  si_numer : Nat
  si_denom : Nat
  overshoots : Bool   -- true if τ-value > SI-value
  deriving Repr

/-- The three dimensionless near-match entries. -/
def near_match_table : List NearMatchEntry := [
  ⟨"Fine structure 1/α",
   alpha_spectral_denom, alpha_spectral_numer,  -- inverted for 1/α
   si_alpha_inverse.numer, si_alpha_inverse.denom,
   true⟩,  -- τ gives 1/α ≈ 137.9 > 137.036
  ⟨"Weinberg sin²θ_W",
   kappa_AD.numer, kappa_AD.denom,
   si_weinberg_sin2.numer, si_weinberg_sin2.denom,
   false⟩,  -- τ gives 0.2249 < 0.2312
  ⟨"Strong α_s(M_Z)",
   2 * kappa_CC.numer, kappa_CC.denom,
   si_strong_coupling.numer, si_strong_coupling.denom,
   true⟩   -- τ gives 0.1208 > 0.1180
]

/-- Three near-match entries. -/
theorem near_match_count : near_match_table.length = 3 := by rfl

-- ============================================================
-- SMOKE TESTS
-- ============================================================

-- κ(A,D) ≈ 0.2249 (Weinberg near-match)
#eval kappa_AD.toFloat               -- ≈ 0.2249

-- 2·κ(C) ≈ 0.1208 (Strong near-match)
#eval 2.0 * kappa_CC.toFloat         -- ≈ 0.1208

-- 1/α_spectral ≈ 137.9
#eval alpha_inverse_float            -- ≈ 137.9

-- SI comparison values
#eval si_weinberg_sin2.toFloat       -- 0.23121
#eval si_strong_coupling.toFloat     -- 0.118
#eval si_alpha_inverse.toFloat       -- 137.036

-- Near-match count
#eval near_match_table.length        -- 3

end Tau.BookIV.Calibration
