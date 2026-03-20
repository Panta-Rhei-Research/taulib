import TauLib.BookIV.Sectors.BoundaryFiltration
import TauLib.BookIV.Sectors.ModeCensus

/-!
# TauLib.BookIV.Sectors.SpectralPage

Tensor-square derivation of 121/225 from the E₁ spectral page.

## Registry Cross-References

- [IV.D331] Tensor-Square Character Algebra — `tensorModes`
- [IV.T133] EM Tensor Density Theorem — `em_tensor_active_count`, `em_tensor_total`
- [IV.P179] E₁ Page Derivation of α-Coefficient — `tensor_equals_sieve_times_correction`
- [IV.R388] OQ-A1 Status Update — RESOLVED

## Mathematical Content

The boundary character algebra A_spec(L) has 15 modes (5 generators × 3 lobe
configurations). The tensor square A_spec(L)^{⊗2} has 225 = 15² mode pairs.
A mode pair (m₁, m₂) is jointly EM-active when both m₁ and m₂ are EM-active.

The EM-active count in the tensor square is 11² = 121 (since each factor
contributes independently). The density 121/225 = (11/15)² is the coefficient
in α = (121/225)·ι_τ⁴.

**Physical interpretation:** α is a coupling constant for emission-absorption.
Each vertex (source, sink) contributes one factor of 11/15. The product
(11/15)² = 121/225 is the joint probability that both endpoints of the EM
propagator land on EM-active boundary modes.

**Unification:** The factorization (8/15)·(121/120) is a COROLLARY of the
tensor-square density, not the other way around.

## Ground Truth Sources
- spectral_page_121_225_sprint.md: mathematical derivation
- BoundaryFiltration.lean: structural EM-activity, twin prime residue
- ModeCensus.lean: mode enumeration, 11/15 census
-/

namespace Tau.BookIV.Sectors.SpectralPage

open Tau.BookIV.Sectors.ModeCensus
open Tau.BookIV.Sectors.BoundaryFiltration

-- ============================================================
-- TENSOR-SQUARE MODES [IV.D331]
-- ============================================================

/-- [IV.D331] All mode pairs in A_spec(L)^{⊗2}. -/
def tensorModes : List (BoundaryMode × BoundaryMode) :=
  allModes.flatMap (fun m₁ => allModes.map (fun m₂ => (m₁, m₂)))

/-- EM-active tensor modes: both endpoints EM-active. -/
def emTensorActive : List (BoundaryMode × BoundaryMode) :=
  tensorModes.filter (fun (m₁, m₂) => emActiveStructural m₁ && emActiveStructural m₂)

/-- EM-silent tensor modes: at least one endpoint silent. -/
def emTensorSilent : List (BoundaryMode × BoundaryMode) :=
  tensorModes.filter (fun (m₁, m₂) => !(emActiveStructural m₁ && emActiveStructural m₂))

-- ============================================================
-- TENSOR DENSITY THEOREM [IV.T133]
-- ============================================================

/-- [IV.T133] Total tensor-square modes = 225 = 15². -/
theorem em_tensor_total : tensorModes.length = 225 := by native_decide

/-- [IV.T133] EM-active tensor modes = 121 = 11². -/
theorem em_tensor_active_count : emTensorActive.length = 121 := by native_decide

/-- Silent tensor modes = 104. -/
theorem em_tensor_silent_count : emTensorSilent.length = 104 := by native_decide

/-- Active + silent = total (consistency). -/
theorem tensor_partition :
    emTensorActive.length + emTensorSilent.length = tensorModes.length := by native_decide

-- ============================================================
-- SQUARE STRUCTURE [IV.P179]
-- ============================================================

/-- 121 = 11² and 225 = 15²: the tensor density IS a perfect square ratio. -/
theorem density_is_square : 121 = 11 * 11 ∧ 225 = 15 * (15 : Nat) := by omega

/-- The density 121/225 = (11/15)². Cross-multiplied form. -/
theorem density_equals_square :
    (121 : Nat) * 15 * 15 = 11 * 11 * 225 := by omega

/-- [IV.P179] Tensor square contains the sieve × correction factorization.
    (8/15)·(121/120) = 121/225.
    Cross-multiplied: 8 · 121 · 225 = 15 · 121 · 120. -/
theorem tensor_equals_sieve_times_correction :
    8 * 121 * 225 = 15 * (121 : Nat) * 120 := by omega

/-- The correction 121/120 is recovered from the tensor density and sieve.
    (121/225) / (8/15) = 121/120.  Cross-multiplied (clearing denominators): -/
theorem correction_cross_mult :
    (121 : Nat) * 15 * 120 = 8 * 225 * 121 := by omega

-- ============================================================
-- SMOKE TESTS
-- ============================================================

#eval tensorModes.length       -- 225
#eval emTensorActive.length    -- 121
#eval emTensorSilent.length    -- 104

end Tau.BookIV.Sectors.SpectralPage
