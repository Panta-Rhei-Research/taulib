import TauLib.BookIV.Sectors.CouplingFormulas
import TauLib.BookIV.Calibration.SIReference

/-!
# TauLib.BookIV.Calibration.DimensionlessCouplings

The 5 self-couplings + 1 cross-coupling from Chapter 10, with their numerical
values presented as the Dimensionless Cascade.

## Registry Cross-References

- [IV.R247] Origin of the No Knobs Principle — (structural remark)
- [IV.D275] Gravitational self-coupling — `grav_self_coupling`
- [IV.P160] Numerical value κ(D) — `grav_coupling_value`
- [IV.D276] Weak self-coupling — `weak_self_coupling`
- [IV.P161] Numerical value κ(A) — `weak_coupling_value`
- [IV.D277] EM self-coupling — `em_self_coupling`
- [IV.P162] Numerical value κ(B) — `em_coupling_value`
- [IV.D278] Strong self-coupling — `strong_self_coupling`
- [IV.P163] Numerical value κ(C) — `strong_coupling_value`
- [IV.R248] Lean verification — (structural remark)
- [IV.D279] Omega self-coupling — `omega_self_coupling`
- [IV.P164] Numerical value κ(ω) — `omega_coupling_value`
- [IV.D280] Weak-gravity cross-coupling — `weak_grav_cross`

## Ground Truth Sources
- Chapter 10 of Book IV (2nd Edition), first half
-/

namespace Tau.BookIV.Calibration

open Tau.Boundary Tau.BookIV.Sectors

-- ============================================================
-- GRAVITATIONAL SELF-COUPLING [IV.D275]
-- ============================================================

/-- [IV.D275] Gravitational self-coupling κ(D;1) = 1 − ι_τ ≈ 0.658541.
    Depth 1, χ₊-dominant. The largest primitive coupling. -/
abbrev grav_self_coupling := kappa_DD

/-- [IV.P160] Numerical value: κ(D;1) is in (658, 659)/1000. -/
theorem grav_coupling_value :
    grav_self_coupling.numer * 1000 > 658 * grav_self_coupling.denom ∧
    grav_self_coupling.numer * 1000 < 659 * grav_self_coupling.denom := by
  constructor <;> native_decide

-- ============================================================
-- WEAK SELF-COUPLING [IV.D276]
-- ============================================================

/-- [IV.D276] Weak self-coupling κ(A;1) = ι_τ ≈ 0.341304.
    Depth 1, balanced polarity. Equals the master constant. -/
abbrev weak_self_coupling := kappa_AA

/-- [IV.P161] Numerical value: κ(A;1) is in (341, 342)/1000. -/
theorem weak_coupling_value :
    weak_self_coupling.numer * 1000 > 341 * weak_self_coupling.denom ∧
    weak_self_coupling.numer * 1000 < 342 * weak_self_coupling.denom := by
  constructor <;> native_decide

-- ============================================================
-- EM SELF-COUPLING [IV.D277]
-- ============================================================

/-- [IV.D277] Electromagnetic self-coupling κ(B;2) = ι_τ² ≈ 0.116594.
    Depth 2, χ₊-dominant. -/
abbrev em_self_coupling := kappa_BB

/-- [IV.P162] Numerical value: κ(B;2) is in (116, 117)/1000. -/
theorem em_coupling_value :
    em_self_coupling.numer * 1000 > 116 * em_self_coupling.denom ∧
    em_self_coupling.numer * 1000 < 117 * em_self_coupling.denom := by
  constructor <;> native_decide

-- ============================================================
-- STRONG SELF-COUPLING [IV.D278]
-- ============================================================

/-- [IV.D278] Strong self-coupling κ(C;3) = ι_τ³/(1−ι_τ) ≈ 0.06046.
    Depth 3, χ₋-dominant. Confinement coupling. -/
abbrev strong_self_coupling := kappa_CC

/-- [IV.P163] Numerical value: κ(C;3) is in (60, 61)/1000. -/
theorem strong_coupling_value :
    strong_self_coupling.numer * 1000 > 60 * strong_self_coupling.denom ∧
    strong_self_coupling.numer * 1000 < 61 * strong_self_coupling.denom := by
  constructor <;> native_decide

-- ============================================================
-- OMEGA SELF-COUPLING [IV.D279]
-- ============================================================

/-- [IV.D279] Omega self-coupling κ(ω) = ι_τ³/(1+ι_τ) ≈ 0.02968.
    Crossing-point readout. The smallest primitive coupling. -/
abbrev omega_self_coupling := kappa_BC

/-- [IV.P164] Numerical value: κ(ω) is in (29, 30)/1000. -/
theorem omega_coupling_value :
    omega_self_coupling.numer * 1000 > 29 * omega_self_coupling.denom ∧
    omega_self_coupling.numer * 1000 < 30 * omega_self_coupling.denom := by
  constructor <;> native_decide

-- [IV.R247] The No Knobs Principle (III.T42) was proved in Book III
-- as a structural consequence of the enrichment ladder.
-- (Structural remark)

-- [IV.R248] The strict ordering κ_D > κ_A > κ_B > κ_C > κ_ω is
-- verified in TauLib.BookIV.Sectors.CouplingFormulas.
-- (Structural remark)

-- ============================================================
-- WEAK-GRAVITY CROSS-COUPLING [IV.D280]
-- ============================================================

/-- [IV.D280] Weak-gravity cross-coupling κ(A,D) = ι_τ(1−ι_τ) ≈ 0.2249.
    Both sectors on base τ¹. Near sin²θ_W = 0.2312. -/
abbrev weak_grav_cross := kappa_AD

-- ============================================================
-- SMOKE TESTS
-- ============================================================

#eval grav_self_coupling.toFloat    -- ≈ 0.6585
#eval weak_self_coupling.toFloat    -- ≈ 0.3415
#eval em_self_coupling.toFloat      -- ≈ 0.1166
#eval strong_self_coupling.toFloat  -- ≈ 0.0605
#eval omega_self_coupling.toFloat   -- ≈ 0.0297
#eval weak_grav_cross.toFloat       -- ≈ 0.2249

end Tau.BookIV.Calibration
