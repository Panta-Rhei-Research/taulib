import TauLib.BookI.Boundary.Iota

/-!
# TauLib.BookIV.Calibration.SIReference

SI physical constants as exact scaled Nat pairs — the calibration targets
against which τ-derived values are compared.

## Registry Cross-References

- [IV.D26] SI Reference Table — `SIConstant`, `si_exact_constants`
- [IV.D27] SI Measured Constants — `si_measured_constants`

## Mathematical Content

### SI Exact Defining Constants (2019 revision)

Since the 2019 SI redefinition, seven constants have exact numerical values:
c, h, e, k_B, N_A, Δν_Cs, K_cd. We store the four structurally relevant ones
(Tiers I and II in the τ-classification) as exact Nat pairs.

### SI Measured Constants (CODATA 2022)

Key measured values that the τ-framework must reproduce:
- Neutron mass m_n (the calibration anchor)
- Electron mass m_e (derived via mass ratio R)
- Proton mass m_p (derived via weak polarization)
- Fine-structure constant α (spectral + holonomy routes)
- Weinberg angle sin²θ_W (weak-gravity coupling)
- Strong coupling α_s(M_Z) (confinement coupling)
- Mass ratio R = m_n/m_e
- Gravitational constant G (frontier, Book V)

All values stored as (numer, denom) Nat pairs with positive denominators.
Float display is available via `.toFloat` for smoke tests only.

## Ground Truth Sources
- CODATA 2022 recommended values (NIST)
- Book IV Part II ch12 (Calibration Anchor), ch13 (Dimensional Bridge)
-/

namespace Tau.BookIV.Calibration

-- ============================================================
-- SI CONSTANT STRUCTURE [IV.D26]
-- ============================================================

/-- [IV.D26] An SI physical constant stored as an exact scaled rational.
    The actual SI value is `numer / denom` in the appropriate SI unit.
    `is_exact = true` for constants that are exact by SI 2019 definition. -/
structure SIConstant where
  /-- Display name of the constant. -/
  name : String
  /-- Scaled numerator. -/
  numer : Nat
  /-- Scale denominator. -/
  denom : Nat
  /-- Denominator is positive. -/
  denom_pos : denom > 0
  /-- True if the value is exact by SI definition (not measured). -/
  is_exact : Bool
  deriving Repr

/-- Float display for SI constant (smoke tests only). -/
def SIConstant.toFloat (c : SIConstant) : Float :=
  Float.ofNat c.numer / Float.ofNat c.denom

-- ============================================================
-- SI EXACT DEFINING CONSTANTS (2019 REVISION) [IV.D26]
-- ============================================================

/-- Speed of light: c = 299 792 458 m/s (EXACT).
    Tier I structural constant: base–fiber conversion factor.
    Stored as 299792458 / 1. -/
def si_speed_of_light : SIConstant where
  name := "Speed of light c"
  numer := 299792458        -- m/s
  denom := 1
  denom_pos := by omega
  is_exact := true

/-- Planck constant: h = 6.626 070 15 × 10⁻³⁴ J·s (EXACT).
    Tier I structural constant: minimal action quantum.
    Stored as 662607015 / 10⁴² (numer = h × 10⁴²). -/
def si_planck_constant : SIConstant where
  name := "Planck constant h"
  numer := 662607015
  denom := 1000000000000000000000000000000000000000000  -- 10⁴²
  denom_pos := by omega
  is_exact := true

/-- Elementary charge: e = 1.602 176 634 × 10⁻¹⁹ C (EXACT).
    Tier II physical constant: EM sector charge quantum.
    Stored as 1602176634 / 10²⁸ (numer = e × 10²⁸). -/
def si_elementary_charge : SIConstant where
  name := "Elementary charge e"
  numer := 1602176634
  denom := 10000000000000000000000000000  -- 10²⁸
  denom_pos := by omega
  is_exact := true

/-- Boltzmann constant: k_B = 1.380 649 × 10⁻²³ J/K (EXACT).
    Tier II physical constant: entropy–energy bridge.
    Stored as 1380649 / 10²⁹ (numer = k_B × 10²⁹). -/
def si_boltzmann : SIConstant where
  name := "Boltzmann constant k_B"
  numer := 1380649
  denom := 100000000000000000000000000000  -- 10²⁹
  denom_pos := by omega
  is_exact := true

/-- Avogadro constant: N_A = 6.022 140 76 × 10²³ mol⁻¹ (EXACT).
    Tier III conventional constant: counting scale.
    Stored as 602214076 / 100 (numer/100 = N_A / 10²¹). -/
def si_avogadro : SIConstant where
  name := "Avogadro constant N_A"
  numer := 602214076
  denom := 100             -- value = 6.02214076 × 10⁶ (×10²¹ to get N_A)
  denom_pos := by omega
  is_exact := true

/-- The 4 structurally relevant SI exact constants. -/
def si_exact_constants : List SIConstant :=
  [si_speed_of_light, si_planck_constant, si_elementary_charge, si_boltzmann]

-- ============================================================
-- SI MEASURED CONSTANTS (CODATA 2022) [IV.D27]
-- ============================================================

/-- [IV.D27] Neutron mass: m_n = 1.674 927 498 04(95) × 10⁻²⁷ kg.
    THE calibration anchor — the single experimental input.
    Relative uncertainty: 5.7 × 10⁻¹⁰.
    Stored as 167492749804 / 10³⁸. -/
def si_neutron_mass : SIConstant where
  name := "Neutron mass m_n"
  numer := 167492749804
  denom := 100000000000000000000000000000000000000  -- 10³⁸
  denom_pos := by omega
  is_exact := false

/-- Electron mass: m_e = 9.109 383 7015(28) × 10⁻³¹ kg.
    Derived via R = m_n/m_e in the τ-framework.
    Stored as 91093837015 / 10⁴¹. -/
def si_electron_mass : SIConstant where
  name := "Electron mass m_e"
  numer := 91093837015
  denom := 100000000000000000000000000000000000000000  -- 10⁴¹
  denom_pos := by omega
  is_exact := false

/-- Proton mass: m_p = 1.672 621 923 69(51) × 10⁻²⁷ kg.
    Derived as neutron minus weak polarization δ_A.
    Stored as 167262192369 / 10³⁸. -/
def si_proton_mass : SIConstant where
  name := "Proton mass m_p"
  numer := 167262192369
  denom := 100000000000000000000000000000000000000  -- 10³⁸
  denom_pos := by omega
  is_exact := false

/-- Fine-structure constant inverse: 1/α = 137.035 999 084(21).
    τ-spectral approximation: (8/15)·ι_τ⁴ → 1/α ≈ 137.9.
    Stored as 137035999084 / 10⁹. -/
def si_alpha_inverse : SIConstant where
  name := "Fine-structure inverse 1/α"
  numer := 137035999084
  denom := 1000000000  -- 10⁹
  denom_pos := by omega
  is_exact := false

/-- Weinberg angle: sin²θ_W = 0.23121(4) (on-shell, CODATA 2022).
    τ-candidate: κ(A,D) = ι_τ(1−ι_τ) ≈ 0.2249.
    Stored as 23121 / 100000. -/
def si_weinberg_sin2 : SIConstant where
  name := "Weinberg angle sin²θ_W"
  numer := 23121
  denom := 100000
  denom_pos := by omega
  is_exact := false

/-- Strong coupling: α_s(M_Z) = 0.1180(9).
    τ-candidate: 2·κ(C) = 2·ι_τ³/(1−ι_τ) ≈ 0.1208.
    Stored as 1180 / 10000. -/
def si_strong_coupling : SIConstant where
  name := "Strong coupling α_s(M_Z)"
  numer := 1180
  denom := 10000
  denom_pos := by omega
  is_exact := false

/-- Neutron-to-electron mass ratio: R = m_n/m_e = 1838.683 661 73(89).
    Dimensionless — determined by ι_τ via depth ordering in the τ-framework.
    Stored as 183868366173 / 10⁸. -/
def si_mass_ratio : SIConstant where
  name := "Mass ratio R = m_n/m_e"
  numer := 183868366173
  denom := 100000000  -- 10⁸
  denom_pos := by omega
  is_exact := false

/-- Neutron–proton mass difference: Δm = 1.293 332 36(46) MeV/c².
    In kg: 2.305 574 35 × 10⁻³⁰ kg.
    Stored as MeV value: 129333236 / 10⁸. -/
def si_np_mass_diff : SIConstant where
  name := "n-p mass difference (MeV)"
  numer := 129333236
  denom := 100000000  -- 10⁸
  denom_pos := by omega
  is_exact := false

/-- Gravitational constant: G = 6.674 30(15) × 10⁻¹¹ m³/(kg·s²).
    The least precisely known fundamental constant (~22 ppm).
    Frontier: requires D-sector base geometry (Book V).
    Stored as 667430 / 10¹⁶. -/
def si_gravitational : SIConstant where
  name := "Gravitational constant G"
  numer := 667430
  denom := 10000000000000000  -- 10¹⁶
  denom_pos := by omega
  is_exact := false

/-- All SI measured constants used for calibration comparison. -/
def si_measured_constants : List SIConstant :=
  [si_neutron_mass, si_electron_mass, si_proton_mass,
   si_alpha_inverse, si_weinberg_sin2, si_strong_coupling,
   si_mass_ratio, si_np_mass_diff, si_gravitational]

-- ============================================================
-- RELATIONAL UNIT VALUES (from Springer Nature paper)
-- ============================================================

/-- τ length scale: L = (π/2)·r_n ≈ 1.32 × 10⁻¹⁵ m.
    From the paper's measured neutron charge radius r_n ≈ 0.84 fm.
    In the τ-framework: determined by torus shape ratio r/R = ι_τ.
    Stored as 132 / 10¹⁷. -/
def si_tau_length : SIConstant where
  name := "τ length scale L"
  numer := 132
  denom := 100000000000000000  -- 10¹⁷
  denom_pos := by omega
  is_exact := false

/-- τ frequency scale: H = R·f_e ≈ 2.2714 × 10²³ Hz.
    Neutron de Broglie frequency.
    In the τ-framework: determined once R and c, h are fixed.
    Stored as 22714 / 10⁻¹⁹ → actually: 22714 × 10¹⁹.
    Better encoding: H_numer = 22714, H_scale = 10¹⁹ (multiply to get Hz). -/
def si_tau_frequency : SIConstant where
  name := "τ frequency scale H"
  numer := 22714           -- × 10¹⁹ Hz
  denom := 10              -- so numer/denom = 2271.4, multiply by 10²⁰ for Hz
  denom_pos := by omega    -- We use a convention: value_Hz = numer/denom × 10²⁰
  is_exact := false

-- ============================================================
-- STRUCTURAL VERIFICATIONS
-- ============================================================

/-- All SI exact constants are flagged as exact. -/
theorem exact_constants_are_exact :
    (si_exact_constants.map SIConstant.is_exact).all (· == true) = true := by
  simp [si_exact_constants, si_speed_of_light, si_planck_constant,
        si_elementary_charge, si_boltzmann]

/-- Exactly 4 exact constants in our reference table. -/
theorem exact_count : si_exact_constants.length = 4 := by rfl

/-- Exactly 9 measured constants in our reference table. -/
theorem measured_count : si_measured_constants.length = 9 := by rfl

/-- No measured constant is flagged as exact. -/
theorem measured_not_exact :
    (si_measured_constants.map SIConstant.is_exact).all (· == false) = true := by
  simp [si_measured_constants, si_neutron_mass, si_electron_mass, si_proton_mass,
        si_alpha_inverse, si_weinberg_sin2, si_strong_coupling,
        si_mass_ratio, si_np_mass_diff, si_gravitational]

/-- Speed of light is exact integer: c = 299792458. -/
theorem c_exact_integer : si_speed_of_light.denom = 1 := by rfl

/-- The neutron mass is the heaviest measured particle mass.
    m_n > m_p (neutron heavier than proton). -/
theorem neutron_heavier_than_proton :
    si_neutron_mass.numer * si_proton_mass.denom >
    si_proton_mass.numer * si_neutron_mass.denom := by
  simp [si_neutron_mass, si_proton_mass]

/-- The mass ratio R > 1838 (neutron is ~1839× heavier than electron). -/
theorem mass_ratio_gt_1838 :
    si_mass_ratio.numer > 1838 * si_mass_ratio.denom := by
  simp [si_mass_ratio]

/-- The mass ratio R < 1840 (neutron is less than 1840× the electron). -/
theorem mass_ratio_lt_1840 :
    si_mass_ratio.numer < 1840 * si_mass_ratio.denom := by
  simp [si_mass_ratio]

/-- α⁻¹ is between 137 and 138 (brackets experimental value). -/
theorem alpha_inverse_in_range :
    si_alpha_inverse.numer > 137 * si_alpha_inverse.denom ∧
    si_alpha_inverse.numer < 138 * si_alpha_inverse.denom := by
  simp [si_alpha_inverse]

-- ============================================================
-- SMOKE TESTS
-- ============================================================

-- SI exact constants
#eval si_speed_of_light.toFloat        -- 299792458.0 (m/s)
#eval si_planck_constant.toFloat       -- ~6.626e-34 (J·s)
#eval si_elementary_charge.toFloat     -- ~1.602e-19 (C)
#eval si_boltzmann.toFloat             -- ~1.381e-23 (J/K)

-- SI measured constants
#eval si_neutron_mass.toFloat          -- ~1.675e-27 (kg)
#eval si_electron_mass.toFloat         -- ~9.109e-31 (kg)
#eval si_proton_mass.toFloat           -- ~1.673e-27 (kg)
#eval si_alpha_inverse.toFloat         -- ~137.036
#eval si_weinberg_sin2.toFloat         -- ~0.23121
#eval si_strong_coupling.toFloat       -- 0.118
#eval si_mass_ratio.toFloat            -- ~1838.68
#eval si_np_mass_diff.toFloat          -- ~1.293 (MeV)
#eval si_gravitational.toFloat         -- ~6.674e-11

-- Relational unit values
#eval si_tau_length.toFloat            -- ~1.32e-15 (m)
#eval si_tau_frequency.toFloat         -- ~2271.4 (×10²⁰ Hz)

-- Counts
#eval si_exact_constants.length        -- 4
#eval si_measured_constants.length     -- 9

end Tau.BookIV.Calibration
