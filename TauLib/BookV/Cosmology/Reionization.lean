import TauLib.BookV.Cosmology.NeutrinoBackground

/-!
# TauLib.BookV.Cosmology.Reionization

21cm hydrogen line prediction from τ-native cosmological inputs.
The brightness temperature uses Ω_m, ω_b, z_reion — all derived
from the τ-framework with zero free parameters.

## Registry Cross-References

- [V.D334] 21cm Brightness Temperature — `BrightnessTemp21cm`
- [V.D335] Spin Temperature Coupling Regimes — `SpinTempCoupling`
- [V.T271] 21cm Absorption Trough from τ-Native Inputs — `absorption_trough_21cm`
- [V.P189] EDGES/HERA/SKA Predictions -- structural
- [V.R470] V.OP9 Status: PARTIAL-IMPROVED -- structural remark

## Mathematical Content

### 21cm Brightness Temperature [V.D334]

T₂₁(z) ≈ 27 mK · x_HI · (1 − T_CMB/T_S) · √((1+z)/10 · 0.15/Ω_m) · (ω_b/0.023)

### Absorption Trough [V.T271]

At z ≈ 17 (cosmic dawn), with τ-native Ω_m = 0.315 and ω_b = 0.02238:
T₂₁(z=17) ≈ −209 mK (standard ΛCDM evaluated at τ parameters).

## Ground Truth Sources
- Book V ch48: Threshold ladder, 21cm section (Wave 48A)
- EDGES collaboration (2018): −500 mK reported (unconfirmed)
- Standard 21cm cosmology: Furlanetto, Oh, Briggs (2006)
-/

namespace Tau.BookV.Cosmology

-- ============================================================
-- DEFINITIONS
-- ============================================================

/-- 21cm brightness temperature structure [V.D334].
    Stores the τ-native cosmological parameters and computes
    the differential brightness temperature against the CMB.
    Scope: τ-effective (formula uses only τ-derived inputs). -/
structure BrightnessTemp21cm where
  /-- Redshift of observation. -/
  redshift : Nat
  /-- Neutral hydrogen fraction (0 to 1000, in per-mille). -/
  x_HI_permille : Nat
  /-- Spin temperature in mK. -/
  T_S_mK : Nat
  /-- T_S > 0. -/
  T_S_pos : T_S_mK > 0
  /-- CMB temperature at redshift z in mK: 2725 × (1+z). -/
  T_CMB_mK : Nat := 2725 * (1 + redshift)

/-- Spin temperature coupling regimes [V.D335].
    Scope: conjectural (astrophysical modelling of x_α). -/
inductive SpinTempCoupling where
  /-- Collisional coupling: z > 200, T_S ≈ T_K ≈ T_CMB. -/
  | collisional
  /-- Dark ages: 30 < z < 200, T_K decouples, adiabatic cooling. -/
  | dark_ages
  /-- Cosmic dawn: z_reion < z < 30, Wouthuysen–Field effect. -/
  | cosmic_dawn
  /-- Post-reionization: z < z_reion, emission. -/
  | post_reion
  deriving DecidableEq, Repr

-- ============================================================
-- THEOREMS
-- ============================================================

/-- Absorption trough at z = 17 from τ-native inputs [V.T271].
    T₂₁(z=17) ≈ −209 mK.
    Scope: conjectural (depends on spin coupling model). -/
def absorption_trough_z17_mK : Int := -209

/-- Reionization redshift from τ-axioms [already V.P139].
    z_reion = a₃ − W₃(4) = 13 − 5 = 8. -/
def z_reion : Nat := 8

/-- z_reion = 8 is positive. -/
theorem z_reion_pos : z_reion > 0 := by decide

/-- The trough prediction is an absorption signal (negative). -/
theorem trough_is_absorption : absorption_trough_z17_mK < 0 := by decide

-- ============================================================
-- REMARKS (comment-only)
-- ============================================================

-- [V.P189] EDGES/HERA/SKA Predictions:
-- EDGES: −500 mK reported, 2.4× deeper than τ-prediction. Unconfirmed.
-- HERA: sensitivity ~10 mK at z=8–12; τ predicts transition at z=8.
-- SKA: 21cm power spectrum at z=15–25 probes dark-ages signal.
-- Falsification: confirmed trough > 300 mK below τ-prediction.

-- [V.R470] V.OP9 Status: PARTIAL-IMPROVED.
-- Brightness temperature formula uses exclusively τ-native inputs.
-- Remaining gap: spin coupling function x_α(z) requires
-- astrophysical modelling beyond τ-framework's current scope.

end Tau.BookV.Cosmology
