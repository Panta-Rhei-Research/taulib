import TauLib.BookIV.Particles.BetaDecay
import TauLib.BookIV.Calibration.CalibrationAnchor
import TauLib.BookIV.Calibration.SharedOntology
import TauLib.BookIV.Calibration.SIReference
import TauLib.BookIV.Sectors.FineStructure
import TauLib.BookIV.Electroweak.EWSynthesis
import TauLib.BookIV.Electroweak.AlphaDerivation
import TauLib.BookIV.Particles.ThreeGenerations

open Tau.BookIV.Particles Tau.BookIV.Calibration
open Tau.BookIV.Sectors Tau.BookIV.Electroweak

/-!
# Guided Tour Companion: Book IV — The Self-Describing Universe

**Companion to**: `launch/guided-tours/guided-tour-book-IV.pdf`

This Lean module walks through the 7 structural hinges of Book IV —
the volume where Category τ crosses into physics. Every prediction
is derived from ι_τ = 2/(π + e) with zero free parameters.

**What Lean proves in this tour:** arithmetic inequalities, data-type
definitions, and data-consistency checks against the Physics-Ledger data
file. The `#check` and `#eval` outputs verify that named constants and
structures inhabit their declared types and that computed values match the
stated numerics.

**What Lean does NOT prove:** that the `τ-effective` formulas match
physical reality, that three winding classes ARE three fermion generations,
or that the α/m_e/G predictions hold to the stated ppm precision in
experiment. The agreement with CODATA and PDG values is presented as an
honest forward falsifier; the physical identification is defended in the
Book IV monograph (relevant chapters). Readers following `#check` outputs
will see theorems about `ℝ`/`Nat` arithmetic and typed data records; the
physical interpretation is monograph content, not Lean-certified.

**Scope key:** `τ-effective` = formula is self-consistent and computes the
stated value. `monograph-level` = physical identification defended in text.
-/

-- ================================================================
-- HINGE 1: Neutron Primacy [IV.D14–D18]
-- ================================================================

/-
The neutron is the first stable ontic particle in τ³.
All other particles are derived from neutron reconfiguration.
-/

#check NeutronParent
#check neutron_as_parent


-- ================================================================
-- HINGE 2: Beta-Decay Rosetta Stone [IV.T3–T4]
-- ================================================================

/-
n → p + e⁻ + ν̄ₑ. All five sectors visible in one process.
The single process that decodes the Standard Model.
-/

#check BetaDecayQValue
#check beta_decay_q_value


-- ================================================================
-- HINGE 3: Calibration Anchor [IV.D19–D25]
-- ================================================================

/-
m_n = ONE measurement. All other scales follow from m_n + ι_τ.
Build before calibrate: physics first, units last.
-/

#check CalibrationAnchor
#check calibration_map
#check neutron_anchor


-- ================================================================
-- HINGE 4: Fine-Structure Constant [IV.T5–T8]
-- ================================================================

/-
α = (121/225) · ι_τ⁴ ≈ 0.007297. Agreement: 9.8 ppm.
11/15 = EM-active fraction of 15 boundary modes. Not fitted.
-/

#check alpha_tau
#check alpha_tau_float
#check holonomy_formula_exact

-- The headline: SM needs 19 parameters, τ needs 0
#check ew_prediction_table
#check zero_vs_nineteen
#eval zero_vs_nineteen.tau_params   -- 0
#eval zero_vs_nineteen.sm_params    -- 19


-- ================================================================
-- HINGE 5: Electron Mass Prediction
-- ================================================================

/-
R₀ = ι_τ⁻⁷ − √3 · ι_τ⁻² ≈ 1838.7
CODATA: m_n/m_e = 1838.684...
Agreement: 7.7 ppm (leading), 0.025 ppm (with holonomy).
-/

#check si_electron_mass


-- ================================================================
-- HINGE 6: Three Generations [IV.T10–T11]
-- ================================================================

/-
The Lean formalization of `exactly_three_generations` proves
`π₁(τ³) ≅ ℤ³`, which implies a 3-winding-class decomposition.
The identification of these three winding classes with the three
fermion generations (electron/muon/tau families) is monograph-level:
it is defended in Book IV (IV.T10–T11) but is not itself a Lean theorem.
The `τ-effective` content here is the topological count of three; the
physical labeling is separate.
-/

#check exactly_three_generations
#eval exactly_three_generations.count  -- 3


-- ================================================================
-- HINGE 7: Self-Description Completion [IV.T12–T14]
-- ================================================================

/-
The derivation chain: τ³ → CR → QM → n → β⁻ → {p,e,ν} → Forces → Constants.
ONE dimensional parameter (m_n). ZERO free dimensionless constants.
-/

-- 9 electroweak predictions, 0 free parameters
#eval ew_prediction_table.length  -- 9


-- ================================================================
-- VERIFICATION SUMMARY
-- ================================================================

/-
All 7 hinges of Book IV are machine-checked:

  H1: NeutronParent, neutron_as_parent                ✓ (Primacy)
  H2: BetaDecayQValue, beta_decay_q_value             ✓ (Rosetta)
  H3: CalibrationAnchor, calibration_map               ✓ (Anchor)
  H4: alpha_tau, zero_vs_nineteen (0 vs 19 params)     ✓ (Alpha)
  H5: si_electron_mass                                 ✓ (Mass ratio)
  H6: exactly_three_generations (count = 3)             ✓ (Topology)
  H7: ew_prediction_table (9 predictions, 0 params)    ✓ (Completion)

Zero sorry. Zero free parameters. The arithmetic and structural identities
compile. Physical identification with SM predictions is monograph-level
and is defended in Book IV; the Lean content is the arithmetic and
data-consistency layer.
-/
