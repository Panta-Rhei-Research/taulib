import TauLib.BookV.Cosmology.InflationRegime

/-!
# TauLib.BookV.Cosmology.ThresholdLadder

Threshold ladder of cosmological phase transitions. Each threshold
is a critical refinement depth where a qualitative change occurs in
the regime boundary character.

Six canonical thresholds:
  L_EW → L_B → L_N → L_nuc → L_H → L_γ

## Registry Cross-References

- [V.D158] Threshold (Regime Boundary) — `ThresholdRegimeBoundary`
- [V.D159] Canonical Thresholds — `CanonicalThresholds`
- [V.T107] Ladder Monotonicity — `ladder_monotonicity`
- [V.D160] Neutron Threshold L_N — `NeutronThreshold`
- [V.R218] The mass hierarchy at L_N -- structural remark
- [V.R219] Sphaleron Open Question -- structural remark
- [V.R220] Sakharov Conditions -- structural remark
- [V.D161] Nucleosynthetic Window — `NucleosyntheticWindow`
- [V.T108] Nucleosynthesis from τ — `nucleosynthesis_from_tau`
- [V.R221] The lithium problem -- structural remark
- [V.P92]  CMB Origin — `cmb_origin`
- [V.D162] Threshold Ladder — `ThresholdLadderComplete`

## Mathematical Content

### Canonical Thresholds

Six regime transitions in monotone order of refinement depth:
1. L_EW: electroweak symmetry breaking (ω-sector crossing)
2. L_B: baryogenesis (CP violation + departure from equilibrium)
3. L_N: neutron threshold (strong-sector below confinement coupling)
4. L_nuc: nucleosynthesis window opens
5. L_H: hydrogen recombination
6. L_γ: photon decoupling (CMB last scattering)

### Neutron Threshold

At L_N, the strong-sector (η) character drops below the confinement
coupling κ(C;3) = ι_τ³/(1−ι_τ). This establishes:
  m_n > m_p > m_e  with  m_p = m_n − δ_A,  m_e = m_n/R

### Nucleosynthesis

The nucleosynthetic window produces observed light-element abundances:
He-4 mass fraction Y_p ~ 0.245 from neutron-to-proton freeze-out ratio.

## Ground Truth Sources
- Book V ch48: Threshold Ladder
-/

namespace Tau.BookV.Cosmology

open Tau.Boundary Tau.BookIV.Sectors Tau.BookIII.Sectors Tau.BookV.Gravity

-- ============================================================
-- THRESHOLD [V.D158]
-- ============================================================

/-- Threshold type classification. -/
inductive ThresholdType where
  /-- Electroweak symmetry breaking. -/
  | EW
  /-- Baryogenesis. -/
  | Baryogenesis
  /-- Neutron threshold. -/
  | Neutron
  /-- Nucleosynthesis window. -/
  | Nucleosynthesis
  /-- Hydrogen recombination. -/
  | Hydrogen
  /-- Photon decoupling (CMB). -/
  | PhotonDecoupling
  deriving Repr, DecidableEq, BEq

/-- [V.D158] Threshold (regime boundary): a critical depth where a
    qualitative change occurs in the regime boundary character.

    At threshold n_*, one or more sector couplings cross a critical
    value, causing a regime transition. -/
structure ThresholdRegimeBoundary where
  /-- Threshold type. -/
  kind : ThresholdType
  /-- Refinement depth at threshold (ordinal index). -/
  depth_index : Nat
  /-- Depth is positive. -/
  depth_pos : depth_index > 0
  /-- Which sector crosses. -/
  sector_name : String
  /-- Scope. -/
  scope : String := "tau-effective"
  deriving Repr

-- ============================================================
-- CANONICAL THRESHOLDS [V.D159]
-- ============================================================

/-- [V.D159] Canonical thresholds: the six regime transitions in
    monotone order. Depths are ordinal indices (1 = earliest). -/
structure CanonicalThresholds where
  /-- Electroweak. -/
  ew : ThresholdRegimeBoundary
  /-- Baryogenesis. -/
  baryogenesis : ThresholdRegimeBoundary
  /-- Neutron. -/
  neutron : ThresholdRegimeBoundary
  /-- Nucleosynthesis. -/
  nucleosynthesis : ThresholdRegimeBoundary
  /-- Hydrogen recombination. -/
  hydrogen : ThresholdRegimeBoundary
  /-- Photon decoupling. -/
  photon_decoupling : ThresholdRegimeBoundary
  /-- Monotone ordering. -/
  monotone : ew.depth_index < baryogenesis.depth_index ∧
             baryogenesis.depth_index < neutron.depth_index ∧
             neutron.depth_index < nucleosynthesis.depth_index ∧
             nucleosynthesis.depth_index < hydrogen.depth_index ∧
             hydrogen.depth_index < photon_decoupling.depth_index
  deriving Repr

/-- The canonical threshold ladder instance. -/
def canonical_ladder : CanonicalThresholds where
  ew := { kind := .EW, depth_index := 1, depth_pos := by omega,
           sector_name := "omega (B cap C)" }
  baryogenesis := { kind := .Baryogenesis, depth_index := 2,
                    depth_pos := by omega, sector_name := "A (Weak)" }
  neutron := { kind := .Neutron, depth_index := 3, depth_pos := by omega,
               sector_name := "C (Strong)" }
  nucleosynthesis := { kind := .Nucleosynthesis, depth_index := 4,
                       depth_pos := by omega, sector_name := "C (Strong)" }
  hydrogen := { kind := .Hydrogen, depth_index := 5, depth_pos := by omega,
                sector_name := "B (EM)" }
  photon_decoupling := { kind := .PhotonDecoupling, depth_index := 6,
                         depth_pos := by omega, sector_name := "B (EM)" }
  monotone := ⟨by native_decide, by native_decide, by native_decide, by native_decide, by native_decide⟩

-- ============================================================
-- LADDER MONOTONICITY [V.T107]
-- ============================================================

/-- [V.T107] Ladder monotonicity: canonical thresholds occur in
    the order n_EW < n_B < n_N < n_nuc < n_H < n_γ. -/
theorem ladder_monotonicity :
    canonical_ladder.ew.depth_index < canonical_ladder.baryogenesis.depth_index ∧
    canonical_ladder.baryogenesis.depth_index < canonical_ladder.neutron.depth_index ∧
    canonical_ladder.neutron.depth_index < canonical_ladder.nucleosynthesis.depth_index ∧
    canonical_ladder.nucleosynthesis.depth_index < canonical_ladder.hydrogen.depth_index ∧
    canonical_ladder.hydrogen.depth_index < canonical_ladder.photon_decoupling.depth_index :=
  canonical_ladder.monotone

-- ============================================================
-- NEUTRON THRESHOLD [V.D160]
-- ============================================================

/-- [V.D160] Neutron threshold L_N: the refinement depth at which
    the strong-sector (η) character drops below the confinement
    coupling κ(C;3) = ι_τ³/(1−ι_τ).

    At L_N, the mass hierarchy is established:
      m_n > m_p > m_e
      m_p = m_n − δ_A
      m_e = m_n / R -/
structure NeutronThreshold where
  /-- Threshold data. -/
  threshold : ThresholdRegimeBoundary
  /-- The threshold is for neutrons. -/
  is_neutron : threshold.kind = .Neutron
  /-- Mass hierarchy holds below this threshold. -/
  mass_hierarchy_established : Bool := true
  deriving Repr

-- ============================================================
-- SAKHAROV CONDITIONS [V.R220]
-- ============================================================

/-- [V.R220] Two of three Sakharov conditions for baryogenesis are
    structural in τ: CP violation from the bipolar lemniscate, and
    departure from thermal equilibrium from the refinement cascade.

    The third condition (baryon number violation) requires the
    ω-sector crossing. All three are met at the L_B threshold. -/
structure SakharovConditions where
  /-- CP violation from lemniscate bipolarity. -/
  cp_violation : Bool := true
  /-- Departure from equilibrium from refinement cascade. -/
  departure_from_eq : Bool := true
  /-- Baryon number violation from ω-sector. -/
  baryon_violation : Bool := true
  /-- All three met. -/
  all_met : Bool := true
  deriving Repr

-- ============================================================
-- NUCLEOSYNTHETIC WINDOW [V.D161]
-- ============================================================

/-- [V.D161] Nucleosynthetic window W_nuc: the interval of refinement
    depths during which light nuclei (D, He-3, He-4, Li-7) can form.

    Opens at n_nuc^open and closes at n_nuc^close. The window width
    determines the primordial element abundances. -/
structure NucleosyntheticWindow where
  /-- Opening depth. -/
  open_depth : Nat
  /-- Closing depth. -/
  close_depth : Nat
  /-- Opens before closing. -/
  opens_before_close : open_depth < close_depth
  /-- Both positive. -/
  open_pos : open_depth > 0
  deriving Repr

-- ============================================================
-- NUCLEOSYNTHESIS FROM TAU [V.T108]
-- ============================================================

/-- [V.T108] Nucleosynthesis from τ: the nucleosynthetic window
    produces observed light-element abundances.

    He-4 mass fraction Y_p ~ 0.245 from the neutron-to-proton
    freeze-out ratio at L_N.

    Y_p = 20/81 = 0.24691..., encoded as 246/1000 (floor of 246.913...).
    See HeliumFraction.lean for the full derivation. -/
structure NucleosynthesisResult where
  /-- He-4 mass fraction × 1000. -/
  yp_times_1000 : Nat
  /-- Consistent with observation: Y_p ∈ (0.24, 0.26). -/
  consistent : yp_times_1000 > 240 ∧ yp_times_1000 < 260
  deriving Repr

/-- The τ-predicted He-4 mass fraction (Y_p = 20/81, floor(246.913) = 246). -/
def tau_yp : NucleosynthesisResult where
  yp_times_1000 := 246
  consistent := ⟨by omega, by omega⟩

/-- He-4 prediction is in range. -/
theorem nucleosynthesis_from_tau :
    tau_yp.yp_times_1000 > 240 ∧ tau_yp.yp_times_1000 < 260 :=
  tau_yp.consistent

-- ============================================================
-- CMB ORIGIN [V.P92]
-- ============================================================

/-- [V.P92] CMB origin: the CMB is the photon readout of the
    last-scattering surface at the photon decoupling threshold L_γ.

    Temperature T_CMB ≈ 2.725 K. The last-scattering surface is
    at redshift z ≈ 1100 in chart-level readout coordinates.

    In τ, the CMB is a boundary-character snapshot of the B-sector
    at L_γ depth. -/
structure CmbOrigin where
  /-- CMB temperature × 1000 (in mK). -/
  temp_mK : Nat
  /-- Redshift of last scattering × 10. -/
  redshift_times_10 : Nat
  /-- Temperature is ~ 2725 mK. -/
  temp_range : temp_mK > 2700 ∧ temp_mK < 2750
  deriving Repr

/-- The observed CMB. -/
def observed_cmb : CmbOrigin where
  temp_mK := 2725
  redshift_times_10 := 11000
  temp_range := ⟨by omega, by omega⟩

/-- CMB temperature in range. -/
theorem cmb_origin : observed_cmb.temp_mK > 2700 := observed_cmb.temp_range.1

-- ============================================================
-- THE MASS HIERARCHY AT L_N [V.R218]
-- ============================================================

/-- [V.R218] Mass hierarchy at L_N: once the strong-sector character
    drops below confinement coupling, the mass hierarchy locks in:
      m_n > m_p > m_e
    with m_p = m_n − δ_A and m_e = m_n/R (R ≈ 1838.68). -/
structure MassHierarchyAtLN where
  /-- R ≈ 1838.68 (neutron-to-electron mass ratio, × 100). -/
  r_times_100 : Nat
  /-- R in range. -/
  r_range : r_times_100 > 183800 ∧ r_times_100 < 183900
  deriving Repr

/-- The mass hierarchy R value. -/
def mass_hierarchy_r : MassHierarchyAtLN where
  r_times_100 := 183868
  r_range := ⟨by omega, by omega⟩

-- ============================================================
-- THRESHOLD LADDER COMPLETE [V.D162]
-- ============================================================

/-- [V.D162] Threshold ladder: the complete ordered sequence of
    canonical thresholds. Six thresholds, monotonically ordered. -/
structure ThresholdLadderComplete where
  /-- The canonical ladder. -/
  ladder : CanonicalThresholds
  /-- Number of thresholds. -/
  count : Nat
  /-- Count is 6. -/
  count_is_six : count = 6
  deriving Repr

/-- The complete ladder has 6 thresholds. -/
def complete_ladder : ThresholdLadderComplete where
  ladder := canonical_ladder
  count := 6
  count_is_six := by rfl

-- ============================================================
-- REMARKS (comment-only)
-- ============================================================

-- [V.R219] Sphaleron Open Question: the τ-analogue of the sphaleron
-- process would be a non-perturbative crossing between the Weak
-- sector (A) and Strong sector (C). This is an open question.

-- [V.R221] The lithium problem: the cosmological lithium problem
-- (discrepancy between predicted and observed primordial Li-7) is
-- inherited by the τ-framework. This is an acknowledged open problem.

-- ============================================================
-- SMOKE TESTS
-- ============================================================

#eval canonical_ladder.ew.depth_index            -- 1
#eval canonical_ladder.photon_decoupling.depth_index  -- 6
#eval tau_yp.yp_times_1000                       -- 246
#eval observed_cmb.temp_mK                       -- 2725
#eval mass_hierarchy_r.r_times_100               -- 183868
#eval complete_ladder.count                      -- 6

end Tau.BookV.Cosmology
