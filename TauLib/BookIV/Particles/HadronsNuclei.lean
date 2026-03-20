import TauLib.BookIV.Particles.BetaDecay

/-!
# TauLib.BookIV.Particles.HadronsNuclei

Hadron structure (baryons, mesons), quark confinement in hadrons,
nucleon mass decomposition, nuclear binding from strong+EM balance,
nuclear shell model, magic numbers, iron peak, and decay channels
from sector admissibility.

## Registry Cross-References

- [IV.D200] Meson Classification — `MesonClassification`
- [IV.D201] Glueball — `GlueballDef`
- [IV.D202] Nuclear Force — `NuclearForce`
- [IV.P128] Nucleon Mass Decomposition — `nucleon_mass_decomposition`
- [IV.P129] Nuclear Force Saturation — `nuclear_force_saturation`
- [IV.P130] Nuclear Shell Structure — `nuclear_shell_structure`
- [IV.P131] Iron Peak from Competing Sectors — `iron_peak`
- [IV.P132] Decay Channels from Sector Admissibility — `decay_channels`
- [IV.R128] Eta-eta' Splitting — `eta_eta_prime` (conjectural)
- [IV.R129] Glueballs and the Mass Gap — `glueballs_mass_gap`
- [IV.R130] Mass from Nothing — comment-only (not_applicable)
- [IV.R131] Isospin Splitting from Polarity — `isospin_splitting`
- [IV.R132] Proton Lighter but Ontologically Later — comment-only (not_applicable)
- [IV.R133] Deuteron Binding in tau-language — `deuteron_binding`
- [IV.R134] Spin-orbit from omega-sector — comment-only (not_applicable)
- [IV.R135] Why He-4 is Tightly Bound — `helium4_tightly_bound`
- [IV.R136] Nucleosynthesis Forward to Book V — `nucleosynthesis_forward`
- [IV.R137] Alpha-decay as Mode Cluster Ejection — `alpha_decay_mode`
- [IV.R138] Neutron Stability inside Nuclei — `neutron_stability_nuclear`
- [IV.R139] Gamma-decay as Mode Transition — `gamma_decay_mode`

## Mathematical Content

Hadrons are color-neutral composites: mesons (qq̄, B = 0) and baryons
(qqq, B = 1). The nucleon mass is 99% vacuum + kinetic energy from
confinement, only 1% from quark rest masses. Nuclear binding comes from
residual C-sector interaction, with shell structure producing magic
numbers (2, 8, 20, 28, 50, 82, 126). The iron peak (A ≈ 56) results
from optimal C-sector binding vs B-sector Coulomb repulsion balance.

## Ground Truth Sources
- Chapter 48 of Book IV (2nd Edition)
-/

namespace Tau.BookIV.Particles

open Tau.Kernel Tau.Boundary Tau.BookIV.Sectors Tau.BookIII.Sectors

-- ============================================================
-- MESON CLASSIFICATION [IV.D200]
-- ============================================================

/-- Hadron baryon number. -/
inductive BaryonNumber where
  /-- Meson: B = 0 (quark-antiquark). -/
  | zero
  /-- Baryon: B = 1 (three quarks). -/
  | one
  deriving Repr, DecidableEq, BEq

/-- [IV.D200] A meson |q_i q̄_j⟩ classified by:
    1. Flavor content (quark flavors from {u,d,s,c,b,t})
    2. Spin-parity J^PC (angular momentum + spin)
    3. Generation class (lemniscate mode classes of constituents)

    Pseudoscalar (J=0): anti-aligned spins.
    Vector (J=1): aligned spins. -/
structure MesonClassification where
  /-- Name. -/
  name : String
  /-- Quark content. -/
  quark : String
  /-- Antiquark content. -/
  antiquark : String
  /-- Spin J. -/
  spin : Nat
  /-- Approximate mass (MeV). -/
  mass_mev : Nat
  deriving Repr

/-- Canonical mesons. -/
def pion_plus : MesonClassification where
  name := "pi+"; quark := "u"; antiquark := "d_bar"; spin := 0; mass_mev := 140

def kaon_plus : MesonClassification where
  name := "K+"; quark := "u"; antiquark := "s_bar"; spin := 0; mass_mev := 494

def rho_meson : MesonClassification where
  name := "rho"; quark := "u"; antiquark := "d_bar"; spin := 1; mass_mev := 775

-- ============================================================
-- ETA-ETA' SPLITTING [IV.R128] (conjectural)
-- ============================================================

/-- [IV.R128] The η-η' mass splitting (~410 MeV) exceeds quark mass
    predictions alone: the resolution is the axial anomaly breaking
    U(1)_A symmetry via quantum effects. Conjectural scope. -/
structure EtaEtaPrime where
  /-- Splitting in MeV. -/
  splitting_mev : Nat := 410
  /-- Mechanism. -/
  mechanism : String := "axial anomaly, U(1)_A breaking"
  /-- Scope. -/
  scope : String := "conjectural"
  deriving Repr

def eta_eta_prime : EtaEtaPrime := {}

-- ============================================================
-- GLUEBALL [IV.D201]
-- ============================================================

/-- [IV.D201] A glueball is a bound state of the strong vacuum field
    Γ_s* with no quark content: a color-neutral excitation of the
    su(3) connection field above the vacuum minimum.

    Predicted by lattice QCD at ~1.5-1.7 GeV for J^PC = 0^++. -/
structure GlueballDef where
  /-- Quark content: none. -/
  quark_content : Nat := 0
  /-- Predicted mass range low (MeV). -/
  mass_low_mev : Nat := 1500
  /-- Predicted mass range high (MeV). -/
  mass_high_mev : Nat := 1700
  /-- Quantum numbers J^PC. -/
  jpc : String := "0++"
  deriving Repr

def glueball_def : GlueballDef := {}

theorem glueball_no_quarks : glueball_def.quark_content = 0 := rfl

-- ============================================================
-- GLUEBALLS AND THE MASS GAP [IV.R129]
-- ============================================================

/-- [IV.R129] Glueball existence is a direct consequence of the mass gap:
    confinement ensures every excitation above vacuum carries positive mass.
    m_gb ≈ 2π/σ_τ^(1/2) ≈ 1.5 GeV. -/
def glueballs_mass_gap : String :=
  "Glueball existence: structural consequence of mass gap (confinement)"

-- ============================================================
-- NUCLEON MASS DECOMPOSITION [IV.P128]
-- ============================================================

/-- [IV.P128] m_N = E_vac + E_kin + Σm_qi
    - C-sector vacuum energy: ~400 MeV (42%)
    - Quark kinetic energy: ~500 MeV (53%)
    - Bare quark rest masses: ~12 MeV (1%)
    - Trace anomaly + sigma terms: ~27 MeV (3%)

    Vacuum + kinetic ≈ 99% of nucleon mass.
    All energies in MeV. -/
structure NucleonMassDecomp where
  /-- Vacuum energy (MeV). -/
  e_vac_mev : Nat := 400
  /-- Kinetic energy (MeV). -/
  e_kin_mev : Nat := 500
  /-- Quark rest masses (MeV). -/
  e_quark_mev : Nat := 12
  /-- Other (trace anomaly, sigma). -/
  e_other_mev : Nat := 27
  /-- Total nucleon mass (MeV, approximate). -/
  total_mev : Nat := 939
  /-- Percentage from non-quark-mass sources. -/
  nonquark_pct : Nat := 99
  deriving Repr

def nucleon_mass_decomposition : NucleonMassDecomp := {}

theorem nucleon_99pct_nonquark :
    nucleon_mass_decomposition.nonquark_pct = 99 := rfl

/-- Decomposition sums to approximately the nucleon mass. -/
theorem nucleon_decomp_sums :
    nucleon_mass_decomposition.e_vac_mev +
    nucleon_mass_decomposition.e_kin_mev +
    nucleon_mass_decomposition.e_quark_mev +
    nucleon_mass_decomposition.e_other_mev =
    nucleon_mass_decomposition.total_mev := by rfl

-- ============================================================
-- ISOSPIN SPLITTING [IV.R131]
-- ============================================================

/-- [IV.R131] m_d > m_u has structural origin: the d-quark has
    η-winding n ≡ 1 mod 3 (χ₋-dominant), while u-quark has
    n ≡ 2 mod 3 (complement class). δ_A ≈ 1.293 MeV. -/
structure IsospinSplitting where
  /-- d-quark winding class mod 3. -/
  d_winding_mod3 : Nat := 1
  /-- u-quark winding class mod 3. -/
  u_winding_mod3 : Nat := 2
  /-- Mass splitting (keV). -/
  delta_A_keV : Nat := 1293
  /-- d heavier than u. -/
  d_heavier : Bool := true
  deriving Repr

def isospin_splitting : IsospinSplitting := {}

-- ============================================================
-- NUCLEAR FORCE [IV.D202]
-- ============================================================

/-- [IV.D202] The nuclear force is the residual C-sector interaction
    from partial overlap of nucleon color fields at ~1 fm.
    Mediated by virtual meson exchange, principally the pion
    (range ≈ ℏ/m_π c ≈ 1.4 fm). -/
structure NuclearForce where
  /-- Range (fm ×10). -/
  range_fm_x10 : Nat := 14
  /-- Mediator. -/
  mediator : String := "pion (primarily)"
  /-- Mechanism. -/
  mechanism : String := "residual C-sector color field overlap"
  deriving Repr

def nuclear_force : NuclearForce := {}

-- ============================================================
-- DEUTERON BINDING [IV.R133]
-- ============================================================

/-- [IV.R133] The deuteron is the minimal two-nucleon winding
    configuration on T². Binding energy B_d ≈ 2.224 MeV from
    η-holonomy field overlap. -/
structure DeuteronBinding where
  /-- Number of nucleons. -/
  nucleon_count : Nat := 2
  /-- Binding energy (keV). -/
  binding_keV : Nat := 2224
  /-- Minimal configuration. -/
  minimal : Bool := true
  deriving Repr

def deuteron_binding : DeuteronBinding := {}

-- ============================================================
-- NUCLEAR FORCE SATURATION [IV.P129]
-- ============================================================

/-- [IV.P129] Each nucleon's defect bundle has finite angular extent
    Δθ ≈ ι_τ on the η-circle, so only ~12 nearest neighbors interact.
    Binding energy per nucleon B/A plateaus near 8.8 MeV for large A. -/
structure NuclearSaturation where
  /-- Max neighbors interacting. -/
  max_neighbors : Nat := 12
  /-- B/A plateau (MeV ×10). -/
  ba_plateau_mev_x10 : Nat := 88
  /-- Angular extent determines saturation. -/
  angular_extent : Bool := true
  deriving Repr

def nuclear_force_saturation : NuclearSaturation := {}

-- ============================================================
-- NUCLEAR SHELL STRUCTURE [IV.P130]
-- ============================================================

/-- [IV.P130] T²-winding modes for nucleons organize into shells.
    Cumulative counts at shell closures produce the magic numbers:
    2, 8, 20, 28, 50, 82, 126. -/
structure NuclearShellStructure where
  /-- Magic numbers. -/
  magic_numbers : List Nat := [2, 8, 20, 28, 50, 82, 126]
  /-- Origin: T²-winding shell closures. -/
  origin : String := "T^2 winding mode shells"
  deriving Repr

def nuclear_shell_structure : NuclearShellStructure := {}

theorem seven_magic_numbers :
    nuclear_shell_structure.magic_numbers.length = 7 := by rfl

-- ============================================================
-- HELIUM-4 TIGHTLY BOUND [IV.R135]
-- ============================================================

/-- [IV.R135] He-4 (Z=N=2) is the first doubly magic nucleus.
    B/A ≈ 7.1 MeV, preferred alpha-decay product.
    Completely fills lowest winding mode (0,0) with all four slots. -/
structure Helium4Bound where
  /-- Atomic number Z. -/
  z : Nat := 2
  /-- Neutron number N. -/
  n : Nat := 2
  /-- Binding per nucleon (MeV ×10). -/
  ba_mev_x10 : Nat := 71
  /-- Doubly magic. -/
  doubly_magic : Bool := true
  /-- Number of nucleon slots filled. -/
  slots_filled : Nat := 4
  deriving Repr

def helium4_tightly_bound : Helium4Bound := {}

theorem helium4_doubly_magic :
    helium4_tightly_bound.doubly_magic = true := rfl

-- ============================================================
-- IRON PEAK [IV.P131]
-- ============================================================

/-- [IV.P131] The binding energy maximum at A ≈ 56 (iron peak) results
    from optimal balance between:
    - C-sector (strong) binding per nucleon (saturating)
    - B-sector (EM) repulsion per nucleon (growing as Z²/A^(1/3))

    Crossover near iron-56 where Coulomb cost exceeds marginal binding. -/
structure IronPeak where
  /-- Peak mass number. -/
  peak_A : Nat := 56
  /-- Binding sector. -/
  binding_sector : Sector := .C
  /-- Repulsion sector. -/
  repulsion_sector : Sector := .B
  /-- B/A at peak (MeV ×100). -/
  ba_peak_mev_x100 : Nat := 879
  deriving Repr

def iron_peak : IronPeak := {}

theorem iron_at_56 : iron_peak.peak_A = 56 := rfl

-- ============================================================
-- NUCLEOSYNTHESIS FORWARD [IV.R136]
-- ============================================================

/-- [IV.R136] Fusion releases energy below iron peak (A < 56),
    fission above it (A > 56). Astrophysical consequences deferred
    to Book V. -/
def nucleosynthesis_forward : String :=
  "Fusion (A<56) and fission (A>56) consequences deferred to Book V"

-- ============================================================
-- ALPHA-DECAY MODE [IV.R137]
-- ============================================================

/-- [IV.R137] Alpha-decay: ejection of a completely filled lowest-winding-mode
    cluster (4 nucleons) from the parent nucleus, tunneling through the
    Coulomb barrier. -/
def alpha_decay_mode : String :=
  "Alpha-decay: 4-nucleon cluster ejection, lowest winding mode, Coulomb tunneling"

-- ============================================================
-- NEUTRON STABILITY [IV.R138]
-- ============================================================

/-- [IV.R138] Free neutrons decay in ~10 min, but bound neutrons are stable
    because nuclear binding makes Q_β < 0 (energetically forbidden).
    This is a readout-level phenomenon; the ontic neutron is unchanged. -/
structure NeutronStabilityNuclear where
  /-- Free lifetime (minutes, approx). -/
  free_lifetime_min : Nat := 10
  /-- Stable in nuclei. -/
  stable_in_nuclei : Bool := true
  /-- Mechanism: Q_β < 0. -/
  mechanism : String := "nuclear binding makes Q_beta < 0"
  deriving Repr

def neutron_stability_nuclear : NeutronStabilityNuclear := {}

-- ============================================================
-- GAMMA-DECAY MODE [IV.R139]
-- ============================================================

/-- [IV.R139] Gamma-decay is the same mechanism as atomic spectral lines:
    a T²-winding mode transition with energy carried by a B-sector photon.
    Only difference: scale (MeV nuclear vs eV atomic). -/
def gamma_decay_mode : String :=
  "Gamma-decay: T^2 mode transition at MeV scale (same mechanism as atomic lines)"

-- ============================================================
-- DECAY CHANNELS [IV.P132]
-- ============================================================

/-- [IV.P132] Every radioactive decay satisfies sector admissibility:
    - Color neutrality (η-holonomy trivial mod 3)
    - Baryon number conserved
    - Electric charge conserved (γ-holonomy)
    - Energy-momentum conserved

    Each decay type corresponds to a specific sector-transition pattern. -/
structure DecayChannels where
  /-- Number of conservation laws. -/
  conservation_laws : Nat := 4
  /-- Decay types. -/
  types : List String := ["alpha", "beta", "gamma"]
  /-- All satisfy sector admissibility. -/
  all_admissible : Bool := true
  deriving Repr

def decay_channels : DecayChannels := {}

theorem three_decay_types : decay_channels.types.length = 3 := by rfl
theorem four_conservation_laws : decay_channels.conservation_laws = 4 := rfl

-- ============================================================
-- SMOKE TESTS
-- ============================================================

#eval pion_plus.mass_mev                              -- 140
#eval glueball_def.quark_content                      -- 0
#eval nucleon_mass_decomposition.nonquark_pct         -- 99
#eval isospin_splitting.delta_A_keV                   -- 1293
#eval nuclear_force.range_fm_x10                      -- 14
#eval nuclear_shell_structure.magic_numbers.length     -- 7
#eval helium4_tightly_bound.slots_filled              -- 4
#eval iron_peak.peak_A                                -- 56
#eval neutron_stability_nuclear.free_lifetime_min     -- 10
#eval decay_channels.conservation_laws                -- 4

end Tau.BookIV.Particles
