import TauLib.BookV.Cosmology.NoShrinkExtended
import TauLib.BookV.Astrophysics.CompactObjects

/-!
# TauLib.BookV.Cosmology.HeavySeedBirth

Heavy-seed black-hole birth in atomic-cooling halos at z ≈ 8–15.
The d_top = 1 birth-condition theorem (V.T-LRD-1) and its four
sub-claims: lower mass cutoff, upper mass cutoff, flat interior
slope, sharp slope transition at the upper cutoff.

This module is the formal scaffolding for the Little Red Dot
(LRD) heavy-seed hypothesis derived in the v2.1 LRD-categorical
research note (Fuchs & Fuchs, April 2026).

## Scope

This is a SKELETON module (registry status `skeleton`, scope
`tau-effective`). Numerical bounds and structural relations are
encoded as `Nat`-scaled rationals on `structure` carriers in the
established BookV.Cosmology pattern (cf. V.T213 Quantitative
Bullet Cluster, V.D272 Einstein Radius with Boundary Holonomy
Mass, both in `CMBSpectrum.lean`). The four sub-theorems are
stated as structural identities on those carriers; the underlying
physics derivation chains are documented in `TODO(V.T-LRD-1 wave)`
honesty markers and live in
`research-notes/V-T-LRD-1-derivation.md`.

The module exposes the carriers needed for downstream imports
(LRD predictions in FalsificationPack, future JWST/ELT comparison
harness) without prematurely committing to a floating-point or
TauReal representation that the BookV.Cosmology corpus has
deliberately avoided.

## Registry Cross-References

- [V.T-LRD-1] d_top = 1 birth-condition theorem — `t_lrd_1_main`
  - Sub-claim A: lower cutoff at ~10^4.5 M_☉ — `t_lrd_1_lower_cutoff`
  - Sub-claim B: upper cutoff at ~10^(6.5±0.15) M_☉ — `t_lrd_1_upper_cutoff`
  - Sub-claim C: |dlogN/dlogM| ≤ 0.3 in interior — `t_lrd_1_flat_shape`
  - Sub-claim D: slope transitions over ≤ 0.2 dex — `t_lrd_1_sharp_transition`
- [V.D-LRD-1a] Atomic-cooling halo floor — `AtomicCoolingHaloFloor`
- [V.D-LRD-1b] DCBH collapse fraction (orthodox) — `DCBHCollapseFraction`
- [V.D-LRD-1c] Spin-parameter log-uniform hypothesis (orthodox)
  — `SpinParameterLogUniform`
- [V.D-LRD-1d] T²-horizon angular-momentum bound (τ-distinctive)
  — `T2HorizonAngularMomentumBound`
- [V.D-LRD-1e] Seed mass distribution carrier — `SeedMassDistribution`

## Inputs (cited registry IDs, all formalized in TauLib)

- [V.T108] Nucleosynthesis from τ (BBN, Y_p = 20/81 exactly)
  — `nucleosynthesis_from_tau`, in `BookV.Cosmology.ThresholdLadder`
  (transitively in scope via the NoShrinkExtended import chain)
- [V.T109] BH Threshold Theorem `G(U) > C_sph`
  — `bh_threshold_theorem`, in `BookV.Cosmology.BHBirthTopology`
- [V.T110] BH Toroidal Topology, r/R = ι_τ
  — `bh_toroidal_topology`, `bh_toroidal_structural`,
    in `BookV.Cosmology.BHBirthTopology`
- [V.R179] No-Primordial-BHs (comment-only structural remark)
  — in `BookV.Astrophysics.CompactObjects`
- [V.T40 / V.T114] No-Shrink Theorem
  — `no_shrink_theorem`, in `BookV.Cosmology.NoShrinkExtended`
- [V.T88] Compact-Object Classification (Mass Gap Prediction)
  — `mass_gap_prediction`, `mass_gap_upper`,
    in `BookV.Astrophysics.CompactObjects`

## τ-distinctive vs. orthodox-imported content

τ-distinctive (load-bearing for V.T-LRD-1):

- The upper cutoff at 10^6.5 M_☉ from the angular-momentum vs.
  T²-geometry constraint (V.T110-derived; the single near-term
  clean falsifier of the LRD note v2.1, signature 1 in N15).
- The flat interior shape (|dlogN/dlogM| ≤ 0.3) following from
  the unit Jacobian |dlogM_BH/dlogλ| = 1 enforced by T²-coherence
  on f_BH(λ) ∝ 1/λ in the regime λ > λ_⋆.
- The sharp slope transition (≤ 0.2 dex) at the upper cutoff
  (Hossenfelder ask in N15 §6.1) — see honest gap below.

Orthodox-imported (acknowledged dependencies on external cosmology):

- The lower cutoff at 10^4.5 M_☉ inherits the atomic-cooling halo
  floor from the standard H I cooling threshold (Bromm & Loeb 2003;
  Rees & Ostriker 1977).
- The DCBH collapse fraction f_DCBH ≈ 10^-2 (Begelman & Volonteri
  2017) is an externally imported normalisation, not τ-derived.
- The halo spin distribution is assumed log-normal in λ centred at
  λ̄ ≈ 0.04 with σ_logλ ≈ 0.30 (Bullock et al. 2001), not τ-derived.

## Honest gap: transition-width width

The Hossenfelder ask in N15 §6.1 of the v2.1 paper is for a
transition width Δlog M_BH ≤ 0.2 dex. Two parallel red-team
specialist derivations disagree on whether this is achievable:

- Specialist A (cutoff in λ-space, Jacobian 1/2): Δlog M_BH ≈
  1.66 dex (substantially wider than the v2.1 paper's claim).
- Specialist C (unit Jacobian from smooth f_BH(λ) ∝ 1/λ):
  Δlog M_BH ≈ 0.41 dex (still wider than 0.2 dex).
- Reconciliation: the two specialists are computing different
  mechanisms (outer-cutoff vs. interior dynamics). If
  σ_logλ ≈ 0.20 for atomic-cooling subsamples specifically
  (Macciò 2007 plausible but unverified), Specialist C's value
  drops to ≈ 0.18 dex and the v2.1 claim survives.

The Lean module records the conservative skeleton-status bound
Δlog M_BH ≤ 0.20 dex at the witness level (matching the v2.1
paper claim) but flags this as the principal pending physics
question for the V.T-LRD-1 wave. See
`research-notes/V-T-LRD-1-derivation.md` §5 for the full
analysis.

## Honest gap markers

The four sub-theorems below are stated structurally on
`Nat`-scaled carriers. Their physics derivation chains are
being filled in by the V.T-LRD-1 wave physics specialists
(cf. v2.1 paper §3.3 Steps 1–5, §7 Gap 1, Appendix B Wave 43
specification, and `research-notes/V-T-LRD-1-derivation.md`
§§2–5). Each `TODO(V.T-LRD-1 wave)` marker names the missing
physics input.

## Ground Truth Sources

- v2.1 LRD-categorical research note (Fuchs & Fuchs, April 2026),
  `papers/research-notes/lrd-categorical-v2/main.tex`,
  Theorem 3.2, §3.3, §6.1 (N15 commitment with sharper bounds),
  §7 Gap 1, Appendix B (Wave 43 V.T-LRD-1 specification).
- Begelman 2010 "Quasi-stars and the cosmic black hole mass
  density" (precursor of the d_top = 1 contraction, brief
  10^5–10^6 yr phase).
- Bromm & Loeb 2003 "Formation of the first supermassive black
  holes" (atomic-cooling halo floor, lower-cutoff anchor).
- Bullock et al. 2001 "A universal angular momentum profile for
  galactic halos" (log-normal spin parameter).
- Inayoshi & Maiolino 2024 "Scattering shroud" (radiative-transfer
  overlay, not used in this module — operates AFTER birth).
- `research-notes/V-T-LRD-1-derivation.md` (full synthesis of
  4 red-team specialist derivations).

-/

namespace Tau.BookV.Cosmology

-- ============================================================
-- IOTA_TAU REBINDING
-- ============================================================

/-- Local re-binding of the master constant ι_τ ≈ 0.341304.

    `iota_tau_x_1000000 = 341304` matches `Tau.Boundary.iota_tau_numer`
    transitively imported via the NoShrinkExtended chain.
    BookV.Cosmology by convention does NOT use `TauReal` directly
    (cf. CMBSpectrum.lean): all numerical content is encoded as
    `Nat`-scaled fields with structural `theorem field = value`
    lemmas.

    This re-binding makes the dependency on V.T110's r/R = ι_τ
    relation visible at the module API level. -/
def iota_tau_x_1000000 : Nat := 341304

/-- ι_τ rebinding agrees with the canonical BookI value
    `Tau.Boundary.iota_tau_numer`. -/
theorem iota_tau_rebind_canonical :
    iota_tau_x_1000000 = Tau.Boundary.iota_tau_numer := by
  unfold iota_tau_x_1000000
  unfold Tau.Boundary.iota_tau_numer
  rfl

-- ============================================================
-- ATOMIC-COOLING HALO FLOOR [V.D-LRD-1a]
-- ============================================================

/-- [V.D-LRD-1a] Atomic-cooling halo floor at redshift z.

    The minimum halo mass M_halo,min(z) at which H I line cooling
    can sustain a quasi-isothermal collapse in a metal-free halo
    (Bromm & Loeb 2003; Rees & Ostriker 1977).

    Encoded as M_halo,min × 10^(-7) × 10, so the canonical value
    M_halo,min(z=10) ≈ 10^7.5 M_☉ ≈ 3.16 × 10^7 M_☉ is stored as
    `m_halo_min_e7_x10 = 32` (= 31.6, rounded).

    Scope: ORTHODOX-IMPORTED. The H I cooling function is taken
    from external cosmology; not τ-derived. The downstream BH
    seed lower cutoff (10^4.5 M_☉) inherits this orthodoxy. -/
structure AtomicCoolingHaloFloor where
  /-- Redshift × 10 (so z = 10 stored as 100). -/
  redshift_x10 : Nat
  /-- M_halo,min in units of 10^7 M_☉, scaled × 10. -/
  m_halo_min_e7_x10 : Nat
  /-- Both positive (the floor is well-defined for z ∈ [8, 15]). -/
  redshift_in_range : redshift_x10 ≥ 80 ∧ redshift_x10 ≤ 150
  /-- The mass floor lies in the atomic-cooling regime
      (~ 10^7 to 10^8 M_☉). -/
  mass_in_atomic_regime : m_halo_min_e7_x10 ≥ 10 ∧ m_halo_min_e7_x10 ≤ 100
  deriving Repr

/-- The canonical atomic-cooling halo floor at z = 10. -/
def atomic_cooling_floor_z10 : AtomicCoolingHaloFloor where
  redshift_x10 := 100
  m_halo_min_e7_x10 := 32  -- 10^7.5 / 10^7 × 10 ≈ 31.6
  redshift_in_range := ⟨by omega, by omega⟩
  mass_in_atomic_regime := ⟨by omega, by omega⟩

-- ============================================================
-- DCBH COLLAPSE FRACTION [V.D-LRD-1b]
-- ============================================================

/-- [V.D-LRD-1b] DCBH (direct-collapse black hole) collapse fraction.

    f_DCBH ≈ 10^-2 is the fraction of atomic-cooling-halo gas
    that reaches the central singularity in a successful d_top = 1
    contraction (rather than fragmenting or being expelled by
    super-Eddington outflows; Begelman 2010 quasi-star phase plus
    disc self-gravity Toomre cap, Begelman & Volonteri 2017).

    Stored as f_DCBH × 10^4 = 100 for f_DCBH = 10^-2.

    Scope: ORTHODOX-IMPORTED. The v2.1 paper §7 Gap 1 explicitly
    flags this as an external dependency. A τ-modified version
    is a natural V.T-NEW-4 candidate. -/
structure DCBHCollapseFraction where
  /-- f_DCBH × 10^4 (so 10^-2 stored as 100). -/
  f_dcbh_x10000 : Nat := 100
  /-- Source citation tag. -/
  source : String := "Begelman & Volonteri 2017 / Begelman 2010"
  /-- Honest scope marker. -/
  is_orthodox_imported : Bool := true
  deriving Repr

def dcbh_fraction : DCBHCollapseFraction := {}

/-- The DCBH fraction is the orthodox 10^-2 value. -/
theorem dcbh_fraction_orthodox :
    dcbh_fraction.f_dcbh_x10000 = 100 ∧
    dcbh_fraction.is_orthodox_imported = true :=
  ⟨rfl, rfl⟩

-- ============================================================
-- SPIN-PARAMETER LOG-UNIFORM ASSUMPTION [V.D-LRD-1c]
-- ============================================================

/-- [V.D-LRD-1c] Halo spin-parameter local-log-uniform hypothesis.

    The Bullock et al. 2001 result that the dimensionless spin
    parameter λ = J |E|^(1/2) / (G M^(5/2)) follows a log-normal
    distribution centred at λ ≈ 0.04 with σ_logλ ≈ 0.30. Over
    the central ±1σ window relevant to the d_top = 1 birth
    condition (λ ∈ [10^-2.5, 10^-1.5]), the distribution is
    APPROXIMATELY LOG-UNIFORM (the log-normal peak is broad over
    this width).

    This is the load-bearing assumption that, combined with the
    τ-distinctive unit Jacobian |dlogM_BH/dlogλ| = 1, makes the
    seed mass distribution flat in dlogN/dlogM_BH.

    Scope: ORTHODOX-IMPORTED, with explicit narrowness disclaimer.
    Stated as a `structure` (not a `Prop` axiom) to keep the
    trust budget clean: this is a HYPOTHESIS recorded with an
    `is_orthodox_imported` marker, not a derivation. -/
structure SpinParameterLogUniform where
  /-- M_halo in units of 10^7 M_☉, scaled × 10. -/
  m_halo_e7_x10 : Nat
  /-- Lower edge of allowed log-λ window magnitude × 100
      (= 250 for log_10 λ = -2.5). -/
  log_lambda_min_abs_x100 : Nat
  /-- Upper edge of allowed log-λ window magnitude × 100
      (= 150 for log_10 λ = -1.5). -/
  log_lambda_max_abs_x100 : Nat
  /-- Window is non-empty: |log λ_max| < |log λ_min|. -/
  window_nonempty : log_lambda_max_abs_x100 < log_lambda_min_abs_x100
  /-- Log-uniformity holds approximately over [λ_min, λ_max]. -/
  log_uniform_on_window : Bool := true
  /-- Source: Bullock 2001, log-normal σ_logλ ≈ 0.30. -/
  source : String := "Bullock 2001 (log-normal, locally log-uniform on ±1σ window)"
  /-- Honest scope marker. -/
  is_orthodox_imported : Bool := true
  deriving Repr

/-- The canonical Bullock 2001 hypothesis on the d_top = 1 window. -/
def bullock_spin_assumption : SpinParameterLogUniform where
  m_halo_e7_x10 := 32           -- 10^7.5 M_☉
  log_lambda_min_abs_x100 := 250    -- |log_10 λ_min| = 2.5
  log_lambda_max_abs_x100 := 150    -- |log_10 λ_max| = 1.5
  window_nonempty := by omega

-- ============================================================
-- T² HORIZON ANGULAR-MOMENTUM BOUND [V.D-LRD-1d]
-- ============================================================

/-- [V.D-LRD-1d] T²-horizon angular-momentum bound
    J_max^{T²}(M_BH, ι_τ).

    From V.T110 (BH Toroidal Topology, r/R = ι_τ), the BH horizon
    has fixed aspect ratio r/R = ι_τ ≈ 0.341. Specialist A's
    structural derivation gives the tight bound

      J_max^{T²}(M_BH) = ι_τ √κ_D · (G M_BH² / c)
                       ≈ 0.277 · J_max^{Kerr},

    combining (a) the projection onto the dominant γ-cycle
    (factor r/R = ι_τ) with (b) the √κ_D centrifugal-opposition
    factor in the V.T109 threshold-survival condition (κ_D = 1 - ι_τ).

    This is TIGHTER than Kerr by ≈ 0.28; a T²-BH supports only
    ~ 28% of the angular momentum of a same-mass Kerr BH.

    For an atomic-cooling halo of mass M_halo and spin parameter
    λ, angular-momentum conservation during the d_top = 1
    contraction requires j_gas(M_halo) · ε_J ≤ j_max^{T²}(M_BH),
    where ε_J ~ (R_vir/r_g)^(-1/2) is the bar-cascade transport
    efficiency (Begelman-Volonteri-Rees 2006). This sets the
    UPPER cutoff at 10^6.5 M_☉.

    Stored as F(ι_τ) × 10^4 with the canonical value
    F(ι_τ) = ι_τ √κ_D ≈ 0.277, so `f_iota_x_10000 = 2773`.

    Scope: τ-DISTINCTIVE. The function F(ι_τ) is the load-bearing
    quantity for signature 1 of N15. -/
structure T2HorizonAngularMomentumBound where
  /-- M_BH in units of 10^4 M_☉, scaled × 10. -/
  m_bh_e4_x10 : Nat
  /-- ι_τ × 10^6 (= 341304). -/
  iota_tau_x_1000000 : Nat := 341304
  /-- F(ι_τ) × 10^4 = ι_τ √κ_D ≈ 2773 (Specialist A derivation). -/
  f_iota_x_10000 : Nat := 2773
  /-- M_BH positive. -/
  m_bh_pos : m_bh_e4_x10 > 0
  /-- F(ι_τ) is a proper reduction (< 1). -/
  f_proper : f_iota_x_10000 < 10000
  deriving Repr

-- ============================================================
-- SEED MASS DISTRIBUTION [V.D-LRD-1e]
-- ============================================================

/-- [V.D-LRD-1e] Predicted seed mass distribution dN/dlogM_BH at
    redshift z.

    The distribution is nonzero in the interior
    [10^4.5, 10^6.5] M_☉ and zero outside (sharp cutoffs).

    The shape is encoded via a discrete histogram: 21 mass bins
    of width 0.1 dex covering [10^4.5, 10^6.5], indexed by
    `bin_index ∈ {0, ..., 20}` corresponding to
    log_10(M_BH/M_☉) = 4.5 + 0.1 · bin_index.

    Each bin stores the predicted log_10(dN/dlogM) value × 100
    plus a constant offset of 1000 so values are non-negative
    `Nat`s. The offset cancels in all derived ratios.

    Scope: τ-DISTINCTIVE on the cutoffs and shape; ORTHODOX-
    IMPORTED on the overall normalisation (DCBH × halo MF). -/
structure SeedMassDistribution where
  /-- Redshift × 10 (z ∈ [8, 15] ⇒ stored ∈ [80, 150]). -/
  redshift_x10 : Nat
  /-- Distribution values in 21 bins of 0.1 dex from 10^4.5 to
      10^6.5, stored as log_10(dN/dlogM) × 100 + 1000 offset. -/
  log_dN_per_dlogM_x100_plus_1000 : Fin 21 → Nat
  /-- Redshift in the seed-formation window [z=8, z=15]. -/
  z_in_window : redshift_x10 ≥ 80 ∧ redshift_x10 ≤ 150
  deriving Repr

-- ============================================================
-- LOWER CUTOFF [V.T-LRD-1, sub-claim A]
-- ============================================================

/-- Carrier for the lower-cutoff statement. The lower cutoff is
    at M_BH = 10^4.5 M_☉ ≈ 31.6 × 10^3 M_☉ (atomic-cooling halo
    floor inheritance). Stored as M_min × 10^(-3) × 10 = 316. -/
structure LowerCutoffStatement where
  /-- Lower cutoff in units of 10^3 M_☉, scaled × 10 (= 316). -/
  m_min_e3_x10 : Nat
  /-- Atomic-cooling floor source. -/
  inherited_from : String := "AtomicCoolingHaloFloor (Bromm-Loeb 2003)"
  /-- Honesty: this is an ORTHODOX inheritance, not τ-distinctive. -/
  is_orthodox_imported : Bool := true
  deriving Repr

def lower_cutoff_statement : LowerCutoffStatement where
  m_min_e3_x10 := 316  -- 10^4.5 / 10^3 × 10 ≈ 31.6

/-- [V.T-LRD-1, A] Lower cutoff: at z ∈ [8, 15], the seed mass
    distribution vanishes for M_BH < 10^4.5 M_☉.

    The lower cutoff is INHERITED from the atomic-cooling halo
    floor (Bromm & Loeb 2003): only halos with
    M_halo > M_halo,min(z) can sustain H I cooling, and only
    the smallest such halos correspond to seed BHs as light as
    10^4.5 M_☉.

    The τ-distinctive content of the lower cutoff is the
    SHARPNESS (no Pop-III remnant tail), not the value: V.T109
    + V.T110 require d_top = 1 contraction, fragmentation
    produces multiple disjoint S²-horizon Schwarzschild
    remnants (excluded from the toroidal-horizon BH population
    counted in N15).

    This sub-claim is ORTHODOX-IMPORTED on the value, τ-DISTINCTIVE
    on the sharpness. See research-notes/V-T-LRD-1-derivation.md §2.

    TODO(V.T-LRD-1 wave): physics input needed —
      (a) Press-Schechter halo abundance n(M_halo, z) at
          z ∈ [8, 15];
      (b) the M_BH(M_halo) mapping under d_top = 1 contraction
          (smallest seed corresponds to the smallest atomic-
          cooling halo, M_halo = M_halo,min(z));
      (c) verification that the resulting M_BH lower edge ≈
          10^4.5 M_☉ (consistent across z ∈ [8, 15]). -/
theorem t_lrd_1_lower_cutoff :
    lower_cutoff_statement.m_min_e3_x10 = 316 ∧
    lower_cutoff_statement.is_orthodox_imported = true := by
  exact ⟨rfl, rfl⟩

-- ============================================================
-- UPPER CUTOFF [V.T-LRD-1, sub-claim B]
-- ============================================================

/-- Carrier for the upper-cutoff statement.

    The upper cutoff is at M_BH = 10^(6.5 ± 0.15) M_☉, i.e.
    centred at 10^6.5 ≈ 3.162 × 10^6 M_☉ with one-sigma width
    10^0.15 ≈ 1.413 multiplicative factor.

    Stored as:
      m_max_e6_x10 = M_max central × 10^(-6) × 10 ≈ 32 (= 31.6)
      m_max_logsigma_x100 = 0.15 × 100 = 15.

    The CENTRAL value 10^6.5 is the load-bearing τ-distinctive
    falsifier (signature 1 of N15). -/
structure UpperCutoffStatement where
  /-- Central upper cutoff in units of 10^6 M_☉, scaled × 10. -/
  m_max_e6_x10 : Nat
  /-- One-sigma width in dex, scaled × 100. -/
  m_max_logsigma_x100 : Nat
  /-- Source: T²-horizon angular-momentum vs. geometry. -/
  derivation_source : String := "T2HorizonAngularMomentumBound (V.T110)"
  /-- This is τ-DISTINCTIVE. -/
  is_tau_distinctive : Bool := true
  /-- Width is in the sharp-prior range (≤ 0.15 dex per N15 §6.1). -/
  width_within_n15_prior : m_max_logsigma_x100 ≤ 15
  deriving Repr

def upper_cutoff_statement : UpperCutoffStatement where
  m_max_e6_x10 := 32  -- 10^6.5 / 10^6 × 10 ≈ 31.6
  m_max_logsigma_x100 := 15
  width_within_n15_prior := by omega

/-- [V.T-LRD-1, B] Upper cutoff: at z ∈ [8, 15], the seed mass
    distribution vanishes for M_BH > 10^(6.5 ± 0.15) M_☉.

    The upper cutoff is τ-DISTINCTIVE: it follows from the
    angular-momentum-vs-T²-geometry constraint. Above 10^6.5 M_☉,
    the T² horizon (V.T110, r/R = ι_τ) cannot accommodate the
    angular momentum delivered by atomic-cooling halos with the
    log-normal spin distribution (V.D-LRD-1c). The contraction
    fragments instead.

    This is the load-bearing signature 1 of N15 (the single
    near-term clean falsifier of the LRD note v2.1).

    Numerical headline (Specialist A derivation; see
    research-notes/V-T-LRD-1-derivation.md §3):

      M_BH^max ≈ (2 λ̄² / ι_τ^n) · f_cool · f_b · M_h^{ACH,max} · √(1+z),

    with n ∈ [2, 3] (Specialist A argued effective n = 2.5
    comprising ι_τ^(-2) from η-cycle absorption + ι_τ^(-1/2)
    from coherent-mode centrifugal suppression). At z = 11,
    λ̄ = 0.04, f_cool = 0.3, f_b = 0.16, M_h^{ACH,max} =
    5×10^8 M_☉, ι_τ = 0.341:
      log_10(M_BH^max/M_☉) ≈ 6.5.

    TODO(V.T-LRD-1 wave): physics input needed —
      (a) Closed-form F(ι_τ) in T2HorizonAngularMomentumBound
          (Specialist A: F(ι_τ) = ι_τ √κ_D ≈ 0.277);
      (b) The angular-momentum transport efficiency ε_J during
          d_top = 1 contraction (from Begelman 2010 quasi-star
          phase; expected ε_J ∈ [0.05, 0.2]);
      (c) Combination J_halo · ε_J ≤ J_max^{T²}(M_BH) yields
          the upper edge at 10^(6.5 ± 0.15) M_☉; the ±0.15 dex
          width is the convolution of the J_halo log-normal
          scatter with the ε_J prior;
      (d) Cross-check with Hossenfelder ask in N15 §6.1
          (the 0.15 dex tightening of the original ±0.5 dex
          prior). -/
theorem t_lrd_1_upper_cutoff :
    upper_cutoff_statement.m_max_e6_x10 = 32 ∧
    upper_cutoff_statement.m_max_logsigma_x100 ≤ 15 ∧
    upper_cutoff_statement.is_tau_distinctive = true :=
  ⟨rfl, upper_cutoff_statement.width_within_n15_prior, rfl⟩

-- ============================================================
-- FLAT INTERIOR SHAPE [V.T-LRD-1, sub-claim C]
-- ============================================================

/-- Carrier for the flat-interior-shape statement.

    Between 10^4.5 and 10^6.5 M_☉, the predicted distribution
    is flat in dlogN/dlogM up to ±0.3 in absolute slope.

    Stored as the maximum |slope| × 100 over the 20 inter-bin
    differences of `SeedMassDistribution`. -/
structure FlatShapeStatement where
  /-- Maximum |dlogN/dlogM| × 100 (= 30 for ±0.3 bound). -/
  max_abs_slope_x100 : Nat
  /-- Bound holds. -/
  bound_holds : max_abs_slope_x100 ≤ 30
  /-- Derivation source. -/
  derivation_source : String :=
    "Unit Jacobian |dlogM_BH/dlogλ|=1 from T²-coherence (Specialist C)"
  /-- This is τ-DISTINCTIVE (single-channel ⇒ flat). -/
  is_tau_distinctive : Bool := true
  deriving Repr

def flat_shape_statement : FlatShapeStatement where
  max_abs_slope_x100 := 30
  bound_holds := by omega

/-- [V.T-LRD-1, C] Flat interior shape: in the interior
    10^4.5 ≤ M_BH ≤ 10^6.5 M_☉, |dlogN/dlogM_BH| ≤ 0.3.

    The flatness is τ-DISTINCTIVE and follows from the unit
    Jacobian |dlogM_BH/dlogλ| = 1 enforced by T²-coherence:
    in the regime λ > λ_⋆ ~ ι_τ λ̄, the central-collapse
    fraction follows f_BH(λ) ∝ 1/λ, so log M_BH = log M_gas +
    log λ_⋆ - log λ at fixed halo mass. This converts the
    broad log-normal λ-spectrum (Bullock 2001) into a broad
    log-uniform M_BH-spectrum at fixed M_halo. Convolution with
    the Sheth-Tormen halo MF (slope α ≈ 1.9) introduces a
    modest correction; over the convolution-relevant width
    (~ 0.6 dex), this contributes Δβ ≈ -0.27, leaving the
    interior slope in [-0.3, +0.3] across the 2-dex flat region.

    Compare orthodox heavy-seed DCBH (Natarajan 2017,
    Volonteri 2010): f_DCBH treated as λ-independent,
    M_BH ∝ M_gas tracks halo MF, β_orthodox ≈ -α + 1 ≈ -0.9.
    The Δβ ≈ 0.9 separation is discriminable at > 5σ for
    N ≥ 60 Inayoshi-corrected LRDs (per v2.1 §6 N15
    power-analysis paragraph).

    See research-notes/V-T-LRD-1-derivation.md §4.

    TODO(V.T-LRD-1 wave): physics input needed —
      (a) Rigorous derivation of f_BH(λ) ∝ 1/λ in the
          λ > λ_⋆ regime from T²-coherence (Specialist C);
      (b) Convolution-correction bound from Sheth-Tormen
          slope α ≈ 1.9 (orthodox-imported);
      (c) Verification that |dlogN/dlogM_BH| stays ≤ 0.3
          across the full 2-dex interior. -/
theorem t_lrd_1_flat_shape :
    flat_shape_statement.max_abs_slope_x100 ≤ 30 ∧
    flat_shape_statement.is_tau_distinctive = true :=
  ⟨flat_shape_statement.bound_holds, rfl⟩

-- ============================================================
-- SHARP TRANSITION AT UPPER CUTOFF [V.T-LRD-1, sub-claim D]
-- ============================================================

/-- Carrier for the sharp-transition statement (Hossenfelder ask).

    The slope transitions from |dlogN/dlogM| ≤ 0.3 (interior)
    to dlogN/dlogM ≤ -2 (exterior, i.e. above 10^6.5 M_☉) over
    a window of width ≤ 0.2 dex centred at M_BH = 10^(6.5 ±
    0.15) M_☉.

    The conservative skeleton-status bound matches the v2.1
    paper claim. The honest gap (see module docstring above):
    two specialist derivations disagreed on the achievable
    width — Specialist A computed 1.66 dex, Specialist C
    computed 0.41 dex (or 0.18 dex if σ_logλ for atomic-
    cooling subsamples is tightened to 0.20). The principal
    pending physics question is reconciling these mechanisms.

    Stored as the transition width × 100. -/
structure SharpTransitionStatement where
  /-- Centre of the transition × 100 in units of
      log_10(M_BH/M_☉) (= 650 for 10^6.5). -/
  transition_centre_x100 : Nat
  /-- Width of the transition × 100 in dex (= 20 for 0.2 dex). -/
  transition_width_x100 : Nat
  /-- Pre-transition slope × 100 absolute bound (= 30 for ≤ 0.3). -/
  pre_slope_max_x100 : Nat
  /-- Post-transition slope × 100 absolute bound (= 200 for ≤ -2,
      stored as the magnitude). -/
  post_slope_min_abs_x100 : Nat
  /-- Width within Hossenfelder bound. -/
  width_within_bound : transition_width_x100 ≤ 20
  /-- Pre-slope is shallow. -/
  pre_slope_shallow : pre_slope_max_x100 ≤ 30
  /-- Post-slope is steep. -/
  post_slope_steep : post_slope_min_abs_x100 ≥ 200
  /-- Derivation source. -/
  derivation_source : String :=
    "T²-cutoff geometric rigidity + log-normal convolution"
  /-- This is τ-DISTINCTIVE (Hossenfelder ask). -/
  is_tau_distinctive : Bool := true
  deriving Repr

def sharp_transition_statement : SharpTransitionStatement where
  transition_centre_x100 := 650
  transition_width_x100 := 20
  pre_slope_max_x100 := 30
  post_slope_min_abs_x100 := 200
  width_within_bound := by omega
  pre_slope_shallow := by omega
  post_slope_steep := by omega

/-- [V.T-LRD-1, D] Sharp transition: the slope of dN/dlogM_BH
    transitions from |slope| ≤ 0.3 to slope ≤ -2 over ≤ 0.2 dex
    centred at M_BH = 10^(6.5 ± 0.15) M_☉.

    This is the SHARPNESS condition required by the Hossenfelder
    ask in v2.1 §6.1: the upper cutoff must be a quasi-step,
    not a smooth power-law tail.

    The sharpness arises from the T² angular-momentum cutoff
    being itself sharp (a hard geometric constraint, not a soft
    one): once J_halo · ε_J exceeds J_max^{T²}, the contraction
    fragments rather than partially succeeding.

    HONEST GAP: the conservative bound recorded here matches
    the v2.1 paper claim but may need to be relaxed to ≤ 0.4
    dex pending reconciliation of two specialist derivations
    that gave incompatible widths (1.66 dex vs. 0.41 dex; see
    module docstring and research-notes/V-T-LRD-1-derivation.md
    §5).

    TODO(V.T-LRD-1 wave): physics input needed —
      (a) Reconcile Specialist A (cutoff in λ-space, Jacobian
          1/2) vs. Specialist C (unit Jacobian from smooth
          f_BH(λ) ∝ 1/λ) on the dominant transition mechanism;
      (b) The width of J_max^{T²} as a function of M_BH
          (sharper than 0.2 dex follows from the τ-distinctive
          geometric rigidity if the T²-cutoff is a hard step);
      (c) The convolution with the J_halo log-normal scatter
          (σ_logJ ≈ 0.30 from Bullock 2001) — this is what
          BROADENS the cutoff from a step to a tanh of width
          σ-controlled;
      (d) Justify σ_logλ ≈ 0.20 for atomic-cooling subsamples
          specifically (Macciò 2007 plausible but unverified)
          to tighten the predicted width to ≤ 0.2 dex; OR
          relax the v2.1 paper claim to ≤ 0.4 dex;
      (e) Verification: pre-transition slope stays shallow up
          to M_BH = 10^6.4 M_☉; post-transition slope is ≤ -2
          by M_BH = 10^6.6 M_☉. -/
theorem t_lrd_1_sharp_transition :
    sharp_transition_statement.transition_width_x100 ≤ 20 ∧
    sharp_transition_statement.pre_slope_max_x100 ≤ 30 ∧
    sharp_transition_statement.post_slope_min_abs_x100 ≥ 200 ∧
    sharp_transition_statement.is_tau_distinctive = true :=
  ⟨sharp_transition_statement.width_within_bound,
   sharp_transition_statement.pre_slope_shallow,
   sharp_transition_statement.post_slope_steep,
   rfl⟩

-- ============================================================
-- MAIN THEOREM [V.T-LRD-1]
-- ============================================================

/-- Carrier for the main V.T-LRD-1 statement, bundling the four
    sub-claims and the input registry citations. -/
structure VTLRD1Main where
  /-- Lower-cutoff witness. -/
  lower : LowerCutoffStatement
  /-- Upper-cutoff witness. -/
  upper : UpperCutoffStatement
  /-- Flat-shape witness. -/
  flat : FlatShapeStatement
  /-- Sharp-transition witness. -/
  sharp : SharpTransitionStatement
  /-- The seed-formation redshift window [z=8, z=15]. -/
  z_min_x10 : Nat := 80
  z_max_x10 : Nat := 150
  /-- Window non-degenerate. -/
  z_window_ok : z_min_x10 < z_max_x10
  /-- Inputs cited (as a comment-readable string field). -/
  inputs_cited : String :=
    "V.T108 (BBN), V.T109 (BH threshold G(U)>C_sph), " ++
    "V.T110 (T² horizon r/R = ι_τ), " ++
    "V.R179 (no PBH), V.T40/T114 (no-shrink), V.T88 (mass gap), " ++
    "atomic-cooling halo MF (orthodox-imported)"
  deriving Repr

def t_lrd_1_witness : VTLRD1Main where
  lower := lower_cutoff_statement
  upper := upper_cutoff_statement
  flat := flat_shape_statement
  sharp := sharp_transition_statement
  z_window_ok := by omega

/-- [V.T-LRD-1] Main theorem: the d_top = 1 birth-condition theorem.

    At z ∈ [8, 15], the seed black-hole mass distribution
    dN/dlogM_BH(z) produced by single quasi-isothermal d_top = 1
    contraction in atomic-cooling halos satisfies all four
    sub-conditions:

    (A) Lower cutoff at M_BH ≈ 10^4.5 M_☉ (atomic-cooling halo
        floor, ORTHODOX-IMPORTED on value, τ-DISTINCTIVE on
        sharpness).
    (B) Upper cutoff at M_BH ≈ 10^(6.5 ± 0.15) M_☉ (T²-horizon
        angular-momentum constraint, τ-DISTINCTIVE — load-bearing
        signature 1 of N15).
    (C) Flat interior shape: |dlogN/dlogM_BH| ≤ 0.3 throughout
        the interior (τ-DISTINCTIVE: unit Jacobian from T²-
        coherence f_BH(λ) ∝ 1/λ).
    (D) Sharp slope transition over ≤ 0.2 dex at the upper
        cutoff (Hossenfelder ask; see honest gap in module
        docstring).

    This combines `t_lrd_1_lower_cutoff`, `t_lrd_1_upper_cutoff`,
    `t_lrd_1_flat_shape`, and `t_lrd_1_sharp_transition` into a
    single registered statement.

    Inputs (all formalized in TauLib): V.T108
    (`nucleosynthesis_from_tau`), V.T109 (`bh_threshold_theorem`),
    V.T110 (`bh_toroidal_topology`, `bh_toroidal_structural`),
    V.R179 (comment-only, in CompactObjects.lean), V.T40/V.T114
    (`no_shrink_theorem`), V.T88 (`mass_gap_prediction`).

    Orthodox-imported inputs (NOT τ-derived):
    - Atomic-cooling halo mass function (Bromm-Loeb 2003);
    - DCBH collapse fraction f_DCBH ≈ 10^-2 (Begelman-Volonteri
      2017);
    - Halo spin-parameter log-normal hypothesis (Bullock 2001).

    Scope: τ-effective. Status: SKELETON (sub-theorem witnesses
    encoded as structural identities on `Nat`-scaled carriers;
    the physics derivation chains live in the
    `TODO(V.T-LRD-1 wave)` markers attached to each sub-theorem
    and in research-notes/V-T-LRD-1-derivation.md).

    Trust budget impact: NONE (no new custom axioms; all
    sub-theorem proofs are `rfl`/`omega` on structural
    identities). -/
theorem t_lrd_1_main :
    t_lrd_1_witness.lower.m_min_e3_x10 = 316 ∧
    t_lrd_1_witness.upper.m_max_e6_x10 = 32 ∧
    t_lrd_1_witness.upper.m_max_logsigma_x100 ≤ 15 ∧
    t_lrd_1_witness.flat.max_abs_slope_x100 ≤ 30 ∧
    t_lrd_1_witness.sharp.transition_width_x100 ≤ 20 ∧
    t_lrd_1_witness.sharp.post_slope_min_abs_x100 ≥ 200 ∧
    t_lrd_1_witness.upper.is_tau_distinctive = true ∧
    t_lrd_1_witness.z_min_x10 < t_lrd_1_witness.z_max_x10 := by
  refine ⟨rfl, rfl, ?_, ?_, ?_, ?_, rfl, ?_⟩
  · exact t_lrd_1_witness.upper.width_within_n15_prior
  · exact t_lrd_1_witness.flat.bound_holds
  · exact t_lrd_1_witness.sharp.width_within_bound
  · exact t_lrd_1_witness.sharp.post_slope_steep
  · exact t_lrd_1_witness.z_window_ok

-- ============================================================
-- INPUT-REGISTRY SANITY (cited theorems still hold)
-- ============================================================

/-- Sanity check: V.T110 toroidal-topology structural form is in
    scope and applicable to any non-trivial linking class. -/
theorem t_lrd_1_uses_v_t110 :
    unit_linking.a ≠ 0 ∨ unit_linking.b ≠ 0 :=
  bh_toroidal_structural unit_linking

/-- Sanity check: V.T88 mass-gap is in scope. The lower cutoff
    of V.T-LRD-1 (10^4.5 M_☉ ≈ 31600 × 10^(-1) M_☉) sits well
    above the V.T88 BH-mass-gap upper edge (5 M_☉ = 50 in the
    same scaled units); no overlap of the LRD-progenitor
    population with stellar-remnant BHs. -/
theorem t_lrd_1_above_mass_gap :
    Tau.BookV.Astrophysics.mass_gap_upper < 31600 := by
  unfold Tau.BookV.Astrophysics.mass_gap_upper
  omega

-- ============================================================
-- SMOKE TESTS
-- ============================================================

#eval iota_tau_x_1000000                                -- 341304
#eval atomic_cooling_floor_z10.m_halo_min_e7_x10        -- 32
#eval dcbh_fraction.f_dcbh_x10000                       -- 100
#eval bullock_spin_assumption.log_lambda_min_abs_x100   -- 250
#eval lower_cutoff_statement.m_min_e3_x10               -- 316
#eval upper_cutoff_statement.m_max_e6_x10               -- 32
#eval upper_cutoff_statement.m_max_logsigma_x100        -- 15
#eval flat_shape_statement.max_abs_slope_x100           -- 30
#eval sharp_transition_statement.transition_width_x100  -- 20
#eval t_lrd_1_witness.z_min_x10                         -- 80
#eval t_lrd_1_witness.z_max_x10                         -- 150

end Tau.BookV.Cosmology
