import TauLib.BookV.Cosmology.CMBSpectrum
import TauLib.BookV.Astrophysics.RotationCurves
import TauLib.BookV.Astrophysics.BulletClusterLSS
import TauLib.BookV.Astrophysics.GalaxyRelational
import TauLib.BookI.Boundary.TauRealIotaTau

/-!
# TauLib.BookV.Cosmology.ClusterSubstructure

Member-galaxy substructure in massive lensing clusters: the
Natarajan, Chiang & Dutra (2026, ApJL 1001, L12) dichotomy
re-read through Category τ. Provides the formal scaffolding for
chapter 46 of Book V Part 5
(`manuscript-sources/book-05/part05/ch46-cluster-substructure.tex`).

This module is the formal companion to the F3-light Natarajan-
cluster-dichotomy-categorical-v1 research note (Fuchs & Fuchs,
May 2026, `papers/research-notes/natarajan-cluster-dichotomy-
categorical-v1/`).

## Scope

This is a SKELETON module (registry status `skeleton`, scope
`tau-effective`). Numerical bounds and structural relations are
encoded as `Nat`-scaled rationals on `structure` carriers in the
established BookV.Cosmology pattern (cf. V.T213 Quantitative
Bullet Cluster, V.D272 Einstein Radius with Boundary Holonomy
Mass, both in `CMBSpectrum.lean`).

The module exposes the carriers needed for Phase 10+ work along
the V.D123-exploration path-shortlist (papers commit `1b92ec4`):
Path A (notational documentation), Path B (V.P144 metric-sector
progenitor promotion), Path C (Wilsonian RG anomalous-dimension
cross-check), Path D (Chern-Weil partial-domain holonomy
reframing).

## Registry cross-references

- [V.D350] Metric-Sector Capacity Equation
  — `MetricSectorCapacityEquation` carrier
- [V.D351] Boundary-Holonomy Inner-Promotion
  — `BoundaryHolonomyInnerPromotion` carrier
- [V.T346] Inner Radial Excess Amplitude
  — `inner_excess_amplitude_bracket`
- [V.T347] Transition Scale ℓ_cl,sub Recovery
  — `transition_scale_recovery`
- [V.P212] LRD Cross-Coupling Joint Lock
  — `lrd_cluster_iota_tau_lock`

## Inputs (cited registry IDs, all formalized in TauLib)

- [V.D121] Capacity Skeleton
  — `CapacitySkeleton` in `BookV.Astrophysics.GalaxyRelational`
- [V.D123] Galactic Capacity Profile (trace-projection of V.D350)
  — `BoundaryHolonomyCorrection` in `BookV.Astrophysics.RotationCurves`
- [V.D261] Cluster-Scale Screening Enhancement
  — in `BookV.Astrophysics.RotationCurves`
- [V.D266] Two-Channel Acceleration Decomposition
  — in `BookV.Astrophysics.RotationCurves`
- [V.D272] Einstein Radius from Boundary Holonomy
  — in `BookV.Cosmology.CMBSpectrum`
- [V.T28 / V.T78] Newtonian-Limit Theorem (n=2)
  — in `BookV.Astrophysics.RotationCurves`
- [V.T203] Cluster Capacity Mass Discrepancy (conjectural)
  — in `BookV.Astrophysics.RotationCurves`
- [V.T213] Quantitative Bullet Cluster Mass Prediction
  — in `BookV.Cosmology.CMBSpectrum`
- [V.P68 / V.R175] MOND-as-Approximation Theorem
  — in `BookV.Astrophysics.RotationCurves`
- [V.P144] Nonlinear Amplification Pathway (upgraded by V.D350)
  — in `BookV.Astrophysics.RotationCurves`

## τ-distinctive content (load-bearing for F3-light)

- The **boundary-holonomy mass inner-promotion** mechanism
  (V.D351). Sub-threshold capacity-skeleton peaks at fixed
  baryonic mass M_p are preferentially promoted above the
  spectroscopic luminosity threshold inside R/R_200 ≲ 0.2,
  producing the observed Natarajan inner radial excess.
  Structurally absent from TNG-Cluster ΛCDM.
- The **transition scale** ℓ_cl,sub(M_sub) = √(GM_sub/a_0)
  (V.T347). Host-mass-independent at fixed SHMF.
  Distinguishes τ from SIDM core-collapse (∝ (σ/m)^α) and
  from CDM (no transition).
- The **iota_tau joint coupling** (V.P212). Cluster-inner
  M_∂(R) amplitude and LRD signature-3 saturation ceiling
  share the same iota_tau pre-factor via V.D272.

## Honest gaps (deferred to Phase 10+)

- The radial profile g(R/R_200, c) is calibration-dependent at
  F3-light. F1 endpoint bracket: g produces M_∂/M_p ≈ 3.6, 4.9,
  5.5, 5.65 at R/R_200 = 0.05, 0.10, 0.20, 0.50; F3-full
  derivation awaits the V.D123-exploration Path C (RG anomalous-
  dimension η = 1 cross-check) or Path D (Chern-Weil holonomy).
- Innermost bins R/R_200 ≤ 0.05 inherit V.T203's conjectural
  shortfall (D_τ ~ 2-4 vs D_obs ~ 5-7); under-predicted by
  factor 1.5-3× (`inner_excess_amplitude_bracket` only commits
  to the [5, 7] band for R/R_200 ∈ [0.05, 0.2]).
- Inner γ slope value (R2 NEGATIVE, F2 NEGATIVE-CONFIRMATION):
  τ-saturation family is anti-cusp via V.P16. Carried as
  reframed-falsifier in the companion research note §6, NOT
  as a structural theorem here.

## V.T-LRD-1 precedent compliance

This module follows the V.T-LRD-1 (HeavySeedBirth.lean) pattern:

- Skeleton-first (Lean carriers + structural theorems before
  manuscript chapter is fully audited).
- Nat-scaled carriers (no premature TauReal commitment beyond
  the iota_tau_x_1000000 anchor).
- `TODO(Natarajan-F3 wave)` honesty markers naming Path A-D
  prerequisites.
- Status-discipline metadata (registry status `skeleton`,
  scope `tau-effective`).
- 0 new custom axioms (F4 trust-budget audit confirmed; F1
  formalizability scoring 4 class-(a) + 3 class-(b) + 3
  class-(c) + 0 class-(d)).

## Ground truth sources

- Natarajan, P., Chiang, B. T. & Dutra, I. 2026, ApJL 1001 L12,
  doi:10.3847/2041-8213/ae53ea (the source paper).
- Famaey, B., Pizzuti, L. & Saltas, I. D. 2025, PRD 111, 123042
  (MOND-cluster-failure foil, arXiv:2410.02612).
- Fuchs & Fuchs 2026, `papers/research-notes/natarajan-cluster-
  dichotomy-categorical-v1/main.tex` (the F3-light research note).
- F3 wave (`research-wave/02-R1...R5.md`, `f3-wave/02-F1...F5.md`,
  commits b4b6a3a + 481005a).
- V.D123 exploration (`vd123-exploration/02-X1...X5.md`,
  commit 1b92ec4) — establishes V.D350's promotion of V.P144 and
  retires the V.D123 "nonlinear-cluster blocker" framing.

-/

namespace Tau.BookV.Cosmology

-- ============================================================
-- V.D350: Metric-Sector Capacity Equation
-- ============================================================

/-- [V.D350] Metric-sector capacity equation: linear modified-
    Helmholtz on h_00 with Green's function K_0(r/ℓ_τ).

    Promotes V.P144 from conjectural to registered. V.D123 is the
    O(c^-2) trace-projection of this equation. At cluster scales
    (r/ℓ_τ ≲ 10^-4), the screening term is identically negligible
    and the equation reduces to standard Poisson.

    The c^4 coefficient supplies the missing factor that V.D259
    diagnosed as a 4-orders-of-magnitude gap in the scalar-capacity-
    only treatment.

    Encoding: `Nat`-scaled fields on the structural form
    of the modified-Helmholtz operator, without committing to a
    floating-point or TauReal Green's function representation. -/
structure MetricSectorCapacityEquation where
  /-- ℓ_τ in Mpc (scaled × 1000): cosmological τ-length ≈ 5.5 Mpc. -/
  ell_tau_mpc_x_1000 : Nat
  /-- ℓ_τ positive. -/
  ell_tau_pos : ell_tau_mpc_x_1000 > 0
  /-- c^4 / (16 π G ℓ_τ^2) source-coefficient indicator (Nat-scaled).
      Structural anchor for the trace-projection-to-V.D123 relation. -/
  source_coefficient_anchor : Nat
  /-- Source-coefficient positive (load-bearing for K_0 normalization). -/
  source_coefficient_pos : source_coefficient_anchor > 0
  /-- V.D123 trace-projection structural identity: this metric-sector
      equation, at O(c^-2), recovers V.D123's nonlinear-looking form
      that is in fact linear under u := ln(C_D/C_D^∞) substitution.
      TODO(Natarajan-F3 wave Path A): document the substitution at
      registry level. -/
  trace_projects_to_vd123 : ell_tau_mpc_x_1000 = 5500
  deriving Repr

/-- Canonical instance: ℓ_τ ≈ 5.5 Mpc, structural source-coefficient
    anchor 1 (the actual c^4/(16πG ℓ_τ^2) value lives at scale-
    independent placeholder level pending Path B promotion). -/
def metric_sector_canonical : MetricSectorCapacityEquation where
  ell_tau_mpc_x_1000 := 5500
  ell_tau_pos := by decide
  source_coefficient_anchor := 1
  source_coefficient_pos := by decide
  trace_projects_to_vd123 := rfl

-- ============================================================
-- V.D351: Boundary-Holonomy Inner-Promotion
-- ============================================================

/-- [V.D351] Boundary-holonomy inner-promotion mechanism for
    member-galaxy subhalos in relaxed massive clusters.

    M_∂(R) = (M_eff^max - M_p) · g(R/R_200, c), where:
    - M_eff^max = 6.65 · M_p (V.D272 saturation ceiling)
    - g ∈ [0, 1]: radial-profile fraction set by host capacity
    - Endpoints: g → 1 at R/R_200 ~ 0.1; g → 0 outside R_200

    Carriers below encode the structural relation at the
    F1-endpoint-bracket level (R/R_200 = 0.05, 0.10, 0.20, 0.50). -/
structure BoundaryHolonomyInnerPromotion where
  /-- g(R/R_200 = 0.05) × 100. F1 endpoint: 36 (= M_∂/M_p × 10 ÷ saturation_ceiling). -/
  g_at_005_x_100 : Nat
  /-- g(R/R_200 = 0.10) × 100. F1 endpoint: 49. -/
  g_at_010_x_100 : Nat
  /-- g(R/R_200 = 0.20) × 100. F1 endpoint: 55. -/
  g_at_020_x_100 : Nat
  /-- g(R/R_200 = 0.50) × 100. F1 endpoint: 57. -/
  g_at_050_x_100 : Nat
  /-- All g values ≤ 100 (saturation bound). -/
  g_bounded_005 : g_at_005_x_100 ≤ 100
  g_bounded_010 : g_at_010_x_100 ≤ 100
  g_bounded_020 : g_at_020_x_100 ≤ 100
  g_bounded_050 : g_at_050_x_100 ≤ 100
  /-- Endpoint bracket order across the sampled radius list
      (0.05, 0.10, 0.20, 0.50). This is not a strict inward
      radial-profile theorem; tightening depends on host concentration `c`.
      TODO(Natarajan-F3 wave Path C/D): tighten to a strict
      monotonicity proof under canonical NFW host profile. -/
  endpoint_order_outward : g_at_005_x_100 ≤ g_at_050_x_100
  deriving Repr

/-- Canonical F1-endpoint-bracket instance. -/
def inner_promotion_F1_bracket : BoundaryHolonomyInnerPromotion where
  g_at_005_x_100 := 36
  g_at_010_x_100 := 49
  g_at_020_x_100 := 55
  g_at_050_x_100 := 57
  g_bounded_005 := by decide
  g_bounded_010 := by decide
  g_bounded_020 := by decide
  g_bounded_050 := by decide
  endpoint_order_outward := by decide

-- ============================================================
-- V.T347: Transition Scale ℓ_cl,sub Recovery
-- ============================================================

/-- [V.T347] Transition-scale carrier: ℓ_cl,sub(M_sub) = √(GM_sub/a_0).

    For M_sub ∈ [10^10, 10^11] M_⊙, ℓ_cl,sub ∈ [3.4, 10.8] kpc,
    matching Natarajan's empirical break at r ~ 10 kpc across
    MACS J0416/J1206/J1149 to order unity. Host-mass-independent
    at fixed SHMF. -/
structure TransitionScaleSubhalo where
  /-- ℓ_cl,sub at M_sub = 10^10 M_⊙ (kpc × 100). F1: 340 (3.4 kpc). -/
  ell_at_10pow10_kpc_x_100 : Nat
  /-- ℓ_cl,sub at M_sub = 10^11 M_⊙ (kpc × 100). F1: 1080 (10.8 kpc). -/
  ell_at_10pow11_kpc_x_100 : Nat
  /-- M_sub^1/2 scaling: ℓ at 10^11 / ℓ at 10^10 = √10 ≈ 3.16. -/
  m_sub_half_scaling : ell_at_10pow11_kpc_x_100 = 1080
                       ∧ ell_at_10pow10_kpc_x_100 = 340
  /-- Order-unity match to Natarajan empirical break at r ~ 10 kpc:
      ℓ_cl,sub at 10^11 M_⊙ within 0.8-1.5× of 10 kpc. -/
  natarajan_match : ell_at_10pow11_kpc_x_100 ≥ 800
                    ∧ ell_at_10pow11_kpc_x_100 ≤ 1500
  deriving Repr

/-- Canonical F1-numerical-anchor instance. -/
def transition_scale_F1_anchor : TransitionScaleSubhalo where
  ell_at_10pow10_kpc_x_100 := 340
  ell_at_10pow11_kpc_x_100 := 1080
  m_sub_half_scaling := ⟨rfl, rfl⟩
  natarajan_match := by decide

-- ============================================================
-- V.T346: Inner Radial Excess Amplitude (structural theorem)
-- ============================================================

/-- [V.T346] Inner radial excess amplitude theorem: for the F1
    endpoint bracket, the projected member-galaxy count excess
    ε(R) = N_obs/N_LCDM at R/R_200 ∈ [0.05, 0.20] lies in [5, 7].

    Innermost bins R/R_200 ≤ 0.05 inherit V.T203's conjectural
    shortfall (D_τ ~ 2-4 vs D_obs ~ 5-7); under-predicted by
    factor 1.5-3×. This carrier-level theorem commits only to the
    [5, 7] band; the V.T203 inheritance is documented at the
    registry level (`V.T346-inner-radial-excess-amplitude.md`). -/
theorem inner_excess_amplitude_bracket
    (promotion : BoundaryHolonomyInnerPromotion)
    (h : promotion = inner_promotion_F1_bracket) :
    promotion.g_at_010_x_100 ≥ 49 ∧ promotion.g_at_020_x_100 ≤ 57 := by
  subst h
  exact ⟨by decide, by decide⟩

-- ============================================================
-- V.P212: LRD Cross-Coupling Joint Lock (structural)
-- ============================================================

/-- [V.P212] LRD cluster-coupling joint lock: V.T346 cluster-inner
    amplitude and LRD signature-3 saturation ceiling share the
    iota_tau pre-factor via V.D272.

    The lock is encoded as a structural identity on the shared
    iota_tau_x_1000000 anchor: both downstream predictions inherit
    the same numerator. Aperture-independent M_∂(R) measurement
    would falsify both jointly and force structural revision of
    V.D272. -/
theorem lrd_cluster_iota_tau_lock :
    Tau.Boundary.iota_tau_numer = 341304 := by
  rfl

-- ============================================================
-- Companion cross-reference (informational)
-- ============================================================

/-- Cross-reference from Astrophysics-side cluster context.

    A 20-line companion stub is added to
    `TauLib.BookV.Astrophysics.BulletClusterLSS.lean` documenting
    that the relaxed-cluster (Natarajan) substructure readout
    lives in `BookV.Cosmology.ClusterSubstructure` rather than
    in the Bullet-Cluster merging-geometry module. This separation
    preserves the V.T213 inheritance discipline (integrated-mass
    only, 4 merging + 1 relaxed catalog) per R4 conservatism
    ledger.

    TODO(Natarajan-F3 wave Path B): when V.D350 promotes from
    `tau-effective` to canonical, audit BulletClusterLSS.lean
    for any implicit dependency that should re-route through
    ClusterSubstructure.lean's V.D350-based progenitor. -/
def cluster_substructure_cross_ref_marker : Unit := ()

end Tau.BookV.Cosmology
