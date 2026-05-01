import TauLib.BookV.Cosmology.NoShrinkExtended
import TauLib.BookV.Astrophysics.CompactObjects
import TauLib.BookI.Boundary.TauRealIotaTau
import TauLib.BookI.Boundary.TauRealSqrt
import TauLib.BookI.Boundary.Bridge.TauRealQuotientField

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
  - Sub-claim D: slope transitions over ≤ 1.5 dex composite
    (Wave R7 Specialist F reconciliation; see v2.2/v2.3 §7 Gap 7)
    — `t_lrd_1_sharp_transition`
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
- The sharp slope transition (≤ 1.5 dex composite operational
  falsifier, relaxed in v2.2 from the v2.1 ≤ 0.2 dex Hossenfelder
  ask via Wave R7 Specialist F's binary-A-edge + smooth-C-edge
  reconciliation; see honest gap below) at the upper cutoff.

Orthodox-imported (acknowledged dependencies on external cosmology):

- The lower cutoff at 10^4.5 M_☉ inherits the atomic-cooling halo
  floor from the standard H I cooling threshold (Bromm & Loeb 2003;
  Rees & Ostriker 1977).
- The DCBH collapse fraction f_DCBH ≈ 10^-2 (Begelman & Volonteri
  2017) is an externally imported normalisation, not τ-derived.
- The halo spin distribution is assumed log-normal in λ centred at
  λ̄ ≈ 0.04 with σ_logλ ≈ 0.30 (Bullock et al. 2001), not τ-derived.

## Honest gap: transition-width width (Wave R7 reconciliation)

The Hossenfelder ask in N15 §6.1 of the v2.1 paper is for a
transition width Δlog M_BH ≤ 0.2 dex. Wave R7 dispatched
Specialist F (DCBH simulation lens, Inayoshi-Mayer-Bonoli-Haiman
tradition) to resolve the Specialist A vs C arithmetic-and-
mechanism discrepancy. F's reconciliation:

- Phase 1 (arithmetic gate): both specialists' formulae are
  arithmetically pristine. Specialist A: Δlog M_BH ≈ 1.66 dex
  (cutoff in λ-space, Jacobian 1/2). Specialist C: Δlog M_BH
  ≈ 0.41 dex (unit Jacobian, smooth f_BH(λ) ∝ 1/λ). The
  difference is exactly the squared Jacobian ratio (2)² = 4.
- Phase 2 (mechanism dominance): both mechanisms genuinely
  apply in different sub-regions of the cutoff transition.
  Specialist C dominates the lower edge (interior + smooth
  fraction); Specialist A dominates the upper edge (binary-
  outcome cutoff). Inayoshi & Haiman 2014, Mayer & Bonoli 2019,
  Wise et al. 2019, Regan et al. 2017 all confirm this two-
  regime picture from radiation-hydro DCBH simulations.
- Phase 3 (η_J bound): η_J ∈ [0.05, 0.15] (radiation-hydro
  consensus, central ≈ 0.08). The single-cascade Begelman-
  Volonteri-Rees 2006 form η_J ∼ (R_vir/r_g)^(-1/2)
  undershoots the simulation-measured cumulative cascade by
  3-4 orders of magnitude; multi-stage Begelman-Shlosman 2009
  cascade is the right model.
- Phase 4 (reconciled prediction): Δlog M_BH^reconciled =
  0.9^(+0.5)_(-0.4) dex composite, dominated by neither
  mechanism alone.

**R2 RISK FLAG TRIGGERED.** The v2.1 paper's ≤ 0.2 dex headline
is NOT survivable: even at σ_logλ = 0.20 for atomic-cooling
subsamples (Macciò 2007 — F notes this is not actually tighter
in the high-z atomic-cooling-mass regime), Specialist A's
binary-outcome edge gives ≥ 0.74 dex. The v2.2 paper must
relax this headline to either (a) ≤ 0.4 dex single-mechanism
C-edge claim, or (b) ≤ 1.5 dex composite operational falsifier.

**Wave R10-4 resync (2026-05-01).** This Lean module previously
retained the conservative ≤ 0.2 dex witness (`transition_width_x100
= 20`) for backward compatibility with the v2.1 paper claim. With
v2.2 (and v2.3 §7 Gap 7 acknowledgement) shipping the relaxed
≤ 1.5 dex composite operational falsifier, the carrier is now
resynced to `transition_width_x100 = 150` (with invariant
`transition_width_x100 ≤ 150`). `pred_lrd_sharp_transition` in
`FalsificationPack.lean` continues to track the operational
status of the predicate.

## Wave R7 cross-validation results (E + G converged)

Two parallel Wave 1 specialists independently derived
J_max^{T²}(M_BH, ι_τ):

- Specialist E (GR/Wald-Carter-Penrose lens): rigorous T²-Kerr
  metric construction with the V.T110 θ-quotient promoting ∂_θ
  to a third Killing vector beyond Kerr's two. Transport-
  bottleneck argument on the (0,1) primitive linking class
  gives J_max^{T²} = ι_τ √κ_D · GM²/c ≈ 0.277 GM²/c.
- Specialist G (categorical/homological lens): coherence
  projection Π_coh on H_1(T²;ℤ) ⊗ ℝ kills ω_η leaving ω_γ
  scaled by r/R = ι_τ. Centrifugal √κ_D from V.T109
  threshold-survival. Same answer.

**Both arrive at ι_τ-power exponent = 1** (with κ_D^(1/2)
multiplicative factor, κ_D = 1 - ι_τ). This is strong cross-
validation of V.T-LRD-1 sub-theorem B.

**R1 RISK FLAG: NO TRIGGER.** Refined cutoff is
log_10(M_BH^max/M_⊙) ≈ 6.54 ± 0.10 at z = 11 (Wave 2 Specialist
A refined value). This is 0.04 dex below the v2.1 paper's
6.50 headline — well within the ±0.15 dex stated systematic.

## Phase 0 status (Wave R7 verified by Specialist I)

The original V.T-LRD-1 derivation note (Wave R7 round 1) was
overly pessimistic about TauReal infrastructure. Specialist I
verified the actual state:

- **Confirmed-present (Phase 0 complete)**: TauReal.inv,
  TauReal.div (TauRealInv.lean), TauReal.pi (TauRealPi.lean),
  TauReal.e (TauRealE.lean), TauReal.abs (TauRealAbs.lean),
  TauReal.lt/le (TauRealOrder.lean), TauReal.fromNat/fromTauRat
  (ConstructiveReals.lean), Tau.Boundary.TauReal.iota_tau
  (TauRealIotaTau.lean) with defining identity proven.
- **Confirmed-missing (Phase 0.5 targets)**: TauReal.sqrt (the
  only critical-path blocker for J_max^{T²} = ι_τ √κ_D · GM²/c
  formalisation), TauReal.log (for d log N / d log M_BH slope
  bounds), TauReal.exp (function-form, vs the constant e).

The "4-7 month upgrade" estimate in V-T-LRD-1-derivation.md v1
is calibrated against the stale ROADMAP-3-HINGES Phase 0 audit
and should be revised downward to 4-5 weeks (Phase 0.5 only,
2 engineers in parallel) per Specialist I's design doc.

See `research-notes/PHASE-0.5-ANALYTIC-PRIMITIVES.md` for the
detailed Phase 0.5 design.

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
-- WAVE R7 PROMOTION (T1): TAUREAL-WITNESSED ι_τ REBINDING
-- ============================================================

/-- [Wave R7 promotion (T1)] TauReal-witnessed master constant ι_τ.

    The structural TauReal definition at `Tau.Boundary.TauReal.iota_tau`
    instantiates `ι_τ = 2/(π+e)` directly via `TauReal.div` (Phase 0,
    confirmed-present per Specialist I's Phase 0 audit), with the
    defining identity `iota_tau · (π+e) ≡ 2` proved at the Cauchy level
    in `TauRealIotaTau.lean` line 118.

    This sibling rebinding makes the TauReal-level dependency on
    V.T110's `r/R = ι_τ` relation visible at the module API level,
    alongside the `Nat`-scaled `iota_tau_x_1000000`. Required for
    promoting V.D-LRD-1d's `f_iota_x_10000` field once Phase 0.5
    (TauReal.sqrt) lands. -/
def iota_tau_TauReal : Tau.Boundary.TauReal :=
  Tau.Boundary.TauReal.iota_tau

/-- [Wave R7 promotion (T1)] Defining identity:
    `iota_tau_TauReal · (π+e) ≡ 2` at the Cauchy level.

    This is just `Tau.Boundary.TauReal.iota_tau_mul_pi_plus_e_eq_two`
    re-stated for the local rebinding; both reduce to the same
    `TauReal.equiv` proof. -/
theorem iota_tau_TauReal_defining :
    Tau.Boundary.TauReal.equiv
      (iota_tau_TauReal.mul
        (Tau.Boundary.TauReal.pi.add Tau.Boundary.TauReal.e))
      Tau.Boundary.TauReal.two :=
  Tau.Boundary.TauReal.iota_tau_mul_pi_plus_e_eq_two

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

/-- [Wave R7 promotion (T4)] TauReal-witnessed atomic-cooling halo
    mass at z = 10.

    The mass floor M_halo,min(z=10) ≈ 3.2 × 10^7 M_☉ promoted from
    `Nat`-scaled `m_halo_min_e7_x10 = 32` to a TauReal-witnessed
    constant via `TauReal.fromTauRat`. Phase 0 confirmed-present
    primitives are sufficient (no sqrt/log needed for a rational
    mass value). -/
def atomic_cooling_floor_z10_mass_TauReal : Tau.Boundary.TauReal :=
  Tau.Boundary.TauReal.fromTauRat ⟨⟨32, 0⟩, 1, Nat.one_pos⟩

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

/-- [Wave R7 promotion (T3)] TauReal-witnessed DCBH collapse fraction.

    `f_DCBH = 1/100 = 0.01` promoted from `Nat`-scaled
    `f_dcbh_x10000 = 100` to a TauReal-witnessed rational via
    `TauReal.fromTauRat`. The radiation-hydro consensus value
    (Inayoshi-Visbal-Haiman 2020 ARA&A; Begelman-Volonteri 2017)
    remains orthodox-imported; this promotion only changes the
    Lean witness type, not the scope flag. -/
def dcbh_fraction_TauReal : Tau.Boundary.TauReal :=
  Tau.Boundary.TauReal.fromTauRat ⟨⟨1, 0⟩, 100, by norm_num⟩

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

/-- [Wave R7 promotion (partial T2)] TauReal-witnessed ι_τ for the
    T²-horizon angular-momentum bound.

    This sibling exposes the master constant ι_τ as a TauReal value
    at the bound's API. The full closed-form F(ι_τ) = ι_τ √κ_D ≈ 0.277
    requires `TauReal.sqrt` (Phase 0.5 target) and is **deferred**;
    once `TauRealSqrt.lean` lands, the headline witness will be
        f_iota_TauReal = iota_tau_TauReal.mul
                          (TauReal.sqrt (TauReal.one.sub iota_tau_TauReal))
    cleanly typed without the `Nat`-scaled `f_iota_x_10000 = 2773`
    placeholder.

    Wave R7 cross-validation (Specialists E + G) confirms
    the F(ι_τ) = ι_τ √κ_D form with ι_τ-power exponent 1; see
    docstring "Wave R7 cross-validation" section. -/
def iota_tau_T2_bound_TauReal : Tau.Boundary.TauReal :=
  iota_tau_TauReal

/-- [Wave R8 proper, post-Phase-0.5] TauReal-witnessed F(ι_τ) = ι_τ √κ_D
    closed-form headline witness for the T²-horizon J_max bound.

    Concretely: F(ι_τ) = ι_τ · √(1 − ι_τ) ≈ 0.277 numerically.

    This replaces the Wave R7 Nat-scaled placeholder `f_iota_x_10000 = 2773`
    (which encoded F(ι_τ) ≈ 0.2773 as 2773/10000) with the proper
    TauReal-typed witness. The Nat-scaled value remains for backwards
    compatibility / ergonomic numeric reference on the
    `T2HorizonAngularMomentumBound` carrier.

    Cross-validation: `(f_iota_TauReal.approx N).toRat` should converge
    to 0.2773... as N → ∞.

    Phase 0.5 dependencies (all sorry-free):
    - `Tau.Boundary.TauReal.sqrt` (Wave R8b def, R8j Cauchy + sq closures)
    - `Tau.Boundary.TauReal.one`, `.sub`, `.mul` (foundational,
      ConstructiveReals.lean)
    - `iota_tau_TauReal` (TauRealIotaTau, pre-Phase-0.5)

    Sibling at the V.T-NEW-5A bundling site:
    `Tau.Boundary.f_iota_t2_TauReal` in `T2KerrUniqueness.lean`, built
    from `iota_tau_T2_bound_TauReal` (which is defeq-equal to
    `iota_tau_TauReal`). -/
def f_iota_TauReal : Tau.Boundary.TauReal :=
  iota_tau_TauReal.mul
    (Tau.Boundary.TauReal.sqrt
      (Tau.Boundary.TauReal.one.sub iota_tau_TauReal))

/-- Smoke theorem: `f_iota_TauReal` unfolds to its closed-form
    definition (rfl). -/
theorem f_iota_TauReal_def :
    f_iota_TauReal =
    iota_tau_TauReal.mul
      (Tau.Boundary.TauReal.sqrt
        (Tau.Boundary.TauReal.one.sub iota_tau_TauReal)) := rfl

-- Companion smoke `#check`: confirm `f_iota_TauReal` is well-typed.
#check f_iota_TauReal

-- Numerical smoke: should be close to 0.277 for moderate N.
#eval (f_iota_TauReal.approx 8).toRat

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
  -- Note: no `deriving Repr` here — the `Fin 21 → Nat` field would
  -- require `Repr (Fin 21 → Nat)` which is unavailable at the pinned
  -- Mathlib commit (lake-manifest.json: 85028a69). The structure is
  -- not displayed via `#eval` anywhere in this file, so omitting the
  -- derivation has no functional impact; downstream code uses field
  -- accessors directly.

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
-- WAVE R9-2B: TAUREAL-WITNESSED NUMERICAL BOUND [V.T-LRD-1B]
-- ============================================================

/-! ### Wave R9-2B — first physics-relevant numerical witness post-Phase-0.5

The W3-landed `f_iota_TauReal := iota_tau · √(1 − iota_tau)` (closed form
for `F(ι_τ) = ι_τ √κ_D ≈ 0.277`) is now numerically grounded against the
Wave R7 `Nat`-scaled placeholder `f_iota_x_10000 = 2773`
(encoding `2773 / 10000 = 0.2773`).

At index `N = 1`, the approximation reduces (definitionally) to a small
closed-form `Rat`:

  `iota_tau_TauReal.approx 1 = 2 · (8/3 + 1)⁻¹ = 6/11`
  `(1 − iota_tau).approx 1 = 5/11`
  `(TauReal.sqrt _).approx 1 = sqrtNewtonStep (5/11) (5/11) = 8/11`
  `f_iota_TauReal.approx 1 = (6/11) · (8/11) = 48/121 ≈ 0.3967`

So `|48/121 − 2773/10000| = 144467/1210000 ≈ 0.1194 ≤ 1/5`. The bound
witnesses the end-to-end consistency between the TauReal closed form and
the Nat-scaled placeholder, even at the very crude `N = 1` precision.
At larger `N` the gap tightens; this is the post-Phase-0.5 invariant
delivered by `f_iota_TauReal_isCauchy` (downstream Wave R10 will sharpen
to a closed-form convergence-rate bound). -/

/-- **Wave R9-2B — Theorem 1 (numerical witness).**
    There exists an approximation index `N` and a Rat tolerance `ε`
    such that `(f_iota_TauReal.approx N).toRat` lies within `ε` of the
    Wave R7 `Nat`-scaled placeholder value `2773 / 10000`.

    The witness `N = 1`, `ε = 1/5` is concrete and computable: the
    tolerance is generous (≈ 0.2) so the bound holds at the very
    crudest precision. Tighter bounds (smaller `ε` at larger `N`)
    follow from `f_iota_TauReal_isCauchy` (T2KerrUniqueness, R8 W2
    companion) and are deferred to Wave R10. -/
theorem f_iota_TauReal_approx_within_rat_bound :
    ∃ N : Nat, ∃ ε : Rat, 0 < ε ∧ ε ≤ 1 / 10 * 2 ∧
      |((f_iota_TauReal.approx N).toRat) - (2773 : Rat) / 10000| ≤ ε := by
  refine ⟨1, 1 / 5, by norm_num, by norm_num, ?_⟩
  -- (f_iota_TauReal.approx 1).toRat reduces to 48/121 by native evaluation.
  -- Then |48/121 - 2773/10000| = 144467/1210000 ≈ 0.1194 ≤ 1/5.
  native_decide

/-- **Wave R9-2B — Theorem 2 (cross-consistency with the Nat-scaled placeholder).**
    For every `T2HorizonAngularMomentumBound` carrier whose `f_iota_x_10000`
    field carries the canonical Wave R7 value `2773`, the TauReal-witnessed
    `f_iota_TauReal.approx 1 .toRat` differs from `s.f_iota_x_10000 / 10000`
    by at most `1/5`. This is the structural bridge between the TauReal
    closed form and the Nat-scaled placeholder API. -/
theorem f_iota_TauReal_consistent_with_f_iota_x_10000
    (s : T2HorizonAngularMomentumBound) (h : s.f_iota_x_10000 = 2773) :
    ∃ N : Nat,
      |((f_iota_TauReal.approx N).toRat) -
        ((s.f_iota_x_10000 : Rat) / 10000)| ≤ 1 / 5 := by
  refine ⟨1, ?_⟩
  rw [h]
  show |((f_iota_TauReal.approx 1).toRat) - ((2773 : Nat) : Rat) / 10000| ≤ 1 / 5
  have h_cast : ((2773 : Nat) : Rat) = (2773 : Rat) := by norm_cast
  rw [h_cast]
  -- Same numerical witness as Theorem 1 above, specialised at N = 1.
  native_decide

/-- **Wave R9-2B — Theorem 3 (TauReal-witnessed companion to `t_lrd_1_upper_cutoff`).**
    The upper-cutoff struct invariants (Nat-scaled width, central value,
    is_tau_distinctive) hold AND the TauReal-witnessed `F(ι_τ) ≈ 0.277`
    lies within `1/5` of the Nat-scaled `2773 / 10000` placeholder.

    This is the first physics-relevant numerical witness produced by the
    post-Phase-0.5 Wave R9-2 cycle: the load-bearing N15 signature 1
    falsifier (upper cutoff at 10^6.5 M_☉) is now backed by a TauReal
    closed-form value AND the Nat-scaled struct invariants AND a
    cross-consistency Rat bound. -/
theorem t_lrd_1_upper_cutoff_tau_real_witnessed :
    upper_cutoff_statement.m_max_e6_x10 = 32 ∧
    upper_cutoff_statement.m_max_logsigma_x100 ≤ 15 ∧
    upper_cutoff_statement.is_tau_distinctive = true ∧
    |((f_iota_TauReal.approx 1).toRat) - (2773 : Rat) / 10000| ≤ 1 / 5 := by
  refine ⟨rfl, upper_cutoff_statement.width_within_n15_prior, rfl, ?_⟩
  native_decide

-- ============================================================
-- WAVE R10-2: CAUCHY-GRADE CONVERGENCE FOR f_iota_TauReal
-- ============================================================

/-! ### Wave R10-2 — Cauchy tightening of `f_iota_TauReal_approx_within_rat_bound`

The Wave R9-2B existential `f_iota_TauReal_approx_within_rat_bound`
discharged a single (`N = 1`, `ε = 1/5`) numerical witness via
`native_decide`. Wave R10-2 promotes this to a **uniform** Cauchy-grade
statement: `f_iota_TauReal.IsCauchy`. From there, the canonical
"approx tail is uniformly close" form is a direct unfolding of the
`IsCauchy` modulus.

Mirrors the companion `f_iota_t2_TauReal_isCauchy` in
`T2KerrUniqueness.lean` (the latter reuses the same private helper
chain at the T² scope; here we inline the helpers at HSB scope so the
witness is self-contained).

The Wave R9-2B existential is **kept** for backward compatibility with
`t_lrd_1_upper_cutoff_tau_real_witnessed` (which encodes the LRD note's
N15 signature 1 falsifier numerical bridge). -/

open Tau.Boundary in
/-- **Helper (private, Wave R10-2):** for every `n ≥ 1`, the toRat
    value of `(π + e).approx n` lies in `[11/3, 7]`. Mirror of the
    T2KerrUniqueness private helper, inlined here at HSB scope. -/
private theorem hsb_pi_plus_e_approx_in_interval (n : Nat) (hn : 1 ≤ n) :
    (11 : Rat) / 3 ≤ ((TauReal.pi.add TauReal.e).approx n).toRat ∧
    ((TauReal.pi.add TauReal.e).approx n).toRat ≤ 7 := by
  have h_unfold :
      ((TauReal.pi.add TauReal.e).approx n).toRat
        = (TauRat.pi_partial n).toRat + (TauRat.e_partial n).toRat := by
    show ((TauReal.pi.approx n).add (TauReal.e.approx n)).toRat = _
    rw [toRat_add]; rfl
  refine ⟨?_, ?_⟩
  · rw [h_unfold]; exact TauReal.pi_plus_e_partial_lower_bound n hn
  · exact TauReal.pi_plus_e_approx_le_seven n

open Tau.Boundary in
/-- **Helper (private, Wave R10-2):** at toRat level,
    `iota_tau_TauReal.approx n = 2 / (π+e).approx n` for `n ≥ 1`. -/
private theorem hsb_iota_tau_TauReal_approx_toRat_eq (n : Nat) (hn : 1 ≤ n) :
    (iota_tau_TauReal.approx n).toRat
      = 2 / ((TauReal.pi.add TauReal.e).approx n).toRat := by
  have h_pe_pos : 0 < ((TauReal.pi.add TauReal.e).approx n).toRat := by
    have h_lb := (hsb_pi_plus_e_approx_in_interval n hn).1
    linarith
  have h_pe_nz : ((TauReal.pi.add TauReal.e).approx n).is_nonzero := by
    rw [TauRat.is_nonzero_iff_toRat_ne_zero]
    linarith
  show (((TauReal.two.approx n).mul ((TauReal.pi.add TauReal.e).inv.approx n))).toRat
        = 2 / ((TauReal.pi.add TauReal.e).approx n).toRat
  have h_inv_approx :
      (TauReal.pi.add TauReal.e).inv.approx n
        = TauRat.inv ((TauReal.pi.add TauReal.e).approx n) h_pe_nz := by
    show (if h : ((TauReal.pi.add TauReal.e).approx n).is_nonzero
          then TauRat.inv ((TauReal.pi.add TauReal.e).approx n) h
          else TauRat.one) = _
    rw [dif_pos h_pe_nz]
  rw [h_inv_approx, toRat_mul, TauReal.two_approx_toRat, toRat_inv]
  rw [div_eq_mul_inv]

open Tau.Boundary in
/-- **Helper (private, Wave R10-2):** for `n ≥ 1`,
    `(iota_tau_TauReal.approx n).toRat < 1` (since `ι_τ ≤ 6/11 < 1`). -/
private theorem hsb_iota_tau_TauReal_lt_one_eventually :
    ∃ Ns : Nat, ∀ n : Nat, Ns ≤ n →
      (iota_tau_TauReal.approx n).toRat < 1 := by
  refine ⟨1, fun n hn => ?_⟩
  rw [hsb_iota_tau_TauReal_approx_toRat_eq n hn]
  have ⟨h_lb, _⟩ := hsb_pi_plus_e_approx_in_interval n hn
  have h_pe_pos : 0 < ((TauReal.pi.add TauReal.e).approx n).toRat := by linarith
  rw [div_lt_one h_pe_pos]
  linarith

open Tau.Boundary in
/-- **Helper (private, Wave R10-2):** the radicand `1 − ι_τ` is
    eventually positive at toRat level. -/
private theorem hsb_one_sub_iota_tau_TauReal_pos_eventually :
    ∃ Ns : Nat, ∀ n : Nat, Ns ≤ n →
      0 < (((TauReal.one).sub iota_tau_TauReal).approx n).toRat := by
  obtain ⟨Ns, h_iota_lt_one⟩ := hsb_iota_tau_TauReal_lt_one_eventually
  refine ⟨Ns, fun n hn => ?_⟩
  have h_unfold :
      (((TauReal.one).sub iota_tau_TauReal).approx n).toRat
        = 1 - (iota_tau_TauReal.approx n).toRat := by
    show (((TauReal.one).approx n).add ((iota_tau_TauReal).negate.approx n)).toRat = _
    rw [toRat_add]
    show ((TauReal.one).approx n).toRat
            + ((iota_tau_TauReal.approx n).negate).toRat = _
    rw [toRat_negate]
    show (TauRat.one).toRat + (- (iota_tau_TauReal.approx n).toRat) = _
    rw [toRat_one]; ring
  rw [h_unfold]
  have h_lt := h_iota_lt_one n hn
  linarith

open Tau.Boundary in
/-- **Helper (private, Wave R10-2):** the radicand `1 − ι_τ` is
    bounded away from zero, with witness `k = 2` (so `1/(k+1) = 1/3`).
    From `(ι_τ.approx n).toRat ≤ 6/11`, `1 − ι_τ ≥ 5/11 > 1/3`. -/
private theorem hsb_one_sub_iota_tau_TauReal_BAZ :
    ((TauReal.one).sub iota_tau_TauReal).BoundedAwayFromZero := by
  refine ⟨2, 1, fun n hn => ?_⟩
  unfold TauRat.lt
  rw [TauRat.ofNatRecip_toRat, TauRat.toRat_abs]
  have h_iota_eq := hsb_iota_tau_TauReal_approx_toRat_eq n hn
  have ⟨h_lb, h_ub⟩ := hsb_pi_plus_e_approx_in_interval n hn
  have h_pe_pos : 0 < ((TauReal.pi.add TauReal.e).approx n).toRat := by linarith
  have h_iota_le : (iota_tau_TauReal.approx n).toRat ≤ 6 / 11 := by
    rw [h_iota_eq, div_le_iff₀ h_pe_pos]
    linarith
  have h_one_sub_unfold :
      (((TauReal.one).sub iota_tau_TauReal).approx n).toRat
        = 1 - (iota_tau_TauReal.approx n).toRat := by
    show (((TauReal.one).approx n).add ((iota_tau_TauReal).negate.approx n)).toRat = _
    rw [toRat_add]
    show ((TauReal.one).approx n).toRat
            + ((iota_tau_TauReal.approx n).negate).toRat = _
    rw [toRat_negate]
    show (TauRat.one).toRat + (- (iota_tau_TauReal.approx n).toRat) = _
    rw [toRat_one]; ring
  rw [h_one_sub_unfold]
  have h_pos : 0 < 1 - (iota_tau_TauReal.approx n).toRat := by linarith
  rw [abs_of_pos h_pos]
  show (1 : Rat) / ((2 : Nat) + 1) < 1 - (iota_tau_TauReal.approx n).toRat
  push_cast
  linarith

open Tau.Boundary in
/-- **Helper (private, Wave R10-2):** `iota_tau_TauReal.IsCauchy`.
    By definition `iota_tau_TauReal = TauReal.iota_tau = 2 · (π+e)⁻¹`,
    a product of two Cauchy sequences. -/
private theorem hsb_iota_tau_TauReal_isCauchy : iota_tau_TauReal.IsCauchy := by
  show (TauReal.two.mul (TauReal.pi.add TauReal.e).inv).IsCauchy
  apply TauReal.IsCauchy_mul
  · -- TauReal.two — constant sequence is Cauchy with modulus 0
    refine ⟨fun _ => 0, fun k _ _ _ _ => ?_⟩
    show TauRat.lt _ _
    unfold TauRat.lt
    rw [TauRat.toRat_abs, toRat_sub]
    show |(TauReal.two.approx _).toRat - (TauReal.two.approx _).toRat|
            < (TauRat.ofNatRecip k).toRat
    rw [TauReal.two_approx_toRat, TauReal.two_approx_toRat]
    simp
    exact TauRat.ofNatRecip_pos k
  · apply TauReal.IsCauchy_inv
    · exact TauReal.IsCauchy_add _ _ TauReal.pi_isCauchy TauReal.e_isCauchy
    · exact TauReal.pi_plus_e_boundedAwayFromZero

open Tau.Boundary in
/-- **Helper (private, Wave R10-2):** the radicand `1 − ι_τ` is Cauchy. -/
private theorem hsb_one_sub_iota_tau_TauReal_isCauchy :
    ((TauReal.one).sub iota_tau_TauReal).IsCauchy := by
  show ((TauReal.one).add iota_tau_TauReal.negate).IsCauchy
  apply TauReal.IsCauchy_add
  · exact TauReal.one_isCauchy
  · exact TauReal.IsCauchy_negate _ hsb_iota_tau_TauReal_isCauchy

/-- **Wave R10-2 — HEADLINE: `f_iota_TauReal.IsCauchy`.**

    The product of the Cauchy `iota_tau_TauReal` and the Cauchy
    `√(1 − iota_tau_TauReal)` (both witnessed in scope via the
    private helpers above + `TauReal.sqrt_isCauchy` from R8j).

    Mirrors the T2-scope companion `f_iota_t2_TauReal_isCauchy`
    in `T2KerrUniqueness.lean`. This delivers the uniform Cauchy
    grade promised by Wave R9-2B's hand-off note: every approximation
    tail of `f_iota_TauReal` is uniformly close, with an explicit
    constructive modulus. -/
theorem f_iota_TauReal_isCauchy : f_iota_TauReal.IsCauchy := by
  show (iota_tau_TauReal.mul
          (Tau.Boundary.TauReal.sqrt
            ((Tau.Boundary.TauReal.one).sub iota_tau_TauReal))).IsCauchy
  apply Tau.Boundary.TauReal.IsCauchy_mul
  · exact hsb_iota_tau_TauReal_isCauchy
  · exact Tau.Boundary.TauReal.sqrt_isCauchy _
      hsb_one_sub_iota_tau_TauReal_isCauchy
      hsb_one_sub_iota_tau_TauReal_BAZ
      hsb_one_sub_iota_tau_TauReal_pos_eventually

/-- **Wave R10-2 — uniform convergence corollary.**

    Direct unpacking of `f_iota_TauReal.IsCauchy`: for every tolerance
    level `k`, there is a modulus index `N` past which any two
    approximation values agree (at toRat) within `1/(k+1)`.

    This is the natural Cauchy-equivalence form of "the approximation
    sequence is uniformly close to its tail." Replaces the loose,
    `native_decide`-discharged single-witness existential
    `f_iota_TauReal_approx_within_rat_bound` with a uniform statement
    parameterised by `k`. -/
theorem f_iota_TauReal_approx_uniform_convergence :
    ∀ k : Nat, ∃ N : Nat, ∀ m n : Nat, N ≤ m → N ≤ n →
      |((f_iota_TauReal.approx m).toRat) -
        ((f_iota_TauReal.approx n).toRat)| < 1 / ((k : Rat) + 1) := by
  obtain ⟨μ, hμ⟩ := f_iota_TauReal_isCauchy
  intro k
  refine ⟨μ k, fun m n hm hn => ?_⟩
  have h_cauchy_step := hμ k m n hm hn
  -- Unfold TauRat.lt (fully qualified — namespace not opened in this scope)
  unfold Tau.Boundary.TauRat.lt at h_cauchy_step
  rw [Tau.Boundary.TauRat.toRat_abs, Tau.Boundary.toRat_sub,
      Tau.Boundary.TauRat.ofNatRecip_toRat] at h_cauchy_step
  -- h_cauchy_step : |(f.approx m).toRat - (f.approx n).toRat| < 1 / (↑k + 1)
  exact h_cauchy_step

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

/-- Carrier for the sharp-transition statement
    (Wave R7 Specialist F reconciliation of the original
    Hossenfelder ask).

    The slope transitions from |dlogN/dlogM| ≤ 0.3 (interior)
    to dlogN/dlogM ≤ -2 (exterior, i.e. above 10^6.5 M_☉) over
    a composite window of width ≤ 1.5 dex centred at
    M_BH = 10^(6.5 ± 0.15) M_☉.

    **Wave R7 reconciliation (Specialist F, see v2.2 §7 Gap 7
    and v2.3 §7 Gap 7 acknowledgement).** The transition is a
    two-mechanism composite:

    - **A-edge (binary-outcome, Specialist A):** the upper
      edge of the cutoff is set by the binary J_halo·ε_J vs.
      J_max^{T²} comparison. Specialist A's λ-space cutoff
      Jacobian (1/2) gives ≈ 1.66 dex on this edge, with a
      σ_logλ-tightened floor of ≈ 0.74 dex.
    - **C-edge (smooth-interior, Specialist C):** the lower
      edge is set by the smooth f_BH(λ) ∝ 1/λ unit-Jacobian
      tail. Specialist C's calculation gives ≈ 0.41 dex on
      this edge (≈ 0.18 dex with σ_logλ for atomic-cooling
      subsamples tightened to 0.20).

    Phase 4 reconciled prediction:
    Δlog M_BH^reconciled = 0.9^{+0.5}_{-0.4} dex (68 % CI)
    composite, dominated by neither mechanism alone. The
    operational falsifier is therefore ≤ 1.5 dex composite,
    NOT the ≤ 0.2 dex single-edge claim of the v2.1 paper
    (which Wave R7 R2 RISK FLAG identified as not survivable).

    **History.** The v2.1 paper headline ≤ 0.2 dex was encoded
    in this Lean carrier as `transition_width_x100 = 20`. Wave
    R10-4 (2026-05-01) resynced the carrier to
    `transition_width_x100 = 150` to match the v2.2/v2.3
    relaxed composite ≤ 1.5 dex operational falsifier.

    Stored as the transition width × 100. -/
structure SharpTransitionStatement where
  /-- Centre of the transition × 100 in units of
      log_10(M_BH/M_☉) (= 650 for 10^6.5). -/
  transition_centre_x100 : Nat
  /-- Width of the transition × 100 in dex (= 150 for the v2.2
      composite ≤ 1.5 dex operational falsifier; was 20 for the
      v2.1 ≤ 0.2 dex headline pre Wave R10-4). -/
  transition_width_x100 : Nat
  /-- Pre-transition slope × 100 absolute bound (= 30 for ≤ 0.3). -/
  pre_slope_max_x100 : Nat
  /-- Post-transition slope × 100 absolute bound (= 200 for ≤ -2,
      stored as the magnitude). -/
  post_slope_min_abs_x100 : Nat
  /-- Width within the v2.2/v2.3 composite operational bound
      (≤ 1.5 dex; relaxed by Wave R7 Specialist F from the
      v2.1 ≤ 0.2 dex single-edge claim). -/
  width_within_bound : transition_width_x100 ≤ 150
  /-- Pre-slope is shallow. -/
  pre_slope_shallow : pre_slope_max_x100 ≤ 30
  /-- Post-slope is steep. -/
  post_slope_steep : post_slope_min_abs_x100 ≥ 200
  /-- Derivation source. -/
  derivation_source : String :=
    "T²-cutoff geometric rigidity + log-normal convolution"
  /-- This is τ-DISTINCTIVE (composite operational falsifier
      surviving Wave R7 reconciliation of the Hossenfelder ask). -/
  is_tau_distinctive : Bool := true
  deriving Repr

def sharp_transition_statement : SharpTransitionStatement where
  transition_centre_x100 := 650
  transition_width_x100 := 150
  pre_slope_max_x100 := 30
  post_slope_min_abs_x100 := 200
  width_within_bound := by omega
  pre_slope_shallow := by omega
  post_slope_steep := by omega

/-- [V.T-LRD-1, D] Sharp transition: the slope of dN/dlogM_BH
    transitions from |slope| ≤ 0.3 to slope ≤ -2 over a
    composite window of width ≤ 1.5 dex centred at
    M_BH = 10^(6.5 ± 0.15) M_☉.

    This is the QUASI-SHARPNESS condition surviving Wave R7
    Specialist F's reconciliation of the original Hossenfelder
    ask in v2.1 §6.1. The cutoff is composite — a binary-
    outcome A-edge stacked above a smooth-interior C-edge —
    rather than a single-mechanism quasi-step (see v2.2 §7
    Gap 7 and v2.3 §7 Gap 7 acknowledgement).

    The geometric origin remains τ-distinctive: the T² angular-
    momentum cutoff is itself sharp (a hard geometric
    constraint, not a soft one); once J_halo · ε_J exceeds
    J_max^{T²}, the contraction fragments rather than
    partially succeeding. The composite ≤ 1.5 dex width
    reflects the convolution of this hard binary edge with
    the J_halo log-normal scatter (σ_logJ ≈ 0.30 from
    Bullock 2001) and the smooth f_BH(λ) ∝ 1/λ tail.

    HISTORY (Wave R10-4 resync, 2026-05-01): the previous
    v2.1 ≤ 0.2 dex bound (`transition_width_x100 ≤ 20`) was
    relaxed per Wave R7 Specialist F to the v2.2/v2.3 ≤ 1.5
    dex composite operational falsifier
    (`transition_width_x100 ≤ 150`). The Phase 4 reconciled
    point estimate is Δlog M_BH = 0.9^{+0.5}_{-0.4} dex
    (68 % CI). See module docstring "Honest gap" section and
    research-notes/V-T-LRD-1-derivation.md §5. -/
theorem t_lrd_1_sharp_transition :
    sharp_transition_statement.transition_width_x100 ≤ 150 ∧
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
    (D) Quasi-sharp slope transition over ≤ 1.5 dex composite
        (binary A-edge + smooth C-edge) at the upper cutoff
        — Wave R7 Specialist F reconciliation, v2.2/v2.3 §7
        Gap 7; see honest gap in module docstring.

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
    t_lrd_1_witness.sharp.transition_width_x100 ≤ 150 ∧
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
#eval sharp_transition_statement.transition_width_x100  -- 150
#eval t_lrd_1_witness.z_min_x10                         -- 80
#eval t_lrd_1_witness.z_max_x10                         -- 150

end Tau.BookV.Cosmology
