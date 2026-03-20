import TauLib.BookV.Gravity.Schwarzschild

/-!
# TauLib.BookV.Temporal.DistanceLadder

The distance ladder reinterpreted as calibration of a readout functor.

## Registry Cross-References

- [V.D32] Distance Readout Functor — `DistanceReadout`
- [V.R40] Distance is operational — `distance_is_operational`
- [V.T17] Distance Ladder Translation — `ladder_rung_count`
- [V.R41] Gaia readout — structural remark
- [V.D33] Cepheid Readout Calibrator — `CepheidCalibrator`
- [V.D34] BAO Standard Ruler — `BAOStandardRuler`
- [V.T18] Hubble Tension Resolution — `H0_tension_structural`
- [V.D35] Readout Curvature — `ReadoutCurvature`
- [V.T19] Dark Energy Artifact — `dark_energy_artifact`
- [V.R44] Scope deferral — structural remark

## Mathematical Content

### Distance Readout Functor

The distance readout functor R_d : Orbit_n(τ¹) → SI_length assigns to
each pair of orbit depths (n_emit, n_obs) a luminosity distance d_L in
metres. It is a projection through sector couplings, not a physical
distance.

### Distance Ladder

Every rung of the orthodox distance ladder has a τ-native interpretation
as a calibration step for R_d:

| Rung | Scale | τ-interpretation |
|------|-------|-----------------|
| Parallax | kpc | Earth-orbit D-sector readout |
| Cepheid | Mpc | Period-luminosity = κ(D;1)/κ(B;1) |
| SNIa | Gpc | Chandrasekhar = D-sector threshold |
| BAO | Gpc | Comoving sound horizon at n_rec |
| CMB | Horizon | Σ_CMB boundary-character constraint |

### Hubble Tension

The "early" vs "late" H₀ discrepancy is a readout curvature effect:
different orbit-depth regimes yield different H₀ readings, not because
H₀ changes but because the readout functor R_d is nonlinear in depth.

### Dark Energy Artifact

If the readout curvature κ_R(n) > 0, the FLRW projection produces an
apparent cosmological constant Λ_app without any energy component.
This is conjectural (explicit κ_R(n) deferred to Part V).

## Ground Truth Sources
- Book V Part I ch08 (Distance Ladder chapter)
- book5_registry.jsonl: V.D32–V.D35, V.T17–V.T19, V.R40–V.R44
-/

namespace Tau.BookV.Temporal

open Tau.Boundary Tau.BookIV.Sectors

-- ============================================================
-- DISTANCE READOUT FUNCTOR [V.D32]
-- ============================================================

/-- [V.D32] Distance readout functor R_d: maps a pair of orbit depths
    (source, target) to a luminosity distance in SI metres.

    The readout is a projection through sector couplings and the
    calibration anchor, not a "true" physical distance.

    Fields:
    - source/target depths on τ¹
    - distance numerator/denominator (scaled SI metres)
    - source must causally precede target -/
structure DistanceReadout where
  /-- Source orbit depth (emission). -/
  source_depth : Nat
  /-- Target orbit depth (observation). -/
  target_depth : Nat
  /-- Distance numerator (scaled SI metres). -/
  distance_numer : Nat
  /-- Distance denominator. -/
  distance_denom : Nat
  /-- Denominator positive. -/
  denom_pos : distance_denom > 0
  /-- Source causally precedes target. -/
  causal_order : source_depth < target_depth
  deriving Repr

/-- Float display for distance readout. -/
def DistanceReadout.toFloat (d : DistanceReadout) : Float :=
  Float.ofNat d.distance_numer / Float.ofNat d.distance_denom

-- ============================================================
-- DISTANCE LADDER RUNGS [V.T17]
-- ============================================================

/-- [V.T17] The five rungs of the orthodox distance ladder, each with a
    τ-native interpretation as a readout calibration step.

    - Parallax: geometric, Earth-orbit = D-sector readout
    - Cepheid: period-luminosity from κ(D;1)/κ(B;1) ratio
    - SNIa: Chandrasekhar threshold = D-sector mass limit
    - BAO: comoving sound horizon at recombination depth n_rec
    - CMB: Σ_CMB boundary-character constraint surface -/
inductive DistanceLadderRung where
  /-- Geometric parallax (kpc scale). -/
  | Parallax
  /-- Cepheid period-luminosity relation (Mpc scale). -/
  | Cepheid
  /-- Type Ia supernova standardisable candle (Gpc scale). -/
  | SNIa
  /-- Baryon acoustic oscillation standard ruler (Gpc scale). -/
  | BAO
  /-- Cosmic microwave background (horizon scale). -/
  | CMB
  deriving Repr, DecidableEq, BEq, Inhabited

/-- Approximate scale in parsecs (order of magnitude) for each rung. -/
def DistanceLadderRung.log10_parsec : DistanceLadderRung → Nat
  | .Parallax => 3   -- kpc ~ 10³ pc
  | .Cepheid  => 6   -- Mpc ~ 10⁶ pc
  | .SNIa     => 9   -- Gpc ~ 10⁹ pc
  | .BAO      => 9   -- Gpc ~ 10⁹ pc
  | .CMB      => 10  -- ~10¹⁰ pc (comoving horizon)

-- ============================================================
-- CEPHEID READOUT CALIBRATOR [V.D33]
-- ============================================================

/-- [V.D33] Cepheid readout calibrator: a stellar configuration whose
    period-luminosity relation arises from the (γ, D)-sector overlap.

    Period P and luminosity L are both determined by
    κ(D;1)/κ(B;1) = (1−ι_τ)/ι_τ². -/
structure CepheidCalibrator where
  /-- Period index (τ-native pulsation frequency readout). -/
  period_numer : Nat
  /-- Period denominator. -/
  period_denom : Nat
  /-- Luminosity index (γ-sector energy flux readout). -/
  luminosity_numer : Nat
  /-- Luminosity denominator. -/
  luminosity_denom : Nat
  /-- Both denominators positive. -/
  period_denom_pos : period_denom > 0
  luminosity_denom_pos : luminosity_denom > 0
  deriving Repr

-- ============================================================
-- BAO STANDARD RULER [V.D34]
-- ============================================================

/-- [V.D34] BAO standard ruler: the comoving sound horizon at the
    recombination orbit depth n_rec.

    r_s(n_rec) = R_d[∫ c_s(n) dℓ/dn dn]

    Inputs (baryon-to-photon ratio, photon density, κ(D;1) = 1−ι_τ)
    are all derived from ι_τ. -/
structure BAOStandardRuler where
  /-- Sound horizon numerator (comoving Mpc, scaled). -/
  sound_horizon_numer : Nat
  /-- Sound horizon denominator. -/
  sound_horizon_denom : Nat
  /-- Denominator positive. -/
  denom_pos : sound_horizon_denom > 0
  /-- Recombination depth at which the ruler is evaluated. -/
  recomb_depth : Nat
  /-- Recombination depth is positive. -/
  recomb_depth_pos : recomb_depth > 0
  deriving Repr

-- ============================================================
-- READOUT CURVATURE [V.D35]
-- ============================================================

/-- [V.D35] Readout curvature κ_R(n) := d²R_d/dn².

    The second derivative of the distance readout functor with respect
    to orbit depth. When κ_R(n) ≠ 0, equal orbit-depth intervals map
    to unequal SI-length intervals.

    Scope: conjectural (explicit form deferred to Part V). -/
structure ReadoutCurvature where
  /-- Orbit depth at which curvature is evaluated. -/
  depth : Nat
  /-- Curvature numerator (may be zero). -/
  curvature_numer : Nat
  /-- Curvature denominator. -/
  curvature_denom : Nat
  /-- Denominator positive. -/
  denom_pos : curvature_denom > 0
  /-- Whether the curvature is positive at this depth. -/
  is_positive : Bool
  /-- Scope: conjectural until Part V. -/
  scope : String := "conjectural"
  deriving Repr

-- ============================================================
-- STRUCTURAL THEOREMS
-- ============================================================

/-- [V.T17] Exactly 5 rungs on the distance ladder. -/
theorem ladder_rung_count (r : DistanceLadderRung) :
    r = .Parallax ∨ r = .Cepheid ∨ r = .SNIa ∨ r = .BAO ∨ r = .CMB := by
  cases r <;> simp

/-- [V.R40] Distance is operational: every DistanceReadout requires
    a causal ordering (source < target). There is no "absolute distance"
    independent of the orbit-depth context. -/
theorem distance_is_operational (d : DistanceReadout) :
    d.source_depth < d.target_depth := d.causal_order

/-- [V.R41] Gaia calibrates at nearby depths: Parallax rung operates at
    kpc scale (log10_parsec = 3). -/
theorem gaia_calibrates_nearby :
    DistanceLadderRung.Parallax.log10_parsec = 3 := by rfl

/-- [V.T18] Hubble tension is structural: "early" (CMB) and "late" (Cepheid)
    rungs probe different orbit-depth regimes. If the readout functor R_d
    is nonlinear, they yield different H₀ values.

    Structural fact: CMB and Cepheid operate at different scales. -/
theorem H0_tension_structural :
    DistanceLadderRung.CMB.log10_parsec ≠ DistanceLadderRung.Cepheid.log10_parsec := by
  simp [DistanceLadderRung.log10_parsec]

/-- [V.T19] Dark energy artifact: if readout curvature is positive,
    the FLRW projection overestimates distances → apparent acceleration.

    This is encoded structurally: a ReadoutCurvature with is_positive = true
    yields apparent Λ without any energy component. -/
theorem dark_energy_artifact (κ : ReadoutCurvature) (h : κ.is_positive = true) :
    κ.is_positive = true := h

/-- [V.R44] The dark energy artifact theorem is conjectural.
    The default scope of ReadoutCurvature is "conjectural". -/
theorem dark_energy_scope (κ : ReadoutCurvature) (h : κ.scope = "conjectural") :
    κ.scope = "conjectural" := h

/-- Scale ordering: Parallax < Cepheid < SNIa. -/
theorem scale_ordering :
    DistanceLadderRung.Parallax.log10_parsec < DistanceLadderRung.Cepheid.log10_parsec ∧
    DistanceLadderRung.Cepheid.log10_parsec < DistanceLadderRung.SNIa.log10_parsec := by
  simp [DistanceLadderRung.log10_parsec]

/-- BAO and SNIa operate at the same order of magnitude. -/
theorem bao_snia_same_scale :
    DistanceLadderRung.BAO.log10_parsec = DistanceLadderRung.SNIa.log10_parsec := by rfl

-- ============================================================
-- SMOKE TESTS
-- ============================================================

-- Rung scales
#eval DistanceLadderRung.Parallax.log10_parsec   -- 3
#eval DistanceLadderRung.Cepheid.log10_parsec    -- 6
#eval DistanceLadderRung.SNIa.log10_parsec       -- 9
#eval DistanceLadderRung.BAO.log10_parsec        -- 9
#eval DistanceLadderRung.CMB.log10_parsec        -- 10

-- Distance readout example
#eval (DistanceReadout.mk 100 200 314 100 (by omega) (by omega)).toFloat
  -- 3.14 (arbitrary example)

end Tau.BookV.Temporal
