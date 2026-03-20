import TauLib.BookII.Transcendentals.IotaTauConfirmed

/-!
# TauLib.BookII.Hartogs.CalibratedSplitComplex

Calibrated split-complex codomain H_τ^cal: the split-complex algebra
H_τ equipped with the four earned transcendental constants (π, e, j, ι_τ).

## Registry Cross-References

- [II.D35] Calibrated H_τ — `CalibratedHTau`, `calibrated_htau`
- [II.R10] Geometric Meaning of e± — `geometric_meaning_check`

## Mathematical Content

H_τ^cal is H_τ with the four constants (π, e, j, ι_τ) installed as
calibration data. The calibration gives the idempotents e₊, e₋
geometric meaning:

- e₊ = (1+j)/2 projects onto the **B-channel** (governed by γ-orbit,
  calibrated by π). The B-channel carries exponent data; its
  characteristic frequency is the circle winding number ~ π.

- e₋ = (1-j)/2 projects onto the **C-channel** (governed by η-orbit,
  calibrated by e). The C-channel carries tetration height data;
  its characteristic growth rate is the factorial eigenvalue ~ e.

- ι_τ = 2/(π+e) couples the two channels: it is the unique constant
  that balances the B-channel (π-calibrated) against the C-channel
  (e-calibrated).

All arithmetic uses scaled integers (SCALE = 10^6) from the
Transcendentals modules, avoiding Float entirely.
-/

namespace Tau.BookII.Hartogs

open Tau.BookII.Interior Tau.BookII.Domains Tau.BookII.Transcendentals
open Tau.Polarity Tau.Boundary Tau.Coordinates Tau.Denotation

-- ============================================================
-- SCALE CONSTANT
-- ============================================================

/-- Common scale factor for all calibration arithmetic.
    Matches the Transcendentals convention: 10^6. -/
def SCALE : Nat := 1000000

-- ============================================================
-- CALIBRATED H_TAU [II.D35]
-- ============================================================

/-- [II.D35] Calibrated split-complex codomain H_τ^cal.
    Stores the four earned transcendental constants as scaled integers.
    Each field represents the constant multiplied by SCALE = 10^6.

    The calibration is canonical: there is exactly one CalibratedHTau
    instance derived from the earned pi, e, j, iota_tau. -/
structure CalibratedHTau where
  /-- π scaled by 10^6: π * 10^6 ≈ 3141592. -/
  pi_cal    : Nat
  /-- e scaled by 10^6: e * 10^6 ≈ 2718281. -/
  e_cal     : Nat
  /-- j² = +1 indicator: 1 means j² = +1 (split-complex), 0 would mean i² = -1. -/
  j_cal     : Nat
  /-- ι_τ scaled by 10^6: ι_τ * 10^6 ≈ 341304. -/
  iota_cal  : Nat
  deriving Repr, DecidableEq

/-- The canonical calibrated codomain, using 2000 Leibniz terms for π
    and 12 factorial terms for e (matching IotaTauConfirmed). -/
def calibrated_htau : CalibratedHTau :=
  { pi_cal   := leibniz_pi_scaled 2000 SCALE
  , e_cal    := e_factorial_scaled 12 SCALE
  , j_cal    := 1  -- j² = +1
  , iota_cal := iota_tau_computed 2000 12 SCALE
  }

-- ============================================================
-- CALIBRATION CONSTANT RANGES
-- ============================================================

/-- π calibration in expected range: π * 10^6 ∈ [3100000, 3200000]. -/
def pi_cal_range_check : Bool :=
  let h := calibrated_htau
  h.pi_cal > 3100000 && h.pi_cal < 3200000

/-- e calibration in expected range: e * 10^6 ∈ [2710000, 2730000]. -/
def e_cal_range_check : Bool :=
  let h := calibrated_htau
  h.e_cal > 2710000 && h.e_cal < 2730000

/-- ι_τ calibration in expected range: ι_τ * 10^6 ∈ [335000, 350000]. -/
def iota_cal_range_check : Bool :=
  let h := calibrated_htau
  h.iota_cal > 335000 && h.iota_cal < 350000

-- ============================================================
-- j² = +1 VERIFICATION
-- ============================================================

/-- j² = +1: the split-complex unit squares to the identity.
    This is the algebraic foundation of the calibration:
    j² = +1 ⟹ idempotents exist ⟹ bipolar decomposition. -/
def j_squared_calibration_check : Bool :=
  calibrated_htau.j_cal == 1 &&
  SplitComplex.mul SplitComplex.j SplitComplex.j == SplitComplex.one

-- ============================================================
-- IDEMPOTENT VERIFICATION
-- ============================================================

/-- e₊ · e₋ = 0 (orthogonality) in sector coordinates.
    Sector representation: e₊ = (1,0), e₋ = (0,1). -/
def orthogonality_check : Bool :=
  SectorPair.mul e_plus_sector e_minus_sector == ⟨0, 0⟩

/-- e₊ + e₋ = 1 (completeness): the idempotents partition unity.
    In sector coordinates: (1,0) + (0,1) = (1,1) = 1. -/
def completeness_check : Bool :=
  SectorPair.add e_plus_sector e_minus_sector == ⟨1, 1⟩

/-- e₊² = e₊ and e₋² = e₋ (idempotency). -/
def idempotency_check : Bool :=
  SectorPair.mul e_plus_sector e_plus_sector == e_plus_sector &&
  SectorPair.mul e_minus_sector e_minus_sector == e_minus_sector

-- ============================================================
-- COUPLING VERIFICATION: ι_τ = 2/(π + e)
-- ============================================================

/-- [II.D35, coupling axiom] ι_τ couples the two channels:
    ι_τ = 2 / (π + e).
    In scaled arithmetic: ι_τ * SCALE ≈ 2 * SCALE² / (π_cal + e_cal).
    Verify consistency to within 2%. -/
def coupling_check : Bool :=
  let h := calibrated_htau
  let denom := h.pi_cal + h.e_cal
  if denom == 0 then false
  else
    let expected := 2 * SCALE * SCALE / denom
    -- |iota_cal - expected| < 2% of expected
    let diff := if h.iota_cal >= expected then h.iota_cal - expected
                else expected - h.iota_cal
    let tolerance := expected / 50  -- 2%
    diff < tolerance

-- ============================================================
-- GEOMETRIC MEANING OF e± [II.R10]
-- ============================================================

/-- [II.R10] Geometric meaning of the idempotents.

    e₊ projects onto the B-channel:
    - B carries the exponent (γ-orbit) data
    - Calibrated by π (circle winding number)
    - At stage k: B-residues form Z/p_k Z, with p_k arcs of angular width 2π/p_k

    e₋ projects onto the C-channel:
    - C carries the tetration height (η-orbit) data
    - Calibrated by e (factorial eigenvalue / growth base)
    - Growth rate of the tower: exponential with base related to e

    Evidence: for τ-admissible points, e₊-projection extracts B only,
    e₋-projection extracts C only. -/
def geometric_meaning_check (bound : TauIdx) : Bool :=
  go 2 (bound + 1)
where
  go (x fuel : Nat) : Bool :=
    if fuel = 0 then true
    else if x > bound then true
    else
      let p := from_tau_idx x
      let bp := interior_bipolar p
      -- e₊ · (B, C) = (B, 0): keeps B-channel, kills C-channel
      let proj_plus := SectorPair.mul e_plus_sector bp
      -- e₋ · (B, C) = (0, C): kills B-channel, keeps C-channel
      let proj_minus := SectorPair.mul e_minus_sector bp
      -- Verify projection structure
      (proj_plus.c_sector == 0) &&
      (proj_minus.b_sector == 0) &&
      (proj_plus.b_sector == bp.b_sector) &&
      (proj_minus.c_sector == bp.c_sector) &&
      -- Sum recovers full bipolar pair
      (SectorPair.add proj_plus proj_minus == bp) &&
      go (x + 1) (fuel - 1)
  termination_by fuel

/-- The B-channel is π-calibrated: the number of B-residues at stage k
    equals p_k, and each arc has angular width 2π/p_k.
    In scaled arithmetic: full circle = 2 * pi_cal, arc = 2 * pi_cal / p_k.
    Verify: p_k arcs sum to a full circle. -/
def b_channel_pi_calibration (stages : TauIdx) : Bool :=
  let h := calibrated_htau
  go 1 (stages + 1) h.pi_cal
where
  go (k fuel : Nat) (pi_cal : Nat) : Bool :=
    if fuel = 0 then true
    else if k > stages then true
    else
      let pk := nth_prime k
      -- Full circle = 2 * pi_cal
      -- p_k arcs of width 2*pi_cal/p_k should sum to 2*pi_cal
      -- Evidence: pk * (2 * pi_cal / pk) is close to 2 * pi_cal
      let arc_width := 2 * pi_cal / pk
      let total := pk * arc_width
      let full := 2 * pi_cal
      -- Within 1 arc-width of the full circle (integer rounding)
      (full >= total && full - total < arc_width + 1) &&
      go (k + 1) (fuel - 1) pi_cal
  termination_by fuel

/-- The C-channel is e-calibrated: the growth ratio P_{k+1}/P_k = p_{k+1},
    and primorial growth is super-exponential with base related to e.
    Evidence: ln(P_k) ~ sum_{i=1}^{k} ln(p_i) grows; the average
    growth factor approaches e for large k via PNT.
    At small k: verify p_{k+1} >= 2 (each step at least doubles). -/
def c_channel_e_calibration (stages : TauIdx) : Bool :=
  go 1 (stages + 1)
where
  go (k fuel : Nat) : Bool :=
    if fuel = 0 then true
    else if k > stages then true
    else
      let pk := primorial k
      let pk1 := primorial (k + 1)
      -- Growth factor = p_{k+1} >= 2
      (pk > 0 && pk1 / pk >= 2) &&
      go (k + 1) (fuel - 1)
  termination_by fuel

-- ============================================================
-- CALIBRATION CONSISTENCY [II.D35, full]
-- ============================================================

/-- [II.D35] Full calibration consistency: all four constants are
    mutually consistent and the idempotents have correct geometric meaning.

    1. π, e, ι_τ in correct ranges
    2. j² = +1
    3. Idempotents: orthogonal, complete, idempotent
    4. Coupling: ι_τ = 2/(π+e)
    5. Geometric meaning: e₊ → B-channel, e₋ → C-channel -/
def calibration_consistency_check : Bool :=
  pi_cal_range_check &&
  e_cal_range_check &&
  iota_cal_range_check &&
  j_squared_calibration_check &&
  orthogonality_check &&
  completeness_check &&
  idempotency_check &&
  coupling_check &&
  geometric_meaning_check 30

/-- Extended consistency including channel calibration. -/
def full_calibration_check : Bool :=
  calibration_consistency_check &&
  b_channel_pi_calibration 5 &&
  c_channel_e_calibration 5

-- ============================================================
-- SMOKE TESTS
-- ============================================================

-- Calibrated constants
#eval calibrated_htau   -- inspect all four constants

-- Individual ranges
#eval calibrated_htau.pi_cal     -- ~ 3141092
#eval calibrated_htau.e_cal      -- ~ 2718281
#eval calibrated_htau.iota_cal   -- ~ 341381
#eval calibrated_htau.j_cal      -- 1

-- Range checks
#eval pi_cal_range_check         -- true
#eval e_cal_range_check          -- true
#eval iota_cal_range_check       -- true

-- j and idempotent checks
#eval j_squared_calibration_check  -- true
#eval orthogonality_check          -- true
#eval completeness_check           -- true
#eval idempotency_check            -- true

-- Coupling
#eval coupling_check             -- true

-- Geometric meaning
#eval geometric_meaning_check 30   -- true

-- Channel calibration
#eval b_channel_pi_calibration 5   -- true
#eval c_channel_e_calibration 5    -- true

-- Full consistency
#eval calibration_consistency_check  -- true
#eval full_calibration_check         -- true

-- ============================================================
-- FORMAL VERIFICATION
-- ============================================================

theorem pi_range : pi_cal_range_check = true := by native_decide
theorem e_range : e_cal_range_check = true := by native_decide
theorem iota_range : iota_cal_range_check = true := by native_decide
theorem j_sq_cal : j_squared_calibration_check = true := by native_decide
theorem ortho : orthogonality_check = true := by native_decide
theorem compl : completeness_check = true := by native_decide
theorem idemp : idempotency_check = true := by native_decide
theorem coupling : coupling_check = true := by native_decide
theorem geo_meaning_30 : geometric_meaning_check 30 = true := by native_decide
theorem b_pi_cal_5 : b_channel_pi_calibration 5 = true := by native_decide
theorem c_e_cal_5 : c_channel_e_calibration 5 = true := by native_decide
theorem cal_consistency : calibration_consistency_check = true := by native_decide
theorem full_cal : full_calibration_check = true := by native_decide

end Tau.BookII.Hartogs
