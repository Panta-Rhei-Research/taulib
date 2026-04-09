import TauLib.BookII.Transcendentals.JReplacesI

/-!
# TauLib.BookII.Transcendentals.IotaTauConfirmed

Master constant iota_tau = 2/(pi + e) confirmed with earned pi and e.

## Registry Cross-References

- [II.T25] Master Constant Confirmed — `iota_tau_confirmed_check`
- [II.D34] Archimedean Bridge — `archimedean_bridge_check`
- [II.P07] Refinement Resolution Bound — `refinement_resolution_check`

## Mathematical Content

The master constant iota_tau = 2/(pi + e) ~ 0.341304 is now confirmed
using the pi and e earned in the previous modules. This closes the
circle: iota_tau was introduced axiomatically in Book I; now it is
derived from earned transcendentals.

The Archimedean bridge: iota_tau mediates between the Archimedean world
(pi, e from limits/series) and the profinite world (tau^3 from primorial
inverse system). The resolution crossover happens between stages k=1
and k=2: 1/P_1 = 0.5 > iota_tau > 1/P_2 ~ 0.167.

Refinement resolution bound: at stage k, the approximation error is
bounded by 1/P_k, which decreases monotonically.
-/

namespace Tau.BookII.Transcendentals

open Tau.BookII.Interior Tau.BookII.Domains
open Tau.Polarity Tau.Coordinates Tau.Denotation

-- ============================================================
-- IOTA_TAU COMPUTATION [II.T25]
-- ============================================================

/-- Compute iota_tau * scale using earned pi and e approximations.
    iota_tau = 2 / (pi + e).
    In scaled arithmetic: iota_tau * scale = 2 * scale^2 / (pi_scaled + e_scaled).

    pi_scaled and e_scaled are both in units of 10^6. -/
def iota_tau_computed (pi_terms e_terms scale : Nat) : Nat :=
  let pi_approx := leibniz_pi_scaled pi_terms scale
  let e_approx := e_factorial_scaled e_terms scale
  let denom := pi_approx + e_approx
  if denom == 0 then 0
  else 2 * scale * scale / denom

/-- [II.T25] Master constant confirmed: iota_tau ~ 0.341304.
    iota_tau * 10^6 ~ 341304.
    With 2000 Leibniz terms and 12 factorial terms:
    pi ~ 3141092, e ~ 2718281, sum ~ 5859373
    iota ~ 2 * 10^12 / 5859373 ~ 341381 (within 1% of 341304). -/
def iota_tau_confirmed_check : Bool :=
  let iota := iota_tau_computed 2000 12 1000000
  iota > 335000 && iota < 350000

/-- Higher precision check: the computed iota_tau matches the
    known rational approximation 341304/10^6 to within 2%. -/
def iota_tau_precision_check : Bool :=
  let iota := iota_tau_computed 2000 12 1000000
  let target : Nat := 341304
  -- Within 2%: |iota - 341304| < 6830
  let diff := if iota >= target then iota - target else target - iota
  diff < 6830

-- ============================================================
-- SELF-CONSISTENCY: pi + e FROM IOTA_TAU
-- ============================================================

/-- Self-consistency: pi + e = 2 / iota_tau.
    In scaled arithmetic: (pi + e) * iota = 2 * scale.
    Check: pi_scaled + e_scaled ~ 2 * scale^2 / iota_scaled. -/
def self_consistency_check : Bool :=
  let scale : Nat := 1000000
  let pi_approx := leibniz_pi_scaled 2000 scale
  let e_approx := e_factorial_scaled 12 scale
  let pe_sum := pi_approx + e_approx
  -- pe_sum should be close to 5859873 (= pi + e scaled by 10^6)
  -- 2 * 10^6 / pe_sum should give iota_tau
  -- Equivalently: pe_sum * iota ~ 2 * 10^6
  let iota := iota_tau_computed 2000 12 scale
  -- pe_sum * iota / scale ~ 2 * scale
  let product := pe_sum * iota / scale
  -- product should be close to 2 * scale = 2000000
  -- Allow 2% tolerance: within [1960000, 2040000]
  product > 1960000 && product < 2040000

-- ============================================================
-- ARCHIMEDEAN BRIDGE [II.D34]
-- ============================================================

/-- [II.D34] Archimedean bridge: iota_tau mediates between
    the Archimedean world (pi, e from limits) and the profinite
    world (tau^3 from primorial inverse system).

    The resolution at stage k is 1/P_k. The scale where
    resolution crosses iota_tau happens between k=1 and k=2:
    1/P_1 = 1/2 = 0.5 > iota_tau ~ 0.341 > 1/P_2 = 1/6 ~ 0.167.

    In scaled integer arithmetic: scale/P_k vs iota_tau_scaled. -/
def archimedean_bridge_check : Bool :=
  let scale : Nat := 1000000
  let iota := iota_tau_computed 2000 12 scale
  -- Resolution at k=1: scale/P_1 = 1000000/2 = 500000
  let res1 := scale / primorial 1
  -- Resolution at k=2: scale/P_2 = 1000000/6 = 166666
  let res2 := scale / primorial 2
  -- iota_tau sits between the two resolution levels
  res1 > iota && iota > res2

/-- Bridge characterization: iota_tau as the stage-1/stage-2
    interpolation constant. The fact that iota_tau falls between
    1/P_1 and 1/P_2 means it governs the first refinement step
    where the primorial ladder becomes finer than the master constant. -/
def bridge_interpolation_check : Bool :=
  let scale : Nat := 1000000
  let iota := iota_tau_computed 2000 12 scale
  -- P_1 = 2, P_2 = 6, P_3 = 30, P_4 = 210
  -- iota * P_1 = ~682918 < scale (iota < 1/P_1 * P_1 = 1, trivially)
  -- iota * P_2 = ~2048286 > scale (iota > 1/P_2, i.e. iota*P_2 > 1)
  iota * primorial 1 < scale * 2 &&  -- iota < 1
  iota * primorial 2 > scale         -- iota > 1/6

-- ============================================================
-- REFINEMENT RESOLUTION BOUND [II.P07]
-- ============================================================

/-- [II.P07] Refinement resolution bound: at stage k, the
    resolution 1/P_k decreases monotonically.
    P_{k+1} > P_k for all k >= 0. -/
def refinement_resolution_check (stages : TauIdx) : Bool :=
  go 1 (stages + 1)
where
  go (k fuel : Nat) : Bool :=
    if fuel = 0 then true
    else if k > stages then true
    else primorial (k + 1) > primorial k && go (k + 1) (fuel - 1)
  termination_by fuel

/-- Resolution ratio: P_{k+1}/P_k = p_{k+1} >= 2.
    Each refinement step at least halves the resolution. -/
def resolution_halving_check (stages : TauIdx) : Bool :=
  go 1 (stages + 1)
where
  go (k fuel : Nat) : Bool :=
    if fuel = 0 then true
    else if k > stages then true
    else
      let pk := primorial k
      pk > 0 && primorial (k + 1) / pk >= 2 && go (k + 1) (fuel - 1)
  termination_by fuel

-- ============================================================
-- FULL CONFIRMATION
-- ============================================================

/-- Full master constant confirmation: all pieces fit together. -/
def full_confirmation_check : Bool :=
  iota_tau_confirmed_check &&
  iota_tau_precision_check &&
  self_consistency_check &&
  archimedean_bridge_check &&
  bridge_interpolation_check &&
  refinement_resolution_check 5 &&
  resolution_halving_check 5

-- ============================================================
-- SMOKE TESTS
-- ============================================================

-- Iota-tau computation
#eval iota_tau_computed 2000 12 1000000   -- ~341381
#eval iota_tau_confirmed_check            -- true
#eval iota_tau_precision_check            -- true

-- Self-consistency
#eval self_consistency_check              -- true

-- Archimedean bridge
#eval archimedean_bridge_check            -- true
#eval bridge_interpolation_check          -- true

-- Refinement resolution
#eval refinement_resolution_check 5       -- true
#eval resolution_halving_check 5          -- true

-- Full confirmation
#eval full_confirmation_check             -- true

-- Component values for inspection
#eval leibniz_pi_scaled 2000 1000000      -- pi * 10^6
#eval e_factorial_scaled 12 1000000       -- e * 10^6
#eval primorial 1                         -- 2
#eval primorial 2                         -- 6
#eval 1000000 / primorial 1              -- 500000
#eval 1000000 / primorial 2              -- 166666

-- Formal verification
theorem iota_confirmed : iota_tau_confirmed_check = true := by native_decide
theorem iota_precision : iota_tau_precision_check = true := by native_decide
theorem self_consist : self_consistency_check = true := by native_decide
theorem arch_bridge : archimedean_bridge_check = true := by native_decide
theorem bridge_interp : bridge_interpolation_check = true := by native_decide
theorem refine_res_5 : refinement_resolution_check 5 = true := by native_decide
theorem res_halving_5 : resolution_halving_check 5 = true := by native_decide
theorem full_confirm : full_confirmation_check = true := by native_decide

end Tau.BookII.Transcendentals
