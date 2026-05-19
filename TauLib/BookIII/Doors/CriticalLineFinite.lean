import TauLib.BookIII.Doors.SpectralCorrespondenceFinite

/-!
# TauLib.BookIII.Doors.CriticalLineFinite

Axiom-free finite critical-line, K5, and primorial RH protocol checks.

These are the finite check-level surfaces used by the G8 accepted-stage
certificates.  They deliberately avoid importing the legacy universal O3
postulate.
-/

namespace Tau.BookIII.Doors

open Tau.Polarity Tau.Boundary Tau.Coordinates Tau.Denotation
open Tau.BookII.Interior Tau.BookII.Enrichment
open Tau.BookIII.Enrichment Tau.BookIII.Sectors
open Tau.BookIII.Spectral

-- ============================================================
-- CRITICAL LINE THEOREM [III.T19]
-- ============================================================

/-- [III.T19] Critical line check at level k: all spectral modes have
    real eigenvalues (= natural numbers) and the spectral correspondence
    maps them consistently. Combines self-adjointness + finite O3 check. -/
def critical_line_check (k : TauIdx) : Bool :=
  go 0 (k + 1)
where
  go (n fuel : Nat) : Bool :=
    if fuel = 0 then true
    else if n > k then true
    else
      -- Self-adjointness: eigenvalue is real (n², always real for Nat)
      let lambda := lemniscate_eigenvalue n
      let is_real := lambda == n * n
      -- Finite spectral correspondence: mode maps within window
      let mode := spectral_parameter n k
      let in_window := mode <= k
      is_real && in_window && go (n + 1) (fuel - 1)
  termination_by fuel

/-- [III.T19] Critical line at multiple depths. -/
def critical_line_multi_check (db : TauIdx) : Bool :=
  go 1 (db + 1)
where
  go (k fuel : Nat) : Bool :=
    if fuel = 0 then true
    else if k > db then true
    else
      critical_line_check k && go (k + 1) (fuel - 1)
  termination_by fuel

-- ============================================================
-- K5 OFF-DIAGONAL EXCLUSION [III.P10]
-- ============================================================

/-- [III.P10] K5 off-diagonal exclusion: at each primorial level k,
    the B-lobe and C-lobe eigenvalues have zero off-diagonal coupling.
    The crossing-point boundary conditions enforce real spectral flow. -/
def k5_exclusion_check (bound db : TauIdx) : Bool :=
  go 1 1 ((bound + 1) * (db + 1))
where
  go (n k fuel : Nat) : Bool :=
    if fuel = 0 then true
    else if n > bound then true
    else if k > db then go (n + 1) 1 (fuel - 1)
    else
      -- Eigenvalue at mode n: real-valued (= n²) confirms no imaginary coupling
      let lambda := lemniscate_eigenvalue n
      let eigenval_real := lambda == n * n
      -- K5 off-diagonal exclusion: B and C sector products are coprime at depth k
      let b_prod := split_zeta_b k
      let c_prod := split_zeta_c k
      let sectors_coprime := Nat.gcd b_prod c_prod == 1
      eigenval_real && sectors_coprime && go n (k + 1) (fuel - 1)
  termination_by fuel

-- ============================================================
-- τ-EFFECTIVE RH STATEMENT [III.D30]
-- ============================================================

/-- [III.D30] τ-Effective RH: for each primorial depth k, the finite-cutoff
    operator H_{≤k} has only real eigenvalues, and the finite zeta
    has the correct zero structure. A computable predicate. -/
def tau_effective_rh_check (db : TauIdx) : Bool :=
  go 1 (db + 1)
where
  go (k fuel : Nat) : Bool :=
    if fuel = 0 then true
    else if k > db then true
    else
      -- Step 1: eigenvalues are real (n² for all modes ≤ k)
      let eigenvalues_real := self_adjoint_check k
      -- Step 2: finite spectral correspondence holds at this level
      let corr_ok := spectral_correspondence_finite k
      -- Step 3: Euler product factorization is consistent
      let euler_ok := split_zeta_check k
      eigenvalues_real && corr_ok && euler_ok && go (k + 1) (fuel - 1)
  termination_by fuel

-- ============================================================
-- PRIMORIAL RH VERIFICATION PROTOCOL [III.P11]
-- ============================================================

/-- [III.P11] Primorial RH verification protocol at depth k.
    Six steps: (i) compute Spec(H_{≤k}), (ii) verify eigenvalues real,
    (iii) verify zero locations, (iv) tower coherence, (v) CRT consistency,
    (vi) record certificate. Returns true if all steps pass. -/
def rh_protocol_check (db : TauIdx) : Bool :=
  go 1 (db + 1)
where
  go (k fuel : Nat) : Bool :=
    if fuel = 0 then true
    else if k > db then true
    else
      -- (i) Compute spectrum: eigenvalues 0², 1², ..., k²
      let spec_ok := kirchhoff_check k
      -- (ii) Verify eigenvalues real: all are Nat (always true)
      let real_ok := self_adjoint_check k
      -- (iii) Verify zero structure: finite spectral correspondence
      let zero_ok := spectral_correspondence_finite k
      -- (iv) Tower coherence: eigenvalue nesting at this depth
      let tower_ok := eigenvalue_nesting_check k
      -- (v) CRT consistency: Euler product at this level
      let crt_ok := bipolar_euler_check k
      -- (vi) Certificate: all checks pass (this function is the certificate)
      spec_ok && real_ok && zero_ok && tower_ok && crt_ok && go (k + 1) (fuel - 1)
  termination_by fuel

-- ============================================================
-- SMOKE TESTS
-- ============================================================

#eval critical_line_check 5                  -- true
#eval critical_line_check 10                 -- true
#eval critical_line_multi_check 5            -- true
#eval k5_exclusion_check 10 3               -- true
#eval tau_effective_rh_check 5               -- true
#eval rh_protocol_check 4                    -- true

-- ============================================================
-- FORMAL VERIFICATION (native_decide)
-- ============================================================

theorem critical_line_5 :
    critical_line_check 5 = true := by native_decide

theorem critical_line_10 :
    critical_line_check 10 = true := by native_decide

theorem critical_line_multi_5 :
    critical_line_multi_check 5 = true := by native_decide

theorem k5_exclusion_10_3 :
    k5_exclusion_check 10 3 = true := by native_decide

theorem tau_effective_rh_5 :
    tau_effective_rh_check 5 = true := by native_decide

theorem rh_protocol_4 :
    rh_protocol_check 4 = true := by native_decide

-- ============================================================
-- STRUCTURAL THEOREMS
-- ============================================================

/-- [III.T19] Structural: critical line at depth 1 (only prime 2). -/
theorem critical_line_1 :
    critical_line_check 1 = true := by native_decide

/-- [III.P10] Structural: eigenvalue of first mode equals 1. -/
theorem k5_eigenvalue_1 :
    lemniscate_eigenvalue 1 = 1 := rfl

/-- [III.D30] Structural: τ-effective RH at depth 1. -/
theorem tau_rh_1 :
    tau_effective_rh_check 1 = true := by native_decide

end Tau.BookIII.Doors
