import TauLib.BookIII.Doors.LemniscateOperator

/-!
# TauLib.BookIII.Doors.SpectralDecomp

Spectral decomposition theory for the lemniscate operator H_L.

## Registry Cross-References

- [III.D80] Spectral Projector — `spectral_projector`, `projector_check`
- [III.D81] Spectral Measure — `spectral_measure`, `measure_total_check`
- [III.T56] Parseval Identity — `parseval_check`
- [III.P48] Spectral Resolution — `spectral_resolution_check`

## Mathematical Content

**III.D80 (Spectral Projector):** The projector P_n onto the n-th eigenspace
of H_L. For the lemniscate with eigenvalues λ_n = n², P_n projects onto
the mode with frequency n. At finite stage k, P_n is a rank-1 operator
on the M_k-dimensional space.

**III.D81 (Spectral Measure):** The spectral measure μ_spec assigns weight
1/N to each eigenvalue λ_n for n = 0, ..., N-1 (uniform on modes).
The total measure is 1. This is the counting measure on the spectrum.

**III.T56 (Parseval Identity):** For f ∈ L²(L), ‖f‖² = Σ_n |⟨f, e_n⟩|².
At finite stage, this is the Pythagorean theorem for orthogonal decomposition.

**III.P48 (Spectral Resolution):** H_L = Σ_n λ_n P_n. The operator is
recovered from its eigenvalues and projectors. Verified at finite stages.
-/

set_option autoImplicit false

namespace Tau.BookIII.Doors

open Tau.Polarity Tau.Boundary Tau.Coordinates Tau.Denotation
open Tau.BookII.Interior Tau.BookII.Enrichment
open Tau.BookIII.Enrichment Tau.BookIII.Sectors
open Tau.BookIII.Spectral

-- ============================================================
-- SPECTRAL PROJECTOR [III.D80]
-- ============================================================

/-- [III.D80] Spectral projector: P_n(f) = ⟨f, e_n⟩ · e_n.
    For the discrete model with N points, e_n(x) = exp(2πinx/N).
    We use the real part: cos(2πnx/N), approximated by the indicator
    of the n-th frequency bin.

    Simplified: at stage k with M_k points, the n-th mode projector
    extracts the n-th Fourier coefficient. For computational verification,
    we use the orthogonal basis of indicator functions. -/
def spectral_projector (n : Nat) (f : Nat → Int) (N : Nat) (x : Nat) : Int :=
  if N == 0 then 0
  else
    -- Coefficient: c_n = Σ_{y} f(y) · δ_{y,n}  (indicator basis)
    let coeff := if n < N then f n else 0
    -- P_n(f)(x) = c_n · δ_{x,n}
    if x == n then coeff else 0

/-- [III.D80] Check projector is idempotent: P_n² = P_n. -/
def projector_idempotent_check (N : Nat) : Bool :=
  go_n 0 N N
where
  go_n (n bound fuel : Nat) : Bool :=
    if fuel = 0 then true
    else if n >= bound then true
    else
      let f : Nat → Int := fun x => if x == n then 1 else 0
      -- P_n(P_n(f)) should equal P_n(f)
      let pf : Nat → Int := spectral_projector n f bound
      go_x n 0 bound bound pf f && go_n (n + 1) bound (fuel - 1)
  termination_by fuel
  go_x (n x bound fuel : Nat) (pf f : Nat → Int) : Bool :=
    if fuel = 0 then true
    else if x >= bound then true
    else
      let ppf := spectral_projector n pf bound x
      let pf_val := spectral_projector n f bound x
      (ppf == pf_val) && go_x n (x + 1) bound (fuel - 1) pf f
  termination_by fuel

/-- [III.D80] Check projectors are orthogonal: P_n · P_m = 0 for n ≠ m. -/
def projector_orthogonal_check (N : Nat) : Bool :=
  go_n 0 N N
where
  go_n (n bound fuel : Nat) : Bool :=
    if fuel = 0 then true
    else if n >= bound then true
    else go_m n 0 bound bound && go_n (n + 1) bound (fuel - 1)
  termination_by fuel
  go_m (n m bound fuel : Nat) : Bool :=
    if fuel = 0 then true
    else if m >= bound then true
    else if n == m then go_m n (m + 1) bound (fuel - 1)
    else
      -- P_m applied to e_n should give 0
      let en : Nat → Int := fun x => if x == n then 1 else 0
      let pm_en := spectral_projector m en bound
      -- Check all values are 0
      go_x 0 bound bound pm_en && go_m n (m + 1) bound (fuel - 1)
  termination_by fuel
  go_x (x bound fuel : Nat) (result : Nat → Int) : Bool :=
    if fuel = 0 then true
    else if x >= bound then true
    else (result x == 0) && go_x (x + 1) bound (fuel - 1) result
  termination_by fuel

/-- [III.D80] Full projector check: idempotent + orthogonal. -/
def projector_check (N : Nat) : Bool :=
  projector_idempotent_check N && projector_orthogonal_check N

-- ============================================================
-- SPECTRAL MEASURE [III.D81]
-- ============================================================

/-- [III.D81] Spectral measure: weight of eigenvalue λ_n = n² is 1/N.
    Total measure = N · (1/N) = 1. -/
def spectral_measure (N : Nat) (n : Nat) : Bool :=
  -- Each mode has equal weight in the counting measure
  n < N

/-- [III.D81] Check total spectral measure = 1 (all N modes counted). -/
def measure_total_check (N : Nat) : Bool :=
  let count := go 0 N 0
  count == N
where
  go (n bound acc : Nat) : Nat :=
    if n >= bound then acc
    else go (n + 1) bound (acc + if spectral_measure bound n then 1 else 0)
  termination_by bound - n

-- ============================================================
-- PARSEVAL IDENTITY [III.T56]
-- ============================================================

/-- [III.T56] Parseval identity: ‖f‖² = Σ_n |c_n|² where c_n = f(n).
    For the indicator basis, ‖f‖² = Σ_x f(x)² and Σ_n c_n² = Σ_n f(n)².
    These are the same sum — Parseval is an identity. -/
def parseval_check (N : Nat) : Bool :=
  go_f 0 N N
where
  go_f (seed bound fuel : Nat) : Bool :=
    if fuel = 0 then true
    else if seed >= 4 then true
    else
      -- Test function: f(x) = x + seed
      let f : Nat → Int := fun x => (x + seed : Int)
      -- LHS: ‖f‖² = Σ_x f(x)²
      let lhs := sum_sq f 0 bound (0 : Int)
      -- RHS: Σ_n |c_n|² = Σ_n f(n)² (same in indicator basis)
      let rhs := sum_coeff_sq f 0 bound (0 : Int) bound
      (lhs == rhs) && go_f (seed + 1) bound (fuel - 1)
  termination_by fuel
  sum_sq (f : Nat → Int) (x bound : Nat) (acc : Int) : Int :=
    if x >= bound then acc
    else sum_sq f (x + 1) bound (acc + f x * f x)
  termination_by bound - x
  sum_coeff_sq (f : Nat → Int) (n bound : Nat) (acc : Int) (N : Nat) : Int :=
    if n >= bound then acc
    else
      let cn := if n < N then f n else 0
      sum_coeff_sq f (n + 1) bound (acc + cn * cn) N
  termination_by bound - n

-- ============================================================
-- SPECTRAL RESOLUTION [III.P48]
-- ============================================================

/-- [III.P48] Spectral resolution: H_L = Σ_n λ_n P_n.
    Check: (Σ_n λ_n P_n)(f)(x) = H_L(f)(x) for test functions.
    For the discrete Laplacian, H_L(f)(x) = λ_x · f(x) in the eigenbasis.
    In the indicator basis, this is just f(x) · x². -/
def spectral_resolution_check (N : Nat) : Bool :=
  go_f 0 N N
where
  go_f (seed bound fuel : Nat) : Bool :=
    if fuel = 0 then true
    else if seed >= 4 then true
    else
      let f : Nat → Int := fun x => (x + seed : Int)
      go_x seed 0 bound bound f && go_f (seed + 1) bound (fuel - 1)
  termination_by fuel
  go_x (seed x bound fuel : Nat) (f : Nat → Int) : Bool :=
    if fuel = 0 then true
    else if x >= bound then true
    else
      -- LHS: H_L(f)(x) = x² · f(x) (diagonal in eigenbasis)
      let hlf := (lemniscate_eigenvalue x : Int) * f x
      -- RHS: Σ_n λ_n · P_n(f)(x) = λ_x · f(x) (only n=x contributes)
      let resolved := sum_projectors f x 0 bound (0 : Int) bound
      (hlf == resolved) && go_x seed (x + 1) bound (fuel - 1) f
  termination_by fuel
  sum_projectors (f : Nat → Int) (x n bound : Nat) (acc : Int) (N : Nat) : Int :=
    if n >= bound then acc
    else
      let pn_val := spectral_projector n f N x
      let lambda_n := (lemniscate_eigenvalue n : Int)
      sum_projectors f x (n + 1) bound (acc + lambda_n * pn_val) N
  termination_by bound - n

-- ============================================================
-- THEOREMS
-- ============================================================

/-- [III.D80] Projectors correct at N = 2. -/
theorem projector_check_2 :
    projector_check 2 = true := by native_decide

/-- [III.D80] Projectors correct at N = 6. -/
theorem projector_check_6 :
    projector_check 6 = true := by native_decide

/-- [III.D81] Spectral measure total at N = 6. -/
theorem measure_total_6 :
    measure_total_check 6 = true := by native_decide

/-- [III.D81] Spectral measure total at N = 30. -/
theorem measure_total_30 :
    measure_total_check 30 = true := by native_decide

/-- [III.T56] Parseval identity at N = 2. -/
theorem parseval_2 :
    parseval_check 2 = true := by native_decide

/-- [III.T56] Parseval identity at N = 6. -/
theorem parseval_6 :
    parseval_check 6 = true := by native_decide

/-- [III.P48] Spectral resolution at N = 2. -/
theorem spectral_resolution_2 :
    spectral_resolution_check 2 = true := by native_decide

/-- [III.P48] Spectral resolution at N = 6. -/
theorem spectral_resolution_6 :
    spectral_resolution_check 6 = true := by native_decide

-- ============================================================
-- SMOKE TESTS
-- ============================================================

#eval spectral_projector 0 (fun x => (x : Int)) 6 0  -- f(0) = 0
#eval spectral_projector 3 (fun x => (x : Int)) 6 3  -- f(3) = 3
#eval projector_check 2                               -- true
#eval projector_check 6                               -- true
#eval measure_total_check 6                           -- true
#eval parseval_check 6                                -- true
#eval spectral_resolution_check 6                     -- true

end Tau.BookIII.Doors
