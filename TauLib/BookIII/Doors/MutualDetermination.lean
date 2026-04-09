import TauLib.BookIII.Spectral.Trichotomy

/-!
# TauLib.BookIII.Doors.MutualDetermination

Mutual Determination Schema: B ↔ I ↔ S at spectral level.

## Registry Cross-References

- [III.D25] Mutual Determination Schema — `MDDescription`, `mutual_det_check`

## Mathematical Content

**III.D25 (Mutual Determination Schema):** The Master Schema formalized:
B (boundary) ↔ I (interior) ↔ S (spectral invariants). Three equivalences:
boundary→interior (Global Hartogs), interior→spectral (spectral decomposition),
closure B↔S (dual perspectives). Uniform template for all millennium problems.
-/

namespace Tau.BookIII.Doors

open Tau.Polarity Tau.Boundary Tau.Coordinates Tau.Denotation
open Tau.BookII.Interior Tau.BookII.Enrichment
open Tau.BookIII.Enrichment Tau.BookIII.Sectors
open Tau.BookIII.Spectral

-- ============================================================
-- MUTUAL DETERMINATION SCHEMA [III.D25]
-- ============================================================

/-- [III.D25] The three descriptions in the Mutual Determination Schema.
    B = Boundary data (CRT residues), I = Interior data (reconstruction),
    S = Spectral data (bipolar B/C/X decomposition). -/
inductive MDDescription where
  | Boundary : MDDescription      -- CRT residues at each prime
  | Interior : MDDescription      -- reconstructed value from residues
  | Spectral : MDDescription      -- bipolar B/C/X decomposition
  deriving Repr, DecidableEq, BEq

/-- [III.D25] Boundary → Interior: reconstruction from CRT residues
    agrees with direct computation. -/
def boundary_to_interior_check (bound db : TauIdx) : Bool :=
  go 0 1 ((bound + 1) * (db + 1))
where
  go (x k fuel : Nat) : Bool :=
    if fuel = 0 then true
    else if x > bound then true
    else if k > db then go (x + 1) 1 (fuel - 1)
    else
      let pk := primorial k
      if pk == 0 then go x (k + 1) (fuel - 1)
      else
        let residues := crt_decompose x k
        let reconstructed := crt_reconstruct residues k
        reconstructed == x % pk && go x (k + 1) (fuel - 1)
  termination_by fuel

/-- [III.D25] Interior → Spectral: the bipolar decomposition of the
    reconstructed value is exact (sums back). -/
def interior_to_spectral_check (bound db : TauIdx) : Bool :=
  go 0 1 ((bound + 1) * (db + 1))
where
  go (x k fuel : Nat) : Bool :=
    if fuel = 0 then true
    else if x > bound then true
    else if k > db then go (x + 1) 1 (fuel - 1)
    else
      let pk := primorial k
      if pk == 0 then go x (k + 1) (fuel - 1)
      else
        let xr := x % pk
        let nf := boundary_normal_form xr k
        let sum := (nf.b_part + nf.c_part + nf.x_part) % pk
        sum == xr && go x (k + 1) (fuel - 1)
  termination_by fuel

/-- [III.D25] Spectral → Boundary: the spectral decomposition uniquely
    determines the boundary data (injectivity). -/
def spectral_to_boundary_check (bound db : TauIdx) : Bool :=
  go 0 0 1 ((bound + 1) * (bound + 1) * (db + 1))
where
  go (x y k fuel : Nat) : Bool :=
    if fuel = 0 then true
    else if x > bound then true
    else if y > bound then go (x + 1) 0 1 (fuel - 1)
    else if k > db then go x (y + 1) 1 (fuel - 1)
    else
      let pk := primorial k
      if pk == 0 then go x y (k + 1) (fuel - 1)
      else
        let xr := x % pk
        let yr := y % pk
        let nfx := boundary_normal_form xr k
        let nfy := boundary_normal_form yr k
        let spectral_agree := nfx.b_part == nfy.b_part &&
                              nfx.c_part == nfy.c_part &&
                              nfx.x_part == nfy.x_part
        let ok := if spectral_agree then xr == yr else true
        ok && go x y (k + 1) (fuel - 1)
  termination_by fuel

/-- [III.D25] Full mutual determination: all three descriptions equivalent. -/
def mutual_det_check (bound db : TauIdx) : Bool :=
  boundary_to_interior_check bound db &&
  interior_to_spectral_check bound db &&
  spectral_to_boundary_check bound db

-- ============================================================
-- SMOKE TESTS
-- ============================================================

#eval boundary_to_interior_check 15 4      -- true
#eval interior_to_spectral_check 15 4      -- true
#eval spectral_to_boundary_check 10 3      -- true
#eval mutual_det_check 10 3                -- true

-- ============================================================
-- FORMAL VERIFICATION (native_decide)
-- ============================================================

theorem b_to_i_15_4 :
    boundary_to_interior_check 15 4 = true := by native_decide

theorem i_to_s_15_4 :
    interior_to_spectral_check 15 4 = true := by native_decide

theorem s_to_b_10_3 :
    spectral_to_boundary_check 10 3 = true := by native_decide

theorem mutual_det_10_3 :
    mutual_det_check 10 3 = true := by native_decide

-- ============================================================
-- STRUCTURAL THEOREMS
-- ============================================================

/-- [III.D25] Structural: boundary→interior is exact for 0. -/
theorem b_to_i_zero :
    crt_reconstruct (crt_decompose 0 3) 3 = 0 := by native_decide

/-- [III.D25] Structural: mutual determination cycle for 42 at depth 3. -/
theorem md_cycle_42_3 :
    let residues := crt_decompose 42 3
    let reconstructed := crt_reconstruct residues 3
    let nf := boundary_normal_form reconstructed 3
    (nf.b_part + nf.c_part + nf.x_part) % primorial 3 = 42 % primorial 3 := by
  native_decide

end Tau.BookIII.Doors
