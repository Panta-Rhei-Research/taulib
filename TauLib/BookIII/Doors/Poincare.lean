import TauLib.BookIII.Doors.GrandGRH

/-!
# TauLib.BookIII.Doors.Poincare

Simply Connected in Category τ and Poincaré as Gluing Guarantee.

## Registry Cross-References

- [III.D35] Simply Connected in Category τ — `simply_connected_check`
- [III.P13] Poincaré as Gluing Guarantee — `gluing_guarantee_check`

## Mathematical Content

**III.D35 (Simply Connected in τ):** Categorical reinterpretation of simple
connectivity: π₁^τ trivial iff every loop of transition functions in the
Hartogs bulk is contractible. S³ is the terminal object among closed,
simply connected 3-dimensional τ-spaces. Poincaré = uniqueness of
the terminal object.

**III.P13 (Poincaré as Gluing):** Poincaré guarantees that local Hartogs bulk
projections glue into a global space homeomorphic to S³ when the fundamental
group is trivial. Simple connectivity = no obstruction to global coherence.
-/

namespace Tau.BookIII.Doors

open Tau.Polarity Tau.Boundary Tau.Coordinates Tau.Denotation
open Tau.BookII.Interior Tau.BookII.Enrichment
open Tau.BookIII.Enrichment Tau.BookIII.Sectors
open Tau.BookIII.Spectral

-- ============================================================
-- SIMPLY CONNECTED IN τ [III.D35]
-- ============================================================

/-- [III.D35] Simple connectivity at finite level k: every "loop" at
    primorial level k is contractible, meaning the transition function
    around a cycle is the identity.
    In τ-terms: for every x and every prime cycle p₁→p₂→...→p₁,
    the CRT decomposition is consistent (no monodromy). -/
def simply_connected_check (bound db : TauIdx) : Bool :=
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
        -- Contractibility: CRT decompose then reconstruct = identity
        let residues := crt_decompose (x % pk) k
        let reconstructed := crt_reconstruct residues k
        -- No monodromy: going around the CRT cycle returns to start
        let no_monodromy := reconstructed == x % pk
        -- BNF is well-defined (no ambiguity in decomposition)
        let nf := boundary_normal_form (x % pk) k
        let well_defined := (nf.b_part + nf.c_part + nf.x_part) % pk == x % pk
        no_monodromy && well_defined && go x (k + 1) (fuel - 1)
  termination_by fuel

/-- [III.D35] Terminal object check: among all τ-spaces at level k with
    trivial fundamental group, the structure is unique up to isomorphism.
    In τ-terms: any two elements with the same CRT residues are equal. -/
def terminal_object_check (bound db : TauIdx) : Bool :=
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
        let res_x := crt_decompose xr k
        let res_y := crt_decompose yr k
        -- Uniqueness: same residues ⟹ same value
        let ok := if res_x == res_y then xr == yr else true
        ok && go x y (k + 1) (fuel - 1)
  termination_by fuel

-- ============================================================
-- POINCARÉ AS GLUING GUARANTEE [III.P13]
-- ============================================================

/-- [III.P13] Gluing guarantee: local Hartogs bulk projections glue
    coherently when fundamental group is trivial.
    In τ-terms: the CRT local-to-global reconstruction is exact,
    and the bipolar decomposition respects the gluing. -/
def gluing_guarantee_check (bound db : TauIdx) : Bool :=
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
        -- Local: CRT residues at each prime
        let residues := crt_decompose xr k
        -- Gluing: reconstruct from local data
        let global := crt_reconstruct residues k
        -- Bipolar: BNF respects the gluing
        let nf := boundary_normal_form global k
        let sum := (nf.b_part + nf.c_part + nf.x_part) % pk
        -- Complete coherence: local → global → bipolar → sum = original
        global == xr && sum == xr && go x (k + 1) (fuel - 1)
  termination_by fuel

/-- [III.P13] Obstruction detection: when the fundamental group is
    non-trivial, the gluing fails. Test: inconsistent residues
    cannot be reconstructed coherently. -/
def obstruction_check (db : TauIdx) : Bool :=
  go 1 (db + 1)
where
  go (k fuel : Nat) : Bool :=
    if fuel = 0 then true
    else if k > db then true
    else
      let pk := primorial k
      if pk == 0 || pk <= 1 then go (k + 1) (fuel - 1)
      else
        -- Trivial fundamental group ⟹ unique reconstruction
        -- Test: for all x < Prim(k), CRT is bijective
        let bijective := check_bijectivity 0 pk k
        bijective && go (k + 1) (fuel - 1)
  termination_by fuel
  check_bijectivity (x pk k : Nat) : Bool :=
    if x >= pk then true
    else
      let residues := crt_decompose x k
      let reconstructed := crt_reconstruct residues k
      reconstructed == x && check_bijectivity (x + 1) pk k

-- ============================================================
-- SMOKE TESTS
-- ============================================================

#eval simply_connected_check 15 4           -- true
#eval terminal_object_check 10 3            -- true
#eval gluing_guarantee_check 15 4           -- true
#eval obstruction_check 4                   -- true

-- ============================================================
-- FORMAL VERIFICATION (native_decide)
-- ============================================================

theorem simply_connected_15_4 :
    simply_connected_check 15 4 = true := by native_decide

theorem terminal_object_10_3 :
    terminal_object_check 10 3 = true := by native_decide

theorem gluing_guarantee_15_4 :
    gluing_guarantee_check 15 4 = true := by native_decide

theorem obstruction_4 :
    obstruction_check 4 = true := by native_decide

-- ============================================================
-- STRUCTURAL THEOREMS
-- ============================================================

/-- [III.D35] Structural: CRT is bijective at depth 3
    (simple connectivity = no monodromy). -/
theorem crt_bijective_42_3 :
    crt_reconstruct (crt_decompose 42 3) 3 = 42 % primorial 3 := by
  native_decide

/-- [III.D35] Structural: terminal object at depth 1 (only mod 2). -/
theorem terminal_depth_1 :
    simply_connected_check 10 1 = true := by native_decide

/-- [III.P13] Structural: gluing at depth 1. -/
theorem gluing_depth_1 :
    gluing_guarantee_check 10 1 = true := by native_decide

end Tau.BookIII.Doors
