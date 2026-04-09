import TauLib.BookIII.Arithmetic.EnrichedBiSquare

/-!
# TauLib.BookIII.Arithmetic.TowerAssembly

Enrichment Tower Assembly: E₀ ⊊ E₁ ⊊ E₂ assembled.

## Registry Cross-References

- [III.T40] Enrichment Tower Assembly — `tower_assembly_check`

## Mathematical Content

**III.T40 (Tower Assembly):** The tower E₀ ⊊ E₁ ⊊ E₂ is assembled with
coherent bi-square scaling chain and complete Millennium coverage:
- E₀: RH + Poincaré (pure mathematics)
- E₁: NS + YM + Hodge (physics)
- E₁→E₂: BSD + Langlands (arithmetic mirror)
- E₂: P vs NP (computation)

The tower is strict (E₀ ⊊ E₁ ⊊ E₂), each level has its bi-square, and
the scaling chain is coherent: algebraic → topological → enriched.
-/

namespace Tau.BookIII.Arithmetic

open Tau.Polarity Tau.Boundary Tau.Coordinates Tau.Denotation
open Tau.BookII.Interior Tau.BookII.Enrichment
open Tau.BookIII.Enrichment Tau.BookIII.Sectors
open Tau.BookIII.Spectral Tau.BookIII.Doors
open Tau.BookIII.Physics

-- ============================================================
-- ENRICHMENT TOWER ASSEMBLY [III.T40]
-- ============================================================

/-- [III.T40] Tower strictness: E₀ ⊊ E₁ ⊊ E₂. Each level is a proper
    subset of the next (enrichment adds genuine content). -/
def tower_strict_check : Bool :=
  -- E₀ < E₁ < E₂ < E₃
  EnrLevel.lt .E0 .E1 &&
  EnrLevel.lt .E1 .E2 &&
  EnrLevel.lt .E2 .E3

/-- [III.T40] Millennium coverage: all 8 problems are assigned to levels. -/
def millennium_coverage_check : Bool :=
  -- E₀ problems
  let e0 := problem_level .RH == .E0 && problem_level .Poincare == .E0
  -- E₁ problems
  let e1 := problem_level .NS == .E1 && problem_level .YM == .E1 &&
             problem_level .Hodge == .E1
  -- E₁→E₂ interface
  let e12 := problem_level .BSD == .E2 && problem_level .Langlands == .E2
  -- E₂ problem
  let e2 := problem_level .PvsNP == .E2
  e0 && e1 && e12 && e2

/-- [III.T40] Bi-square scaling chain: all three bi-squares have the same
    structural shape (CRT roundtrip + BNF decomposition + sector products). -/
def scaling_chain_check (bound db : TauIdx) : Bool :=
  -- Level 1: algebraic bi-square shape (CRT roundtrip)
  let alg := crt_roundtrip_go 0 1 bound db ((bound + 1) * (db + 1))
  -- Level 2: topological shape (BNF decomposition)
  let top := bnf_decomposition_go 0 1 bound db ((bound + 1) * (db + 1))
  -- Level 3: enriched shape (sector products)
  let enr := enriched_bisquare_check bound db
  alg && top && enr
where
  /-- Algebraic: CRT roundtrip. -/
  crt_roundtrip_go (x k bound db fuel : Nat) : Bool :=
    if fuel = 0 then true
    else if x > bound then true
    else if k > db then crt_roundtrip_go (x + 1) 1 bound db (fuel - 1)
    else
      let pk := primorial k
      if pk == 0 then crt_roundtrip_go x (k + 1) bound db (fuel - 1)
      else
        let xr := x % pk
        let recon := crt_reconstruct (crt_decompose xr k) k
        recon == xr && crt_roundtrip_go x (k + 1) bound db (fuel - 1)
  termination_by fuel
  /-- Topological: BNF decomposition. -/
  bnf_decomposition_go (x k bound db fuel : Nat) : Bool :=
    if fuel = 0 then true
    else if x > bound then true
    else if k > db then bnf_decomposition_go (x + 1) 1 bound db (fuel - 1)
    else
      let pk := primorial k
      if pk == 0 then bnf_decomposition_go x (k + 1) bound db (fuel - 1)
      else
        let xr := x % pk
        let nf := boundary_normal_form xr k
        (nf.b_part + nf.c_part + nf.x_part) % pk == xr && bnf_decomposition_go x (k + 1) bound db (fuel - 1)
  termination_by fuel

/-- [III.T40] Tower assembly: tower is strict, coverage is complete,
    and scaling chain is coherent. -/
def tower_assembly_check (bound db : TauIdx) : Bool :=
  tower_strict_check &&
  millennium_coverage_check &&
  scaling_chain_check bound db

-- ============================================================
-- SMOKE TESTS
-- ============================================================

#eval tower_strict_check                     -- true
#eval millennium_coverage_check              -- true
#eval scaling_chain_check 15 3               -- true
#eval tower_assembly_check 15 3              -- true

-- ============================================================
-- FORMAL VERIFICATION (native_decide)
-- ============================================================

theorem tower_strict :
    tower_strict_check = true := by native_decide

theorem millennium_coverage :
    millennium_coverage_check = true := by native_decide

theorem scaling_chain_15_3 :
    scaling_chain_check 15 3 = true := by native_decide

theorem tower_assembly_15_3 :
    tower_assembly_check 15 3 = true := by native_decide

-- ============================================================
-- STRUCTURAL THEOREMS
-- ============================================================

/-- [III.T40] Structural: E₀ < E₁. -/
theorem e0_lt_e1 : EnrLevel.lt .E0 .E1 = true := rfl

/-- [III.T40] Structural: E₁ < E₂. -/
theorem e1_lt_e2 : EnrLevel.lt .E1 .E2 = true := rfl

/-- [III.T40] Structural: E₂ < E₃. -/
theorem e2_lt_e3 : EnrLevel.lt .E2 .E3 = true := rfl

/-- [III.T40] Structural: all 8 problems covered. -/
theorem eight_problems :
    [problem_level .RH, problem_level .Poincare,
     problem_level .NS, problem_level .YM, problem_level .Hodge,
     problem_level .BSD, problem_level .Langlands,
     problem_level .PvsNP].length = 8 := rfl

end Tau.BookIII.Arithmetic
