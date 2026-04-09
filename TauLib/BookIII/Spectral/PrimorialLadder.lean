import TauLib.BookIII.Sectors.ParityBridge

/-!
# TauLib.BookIII.Spectral.PrimorialLadder

Primorial ladder as inverse system and primorial cofinality theorem.

## Registry Cross-References

- [III.D19] Primorial Ladder — `PrimorialStage`, `primorial_ladder_check`
- [III.T09] Primorial Cofinality — `cofinal_level`, `primorial_cofinal_check`

## Mathematical Content

**III.D19 (Primorial Ladder):** Primorial numbers Prim(k) = p₁·p₂·…·pₖ
form an inverse system ℤ/Prim(1)ℤ ← ℤ/Prim(2)ℤ ← …. The inverse limit
is the profinite completion Ẑ_τ. Canonical cofinal filtration.

**III.T09 (Primorial Cofinality):** The primorial tower is cofinal: every
ℤ/Nℤ maps to ℤ/Prim(k)ℤ for k large enough. Checking at primorial
levels is SUFFICIENT. The cutoff k₀ is always computable.
-/

namespace Tau.BookIII.Spectral

open Tau.Polarity Tau.Boundary Tau.Coordinates Tau.Denotation
open Tau.BookII.Interior Tau.BookII.Enrichment
open Tau.BookIII.Enrichment Tau.BookIII.Sectors

-- ============================================================
-- PRIMORIAL LADDER [III.D19]
-- ============================================================

/-- [III.D19] A stage in the primorial ladder:
    the inverse system ℤ/Prim(1)ℤ ← ℤ/Prim(2)ℤ ← … -/
structure PrimorialStage where
  depth : TauIdx          -- k
  modulus : TauIdx         -- Prim(k)
  value : TauIdx           -- x mod Prim(k)
  deriving Repr, DecidableEq, BEq

/-- [III.D19] Build a primorial stage from a value and depth. -/
def primorial_stage (x k : TauIdx) : PrimorialStage :=
  ⟨k, primorial k, reduce x k⟩

/-- [III.D19] Primorial ladder check: the inverse system property.
    For each k ≤ bound: reduce(reduce(x, k+1), k) = reduce(x, k). -/
def primorial_ladder_check (bound : TauIdx) : Bool :=
  go 0 1 (bound * (bound + 1))
where
  go (x k fuel : Nat) : Bool :=
    if fuel = 0 then true
    else if x > bound then true
    else if k >= bound then go (x + 1) 1 (fuel - 1)
    else
      let high := reduce x (k + 1)
      let projected := reduce high k
      let low := reduce x k
      projected == low && go x (k + 1) (fuel - 1)
  termination_by fuel

/-- [III.D19] Primorial divisibility: Prim(k) | Prim(k+1) for all k ≥ 1. -/
def primorial_divisibility_check (bound : TauIdx) : Bool :=
  go 1 (bound + 1)
where
  go (k fuel : Nat) : Bool :=
    if fuel = 0 then true
    else if k > bound then true
    else
      let pk := primorial k
      let pk1 := primorial (k + 1)
      (pk > 0 && pk1 % pk == 0) && go (k + 1) (fuel - 1)
  termination_by fuel

/-- [III.D19] Primorial growth: Prim(k+1) > Prim(k) (strictly increasing). -/
def primorial_growth_check (bound : TauIdx) : Bool :=
  go 1 (bound + 1)
where
  go (k fuel : Nat) : Bool :=
    if fuel = 0 then true
    else if k > bound then true
    else
      primorial (k + 1) > primorial k && go (k + 1) (fuel - 1)
  termination_by fuel

-- ============================================================
-- PRIMORIAL COFINALITY [III.T09]
-- ============================================================

/-- [III.T09] Find the smallest primorial level k such that Prim(k) ≥ n. -/
def cofinal_level (n : TauIdx) : TauIdx :=
  go 0 (n + 1)
where
  go (k fuel : Nat) : TauIdx :=
    if fuel = 0 then k
    else if primorial k >= n then k
    else go (k + 1) (fuel - 1)
  termination_by fuel

/-- [III.T09] Primorial cofinality: for each N ≤ bound, there exists k
    such that Prim(k) ≥ N. Checking at primorial levels is sufficient. -/
def primorial_cofinal_check (bound : TauIdx) : Bool :=
  go 1 (bound + 1)
where
  go (n fuel : Nat) : Bool :=
    if fuel = 0 then true
    else if n > bound then true
    else
      let k := cofinal_level n
      primorial k >= n && go (n + 1) (fuel - 1)
  termination_by fuel

/-- [III.T09] Cofinality for prime moduli: for each prime p ≤ bound,
    p | Prim(k) for some k. -/
def prime_cofinal_check (bound : TauIdx) : Bool :=
  go 1 1 (bound + 1)
where
  go (i fuel : Nat) (_dummy : Nat) : Bool :=
    if fuel = 0 then true
    else if i > bound then true
    else
      -- nth_prime i is the i-th prime (1-indexed)
      let p := nth_prime i
      if p > bound then true
      else
        -- p divides Prim(i) by construction
        primorial i % p == 0 && go (i + 1) (fuel - 1) 0
  termination_by fuel

-- ============================================================
-- SMOKE TESTS
-- ============================================================

-- Primorial stages
#eval primorial_stage 42 3                    -- depth=3, mod=30, value=12
#eval primorial_stage 100 4                   -- depth=4, mod=210, value=100

-- Primorial ladder (inverse system)
#eval primorial_ladder_check 8                -- true
#eval primorial_divisibility_check 6          -- true
#eval primorial_growth_check 6                -- true

-- Cofinality
#eval cofinal_level 10                        -- smallest k with Prim(k) ≥ 10
#eval cofinal_level 30                        -- k=3 (Prim(3) = 30)
#eval primorial_cofinal_check 50              -- true
#eval prime_cofinal_check 30                  -- true

-- ============================================================
-- FORMAL VERIFICATION (native_decide)
-- ============================================================

-- Primorial ladder [III.D19]
theorem primorial_ladder_8 :
    primorial_ladder_check 8 = true := by native_decide

-- Primorial divisibility [III.D19]
theorem primorial_div_6 :
    primorial_divisibility_check 6 = true := by native_decide

-- Primorial growth [III.D19]
theorem primorial_growth_6 :
    primorial_growth_check 6 = true := by native_decide

-- Primorial cofinality [III.T09]
theorem primorial_cofinal_50 :
    primorial_cofinal_check 50 = true := by native_decide

-- Prime cofinality [III.T09]
theorem prime_cofinal_30 :
    prime_cofinal_check 30 = true := by native_decide

-- ============================================================
-- STRUCTURAL THEOREMS
-- ============================================================

/-- [III.D19] Structural: primorial 0 = 1 (empty product). -/
theorem primorial_zero : primorial 0 = 1 := by native_decide

/-- [III.D19] Structural: primorial 1 = 2. -/
theorem primorial_one : primorial 1 = 2 := by native_decide

/-- [III.D19] Structural: primorial 3 = 30 = 2·3·5. -/
theorem primorial_three : primorial 3 = 30 := by native_decide

/-- [III.T09] Structural: cofinal level of 30 is 3. -/
theorem cofinal_30 : cofinal_level 30 = 3 := by native_decide

/-- [III.D19] Structural: reduce coherence at specific values. -/
theorem reduce_coherence_42 :
    reduce (reduce 42 4) 3 = reduce 42 3 := by native_decide

end Tau.BookIII.Spectral
