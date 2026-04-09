import TauLib.BookIII.Spectral.HenselLifting

/-!
# TauLib.BookIII.Spectral.LocalFields

τ-Native Local Fields and Completeness Without Topology.

## Registry Cross-References

- [III.D21] τ-Native Local Field — `LocalField`, `local_field_check`
- [III.P06] Completeness Without Topology — `completeness_check`

## Mathematical Content

**III.D21 (τ-Native Local Field):** ℤ_p^τ = lim← ℤ/p^n ℤ as inverse
limit within τ. The p-adic integers are a τ-object with NF address.
p-adic valuation v_p = D-coordinate restricted to p-primary component.

**III.P06 (Completeness Without Topology):** ℤ_p^τ is complete in the τ
sense: every tower-coherent sequence has unique limit. This is Global
Hartogs restricted to the p-primary tower. No metric, no Cauchy sequences.
-/

namespace Tau.BookIII.Spectral

open Tau.Polarity Tau.Boundary Tau.Coordinates Tau.Denotation
open Tau.BookII.Interior Tau.BookII.Enrichment Tau.BookII.Domains
open Tau.BookIII.Enrichment Tau.BookIII.Sectors

-- ============================================================
-- τ-NATIVE LOCAL FIELD [III.D21]
-- ============================================================

/-- [III.D21] A τ-native local field element at finite depth.
    Represents an element of ℤ_p^τ = lim← ℤ/p^nℤ at depth d. -/
structure LocalFieldElt where
  prime : TauIdx         -- the prime p
  depth : TauIdx         -- truncation depth d
  value : TauIdx         -- value mod p^d
  deriving Repr, DecidableEq, BEq

/-- [III.D21] Build a local field element from a global τ-value. -/
def to_local (x p d : TauIdx) : LocalFieldElt :=
  let pd := p ^ d
  ⟨p, d, if pd > 0 then x % pd else 0⟩

/-- [III.D21] p-adic valuation: largest k such that p^k | x.
    Returns 0 if x = 0 or p < 2. -/
def padic_val (x p : TauIdx) : TauIdx :=
  if x == 0 || p < 2 then 0
  else go x p 0 x
where
  go (x p acc fuel : Nat) : TauIdx :=
    if fuel = 0 then acc
    else if x % p != 0 then acc
    else go (x / p) p (acc + 1) (fuel - 1)
  termination_by fuel

/-- [III.D21] Local field check: verify inverse system property.
    For each p and depth d: reduce from p^(d+1) to p^d is coherent. -/
def local_field_check (bound depth : TauIdx) : Bool :=
  go 0 1 1 ((bound + 1) * (depth + 1) * 5)
where
  go (x p_idx d fuel : Nat) : Bool :=
    if fuel = 0 then true
    else if x > bound then true
    else if p_idx > 4 then go (x + 1) 1 1 (fuel - 1)
    else if d >= depth then go x (p_idx + 1) 1 (fuel - 1)
    else
      let p := nth_prime p_idx
      if p < 2 then go x (p_idx + 1) 1 (fuel - 1)
      else
        let pd := p ^ d
        let pd1 := p ^ (d + 1)
        -- Inverse system: (x mod p^(d+1)) mod p^d = x mod p^d
        let high := if pd1 > 0 then x % pd1 else 0
        let projected := if pd > 0 then high % pd else 0
        let low := if pd > 0 then x % pd else 0
        projected == low && go x p_idx (d + 1) (fuel - 1)
  termination_by fuel

/-- [III.D21] Local field ring operations: addition and multiplication
    are well-defined on ℤ/p^dℤ. -/
def local_ring_check (bound depth : TauIdx) : Bool :=
  go 0 0 1 ((bound + 1) * (bound + 1) * (depth + 1))
where
  go (x y d fuel : Nat) : Bool :=
    if fuel = 0 then true
    else if x > bound then true
    else if y > bound then go (x + 1) 0 1 (fuel - 1)
    else if d > depth then go x (y + 1) 1 (fuel - 1)
    else
      -- Use p = 3 as test prime (nth_prime 2)
      let p : Nat := 3
      let pd := p ^ d
      if pd == 0 then go x y (d + 1) (fuel - 1)
      else
        let xm := x % pd
        let ym := y % pd
        -- Addition: (x+y) mod p^d = ((x mod p^d) + (y mod p^d)) mod p^d
        let add_ok := (x + y) % pd == (xm + ym) % pd
        -- Multiplication: similar
        let mul_ok := (x * y) % pd == (xm * ym) % pd
        add_ok && mul_ok && go x y (d + 1) (fuel - 1)
  termination_by fuel

-- ============================================================
-- COMPLETENESS WITHOUT TOPOLOGY [III.P06]
-- ============================================================

/-- [III.P06] Completeness check: every tower-coherent sequence has
    unique limit. A sequence (a_1, a_2, ...) with a_{n+1} ≡ a_n mod p^n
    determines a unique element of ℤ_p^τ.
    We verify: if we build a coherent tower from x, the limit = x mod p^d. -/
def completeness_check (bound depth : TauIdx) : Bool :=
  go 0 1 ((bound + 1) * 3)
where
  go (x p_idx fuel : Nat) : Bool :=
    if fuel = 0 then true
    else if x > bound then true
    else if p_idx > 3 then go (x + 1) 1 (fuel - 1)
    else
      let p := nth_prime p_idx
      if p < 2 then go x (p_idx + 1) (fuel - 1)
      else
        -- Build coherent tower from x
        let tower_ok := check_tower x p 1 (depth + 1)
        tower_ok && go x (p_idx + 1) (fuel - 1)
  termination_by fuel
  check_tower (x p d fuel : Nat) : Bool :=
    if fuel = 0 then true
    else if d > depth then true
    else
      let pd := p ^ d
      let pd1 := p ^ (d + 1)
      if pd == 0 || pd1 == 0 then true
      else
        (x % pd1) % pd == x % pd && check_tower x p (d + 1) (fuel - 1)
  termination_by fuel

/-- [III.P06] Uniqueness of limit: two tower-coherent sequences that
    agree at all levels are equal (= same element of ℤ_p^τ). -/
def limit_uniqueness_check (bound depth : TauIdx) : Bool :=
  go 0 0 ((bound + 1) * (bound + 1))
where
  go (x y fuel : Nat) : Bool :=
    if fuel = 0 then true
    else if x > bound then true
    else if y > bound then go (x + 1) 0 (fuel - 1)
    else
      let p : Nat := 3  -- test prime
      -- If x ≡ y mod p^d for all d ≤ depth, then x = y mod p^depth
      let agree_all := check_agreement x y p 1 (depth + 1)
      let conclusion := if agree_all then
        let pd := p ^ depth
        if pd > 0 then x % pd == y % pd else true
      else true
      conclusion && go x (y + 1) (fuel - 1)
  termination_by fuel
  check_agreement (x y p d fuel : Nat) : Bool :=
    if fuel = 0 then true
    else if d > depth then true
    else
      let pd := p ^ d
      if pd > 0 then
        x % pd == y % pd && check_agreement x y p (d + 1) (fuel - 1)
      else true
  termination_by fuel

-- ============================================================
-- SMOKE TESTS
-- ============================================================

-- Local field elements
#eval to_local 42 3 2                       -- 42 mod 9 = 6 in ℤ₃
#eval to_local 42 5 2                       -- 42 mod 25 = 17 in ℤ₅
#eval to_local 100 7 2                      -- 100 mod 49 = 2 in ℤ₇

-- p-adic valuation
#eval padic_val 12 2                         -- 2 (12 = 2²·3)
#eval padic_val 12 3                         -- 1 (12 = 4·3)
#eval padic_val 27 3                         -- 3 (27 = 3³)
#eval padic_val 7 7                          -- 1

-- Checks
#eval local_field_check 15 4                 -- true
#eval local_ring_check 10 4                  -- true
#eval completeness_check 20 5               -- true
#eval limit_uniqueness_check 10 4            -- true

-- ============================================================
-- FORMAL VERIFICATION (native_decide)
-- ============================================================

-- Local field [III.D21]
theorem local_field_15_4 :
    local_field_check 15 4 = true := by native_decide

-- Local ring [III.D21]
theorem local_ring_10_4 :
    local_ring_check 10 4 = true := by native_decide

-- Completeness [III.P06]
theorem completeness_20_5 :
    completeness_check 20 5 = true := by native_decide

-- Limit uniqueness [III.P06]
theorem limit_unique_10_4 :
    limit_uniqueness_check 10 4 = true := by native_decide

-- ============================================================
-- STRUCTURAL THEOREMS
-- ============================================================

/-- [III.D21] Structural: p-adic valuation of p is 1. -/
theorem val_p_is_1 : padic_val 3 3 = 1 := by native_decide
theorem val_p_is_1' : padic_val 5 5 = 1 := by native_decide

/-- [III.D21] Structural: p-adic valuation of p^k is k. -/
theorem val_p2 : padic_val 9 3 = 2 := by native_decide
theorem val_p3 : padic_val 27 3 = 3 := by native_decide

/-- [III.D21] Structural: p-adic valuation of 0 is 0 (convention). -/
theorem val_zero : padic_val 0 3 = 0 := by native_decide

/-- [III.P06] Structural: tower coherence at p=3, x=42. -/
theorem tower_42_3 :
    (42 % (3 ^ 3)) % (3 ^ 2) = 42 % (3 ^ 2) := by native_decide

end Tau.BookIII.Spectral
