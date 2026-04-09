import TauLib.BookII.Transcendentals.Lines

/-!
# TauLib.BookII.Transcendentals.Circles

Solenoidal circles and S^1 as a profinite limit.

## Registry Cross-References

- [II.D26] Solenoidal Circle — `solenoidal_b_orbit`, `solenoidal_c_orbit`
- [II.T21] S^1 as Profinite Limit — `circle_profinite_check`
- [II.D27] Geometric-Topological Unification — `geo_topo_check`

## Mathematical Content

Solenoidal circles: B and C coordinates cycle through residues mod p_k
at each stage k. The B-orbit at prime p_k is the residue class of B mod p_k.

S^1 = profinite limit of Z/p_k Z: all residues 0..p_k-1 appear in the
B-coordinate of some tau-admissible point.

The two solenoidal directions (B-orbit, C-orbit) are independently cyclic
at each stage, witnessing the T^2 = S^1 x S^1 torus structure.
-/

namespace Tau.BookII.Transcendentals

open Tau.BookII.Interior Tau.BookII.Domains
open Tau.Polarity Tau.Coordinates Tau.Denotation

-- ============================================================
-- SOLENOIDAL CIRCLE [II.D26]
-- ============================================================

/-- [II.D26] Solenoidal B-orbit at the k-th prime: B mod p_k.
    This is the residue of the exponent coordinate in the k-th cyclic factor
    of the profinite group hat(Z). -/
def solenoidal_b_orbit (x k : TauIdx) : TauIdx :=
  (from_tau_idx x).b % nth_prime k

/-- Solenoidal C-orbit at the k-th prime: C mod p_k. -/
def solenoidal_c_orbit (x k : TauIdx) : TauIdx :=
  (from_tau_idx x).c % nth_prime k

-- ============================================================
-- S^1 AS PROFINITE LIMIT [II.T21]
-- ============================================================

/-- Check whether a given residue r appears as a B-residue mod p_k
    in some tau-admissible point in [2, bound]. -/
def exists_with_b_residue (r k bound : TauIdx) : Bool :=
  go 2 (bound + 1)
where
  go (x fuel : Nat) : Bool :=
    if fuel = 0 then false
    else if x > bound then false
    else if solenoidal_b_orbit x k == r then true
    else go (x + 1) (fuel - 1)
  termination_by fuel

/-- Check whether a given residue r appears as a C-residue mod p_k. -/
def exists_with_c_residue (r k bound : TauIdx) : Bool :=
  go 2 (bound + 1)
where
  go (x fuel : Nat) : Bool :=
    if fuel = 0 then false
    else if x > bound then false
    else if solenoidal_c_orbit x k == r then true
    else go (x + 1) (fuel - 1)
  termination_by fuel

/-- [II.T21] S^1 as profinite limit: all residues 0..p_k-1 appear
    in the B-coordinate of some tau-admissible point in [2, bound].
    This witnesses the surjectivity of the B-projection onto Z/p_k Z. -/
def circle_profinite_b_check (k bound : TauIdx) : Bool :=
  let pk := nth_prime k
  go 0 (pk + 1)
where
  go (r fuel : Nat) : Bool :=
    if fuel = 0 then true
    else if r >= nth_prime k then true
    else exists_with_b_residue r k bound && go (r + 1) (fuel - 1)
  termination_by fuel

/-- Same for C-coordinate. -/
def circle_profinite_c_check (k bound : TauIdx) : Bool :=
  let pk := nth_prime k
  go 0 (pk + 1)
where
  go (r fuel : Nat) : Bool :=
    if fuel = 0 then true
    else if r >= nth_prime k then true
    else exists_with_c_residue r k bound && go (r + 1) (fuel - 1)
  termination_by fuel

-- ============================================================
-- GEOMETRIC-TOPOLOGICAL UNIFICATION [II.D27]
-- ============================================================

/-- [II.D27] Geometric-topological unification: B and C orbits are
    independently cyclic at each stage. T^2 = S^1_B x S^1_C.

    Evidence: both B and C projections are surjective onto Z/p_k Z
    for the first few primes. -/
def geo_topo_check (bound : TauIdx) : Bool :=
  -- Check for k=1 (p=2) and k=2 (p=3)
  circle_profinite_b_check 1 bound &&
  circle_profinite_c_check 1 bound &&
  circle_profinite_b_check 2 bound &&
  circle_profinite_c_check 2 bound

/-- Independence check: B and C orbits are genuinely independent.
    Witness: find points with same B but different C, and vice versa. -/
def bc_independence_check : Bool :=
  -- 8=(2,3,1,1) vs 64=(2,3,2,1): same B=3 but C=1 vs C=2
  let p8 := from_tau_idx 8
  let p64 := from_tau_idx 64
  (p8.b == p64.b && p8.c != p64.c) &&
  -- 2=(2,1,1,1) vs 8=(2,3,1,1): different B, same C=1
  let p2 := from_tau_idx 2
  (p2.c == p8.c && p2.b != p8.b)

-- ============================================================
-- SMOKE TESTS
-- ============================================================

-- Solenoidal orbits
#eval solenoidal_b_orbit 8 1    -- B=3, p_1=2: 3%2 = 1
#eval solenoidal_b_orbit 8 2    -- B=3, p_2=3: 3%3 = 0
#eval solenoidal_c_orbit 64 1   -- C=2, p_1=2: 2%2 = 0
#eval solenoidal_c_orbit 64 2   -- C=2, p_2=3: 2%3 = 2

-- B-residue existence
#eval exists_with_b_residue 0 1 50   -- true: exists x with B%2=0
#eval exists_with_b_residue 1 1 50   -- true: exists x with B%2=1

-- Circle profinite checks
#eval circle_profinite_b_check 1 100  -- true: all B%2 residues appear
#eval circle_profinite_b_check 2 100  -- true: all B%3 residues appear
#eval circle_profinite_c_check 1 200  -- true: all C%2 residues appear

-- Geo-topo unification
#eval geo_topo_check 200        -- true

-- Independence
#eval bc_independence_check     -- true

-- Formal verification
theorem circle_b_k1 : circle_profinite_b_check 1 100 = true := by native_decide
theorem circle_b_k2 : circle_profinite_b_check 2 100 = true := by native_decide
theorem circle_c_k1 : circle_profinite_c_check 1 200 = true := by native_decide
theorem geo_topo_200 : geo_topo_check 200 = true := by native_decide
theorem bc_indep : bc_independence_check = true := by native_decide

end Tau.BookII.Transcendentals
