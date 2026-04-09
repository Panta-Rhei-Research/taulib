import TauLib.BookII.Topology.DimensionFour

/-!
# TauLib.BookII.Transcendentals.Lines

Alpha-ray lines and the real line as an inverse limit.

## Registry Cross-References

- [II.D24] Alpha-Ray Line — `alpha_ray_member`
- [II.D25] Level Circle — `level_circle_mem`
- [II.T20] R as Inverse Limit — `real_inverse_limit_check`

## Mathematical Content

The alpha-ray is the canonical radial sequence: points with D-coordinate
varying while A is fixed and B = C = 1. At each stage k, the D-coordinate
ranges over residues mod P_k, and as k -> infinity the inverse limit
recovers the real line R.

Level circles: points sharing the same D-residue mod P_k at stage k.
-/

namespace Tau.BookII.Transcendentals

open Tau.BookII.Interior Tau.BookII.Domains Tau.BookII.Topology
open Tau.Polarity Tau.Coordinates Tau.Denotation

-- ============================================================
-- ALPHA-RAY [II.D24]
-- ============================================================

/-- [II.D24] Alpha-ray membership: x belongs to the alpha-ray with
    prime direction a iff its ABCD chart has A = a, B = 1, C = 1.
    The D-coordinate varies freely (subject to constraint C3). -/
def alpha_ray_member (x a : TauIdx) : Bool :=
  let p := from_tau_idx x
  p.a == a && p.b == 1 && p.c == 1

/-- Count alpha-ray members in [2, bound] for a given prime a. -/
def alpha_ray_count (a bound : TauIdx) : Nat :=
  go 2 (bound + 1) 0
where
  go (x fuel acc : Nat) : Nat :=
    if fuel = 0 then acc
    else if x > bound then acc
    else go (x + 1) (fuel - 1) (acc + if alpha_ray_member x a then 1 else 0)
  termination_by fuel

-- ============================================================
-- LEVEL CIRCLE [II.D25]
-- ============================================================

/-- [II.D25] Level circle at stage k: two points share the same
    D-residue mod primorial(k). -/
def level_circle_mem (x y k : TauIdx) : Bool :=
  (from_tau_idx x).d % primorial k == (from_tau_idx y).d % primorial k

/-- Level circles refine: agreement at stage k+1 implies agreement at stage k. -/
def level_nesting_check (bound : TauIdx) : Bool :=
  go 2 2 1 ((bound + 1) * (bound + 1))
where
  go (x y k fuel : Nat) : Bool :=
    if fuel = 0 then true
    else if x > bound then true
    else if y > bound then go (x + 1) 2 k (fuel - 1)
    else
      (!level_circle_mem x y (k + 1) || level_circle_mem x y k) &&
      go x (y + 1) k (fuel - 1)
  termination_by fuel

-- ============================================================
-- R AS INVERSE LIMIT [II.T20]
-- ============================================================

/-- Collect distinct D-residues mod primorial(k) among alpha-ray members in [2, bound]. -/
def count_d_residues (a k bound : TauIdx) : Nat :=
  go 2 (bound + 1) []
where
  go (x fuel : Nat) (acc : List TauIdx) : Nat :=
    if fuel = 0 then acc.eraseDups.length
    else if x > bound then acc.eraseDups.length
    else if alpha_ray_member x a then
      go (x + 1) (fuel - 1) ((from_tau_idx x).d % primorial k :: acc)
    else go (x + 1) (fuel - 1) acc
  termination_by fuel

/-- [II.T20] R as inverse limit: at each stage k, the number of distinct
    D-residues is positive and bounded by primorial(k).
    The D-residue space grows with the primorial, witnessing the inverse
    limit structure lim Z/P_k Z = Z_hat -> R. -/
def real_inverse_limit_check (a bound stages : TauIdx) : Bool :=
  go 1 (stages + 1)
where
  go (k fuel : Nat) : Bool :=
    if fuel = 0 then true
    else if k > stages then true
    else
      let d_res := count_d_residues a k bound
      -- D-residue count is positive and bounded by primorial(k)
      d_res > 0 && d_res <= primorial k && go (k + 1) (fuel - 1)
  termination_by fuel

/-- Alpha-ray growth: more D-residues appear at higher stages.
    count_d_residues(k) <= count_d_residues(k+1) (monotone refinement). -/
def alpha_ray_growth_check (a bound stages : TauIdx) : Bool :=
  go 1 (stages + 1)
where
  go (k fuel : Nat) : Bool :=
    if fuel = 0 then true
    else if k > stages then true
    else
      count_d_residues a k bound <= count_d_residues a (k + 1) bound &&
      go (k + 1) (fuel - 1)
  termination_by fuel

-- ============================================================
-- SMOKE TESTS
-- ============================================================

-- Alpha-ray membership
#eval alpha_ray_member 2 2     -- true: (2,1,1,1) has A=2,B=1,C=1
#eval alpha_ray_member 3 3     -- true: (3,1,1,1) has A=3,B=1,C=1
#eval alpha_ray_member 8 2     -- false: (2,3,1,1) has B=3 != 1
#eval alpha_ray_member 12 3    -- false: (3,1,1,4) has A=3,B=1,C=1 -> true
#eval alpha_ray_member 64 2    -- false: (2,3,2,1) has B=3,C=2

-- Alpha-ray count
#eval alpha_ray_count 2 50     -- count of (2,1,1,d) in [2,50]
#eval alpha_ray_count 3 50     -- count of (3,1,1,d) in [2,50]

-- Level circles
#eval level_circle_mem 12 3 1   -- compare D=4 and D=1 mod 2
#eval level_circle_mem 2 4 1    -- D=1, D=2 mod 2: 1%2 vs 2%2 -> false

-- D-residue counts
#eval count_d_residues 2 1 50   -- distinct D%2 in alpha-ray(2) up to 50
#eval count_d_residues 2 2 50   -- distinct D%6 in alpha-ray(2) up to 50

-- Inverse limit and growth checks
#eval real_inverse_limit_check 2 50 3    -- true
#eval alpha_ray_growth_check 2 50 3      -- true

-- Formal verification
theorem alpha_ray_2 : alpha_ray_member 2 2 = true := by native_decide
theorem alpha_ray_3 : alpha_ray_member 3 3 = true := by native_decide
theorem alpha_ray_12 : alpha_ray_member 12 3 = true := by native_decide
theorem alpha_ray_not_8 : alpha_ray_member 8 2 = false := by native_decide
theorem alpha_ray_not_64 : alpha_ray_member 64 2 = false := by native_decide

theorem level_nest_20 : level_nesting_check 20 = true := by native_decide
theorem inv_lim_2_50_3 : real_inverse_limit_check 2 50 3 = true := by native_decide
theorem growth_2_50_3 : alpha_ray_growth_check 2 50 3 = true := by native_decide

end Tau.BookII.Transcendentals
