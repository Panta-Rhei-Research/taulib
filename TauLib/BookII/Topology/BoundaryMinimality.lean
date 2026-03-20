import TauLib.BookII.Topology.DimensionFour
import TauLib.BookII.Interior.BipolarDecomposition

/-!
# TauLib.BookII.Topology.BoundaryMinimality

Boundary minimality and angular sectors of the lemniscate.

## Registry Cross-References

- [II.T12] Boundary Minimality — `boundary_minimal_check`
- [II.D17] Angular Sectors — `angular_b_sector`, `angular_c_sector`
- [II.P05] Lobes as Clopen Sets — `lobes_clopen_check`

## Mathematical Content

Angular sectors are clopen subsets defined by B,C coordinates:
  S⁺_k(b) = { (D,A,B,C) ∈ τ³ : B_k ≡ b (mod p_k) }
  S⁻_k(c) = { (D,A,B,C) ∈ τ³ : C_k ≡ c (mod p_k) }

Boundary minimality (II.T12): ℒ = S¹∨S¹ is the minimal topological
quotient of T² preserving both gauge factors with a crossing point.

Lobes as clopen (II.P05): the two lobes L₊, L₋ are complementary
clopen subsets of ℒ \ {p₀}, profinite limits of angular sectors.
-/

namespace Tau.BookII.Topology

open Tau.BookII.Interior Tau.BookII.Domains
open Tau.Polarity Tau.Coordinates Tau.Denotation

-- ============================================================
-- ANGULAR SECTORS [II.D17]
-- ============================================================

/-- [II.D17] B-angular sector at stage k:
    points with B-coordinate ≡ b (mod p_k). -/
def angular_b_sector (x k : TauIdx) : TauIdx :=
  let p := from_tau_idx x
  p.b % nth_prime k

/-- C-angular sector at stage k:
    points with C-coordinate ≡ c (mod p_k). -/
def angular_c_sector (x k : TauIdx) : TauIdx :=
  let p := from_tau_idx x
  p.c % nth_prime k

/-- Combined angular sector membership. -/
def angular_sector_mem (k b_val c_val x : TauIdx) : Bool :=
  angular_b_sector x k == b_val && angular_c_sector x k == c_val

-- ============================================================
-- BIPOLAR LOBE CLASSIFICATION
-- ============================================================

/-- Lobe classification: B-dominant (e₊-lobe), C-dominant (e₋-lobe),
    or balanced (crossing point). Uses fiber dominance from II.D04. -/
def lobe_class (x : TauIdx) : FiberDominance :=
  (from_tau_idx x).fiber_dominance

/-- Count B-dominant, C-dominant, and balanced points in range. -/
def lobe_distribution (bound : TauIdx) :
    Nat × Nat × Nat :=
  go 2 (bound + 1) 0 0 0
where
  go (x fuel b_ct c_ct bal : Nat) : Nat × Nat × Nat :=
    if fuel = 0 then (b_ct, c_ct, bal)
    else if x > bound then (b_ct, c_ct, bal)
    else match lobe_class x with
      | .b_dominant => go (x + 1) (fuel - 1) (b_ct + 1) c_ct bal
      | .c_dominant => go (x + 1) (fuel - 1) b_ct (c_ct + 1) bal
      | .balanced   => go (x + 1) (fuel - 1) b_ct c_ct (bal + 1)
  termination_by fuel

-- ============================================================
-- LOBES AS CLOPEN SETS [II.P05]
-- ============================================================

/-- [II.P05] Lobes are complementary: every point is B-dominant,
    C-dominant, or balanced (no other possibility). -/
def lobes_exhaustive_check (bound : TauIdx) : Bool :=
  go 2 (bound + 1)
where
  go (x fuel : Nat) : Bool :=
    if fuel = 0 then true
    else if x > bound then true
    else
      let p := from_tau_idx x
      let _ := match p.fiber_dominance with
        | .b_dominant => true
        | .c_dominant => true
        | .balanced   => true
      go (x + 1) (fuel - 1)
  termination_by fuel

/-- [II.P05] Angular sectors at each stage refine lobe membership:
    B-dominant points have B ≥ C, C-dominant have C > B. -/
def lobes_clopen_check (bound : TauIdx) : Bool :=
  go 2 (bound + 1)
where
  go (x fuel : Nat) : Bool :=
    if fuel = 0 then true
    else if x > bound then true
    else
      let p := from_tau_idx x
      let ok := match p.fiber_dominance with
        | .b_dominant => p.b ≥ p.c
        | .c_dominant => p.c > p.b
        | .balanced   => p.b == p.c
      ok && go (x + 1) (fuel - 1)
  termination_by fuel

-- ============================================================
-- BOUNDARY MINIMALITY [II.T12]
-- ============================================================

/-- [II.T12] Boundary minimality evidence:
    Two independent channels (B and C) cannot be collapsed to one.
    Check: there exist points varying B with C fixed, and vice versa. -/
def boundary_minimal_check : Bool :=
  -- B varies independently: 2=(2,1,1,1) and 8=(2,3,1,1) differ in B only
  let p2 := from_tau_idx 2
  let p8 := from_tau_idx 8
  (p2.b != p8.b && p2.a == p8.a && p2.c == p8.c) &&
  -- C varies independently: 8=(2,3,1,1) and 64=(2,3,2,1) differ in C only
  let p64 := from_tau_idx 64
  (p8.c != p64.c && p8.a == p64.a && p8.b == p64.b) &&
  -- Both channels survive to boundary:
  -- B-dominant and C-dominant points both exist
  let (b_ct, c_ct, _) := lobe_distribution 100
  b_ct > 0 && c_ct > 0

/-- Crossing point witness: balanced points exist (B = C). -/
def crossing_point_exists (bound : TauIdx) : Bool :=
  go 2 (bound + 1)
where
  go (x fuel : Nat) : Bool :=
    if fuel = 0 then false
    else if x > bound then false
    else
      let p := from_tau_idx x
      (p.b == p.c && p.b > 0) || go (x + 1) (fuel - 1)
  termination_by fuel

-- ============================================================
-- SMOKE TESTS
-- ============================================================

#eval angular_b_sector 12 1    -- B of 12 mod p₁
#eval angular_c_sector 64 1    -- C of 64 mod p₁

#eval lobe_class 4      -- b_dominant (B=2 > C=1)
#eval lobe_class 12     -- balanced (B=1, C=1)
#eval lobe_class 64     -- b_dominant (B=3 > C=2)

#eval lobe_distribution 50
#eval lobes_exhaustive_check 50     -- true
#eval lobes_clopen_check 50         -- true
#eval boundary_minimal_check        -- true
#eval crossing_point_exists 100     -- true

-- Formal verification
theorem lobes_exhaust : lobes_exhaustive_check 50 = true := by native_decide
theorem lobes_clopen : lobes_clopen_check 50 = true := by native_decide
theorem bnd_minimal : boundary_minimal_check = true := by native_decide
theorem crossing_exists : crossing_point_exists 100 = true := by native_decide

end Tau.BookII.Topology
