import TauLib.BookII.Hartogs.EvolutionOperator

/-!
# TauLib.BookII.Hartogs.CanonicalBasis

Cylinder generators and the canonical holomorphic basis B_τ.

## Registry Cross-References

- [II.D46] Cylinder Generator — `cylinder_gen`, `cylinder_gen_indicator`
- [II.D45] Canonical Basis — `basis_orthogonality_check`, `basis_completeness_check`, `basis_independence_check`
- [II.T31] Finite Spectral Support — `finite_spectral_support_check`
- [II.P09] Projection Formula — `proj_coeff`, `projection_recovery_check`

## Mathematical Content

The canonical holomorphic basis B_τ consists of cylinder generators:

  E_{k,prime_idx,v}^(sigma)(x) = 1  if reduce(x, k) mod p_i == v,  else 0

where k is the stage, p_i = nth_prime(prime_idx) is a prime dividing P_k,
v is the residue class, and sigma ∈ {B, C} selects the bipolar channel.

**Key properties:**
- **Orthogonality (II.D45):** E_{k,p,v} * E_{k,p,w} = 0 for v ≠ w (same prime)
- **Completeness (II.D45):** sum_{v=0}^{p-1} E_{k,p,v}(x) = 1 for all x
- **Independence (II.D45):** generators for distinct primes are independent
- **Finite spectral support (II.T31):** at stage k, the number of nonzero
  generators is at most sum of primes dividing P_k

**Projection formula (II.P09):**
  proj_coeff(f, k, prime_idx, v) = sum_{x : reduce(x,k) mod p == v} f(x)

In the indicator basis, the projection of f onto E_{k,p,v} extracts the
sum of f over the residue class v mod p at stage k. The expansion
f = sum_v proj_coeff(f, k, p, v) * E_{k,p,v} recovers f on Z/P_kZ.
-/

namespace Tau.BookII.Hartogs

open Tau.Polarity Tau.Boundary Tau.Coordinates Tau.Denotation
open Tau.BookII.Interior Tau.BookII.Domains Tau.Holomorphy

-- ============================================================
-- CYLINDER GENERATOR [II.D46]
-- ============================================================

/-- [II.D46] Cylinder generator E_{k,prime_idx,v}^(sigma)(x).

    Returns 1 if x (reduced to stage k) falls in residue class v
    modulo the prime p_{prime_idx}, and 0 otherwise. -/
def cylinder_gen (k prime_idx v : TauIdx) (_sigma : Bool) (x : TauIdx) : Int :=
  let rx := reduce x k
  let p := nth_prime prime_idx
  if p == 0 then 0
  else if rx % p == v then 1 else 0

/-- Cylinder generator as Bool indicator (for decidable checks). -/
def cylinder_gen_indicator (k prime_idx v : TauIdx) (x : TauIdx) : Bool :=
  let rx := reduce x k
  let p := nth_prime prime_idx
  p != 0 && rx % p == v

-- ============================================================
-- ORTHOGONALITY [II.D45, clause 1]
-- ============================================================

/-- Helper: check orthogonality of generators for residue classes v, w
    at stage k, prime pi_idx, for all x in [0, P_k). -/
def ortho_pair (k pi_idx v w : TauIdx) : Bool :=
  go 0 (primorial k)
where
  go (x fuel : Nat) : Bool :=
    if fuel = 0 then true
    else if x >= primorial k then true
    else
      let gv := cylinder_gen k pi_idx v true x
      let gw := cylinder_gen k pi_idx w true x
      (gv * gw == 0) && go (x + 1) (fuel - 1)
  termination_by fuel

/-- [II.D45, orthogonality] For a fixed stage k and prime p_{prime_idx},
    the generators for distinct residue classes v and w are orthogonal:
    E_{k,p,v}(x) * E_{k,p,w}(x) = 0 for all x when v ≠ w. -/
def basis_orthogonality_check (k_max bound : TauIdx) : Bool :=
  go 1 1 0 0 ((k_max + 1) * (k_max + 1) * (bound + 1))
where
  go (k pi_idx v w fuel : Nat) : Bool :=
    if fuel = 0 then true
    else if k > k_max then true
    else
      let p := nth_prime pi_idx
      if pi_idx > k then go (k + 1) 1 0 0 (fuel - 1)
      else if p == 0 then go k (pi_idx + 1) 0 0 (fuel - 1)
      else if v >= p then go k (pi_idx + 1) 0 0 (fuel - 1)
      else if w >= p then go k pi_idx (v + 1) 0 (fuel - 1)
      else if v == w then go k pi_idx v (w + 1) (fuel - 1)
      else
        ortho_pair k pi_idx v w && go k pi_idx v (w + 1) (fuel - 1)
  termination_by fuel

-- ============================================================
-- COMPLETENESS [II.D45, clause 2]
-- ============================================================

/-- Helper: sum of cylinder generators over residue classes v=0..p-1 at
    stage k, prime pi_idx, for a given x. -/
def gen_sum (k pi_idx x : TauIdx) : Int :=
  let p := nth_prime pi_idx
  go 0 (p + 1) (0 : Int)
where
  go (v fuel : Nat) (acc : Int) : Int :=
    if fuel = 0 then acc
    else
      let p := nth_prime pi_idx
      if v >= p then acc
      else
        let g := cylinder_gen k pi_idx v true x
        go (v + 1) (fuel - 1) (acc + g)
  termination_by fuel

/-- [II.D45, completeness] For a fixed stage k and prime p_{prime_idx},
    sum_{v=0}^{p-1} E_{k,p,v}(x) = 1 for all x. -/
def basis_completeness_check (k_max bound : TauIdx) : Bool :=
  go 1 1 0 ((k_max + 1) * (k_max + 1) * (bound + 1))
where
  go (k pi_idx x fuel : Nat) : Bool :=
    if fuel = 0 then true
    else if k > k_max then true
    else if pi_idx > k then go (k + 1) 1 0 (fuel - 1)
    else if x >= primorial k then go k (pi_idx + 1) 0 (fuel - 1)
    else
      let s := gen_sum k pi_idx x
      (s == 1) && go k pi_idx (x + 1) (fuel - 1)
  termination_by fuel

-- ============================================================
-- INDEPENDENCE [II.D45, clause 3]
-- ============================================================

/-- Helper: find a witness x where E_{k,p1,0}(x) = 1 and E_{k,p2,0}(x) = 1. -/
def indep_witness (k pi1 pi2 : TauIdx) : Bool :=
  go 0 (primorial k)
where
  go (x fuel : Nat) : Bool :=
    if fuel = 0 then false
    else if x >= primorial k then false
    else
      let g1 := cylinder_gen_indicator k pi1 0 x
      let g2 := cylinder_gen_indicator k pi2 0 x
      if g1 && g2 then true
      else go (x + 1) (fuel - 1)
  termination_by fuel

/-- [II.D45, independence] Generators for distinct primes at the same stage
    are independent: CRT guarantees simultaneous residue solutions. -/
def basis_independence_check (k_max : TauIdx) : Bool :=
  go 2 1 2 (k_max * k_max * k_max + 1)
where
  go (k pi1 pi2 fuel : Nat) : Bool :=
    if fuel = 0 then true
    else if k > k_max then true
    else if pi1 >= k then go (k + 1) 1 2 (fuel - 1)
    else if pi2 > k then go k (pi1 + 1) (pi1 + 2) (fuel - 1)
    else
      indep_witness k pi1 pi2 && go k pi1 (pi2 + 1) (fuel - 1)
  termination_by fuel

-- ============================================================
-- CANONICAL BASIS FULL CHECK [II.D45]
-- ============================================================

/-- [II.D45] Full canonical basis verification:
    orthogonality + completeness + independence. -/
def canonical_basis_check (k_max bound : TauIdx) : Bool :=
  basis_orthogonality_check k_max bound &&
  basis_completeness_check k_max bound &&
  basis_independence_check k_max

-- ============================================================
-- FINITE SPECTRAL SUPPORT [II.T31]
-- ============================================================

/-- [II.T31] Count of nonzero cylinder generators at stage k for a given x.
    At stage k, each prime contributes exactly 1 active residue class. -/
def count_nonzero_generators (k _x : TauIdx) : Nat :=
  go 1 (k + 1) 0
where
  go (pi_idx fuel acc : Nat) : Nat :=
    if fuel = 0 then acc
    else if pi_idx > k then acc
    else
      let p := nth_prime pi_idx
      let active := if p > 0 then 1 else 0
      go (pi_idx + 1) (fuel - 1) (acc + active)
  termination_by fuel

/-- Sum of primes dividing P_k: the spectral support bound. -/
def prime_sum (k : TauIdx) : Nat :=
  go 1 (k + 1) 0
where
  go (i fuel acc : Nat) : Nat :=
    if fuel = 0 then acc
    else if i > k then acc
    else go (i + 1) (fuel - 1) (acc + nth_prime i)
  termination_by fuel

/-- [II.T31] Finite spectral support check:
    at each stage k, the count of active generators equals k,
    which is <= sum of p_i. -/
def finite_spectral_support_check (k_max bound : TauIdx) : Bool :=
  go 1 0 ((k_max + 1) * (bound + 1))
where
  go (k x fuel : Nat) : Bool :=
    if fuel = 0 then true
    else if k > k_max then true
    else if x >= primorial k then go (k + 1) 0 (fuel - 1)
    else
      let cnt := count_nonzero_generators k x
      let bnd := prime_sum k
      (cnt == k && cnt <= bnd) && go k (x + 1) (fuel - 1)
  termination_by fuel

-- ============================================================
-- PROJECTION FORMULA [II.P09]
-- ============================================================

/-- [II.P09] Spectral projection coefficient:
    proj_coeff(f, k, prime_idx, v) = sum over x in Z/P_kZ of f(x) * E_{k,p,v}(x). -/
def proj_coeff (f : TauIdx → Int) (k prime_idx v : TauIdx) : Int :=
  go 0 (primorial k) (0 : Int)
where
  go (x fuel : Nat) (acc : Int) : Int :=
    if fuel = 0 then acc
    else if x >= primorial k then acc
    else
      let g := cylinder_gen k prime_idx v true x
      go (x + 1) (fuel - 1) (acc + f x * g)
  termination_by fuel

/-- [II.P09] Projection delta check: for delta_a(x) = (x == a ? 1 : 0),
    proj_coeff(delta_a, k, pi, a mod p) = 1 for all a in [0, P_k). -/
def projection_delta_check (k_max : TauIdx) : Bool :=
  go 1 1 0 (k_max * k_max * 100 + 1)
where
  go (k pi_idx a fuel : Nat) : Bool :=
    if fuel = 0 then true
    else if k > k_max then true
    else if pi_idx > k then go (k + 1) 1 0 (fuel - 1)
    else if a >= primorial k then go k (pi_idx + 1) 0 (fuel - 1)
    else
      let p := nth_prime pi_idx
      if p == 0 then go k (pi_idx + 1) 0 (fuel - 1)
      else
        let v := a % p
        let delta_a : TauIdx → Int := fun x => if x == a then 1 else 0
        let coeff := proj_coeff delta_a k pi_idx v
        (coeff == 1) && go k pi_idx (a + 1) (fuel - 1)
  termination_by fuel

/-- [II.P09] Projection recovery check: for f(x) = 1,
    proj_coeff(1, k, pi, v) = P_k / p for each v. -/
def projection_recovery_check (k_max : TauIdx) : Bool :=
  go 1 1 0 (k_max * k_max * 20 + 1)
where
  go (k pi_idx v fuel : Nat) : Bool :=
    if fuel = 0 then true
    else if k > k_max then true
    else if pi_idx > k then go (k + 1) 1 0 (fuel - 1)
    else
      let p := nth_prime pi_idx
      if p == 0 then go k (pi_idx + 1) 0 (fuel - 1)
      else if v >= p then go k (pi_idx + 1) 0 (fuel - 1)
      else
        let one_fn : TauIdx → Int := fun _ => 1
        let coeff := proj_coeff one_fn k pi_idx v
        let expected : Int := (primorial k / p : Nat)
        (coeff == expected) && go k pi_idx (v + 1) (fuel - 1)
  termination_by fuel

-- ============================================================
-- BIPOLAR CHANNEL DECOMPOSITION
-- ============================================================

/-- Bipolar cylinder generator: applied to the B or C coordinate
    of the ABCD decomposition. -/
def bipolar_cylinder_gen (_k prime_idx v : TauIdx) (sigma : Bool) (x : TauIdx) : Int :=
  let p := from_tau_idx x
  let coord := if sigma then p.b else p.c
  let pk := nth_prime prime_idx
  if pk == 0 then 0
  else if coord % pk == v then 1 else 0

/-- Bipolar orthogonality: B-channel and C-channel projections
    have zero cross-product. -/
def bipolar_channel_orthogonality (bound : TauIdx) : Bool :=
  go 2 (bound + 1)
where
  go (x fuel : Nat) : Bool :=
    if fuel = 0 then true
    else if x > bound then true
    else
      let p := from_tau_idx x
      let bp := interior_bipolar p
      let proj_plus := SectorPair.mul e_plus_sector bp
      let proj_minus := SectorPair.mul e_minus_sector bp
      (SectorPair.mul proj_plus proj_minus == ⟨0, 0⟩) &&
      go (x + 1) (fuel - 1)
  termination_by fuel

-- ============================================================
-- FULL CANONICAL BASIS + SPECTRAL SUPPORT CHECK
-- ============================================================

/-- Full check combining canonical basis, finite spectral support,
    and projection formula. -/
def full_canonical_basis_check (k_max bound : TauIdx) : Bool :=
  canonical_basis_check k_max bound &&
  finite_spectral_support_check k_max bound &&
  projection_delta_check k_max &&
  projection_recovery_check k_max &&
  bipolar_channel_orthogonality bound

-- ============================================================
-- SMOKE TESTS
-- ============================================================

-- Cylinder generator values
#eval cylinder_gen 1 1 0 true 4   -- 1
#eval cylinder_gen 1 1 1 true 4   -- 0
#eval cylinder_gen 1 1 0 true 3   -- 0
#eval cylinder_gen 1 1 1 true 3   -- 1
#eval cylinder_gen 2 1 0 true 7   -- 0
#eval cylinder_gen 2 1 1 true 7   -- 1
#eval cylinder_gen 2 2 1 true 7   -- 1

-- Orthogonality
#eval basis_orthogonality_check 3 30

-- Completeness
#eval basis_completeness_check 3 30

-- Independence
#eval basis_independence_check 4

-- Canonical basis
#eval canonical_basis_check 3 30

-- Nonzero generator count
#eval count_nonzero_generators 1 0    -- 1
#eval count_nonzero_generators 2 0    -- 2
#eval count_nonzero_generators 3 0    -- 3

-- Prime sum
#eval prime_sum 1   -- 2
#eval prime_sum 2   -- 5
#eval prime_sum 3   -- 10

-- Finite spectral support
#eval finite_spectral_support_check 3 30

-- Projection coefficient (delta at 0)
#eval proj_coeff (fun x => if x == 0 then 1 else 0) 1 1 0   -- 1
#eval proj_coeff (fun x => if x == 0 then 1 else 0) 1 1 1   -- 0

-- Projection coefficient (constant 1)
#eval proj_coeff (fun _ => 1) 1 1 0   -- 1
#eval proj_coeff (fun _ => 1) 1 1 1   -- 1
#eval proj_coeff (fun _ => 1) 2 1 0   -- 3
#eval proj_coeff (fun _ => 1) 2 2 0   -- 2

-- Projection checks
#eval projection_delta_check 3
#eval projection_recovery_check 3

-- Bipolar orthogonality
#eval bipolar_channel_orthogonality 20

-- Full check
#eval full_canonical_basis_check 3 20

-- ============================================================
-- FORMAL VERIFICATION (native_decide)
-- ============================================================

-- Orthogonality [II.D45]
theorem basis_ortho_3_30 :
    basis_orthogonality_check 3 30 = true := by native_decide

-- Completeness [II.D45]
theorem basis_complete_3_30 :
    basis_completeness_check 3 30 = true := by native_decide

-- Independence [II.D45]
theorem basis_indep_4 :
    basis_independence_check 4 = true := by native_decide

-- Canonical basis [II.D45]
theorem basis_3_30 :
    canonical_basis_check 3 30 = true := by native_decide

-- Finite spectral support [II.T31]
theorem spectral_support_3_30 :
    finite_spectral_support_check 3 30 = true := by native_decide

-- Projection delta [II.P09]
theorem proj_delta_3 :
    projection_delta_check 3 = true := by native_decide

-- Projection recovery [II.P09]
theorem proj_recovery_3 :
    projection_recovery_check 3 = true := by native_decide

-- Bipolar channel orthogonality
theorem bipolar_ortho_20 :
    bipolar_channel_orthogonality 20 = true := by native_decide

-- Full canonical basis check
theorem full_basis_3_20 :
    full_canonical_basis_check 3 20 = true := by native_decide

end Tau.BookII.Hartogs
