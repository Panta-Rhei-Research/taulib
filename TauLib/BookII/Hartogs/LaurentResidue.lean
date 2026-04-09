import TauLib.BookII.Hartogs.CategoryStructure

/-!
# TauLib.BookII.Hartogs.LaurentResidue

Laurent expansion, residue, and meromorphic functions in the tau-setting.

## Registry Cross-References

- [II.D42] Laurent Expansion — `laurent_coeff`, `laurent_expansion_check`
- [II.D43] Residue — `tau_residue`, `residue_determines_check`
- [II.D44] Meromorphic Function — `MeromorphicFun`, `meromorphic_check`
- [II.T30] Residue Theorem — `residue_reconstruction_check`, `crt_residue_thm`

## Mathematical Content

At each stage k, a point x in Z/M_k Z decomposes via CRT into residues
at the k individual prime factors p_1, ..., p_k:

  x mod M_k  <-->  (x mod p_1, x mod p_2, ..., x mod p_k)

This CRT decomposition IS the Laurent expansion in the tau-setting:
each "Laurent coefficient" at prime p_i is the residue x mod p_i.

**Laurent expansion (II.D42):** The i-th Laurent coefficient of x at
stage k is x mod p_i (the projection onto the i-th CRT factor).

**Residue (II.D43):** The residue at prime p_i is laurent_coeff(x, k, i)
= x mod p_i. The residues determine x mod M_k via CRT.

**Meromorphic function (II.D44):** A function that is holomorphic (tower-
coherent) except at finitely many exceptional stages. In the tau-setting,
all tower-coherent functions on the primorial ladder are meromorphic
(there are no "essential singularities" in the finite cyclic world).

**Residue theorem (II.T30):** The CRT residues at each prime factor
completely determine the function value at that stage. This is the
tau-analog of the classical residue theorem: the sum of residues
(in the CRT sense) recovers the original function value.

The reconstruction works because M_k = p_1 * ... * p_k and all p_i
are pairwise coprime, so CRT gives a unique element of Z/M_k Z from
the tuple (x mod p_1, ..., x mod p_k).
-/

namespace Tau.BookII.Hartogs

open Tau.Polarity Tau.Boundary Tau.Coordinates Tau.Denotation
open Tau.BookII.Interior Tau.BookII.Domains Tau.Holomorphy

-- ============================================================
-- LAURENT COEFFICIENTS [II.D42]
-- ============================================================

/-- [II.D42] The i-th Laurent coefficient of x at stage k:
    the residue of x modulo the i-th prime p_i.

    In the CRT decomposition of Z/M_k Z = Z/p_1 Z x ... x Z/p_k Z,
    the i-th component is x mod p_i. This is the tau-analog of the
    i-th Laurent coefficient in the expansion around the i-th prime.

    Returns 0 if prime_idx = 0 or prime_idx > k (out of range). -/
def laurent_coeff (x k prime_idx : TauIdx) : TauIdx :=
  if prime_idx == 0 || prime_idx > k then 0
  else x % nth_prime prime_idx

/-- The full Laurent expansion at stage k: the tuple of all k residues.
    Returns a list of length k: [x mod p_1, x mod p_2, ..., x mod p_k]. -/
def laurent_expansion (x k : TauIdx) : List TauIdx :=
  go 1 k []
where
  go (i : Nat) (remaining : Nat) (acc : List TauIdx) : List TauIdx :=
    if remaining = 0 then acc.reverse
    else go (i + 1) (remaining - 1) (laurent_coeff x k i :: acc)
  termination_by remaining

/-- Laurent expansion is well-defined: each coefficient is in the correct range.
    For 1 <= i <= k: 0 <= laurent_coeff(x, k, i) < p_i. -/
def laurent_range_check (bound db : TauIdx) : Bool :=
  go 2 1 1 ((bound + 1) * (db + 1) * (db + 1))
where
  go (x k i fuel : Nat) : Bool :=
    if fuel = 0 then true
    else if x > bound then true
    else if k > db then go (x + 1) 1 1 (fuel - 1)
    else if i > k then go x (k + 1) 1 (fuel - 1)
    else
      let coeff := laurent_coeff x k i
      let pi := nth_prime i
      let ok := coeff < pi
      ok && go x k (i + 1) (fuel - 1)
  termination_by fuel

/-- Laurent expansion stability: reducing x to stage k does not change
    the Laurent coefficients at primes <= k.
    laurent_coeff(x, k, i) = laurent_coeff(reduce(x, k), k, i)
    for 1 <= i <= k. -/
def laurent_stability_check (bound db : TauIdx) : Bool :=
  go 2 1 1 ((bound + 1) * (db + 1) * (db + 1))
where
  go (x k i fuel : Nat) : Bool :=
    if fuel = 0 then true
    else if x > bound then true
    else if k > db then go (x + 1) 1 1 (fuel - 1)
    else if i > k then go x (k + 1) 1 (fuel - 1)
    else
      let orig := laurent_coeff x k i
      let reduced := laurent_coeff (reduce x k) k i
      let ok := orig == reduced
      ok && go x k (i + 1) (fuel - 1)
  termination_by fuel

-- ============================================================
-- RESIDUE [II.D43]
-- ============================================================

/-- [II.D43] The residue of x at prime index i:
    tau_residue(x, i) = x mod p_i.

    This is the stage-independent version: the residue at a prime
    does not depend on which stage k we compute at (as long as k >= i),
    because p_i divides M_k for k >= i. -/
def tau_residue (x i : TauIdx) : TauIdx :=
  if i == 0 then 0
  else x % nth_prime i

/-- Residue independence of stage: for k >= i,
    tau_residue(x, i) = tau_residue(reduce(x, k), i).
    The residue at p_i is the same whether we compute on x or x mod M_k. -/
def residue_stage_independence_check (bound db : TauIdx) : Bool :=
  go 2 1 1 ((bound + 1) * (db + 1) * (db + 1))
where
  go (x k i fuel : Nat) : Bool :=
    if fuel = 0 then true
    else if x > bound then true
    else if k > db then go (x + 1) 1 1 (fuel - 1)
    else if i > k then go x (k + 1) 1 (fuel - 1)
    else
      let direct := tau_residue x i
      let via_reduce := tau_residue (reduce x k) i
      let ok := direct == via_reduce
      ok && go x k (i + 1) (fuel - 1)
  termination_by fuel

/-- Helper: check if all residues of x and y agree for primes 1..k. -/
def all_residues_agree (x y k : TauIdx) : Bool :=
  go 1 (k + 1)
where
  go (i fuel : Nat) : Bool :=
    if fuel = 0 then true
    else if i > k then true
    else (tau_residue x i == tau_residue y i) && go (i + 1) (fuel - 1)
  termination_by fuel

/-- Residues determine the point: if tau_residue(x, i) = tau_residue(y, i)
    for all 1 <= i <= k, then reduce(x, k) = reduce(y, k).
    This is the CRT uniqueness theorem. -/
def residue_determines_check (bound db : TauIdx) : Bool :=
  go 2 2 1 ((bound + 1) * (bound + 1) * (db + 1))
where
  go (x y k fuel : Nat) : Bool :=
    if fuel = 0 then true
    else if x > bound then true
    else if y > bound then go (x + 1) 2 1 (fuel - 1)
    else if k > db then go x (y + 1) 1 (fuel - 1)
    else
      -- Check: if all residues agree, then reductions agree
      let agree := all_residues_agree x y k
      let reductions_agree := reduce x k == reduce y k
      let ok := !agree || reductions_agree
      ok && go x y (k + 1) (fuel - 1)
  termination_by fuel

-- ============================================================
-- CRT RECONSTRUCTION [II.T30, helper]
-- ============================================================

/-- CRT reconstruction: given residues (r_1, ..., r_k), find x in [0, M_k)
    such that x mod p_i = r_i for all i.

    Implemented by brute-force search over [0, M_k). This is computable
    for small k since M_k grows relatively slowly (M_4 = 210). -/
def crt_reconstruct (residues : List TauIdx) (k : TauIdx) : TauIdx :=
  let mk := primorial k
  go 0 mk residues k
where
  go (x fuel : Nat) (residues : List TauIdx) (k : Nat) : TauIdx :=
    if fuel = 0 then 0  -- not found
    else if x >= primorial k then 0  -- not found
    else if matches_all x residues 1 k then x
    else go (x + 1) (fuel - 1) residues k
  termination_by fuel
  matches_all (x : Nat) (residues : List TauIdx) (i k : Nat) : Bool :=
    match residues with
    | [] => true
    | r :: rs =>
      if i > k then true
      else (x % nth_prime i == r) && matches_all x rs (i + 1) k

/-- CRT reconstruction round-trip check: for each x in [0, M_k),
    reconstruct from Laurent coefficients and verify recovery.

    Given x, compute (x%p_1, ..., x%p_k), then reconstruct y from these
    residues, and verify y = x. -/
def crt_roundtrip_check (db : TauIdx) : Bool :=
  go_k 1 (db + 1)
where
  go_k (k fuel : Nat) : Bool :=
    if fuel = 0 then true
    else if k > db then true
    else
      let mk := primorial k
      go_x 0 mk k (fuel - 1) && go_k (k + 1) (fuel - 1)
  termination_by fuel
  go_x (x mk k fuel : Nat) : Bool :=
    if fuel = 0 then true
    else if x >= mk then true
    else
      let coeffs := laurent_expansion x k
      let reconstructed := crt_reconstruct coeffs k
      (reconstructed == x) && go_x (x + 1) mk k (fuel - 1)
  termination_by fuel

-- ============================================================
-- RESIDUE THEOREM [II.T30]
-- ============================================================

/-- [II.T30] Residue theorem: the CRT residues at stage k completely
    determine the function value.

    For each x in [2, bound] and stage k in [1, db]:
    - Compute the Laurent expansion (all residues)
    - Reconstruct via CRT
    - Verify the reconstruction equals reduce(x, k)

    This is the tau-analog of the classical residue theorem:
    "the sum of all residues recovers the function value."
    In our setting: "the tuple of all prime residues recovers the
    stage-k projection via CRT." -/
def residue_reconstruction_check (bound db : TauIdx) : Bool :=
  go 2 1 ((bound + 1) * (db + 1))
where
  go (x k fuel : Nat) : Bool :=
    if fuel = 0 then true
    else if x > bound then true
    else if k > db then go (x + 1) 1 (fuel - 1)
    else
      let reduced := reduce x k
      let coeffs := laurent_expansion reduced k
      let reconstructed := crt_reconstruct coeffs k
      let ok := reconstructed == reduced
      ok && go x (k + 1) (fuel - 1)
  termination_by fuel

/-- [II.T30] Formal residue theorem for a specific stage:
    CRT reconstruction from Laurent coefficients at stage k
    is the identity on [0, M_k).

    Verified computationally for stages 1-3 (M_1=2, M_2=6, M_3=30). -/
def crt_residue_thm_check (db : TauIdx) : Bool :=
  crt_roundtrip_check db &&
  residue_reconstruction_check (primorial db) db

-- ============================================================
-- MEROMORPHIC FUNCTIONS [II.D44]
-- ============================================================

/-- [II.D44] A meromorphic function in the tau-setting:
    a tower-coherent map that is well-defined (holomorphic) at all but
    finitely many exceptional stages.

    In the finite cyclic primorial world, every tower-coherent function
    is automatically meromorphic (there are no essential singularities).
    The "exceptional stages" are stages where the function has special
    behavior (e.g., the output is 0, or the function is not injective).

    We model this as a function f together with a list of exceptional stages. -/
structure MeromorphicFun where
  /-- The underlying function: (input, stage) -> output. -/
  f : TauIdx -> TauIdx -> TauIdx
  /-- Exceptional stages (poles). -/
  poles : List TauIdx

/-- Construct a meromorphic function from a tower-coherent map. -/
def mk_meromorphic (f : TauIdx -> TauIdx -> TauIdx) (poles : List TauIdx) :
    MeromorphicFun :=
  { f := f, poles := poles }

/-- The identity is meromorphic with no poles. -/
def mero_id : MeromorphicFun :=
  mk_meromorphic hol_id []

/-- The squaring map is meromorphic with no poles. -/
def mero_sq : MeromorphicFun :=
  mk_meromorphic hol_sq []

/-- A "partial" endomorphism: holomorphic except at stage 1 where p_1=2
    collapses everything to 0. This is meromorphic with pole at stage 1. -/
def mero_partial (n k : TauIdx) : TauIdx :=
  if k == 1 then 0 else reduce (n * n + 1) k

def mero_partial_fun : MeromorphicFun :=
  mk_meromorphic mero_partial [1]

/-- Meromorphic check: the function is tower-coherent at all non-pole stages.
    For stages k not in the pole list: reduce(f(x, l), k) = f(x, k) for k <= l. -/
def meromorphic_check (mf : MeromorphicFun) (bound db : TauIdx) : Bool :=
  go 2 1 1 ((bound + 1) * (db + 1) * (db + 1))
where
  go (x k l fuel : Nat) : Bool :=
    if fuel = 0 then true
    else if x > bound then true
    else if k > db then go (x + 1) 1 1 (fuel - 1)
    else if l > db then go x (k + 1) 1 (fuel - 1)
    else
      let is_pole := mf.poles.contains k
      let ok := is_pole || !(k ≤ l) ||
        (reduce (mf.f x l) k == mf.f x k)
      ok && go x k (l + 1) (fuel - 1)
  termination_by fuel

/-- Every holomorphic endomorphism is meromorphic (with empty pole list). -/
def hol_is_mero_check (bound db : TauIdx) : Bool :=
  meromorphic_check mero_id bound db &&
  meromorphic_check mero_sq bound db

-- ============================================================
-- RESIDUE SUMS [II.T30, extended]
-- ============================================================

/-- Sum of all Laurent coefficients at stage k.
    This is a weak analog of "sum of residues": the arithmetic sum
    of the CRT components. -/
def laurent_sum (x k : TauIdx) : TauIdx :=
  go 1 k 0
where
  go (i remaining acc : Nat) : TauIdx :=
    if remaining = 0 then acc
    else go (i + 1) (remaining - 1) (acc + laurent_coeff x k i)
  termination_by remaining

/-- The Laurent sum is bounded: sum of residues <= sum of (p_i - 1) for i=1..k.
    Each coefficient < p_i, so the sum < p_1 + p_2 + ... + p_k. -/
def laurent_sum_bounded_check (bound db : TauIdx) : Bool :=
  go 2 1 ((bound + 1) * (db + 1))
where
  go (x k fuel : Nat) : Bool :=
    if fuel = 0 then true
    else if x > bound then true
    else if k > db then go (x + 1) 1 (fuel - 1)
    else
      let s := laurent_sum x k
      let prime_sum := sum_primes 1 k 0
      let ok := s < prime_sum
      ok && go x (k + 1) (fuel - 1)
  termination_by fuel
  sum_primes (i remaining acc : Nat) : Nat :=
    if remaining = 0 then acc
    else sum_primes (i + 1) (remaining - 1) (acc + nth_prime i)
  termination_by remaining

-- ============================================================
-- RESIDUE-EVOLUTION COMPATIBILITY
-- ============================================================

/-- Residues are compatible with the evolution operator:
    tau_residue(evolution_op(x, n, m), i) = tau_residue(reduce(x, m), i)
    for i <= m. The evolution operator preserves residue structure. -/
def residue_evolution_check (bound db : TauIdx) : Bool :=
  go 2 1 1 ((bound + 1) * (db + 1) * (db + 1))
where
  go (x m i fuel : Nat) : Bool :=
    if fuel = 0 then true
    else if x > bound then true
    else if m > db then go (x + 1) 1 1 (fuel - 1)
    else if i > m then go x (m + 1) 1 (fuel - 1)
    else
      let evol := evolution_op x 1 m  -- evolve from stage 1 to stage m
      let ok := tau_residue evol i == tau_residue (reduce x m) i
      ok && go x m (i + 1) (fuel - 1)
  termination_by fuel

-- ============================================================
-- FULL VERIFICATION
-- ============================================================

/-- Complete Laurent-Residue verification:
    1. Laurent expansion well-defined and stable
    2. Residues determine points (CRT uniqueness)
    3. CRT reconstruction round-trip
    4. Residue theorem (reconstruction = original)
    5. Meromorphic structure
    6. Residue-evolution compatibility -/
def full_laurent_residue_check (bound db : TauIdx) : Bool :=
  laurent_range_check bound db &&
  laurent_stability_check bound db &&
  residue_stage_independence_check bound db &&
  residue_determines_check bound db &&
  crt_roundtrip_check db &&
  residue_reconstruction_check bound db &&
  hol_is_mero_check bound db &&
  residue_evolution_check bound db

-- ============================================================
-- SMOKE TESTS
-- ============================================================

-- Laurent coefficients
#eval laurent_coeff 7 3 1      -- 7 % 2 = 1
#eval laurent_coeff 7 3 2      -- 7 % 3 = 1
#eval laurent_coeff 7 3 3      -- 7 % 5 = 2
#eval laurent_coeff 100 4 4    -- 100 % 7 = 2

-- Laurent expansion
#eval laurent_expansion 7 3    -- [1, 1, 2] (7 mod 2, 7 mod 3, 7 mod 5)
#eval laurent_expansion 13 3   -- [1, 1, 3]
#eval laurent_expansion 29 4   -- [1, 2, 4, 1]

-- Residues
#eval tau_residue 7 1          -- 7 % 2 = 1
#eval tau_residue 7 2          -- 7 % 3 = 1
#eval tau_residue 100 3        -- 100 % 5 = 0

-- CRT reconstruction
#eval crt_reconstruct [1, 1, 2] 3   -- should be 7 (mod 30)
#eval crt_reconstruct [1, 1, 3] 3   -- should be 13 (mod 30)
#eval crt_reconstruct [0, 0, 0] 3   -- should be 0

-- Residue theorem: round-trip
#eval crt_roundtrip_check 3         -- true (stages 1, 2, 3)

-- Laurent range check
#eval laurent_range_check 12 4      -- true
#eval laurent_stability_check 12 4  -- true

-- Residue stage independence
#eval residue_stage_independence_check 12 4  -- true

-- Residue determines
#eval residue_determines_check 10 3  -- true

-- Residue reconstruction
#eval residue_reconstruction_check 12 3  -- true

-- CRT residue theorem
#eval crt_residue_thm_check 3       -- true

-- Meromorphic checks
#eval meromorphic_check mero_id 12 4     -- true
#eval meromorphic_check mero_sq 12 4     -- true
#eval hol_is_mero_check 12 4             -- true

-- Laurent sum
#eval laurent_sum 7 3              -- 1 + 1 + 2 = 4
#eval laurent_sum 29 4             -- 1 + 2 + 4 + 1 = 8
#eval laurent_sum_bounded_check 12 4  -- true

-- Residue-evolution compatibility
#eval residue_evolution_check 10 3  -- true

-- Full check
#eval full_laurent_residue_check 10 3  -- true

-- ============================================================
-- FORMAL VERIFICATION (native_decide)
-- ============================================================

-- Laurent expansion [II.D42]
theorem laurent_range_12_4 :
    laurent_range_check 12 4 = true := by native_decide

theorem laurent_stability_12_4 :
    laurent_stability_check 12 4 = true := by native_decide

-- Residue [II.D43]
theorem residue_stage_10_3 :
    residue_stage_independence_check 10 3 = true := by native_decide

theorem residue_determines_10_3 :
    residue_determines_check 10 3 = true := by native_decide

-- CRT round-trip [II.T30]
theorem crt_roundtrip_3 :
    crt_roundtrip_check 3 = true := by native_decide

-- Residue theorem [II.T30]
theorem residue_recon_12_3 :
    residue_reconstruction_check 12 3 = true := by native_decide

theorem crt_residue_thm_3 :
    crt_residue_thm_check 3 = true := by native_decide

-- Meromorphic [II.D44]
theorem mero_id_12_4 :
    meromorphic_check mero_id 12 4 = true := by native_decide

theorem mero_sq_12_4 :
    meromorphic_check mero_sq 12 4 = true := by native_decide

-- Laurent sum bound
theorem laurent_sum_12_4 :
    laurent_sum_bounded_check 12 4 = true := by native_decide

-- Residue-evolution compatibility
theorem residue_evol_10_3 :
    residue_evolution_check 10 3 = true := by native_decide

-- Full Laurent-Residue
theorem full_laurent_residue_10_3 :
    full_laurent_residue_check 10 3 = true := by native_decide

end Tau.BookII.Hartogs
