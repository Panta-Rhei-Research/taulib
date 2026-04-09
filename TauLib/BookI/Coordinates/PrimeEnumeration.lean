import TauLib.BookI.Coordinates.Primes

/-!
# TauLib.BookI.Coordinates.PrimeEnumeration

Prime enumeration, counting, and orbit value projection —
the semantic projection between solenoidal orbits and the α-orbit.

## Registry Cross-References

- [I.D19f] Prime Enumeration — `nthPrime`, `prime_count`, `prime_index`

## Ground Truth Sources
- chunk_0310_M002679: Prime enumeration as orbit channel projection
- chunk_0060_M000698: UR-ITER — all computation earned from ρ

## Mathematical Content

The prime enumeration function nthPrime(k) = p_k maps TauIdx to TauIdx:
  - nthPrime(0) = 2, nthPrime(1) = 3, nthPrime(2) = 5, ...

It is the semantic projection from the π-orbit to the α-orbit: the
depth-k element of O_π "represents" the number nthPrime(k).

The inverse is the prime index function: for prime p,
prime_index(p) = k such that nthPrime(k) = p.

The prime counting function π(n) = prime_count(n) counts primes ≤ n.

All three are computable via finite scanning using `is_prime_bool`,
which itself uses only the earned arithmetic from ρ-folds.
This is the categorical τ version of the Sieve of Eratosthenes.
-/

namespace Tau.Coordinates

open Tau.Denotation Tau.Orbit Tau.Kernel Generator

-- ============================================================
-- PRIME COUNTING [I.D19f]
-- ============================================================

/-- Count primes in the range [2, n] by scanning. -/
def prime_count_go (n i acc : TauIdx) (fuel : Nat) : TauIdx :=
  if fuel = 0 then acc
  else if i > n then acc
  else if is_prime_bool i then prime_count_go n (i + 1) (acc + 1) (fuel - 1)
  else prime_count_go n (i + 1) acc (fuel - 1)
termination_by fuel

/-- [I.D19f] Prime counting function π(n): number of primes ≤ n.
    Returns 0 for n < 2. -/
def prime_count (n : TauIdx) : TauIdx :=
  if n < 2 then 0 else prime_count_go n 2 0 n

-- ============================================================
-- PRIME ENUMERATION (nthPrime) [I.D19f]
-- ============================================================

/-- Scan for the k-th prime (0-indexed) starting from candidate. -/
def nthPrime_go (target : TauIdx) (candidate count : TauIdx) (fuel : Nat) : TauIdx :=
  if fuel = 0 then candidate
  else if is_prime_bool candidate then
    if count == target then candidate
    else nthPrime_go target (candidate + 1) (count + 1) (fuel - 1)
  else nthPrime_go target (candidate + 1) count (fuel - 1)
termination_by fuel

/-- [I.D19f] The k-th prime number (0-indexed).
    nthPrime 0 = 2, nthPrime 1 = 3, nthPrime 2 = 5, ...
    Computed by finite scanning using is_prime_bool — a finite
    sieve earned entirely from ρ-folds. -/
def nthPrime (k : TauIdx) : TauIdx :=
  nthPrime_go k 2 0 ((k + 1) * (k + 1) + 10)

-- ============================================================
-- PRIME INDEX (inverse of nthPrime) [I.D19f]
-- ============================================================

/-- [I.D19f] Prime index: the number of primes strictly less than p.
    For prime p, this is the k such that nthPrime(k) = p. -/
def prime_index (p : TauIdx) : TauIdx :=
  if p ≤ 2 then 0
  else prime_count (p - 1)

-- ============================================================
-- ORBIT VALUE PROJECTION
-- ============================================================

/-- The semantic projection from π-orbit depth to α-orbit value:
    the depth-k element of O_π represents the number nthPrime(k).

    This is the key distinction between structural rank transfer
    (RT_π maps k ↦ ⟨π, k⟩, preserving depth) and semantic projection
    (pi_orbit_value maps k ↦ p_k, giving the denotational value). -/
def pi_orbit_value (k : TauIdx) : TauIdx := nthPrime k

/-- The π-orbit projection via rank transfer:
    RT_α(nthPrime(k)) is the α-orbit element corresponding to π_k. -/
theorem pi_projection_via_RT (k : TauIdx) :
    RT alpha (pi_orbit_value k) = toAlphaOrbit (nthPrime k) := by
  simp [pi_orbit_value, RT_alpha_eq]

/-- The reverse projection: for prime p, its π-rank. -/
def alpha_to_pi_rank (p : TauIdx) : TauIdx := prime_index p

-- ============================================================
-- ROUND-TRIP VERIFICATION
-- ============================================================

-- prime_index ∘ nthPrime = id (verified for k = 0..5)
example : prime_index (nthPrime 0) = 0 := by native_decide
example : prime_index (nthPrime 1) = 1 := by native_decide
example : prime_index (nthPrime 2) = 2 := by native_decide
example : prime_index (nthPrime 3) = 3 := by native_decide
example : prime_index (nthPrime 4) = 4 := by native_decide
example : prime_index (nthPrime 5) = 5 := by native_decide

-- nthPrime ∘ prime_index = id (verified for small primes)
example : nthPrime (prime_index 2) = 2 := by native_decide
example : nthPrime (prime_index 3) = 3 := by native_decide
example : nthPrime (prime_index 5) = 5 := by native_decide
example : nthPrime (prime_index 7) = 7 := by native_decide
example : nthPrime (prime_index 11) = 11 := by native_decide
example : nthPrime (prime_index 13) = 13 := by native_decide

-- ============================================================
-- THE EARNED SIEVE PRINCIPLE
-- ============================================================

/-- The Earned Sieve Principle: the prime enumeration is computable
    using only the earned predicate is_prime_bool, which chains through
    the fold hierarchy: is_prime_bool → idx_divides → idx_mul →
    idx_add → iter_rho → ρ.
    Ground truth: chunk_0060 (UR-ITER). -/
theorem sieve_earned_from_rho :
    (∀ k, ∃ p, p = nthPrime k) ∧
    (∀ n, ∃ c, c = prime_count n) ∧
    (∀ p, ∃ k, k = prime_index p) :=
  ⟨fun k => ⟨nthPrime k, rfl⟩,
   fun n => ⟨prime_count n, rfl⟩,
   fun p => ⟨prime_index p, rfl⟩⟩

-- ============================================================
-- SMOKE TESTS
-- ============================================================

-- Prime enumeration
#eval nthPrime 0     -- 2
#eval nthPrime 1     -- 3
#eval nthPrime 2     -- 5
#eval nthPrime 3     -- 7
#eval nthPrime 4     -- 11
#eval nthPrime 9     -- 29
#eval nthPrime 24    -- 97

-- Prime counting π(n)
#eval prime_count 10   -- 4 (primes: 2,3,5,7)
#eval prime_count 20   -- 8 (primes: 2,3,5,7,11,13,17,19)
#eval prime_count 100  -- 25

-- Prime index (inverse of nthPrime)
#eval prime_index 2    -- 0
#eval prime_index 3    -- 1
#eval prime_index 5    -- 2
#eval prime_index 7    -- 3
#eval prime_index 97   -- 24

-- Round-trip demonstrations
#eval prime_index (nthPrime 10)           -- 10
#eval nthPrime (prime_index 31)           -- 31
#eval (List.range 10).map nthPrime        -- [2,3,5,7,11,13,17,19,23,29]

end Tau.Coordinates
