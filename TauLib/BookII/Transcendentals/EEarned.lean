import TauLib.BookII.Transcendentals.PiEarned

/-!
# TauLib.BookII.Transcendentals.EEarned

Euler's number e earned from the factorial series and primorial growth.

## Registry Cross-References

- [II.D30] e as Iterator Eigenvalue — `e_factorial_scaled`
- [II.D31] Growth Base — `primorial_growth_check`
- [II.T23] e from Index Arithmetic — `e_convergence_check`

## Mathematical Content

e is earned from the growth rate of the primorial tower and the factorial
series e = sum_{k=0}^{N} 1/k!.

Since Float arithmetic is unreliable in Lean 4, all computations use
scaled integer arithmetic: e * 10^6 ~ 2718281.

The primorial growth P_{k+1}/P_k = p_{k+1} is super-exponential.
By PNT, ln(P_k) = sum ln(p_i) ~ k*ln(k), so the growth base
e appears naturally as the base of natural logarithms.
-/

namespace Tau.BookII.Transcendentals

open Tau.BookII.Interior Tau.BookII.Domains
open Tau.Polarity Tau.Coordinates Tau.Denotation

-- ============================================================
-- FACTORIAL SERIES FOR e [II.D30]
-- ============================================================

/-- [II.D30] e via factorial series: e = sum_{k=0}^{N} 1/k!
    Returns e * scale (approximately).
    Tracks the running factorial to avoid recomputation. -/
def e_factorial_scaled (terms scale : Nat) : Nat :=
  go 0 (terms + 1) 1 0
where
  go (k fuel factorial acc : Nat) : Nat :=
    if fuel = 0 then acc
    else if k >= terms then acc
    else
      let fact := if k == 0 then 1 else factorial * k
      let term := scale / fact
      go (k + 1) (fuel - 1) fact (acc + term)
  termination_by fuel

/-- e approximation: e * 10^6 using N terms of the factorial series. -/
def e_scaled (terms : Nat) : Nat := e_factorial_scaled terms 1000000

-- ============================================================
-- e CONVERGENCE [II.T23]
-- ============================================================

/-- [II.T23] e from index arithmetic: e * 10^6 ~ 2718281.
    The factorial series converges MUCH faster than Leibniz:
    10 terms gives 6+ digits of accuracy.
    Check: result in [2700000, 2750000]. -/
def e_convergence_check : Bool :=
  let e_approx := e_scaled 10
  e_approx > 2700000 && e_approx < 2750000

/-- Rapid convergence: fewer terms already give reasonable accuracy. -/
def e_rapid_convergence_check : Bool :=
  let e5 := e_scaled 5
  let e10 := e_scaled 10
  let e15 := e_scaled 15
  -- All in reasonable range
  e5 > 2600000 && e5 < 2800000 &&
  e10 > 2710000 && e10 < 2720000 &&
  e15 > 2710000 && e15 < 2720000 &&
  -- e10 closer to target than e5
  let target : Nat := 2718281
  let err10 := if e10 >= target then e10 - target else target - e10
  let err5 := if e5 >= target then e5 - target else target - e5
  err10 < err5

-- ============================================================
-- PRIMORIAL GROWTH [II.D31]
-- ============================================================

/-- [II.D31] Growth base: consecutive primorial ratios.
    P_{k+1} / P_k = p_{k+1} >= 2 for all k >= 0.
    The primorial sequence grows super-exponentially. -/
def primorial_growth_check (stages : TauIdx) : Bool :=
  go 1 (stages + 1)
where
  go (k fuel : Nat) : Bool :=
    if fuel = 0 then true
    else if k > stages then true
    else
      -- P_{k+1} / P_k = p_{k+1} >= 2
      let pk := primorial k
      let pk1 := primorial (k + 1)
      (pk > 0 && pk1 / pk >= 2) && go (k + 1) (fuel - 1)
  termination_by fuel

/-- Primorial ratios match primes: P_{k+1}/P_k = p_{k+1} exactly. -/
def primorial_ratio_check (stages : TauIdx) : Bool :=
  go 1 (stages + 1)
where
  go (k fuel : Nat) : Bool :=
    if fuel = 0 then true
    else if k > stages then true
    else
      let pk := primorial k
      let pk1 := primorial (k + 1)
      let next_p := nth_prime (k + 1)
      (pk > 0 && pk1 / pk == next_p && pk1 % pk == 0) &&
      go (k + 1) (fuel - 1)
  termination_by fuel

-- ============================================================
-- FACTORIAL GROWTH COMPARISON
-- ============================================================

/-- Factorial function for comparison with primorial. -/
def nat_factorial : Nat -> Nat
  | 0 => 1
  | n + 1 => (n + 1) * nat_factorial n

/-- Factorial vs primorial comparison: for small k, primorial(k) < k!
    (since primes are sparse), but both grow super-exponentially.
    The ratio n!/P_n provides an e-related growth constant. -/
def factorial_primorial_compare (k : TauIdx) : Nat × Nat :=
  (nat_factorial k, primorial k)

-- ============================================================
-- SMOKE TESTS
-- ============================================================

-- Factorial series at various term counts
#eval e_scaled 5       -- ~2708333
#eval e_scaled 10      -- ~2718281
#eval e_scaled 15      -- ~2718281 (converged)

-- Convergence
#eval e_convergence_check          -- true
#eval e_rapid_convergence_check    -- true

-- Primorial growth
#eval primorial_growth_check 5     -- true
#eval primorial_ratio_check 5      -- true

-- Factorial vs primorial
#eval factorial_primorial_compare 1  -- (1, 2)
#eval factorial_primorial_compare 2  -- (2, 6)
#eval factorial_primorial_compare 3  -- (6, 30)
#eval factorial_primorial_compare 4  -- (24, 210)
#eval factorial_primorial_compare 5  -- (120, 2310)

-- Formal verification
theorem e_conv : e_convergence_check = true := by native_decide
theorem e_rapid : e_rapid_convergence_check = true := by native_decide
theorem prim_growth_5 : primorial_growth_check 5 = true := by native_decide
theorem prim_ratio_5 : primorial_ratio_check 5 = true := by native_decide

end Tau.BookII.Transcendentals
