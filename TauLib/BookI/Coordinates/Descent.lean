import TauLib.BookI.Coordinates.NormalForm

/-!
# TauLib.BookI.Coordinates.Descent

Remainder descent and prime stratum descent for greedy peel.

## Registry Cross-References

- [I.L04] Remainder Descent — `div_lt_of_ge_two`, descent checks

## Ground Truth Sources
- chunk_0241_M002280: Remainder descent D < X, prime stratum descent

## Mathematical Content

When X ≥ 2, the greedy peel extracts T(A,B,C) with T ≥ 2. Since D = X / T
and T ∣ X, we have D < X (strict descent).

Additionally, the largest prime of D is strictly less than A (prime stratum
descent). This ensures the spine terminates with strictly decreasing primes.
-/

namespace Tau.Coordinates

open Tau.Denotation Tau.Orbit

-- ============================================================
-- ABSTRACT NAT DESCENT LEMMAS
-- ============================================================

/-- If d ≥ 2 divides x and x ≥ 1, then x / d < x. -/
theorem div_lt_of_ge_two {x d : Nat} (hx : x ≥ 1) (hd : d ≥ 2)
    (_hdvd : d ∣ x) : x / d < x :=
  Nat.div_lt_self (by omega) (by omega)

/-- A product a * b with a ≥ 2 is strictly larger than b (when b ≥ 1). -/
theorem lt_mul_of_ge_two {a b : Nat} (ha : a ≥ 2) (hb : b ≥ 1) :
    b < a * b := by
  have : a * b ≥ 2 * b := Nat.mul_le_mul_right b ha
  omega

-- ============================================================
-- COMPUTABLE DESCENT CHECKS [I.L04]
-- ============================================================

/-- [I.L04] Check that greedy_peel remainder D < X for X ≥ 2.
    Also checks T(A,B,C) * D = X (reconstruction). -/
def descent_check (x : TauIdx) : Bool :=
  if x ≤ 1 then true
  else
    let (a, b, c, d) := greedy_peel x
    let t := tower_atom a b c
    (t * d == x) && (d < x)

/-- Check that the largest prime of D is strictly less than A. -/
def prime_stratum_descent_check (x : TauIdx) : Bool :=
  if x ≤ 1 then true
  else
    let (a, _, _, d) := greedy_peel x
    if d ≤ 1 then true
    else largest_prime_divisor d < a

/-- Combined descent: remainder descent + prime stratum descent. -/
def full_descent_check (x : TauIdx) : Bool :=
  descent_check x && prime_stratum_descent_check x

-- ============================================================
-- BATCH VERIFICATION
-- ============================================================

/-- Verify descent for all X from 2 to n. -/
def verify_descent_up_to_go (i n : Nat) (fuel : Nat) : Bool :=
  if fuel = 0 then true
  else if i > n then true
  else full_descent_check i && verify_descent_up_to_go (i + 1) n (fuel - 1)
termination_by fuel

def verify_descent_up_to (n : TauIdx) : Bool := verify_descent_up_to_go 2 n n

-- ============================================================
-- SMOKE TESTS
-- ============================================================

-- Individual descent checks
#eval descent_check 12     -- true: T(3,1,1)*4 = 12, 4 < 12
#eval descent_check 64     -- true: T(2,3,2)*1 = 64, 1 < 64
#eval descent_check 7      -- true: T(7,1,1)*1 = 7, 1 < 7
#eval descent_check 360    -- true

-- Prime stratum descent
#eval prime_stratum_descent_check 12    -- true: D=4, lpd(4)=2 < 3=A
#eval prime_stratum_descent_check 360   -- true: D=72, lpd(72)=3 < 5=A

-- Batch verification: all X from 2 to 1000
#eval verify_descent_up_to 1000  -- true

end Tau.Coordinates
