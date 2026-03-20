import TauLib.BookI.Coordinates.ABCD
import TauLib.BookI.Coordinates.Primes

/-!
# TauLib.BookII.Interior.TauAdmissible

τ-admissible points: the coordinate space of τ³.

## Registry Cross-References

- [II.D02] τ-Admissible Point — `TauAdmissiblePoint`, `from_tau_idx`
- [II.D03] Constraint Lattice — `constraint_C1` .. `constraint_C5`
- [II.T01] Point Set Well-Defined — `round_trip_check`, `admissible_check`

## Mathematical Content

A τ-admissible point is a quadruple (A, B, C, D) ∈ τ-Idx⁴ satisfying:
- C1: A ∈ ℙ_τ ∪ {1} (prime or unity)
- C2: B, C, D ≥ 0 (non-negativity; automatic for ℕ)
- C3: every prime factor of D is strictly < A
- C4: if A = 1 then B = 0 and C = 0
- C5: normalization (greedy peel consistency)

The point set τ³ := τ³_fin ∪ τ³_lim is well-defined:
- τ³_fin bijects with Obj(τ) via the ABCD chart Φ
- τ³_lim is non-empty (primorial tower)
- τ³ is closed under CRT reduction
-/

namespace Tau.BookII.Interior

open Tau.Coordinates Tau.Denotation

-- ============================================================
-- CONSTRAINT LATTICE [II.D03]
-- ============================================================

/-- [II.D03/C1] Prime constraint: A is prime or 1. -/
def constraint_C1 (a : TauIdx) : Bool :=
  is_prime_bool a || a == 1

/-- [II.D03/C3] Remainder constraint: largest prime factor of D < A.
    Returns true if all prime factors of d are strictly less than bound. -/
def largest_prime_factor_aux (n d best fuel : Nat) : Nat :=
  if fuel = 0 then max best (if n > 1 then n else 0)
  else if n ≤ 1 then best
  else if d * d > n then max best n  -- n is prime
  else if n % d == 0 then
    largest_prime_factor_aux (n / d) d (max best d) (fuel - 1)
  else
    largest_prime_factor_aux n (d + 1) best (fuel - 1)
termination_by fuel

/-- Largest prime factor of n, or 0 if n ≤ 1. -/
def largest_prime_factor (n : TauIdx) : TauIdx :=
  if n ≤ 1 then 0
  else largest_prime_factor_aux n 2 0 n

/-- [II.D03/C3] Every prime factor of D is strictly < A. -/
def constraint_C3 (d a : TauIdx) : Bool :=
  d ≤ 1 || largest_prime_factor d < a

/-- [II.D03/C4] Tower constraint: if A = 1 then B = C = 0. -/
def constraint_C4 (a b c : TauIdx) : Bool :=
  if a == 1 then b == 0 && c == 0 else true

/-- [II.D03/C5] Normalization: round-trip through abcd_chart is consistent. -/
def constraint_C5 (a b c d : TauIdx) : Bool :=
  let x := tower_atom a b c * d
  if x ≤ 1 then a ≤ 1
  else
    let (a', b', c', d') := abcd_chart x
    a == a' && b == b' && c == c' && d == d'

/-- [II.D03] Full constraint lattice check for a candidate (A, B, C, D). -/
def is_tau_admissible (a b c d : TauIdx) : Bool :=
  constraint_C1 a && constraint_C3 d a && constraint_C4 a b c && constraint_C5 a b c d

-- ============================================================
-- τ-ADMISSIBLE POINT [II.D02]
-- ============================================================

/-- [II.D02] A τ-admissible point: ABCD quadruple from the greedy peel
    decomposition. Every object X ∈ Obj(τ) has a unique such representation
    via the Hyperfactorization Theorem (I.T04). -/
structure TauAdmissiblePoint where
  a : TauIdx  -- A: prime direction (π-channel)
  b : TauIdx  -- B: exponent (γ-channel)
  c : TauIdx  -- C: tetration height (η-channel)
  d : TauIdx  -- D: remainder (α-channel)
  deriving Repr, DecidableEq

/-- Construct τ-admissible point from a τ-index via the ABCD chart. -/
def from_tau_idx (x : TauIdx) : TauAdmissiblePoint :=
  let chart := abcd_chart x
  ⟨chart.1, chart.2.1, chart.2.2.1, chart.2.2.2⟩

/-- Reconstruct τ-index from an admissible point: T(A,B,C) · D. -/
def to_tau_idx (p : TauAdmissiblePoint) : TauIdx :=
  tower_atom p.a p.b p.c * p.d

/-- Check that a TauAdmissiblePoint satisfies all constraints. -/
def TauAdmissiblePoint.valid (p : TauAdmissiblePoint) : Bool :=
  is_tau_admissible p.a p.b p.c p.d

-- ============================================================
-- POINT SET WELL-DEFINED [II.T01]
-- ============================================================

/-- [II.T01, clause 1] Round-trip: from_tau_idx ∘ to_tau_idx is consistent
    with chart_value. -/
def round_trip_check (x : TauIdx) : Bool :=
  to_tau_idx (from_tau_idx x) == x

/-- [II.T01, clause 1] Admissibility: ABCD chart always produces admissible
    quadruples. -/
def admissible_check (x : TauIdx) : Bool :=
  (from_tau_idx x).valid

/-- [II.T01, clause 1] Batch verification for X = 2..bound. -/
def batch_verify (bound : TauIdx) : Bool :=
  go 2 (bound + 1)
where
  go (start fuel : Nat) : Bool :=
    if fuel = 0 then true
    else if start > bound then true
    else round_trip_check start && admissible_check start && go (start + 1) (fuel - 1)
  termination_by fuel

-- ============================================================
-- PRIMORIAL WITNESSES [II.T01, clause 2]
-- ============================================================

/-- Primorial P_k = p₁ · p₂ · ... · p_k. -/
def primorial_witness : List (TauIdx × TauAdmissiblePoint) :=
  [ (2,    from_tau_idx 2)      -- P₁ = 2:    Φ = (2,1,1,1)
  , (6,    from_tau_idx 6)      -- P₂ = 6:    Φ = (3,1,1,2)
  , (30,   from_tau_idx 30)     -- P₃ = 30:   Φ = (5,1,1,6)
  , (210,  from_tau_idx 210)    -- P₄ = 210:  Φ = (7,1,1,30)
  , (2310, from_tau_idx 2310)   -- P₅ = 2310: Φ = (11,1,1,210)
  ]

/-- Primorial readouts have A = p_k, B = 1, C = 1, D = P_{k-1}. -/
def primorial_b_eq_one : Bool :=
  primorial_witness.all fun (_, p) => p.b == 1

def primorial_c_eq_one : Bool :=
  primorial_witness.all fun (_, p) => p.c == 1

/-- Primorial A-values form an increasing sequence of primes. -/
def primorial_a_increasing : Bool :=
  let as := primorial_witness.map fun (_, p) => p.a
  as == [2, 3, 5, 7, 11]

-- ============================================================
-- SMOKE TESTS
-- ============================================================

-- Constraint checks
#eval constraint_C1 2      -- true (prime)
#eval constraint_C1 1      -- true (unity)
#eval constraint_C1 4      -- false (composite)

#eval largest_prime_factor 12   -- 3
#eval largest_prime_factor 30   -- 5
#eval largest_prime_factor 7    -- 7
#eval largest_prime_factor 1    -- 0

#eval constraint_C3 4 5    -- true (lpf(4)=2 < 5)
#eval constraint_C3 6 3    -- false (lpf(6)=3, not < 3)
#eval constraint_C3 1 2    -- true (d=1, no prime factors)

-- From/to τ-index
#eval from_tau_idx 12       -- (3, 1, 1, 4)
#eval from_tau_idx 64       -- (2, 3, 2, 1)
#eval from_tau_idx 360      -- (5, 1, 1, 72)

#eval to_tau_idx (from_tau_idx 12)    -- 12
#eval to_tau_idx (from_tau_idx 64)    -- 64
#eval to_tau_idx (from_tau_idx 360)   -- 360

-- Round-trip and admissibility
#eval round_trip_check 12     -- true
#eval round_trip_check 64     -- true
#eval admissible_check 12     -- true
#eval admissible_check 64     -- true

-- Batch verification
#eval batch_verify 100    -- true (all X = 2..100 pass)

-- Primorial witnesses
#eval primorial_witness.map fun (x, p) => (x, p.a, p.b, p.c, p.d)
#eval primorial_b_eq_one        -- true
#eval primorial_c_eq_one        -- true
#eval primorial_a_increasing    -- true

-- Formal verification for small range
theorem admissible_2_to_20 : batch_verify 20 = true := by native_decide

end Tau.BookII.Interior
