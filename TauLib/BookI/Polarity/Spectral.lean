import TauLib.BookI.Coordinates.Hyperfact

/-!
# TauLib.BookI.Polarity.Spectral

Spectral signatures and growth-rate separation.

## Registry Cross-References

- [I.D19e] Spectral Signature — `spectral_sig`, `pol_at`

## Ground Truth Sources
- chunk_0310_M002679: Spectral signature σ_N(p), growth-rate separation, polarity predicate

## Mathematical Content

For a prime p and bound N, the spectral signature σ_N(p) = (B_max, C_max)
records the highest B and C coordinates among objects X ≤ N with coord_A(X) = p.

The growth-rate separation theorem shows tetration eventually dominates
exponentiation: for every B, there exists C such that a↑↑C > a^B.
This is already proved as `tetration_unbounded` in TowerAtoms.

The polarity at bound N is: p is B-dominant if B_max > C_max.
-/

namespace Tau.Polarity

open Tau.Denotation Tau.Orbit Tau.Coordinates

-- ============================================================
-- SPECTRAL SIGNATURE [I.D19e]
-- ============================================================

/-- Scan objects from i to N, tracking max B and C for objects with A = p. -/
def spectral_scan (p i N bmax cmax : TauIdx) (fuel : Nat) : TauIdx × TauIdx :=
  if fuel = 0 then (bmax, cmax)
  else if i > N then (bmax, cmax)
  else
    if coord_A i == p then
      let b := coord_B i
      let c := coord_C i
      let bmax' := if b > bmax then b else bmax
      let cmax' := if c > cmax then c else cmax
      spectral_scan p (i + 1) N bmax' cmax' (fuel - 1)
    else
      spectral_scan p (i + 1) N bmax cmax (fuel - 1)
termination_by fuel

/-- [I.D19e] Spectral signature σ_N(p) = (B_max, C_max). -/
def spectral_sig (p N : TauIdx) : TauIdx × TauIdx :=
  spectral_scan p 2 N 0 0 N

/-- B_max component of the spectral signature. -/
def b_max (p N : TauIdx) : TauIdx := (spectral_sig p N).1

/-- C_max component of the spectral signature. -/
def c_max (p N : TauIdx) : TauIdx := (spectral_sig p N).2

-- ============================================================
-- POLARITY AT A BOUND
-- ============================================================

/-- Polarity at bound N: true = B-dominant, false = C-dominant. -/
def pol_at (p N : TauIdx) : Bool := b_max p N > c_max p N

/-- String polarity label. -/
def pol_label (p N : TauIdx) : String :=
  if pol_at p N then "B" else "C"

-- ============================================================
-- GROWTH-RATE SEPARATION
-- ============================================================

/-- Growth-rate separation: for a ≥ 2 and any B, there exists C such that
    a↑↑C > a^B. This is a direct corollary of tetration_unbounded. -/
theorem growth_rate_separation (a : Nat) (ha : a ≥ 2) (B : Nat) :
    ∃ C, tetration a C > a ^ B := tetration_unbounded a ha (a ^ B)

/-- Tetration grows at least as fast as the argument: a↑↑c ≥ c for a ≥ 2. -/
theorem tetration_ge_arg (a : Nat) (ha : a ≥ 2) (c : Nat) :
    tetration a c ≥ c := by
  induction c with
  | zero => simp [tetration]
  | succ c ih =>
    have := tetration_strict_mono a ha c
    omega

-- ============================================================
-- SMOKE TESTS
-- ============================================================

-- Spectral signatures for small primes
#eval spectral_sig 2 100    -- B_max and C_max for prime 2 up to 100
#eval spectral_sig 3 100    -- for prime 3
#eval spectral_sig 5 100    -- for prime 5
#eval spectral_sig 7 100    -- for prime 7

-- Polarity at various bounds
#eval pol_label 2 100       -- polarity of 2 up to 100
#eval pol_label 3 100
#eval pol_label 5 100
#eval pol_label 7 100
#eval pol_label 2 1000

-- Growth rate: tetration beats power
#eval (tetration 2 3, 2 ^ 3)   -- (16, 8): 2↑↑3 = 16 > 8 = 2^3
#eval (tetration 2 4, 2 ^ 4)   -- (65536, 16): 2↑↑4 >> 2^4

end Tau.Polarity
