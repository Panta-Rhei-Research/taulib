import TauLib.BookIII.Spectral.SieveInfrastructure
import TauLib.BookIII.Spectral.AdditiveConjectures

/-!
# TauLib.BookIII.Spectral.TwinPrimeDeep

Deep analysis of the twin prime conjecture on the primorial tower:
extended counting, Hardy-Littlewood constant approximation,
CRT admissibility, and structural theorems.

## Registry Cross-References

- [III.D105] Twin Prime Sieve Count — `twin_prime_sieve_count`
- [III.D106] Hardy-Littlewood Constant — `hl_twin_constant_approx`
- [III.D107] CRT Twin Admissibility — `crt_twin_admissible`
- [III.T72] Twin Primes to 500 — `twin_primes_500`
- [III.T73] Twin Density Primorial — `twin_density_primorial_5`
- [III.T74] HL Constant Convergence — `hl_constant_decreasing_5`
- [III.T75] CRT Admissible Positive — `crt_admissible_positive_4`
- [III.P45] Twin Admissibility Fraction — `twin_admissibility_fraction_5`
- [III.P46] Twin Gap Characterization — (meta-theorem, see docstring)

## Mathematical Content

**III.D107 (CRT Twin Admissibility):** At primorial level k, count residue
classes r mod M_k such that for ALL primes p_i (i≤k), neither r nor r+2
is divisible by p_i. For p=2: r must be odd. For p≥3: r mod p ∉ {0, p-2}.

**III.P45 (Admissibility Fraction):** At each odd prime p ≥ 3, exactly
(p-2) out of p residue classes are twin-admissible. For p=2, exactly 1
out of 2 (the odd residue). Product gives the admissible fraction.

**III.P46 (Twin Gap):** Admissible classes are nonempty at every prime.
Infinitude requires equidistribution (Bombieri-Vinogradov or stronger).
-/

set_option autoImplicit false

namespace Tau.BookIII.Spectral

open Tau.Polarity Tau.Boundary Tau.Coordinates Tau.Denotation
open Tau.BookII.Interior Tau.BookII.Enrichment
open Tau.BookIII.Enrichment Tau.BookIII.Sectors

-- ============================================================
-- TWIN PRIME SIEVE COUNT [III.D105]
-- ============================================================

/-- [III.D105] Count twin prime pairs (p, p+2) with p ≤ bound via sieve. -/
def twin_prime_sieve_count (bound : Nat) : Nat :=
  go 2 0 (bound + 1)
where
  go (p acc fuel : Nat) : Nat :=
    if fuel = 0 then acc
    else if p > bound then acc
    else
      let hit := if eratosthenes_sieve p && eratosthenes_sieve (p + 2) then 1 else 0
      go (p + 1) (acc + hit) (fuel - 1)
  termination_by fuel

-- ============================================================
-- HARDY-LITTLEWOOD CONSTANT [III.D106]
-- ============================================================

/-- [III.D106] Hardy-Littlewood twin constant C₂(k) approximation.
    C₂(k) = ∏_{i=2}^{k} p_i(p_i-2)/(p_i-1)² (starting from p₂=3).
    Returns (numerator, denominator) as integers. -/
def hl_twin_constant_approx (k : Nat) : Nat × Nat :=
  go 2 1 1 (k + 1)
where
  go (i num den fuel : Nat) : Nat × Nat :=
    if fuel = 0 then (num, den)
    else if i > k then (num, den)
    else
      let p := nth_prime i
      if p < 3 then go (i + 1) num den (fuel - 1)
      else
        let num' := num * (p * (p - 2))
        let den' := den * ((p - 1) * (p - 1))
        go (i + 1) num' den' (fuel - 1)
  termination_by fuel

/-- [III.T74] HL constant is decreasing: C₂(k+1) ≤ C₂(k). -/
def hl_constant_decreasing_check (lo hi : Nat) : Bool :=
  go lo (hi - lo + 1)
where
  go (k fuel : Nat) : Bool :=
    if fuel = 0 then true
    else if k >= hi then true
    else
      let (n1, d1) := hl_twin_constant_approx k
      let (n2, d2) := hl_twin_constant_approx (k + 1)
      (n2 * d1 <= n1 * d2) && go (k + 1) (fuel - 1)
  termination_by fuel

-- ============================================================
-- CRT TWIN ADMISSIBILITY [III.D107]
-- ============================================================

/-- Helper: check if residue r is twin-admissible at all primes up to depth d.
    For each p_i (i=1..d): r mod p_i ≠ 0 AND (r+2) mod p_i ≠ 0.
    This includes p=2: r must be odd. -/
def is_twin_admissible (r d : Nat) : Bool :=
  go 1 (d + 1)
where
  go (i fuel : Nat) : Bool :=
    if fuel = 0 then true
    else if i > d then true
    else
      let p := nth_prime i
      if p == 0 then go (i + 1) (fuel - 1)
      else
        let r_mod := r % p
        let r2_mod := (r + 2) % p
        if r_mod == 0 || r2_mod == 0 then false
        else go (i + 1) (fuel - 1)
  termination_by fuel

/-- [III.D107] Count twin-admissible residues mod M_k. -/
def crt_twin_admissible (k : Nat) : Nat :=
  let pk := primorial k
  go 0 0 (pk + 1)
where
  go (r acc fuel : Nat) : Nat :=
    if fuel = 0 then acc
    else if r >= primorial k then acc
    else
      let acc' := if is_twin_admissible r k then acc + 1 else acc
      go (r + 1) acc' (fuel - 1)
  termination_by fuel

/-- [III.T75] Twin-admissible residues are positive at each depth. -/
def crt_admissible_positive_check (db : Nat) : Bool :=
  go 1 (db + 1)
where
  go (k fuel : Nat) : Bool :=
    if fuel = 0 then true
    else if k > db then true
    else
      (crt_twin_admissible k > 0) && go (k + 1) (fuel - 1)
  termination_by fuel

-- ============================================================
-- TWIN DENSITY AT PRIMORIAL LEVELS [III.T73]
-- ============================================================

/-- [III.T73] Twin prime density: at least one twin pair exists at
    each primorial level k ≥ 2 (M_1=2 is too small).
    Uses min(M_k, 500) for computability. -/
def twin_density_primorial_check (db : Nat) : Bool :=
  go 2 (db + 1)
where
  go (k fuel : Nat) : Bool :=
    if fuel = 0 then true
    else if k > db then true
    else
      let pk := primorial k
      let bound := min pk 500
      let count := twin_prime_sieve_count bound
      count > 0 && go (k + 1) (fuel - 1)
  termination_by fuel

-- ============================================================
-- ADMISSIBILITY FRACTION [III.P45]
-- ============================================================

/-- Helper: count r in [0..p-1] with r%p ≠ 0 AND (r+2)%p ≠ 0. -/
def count_admissible_at_prime (p : Nat) : Nat :=
  go 0 0 (p + 1)
where
  go (r acc fuel : Nat) : Nat :=
    if fuel = 0 then acc
    else if r >= p then acc
    else
      let ok := r % p != 0 && (r + 2) % p != 0
      go (r + 1) (if ok then acc + 1 else acc) (fuel - 1)
  termination_by fuel

/-- [III.P45] At each odd prime p ≥ 3, exactly (p-2) out of p residue classes
    are twin-admissible. For p=2, exactly 0 out of 2 (since both r=0 and
    r=1 fail: r=0 has r%2=0, r=1 has (r+2)%2=1%2≠0 but r=1 has r%2=1≠0
    and 3%2=1≠0... actually for p=2: r=1 gives r%2=1, (r+2)%2=1, so admissible.
    r=0 gives r%2=0, blocked. So p=2 has 1 admissible. We check p ≥ 3 gives p-2. -/
def twin_admissibility_fraction_check (db : Nat) : Bool :=
  go 2 (db + 1)
where
  go (i fuel : Nat) : Bool :=
    if fuel = 0 then true
    else if i > db then true
    else
      let p := nth_prime i
      if p < 3 then go (i + 1) (fuel - 1)
      else
        let admissible := count_admissible_at_prime p
        (admissible == p - 2) && go (i + 1) (fuel - 1)
  termination_by fuel

-- ============================================================
-- THEOREMS
-- ============================================================

/-- [III.T72] At least 20 twin prime pairs below 500. -/
theorem twin_primes_500 :
    twin_prime_sieve_count 500 >= 20 := by native_decide

/-- [III.T73] Twin prime density positive at primorial depths 1..5. -/
theorem twin_density_primorial_5 :
    twin_density_primorial_check 5 = true := by native_decide

/-- [III.T74] HL constant decreasing for k = 2..5. -/
theorem hl_constant_decreasing_5 :
    hl_constant_decreasing_check 2 5 = true := by native_decide

/-- [III.T75] CRT-admissible residues positive at depths 1..4. -/
theorem crt_admissible_positive_4 :
    crt_admissible_positive_check 4 = true := by native_decide

/-- [III.P45] Admissibility fraction = (p-2)/p for primes 3,5,7,11. -/
theorem twin_admissibility_fraction_5 :
    twin_admissibility_fraction_check 5 = true := by native_decide

-- ============================================================
-- STRUCTURAL THEOREMS
-- ============================================================

/-- [III.D105] Twin prime count at 100 ≥ 8. -/
theorem twin_count_100 :
    twin_prime_sieve_count 100 >= 8 := by native_decide

/-- [III.D106] HL constant at depth 2: C₂(2) = 3·1/(2·2) = 3/4. -/
theorem hl_depth_2 :
    hl_twin_constant_approx 2 = (3, 4) := by native_decide

/-- [III.D107] Twin-admissible residues at depth 1 (mod 2): 1 (only odd). -/
theorem twin_admissible_1 :
    crt_twin_admissible 1 = 1 := by native_decide

/-- [III.D107] Twin-admissible residues at depth 3 (mod 30). -/
theorem twin_admissible_3_pos :
    crt_twin_admissible 3 > 0 := by native_decide

/-- [III.P45] At prime 3: 1 out of 3 admissible (3-2=1). -/
theorem admissible_at_3 :
    count_admissible_at_prime 3 = 1 := by native_decide

/-- [III.P45] At prime 5: 3 out of 5 admissible (5-2=3). -/
theorem admissible_at_5 :
    count_admissible_at_prime 5 = 3 := by native_decide

/-- [III.P45] At prime 7: 5 out of 7 admissible (7-2=5). -/
theorem admissible_at_7 :
    count_admissible_at_prime 7 = 5 := by native_decide

-- ============================================================
-- SMOKE TESTS
-- ============================================================

#eval twin_prime_sieve_count 30     -- ≥ 5
#eval twin_prime_sieve_count 100    -- ≥ 8
#eval twin_prime_sieve_count 500    -- ≥ 35
#eval hl_twin_constant_approx 2     -- (3, 4)
#eval hl_twin_constant_approx 3     -- (45, 64)
#eval crt_twin_admissible 1         -- 1
#eval crt_twin_admissible 2         -- should be > 0
#eval crt_twin_admissible 3         -- should be > 0
#eval crt_twin_admissible 4         -- admissible mod 210
#eval count_admissible_at_prime 3   -- 1
#eval count_admissible_at_prime 5   -- 3
#eval count_admissible_at_prime 7   -- 5
#eval twin_density_primorial_check 5 -- true
#eval twin_admissibility_fraction_check 5  -- true

end Tau.BookIII.Spectral
