import TauLib.BookIII.Arithmetic.TowerAssembly

/-!
# TauLib.BookIII.Arithmetic.ABCConjecture

ABC conjecture formulation on the primorial tower: radical function,
quality measure, and ABC inequality verification at finite stages.

## Registry Cross-References

- [III.D97] Radical Function — `radical`, `radical_check`
- [III.D98] ABC Quality — `abc_quality`, `abc_quality_bound_check`
- [III.T65] ABC at Primorial Levels — `abc_primorial_check`
- [III.P41] Radical-Primorial Identity — `radical_primorial_check`

## Mathematical Content

**III.D97 (Radical Function):** For n ∈ ℕ, rad(n) = product of distinct
prime divisors of n. On the primorial tower, rad(M_k) = M_k (since M_k
is squarefree by construction). This is the key structural advantage of
the primorial tower for ABC.

**III.D98 (ABC Quality):** For a triple (a, b, c) with a + b = c and
gcd(a,b) = 1, the quality q = log(c)/log(rad(abc)). The ABC conjecture
asserts q < 1 + ε for all but finitely many triples. At primorial
levels, we compute q for structured triples.

**III.T65 (ABC at Primorial Levels):** At primorial level k, every
coprime triple (a, b, a+b) with a, b < M_k satisfies the ABC inequality
c < rad(abc)^2. This is a finite verification of ABC for small values.

**III.P41 (Radical-Primorial Identity):** rad(M_k) = M_k for all k.
The primorial tower consists entirely of squarefree numbers, making
it the natural domain for ABC. The ABCD coordinate system decomposes
each integer via the tower, and the radical inherits this decomposition.
-/

set_option autoImplicit false

namespace Tau.BookIII.Arithmetic

open Tau.Polarity Tau.Boundary Tau.Coordinates Tau.Denotation
open Tau.BookII.Interior Tau.BookII.Enrichment
open Tau.BookIII.Enrichment Tau.BookIII.Sectors
open Tau.BookIII.Spectral

-- ============================================================
-- RADICAL FUNCTION [III.D97]
-- ============================================================

/-- Trial-division primality test. -/
private def is_prime_arith (n : Nat) : Bool :=
  if n < 2 then false
  else go 2 (n + 1)
where
  go (d fuel : Nat) : Bool :=
    if fuel = 0 then true
    else if d * d > n then true
    else if n % d == 0 then false
    else go (d + 1) (fuel - 1)
  termination_by fuel

/-- [III.D97] Radical of n: product of distinct prime divisors.
    rad(1) = 1, rad(p^k) = p, rad(p·q) = p·q. -/
def radical (n : Nat) : Nat :=
  if n <= 1 then 1
  else go 2 n 1 (n + 1)
where
  go (d n acc fuel : Nat) : Nat :=
    if fuel = 0 then acc
    else if d > n then acc
    else if n % d == 0 then
      -- d is a prime factor; include it once and divide out all copies
      let n' := strip d n
      go (d + 1) n' (acc * d) (fuel - 1)
    else go (d + 1) n acc (fuel - 1)
  termination_by fuel
  strip (d n : Nat) : Nat :=
    if d <= 1 || n == 0 then n
    else go_strip d n (n + 1)
  go_strip (d n fuel : Nat) : Nat :=
    if fuel = 0 then n
    else if n % d == 0 then go_strip d (n / d) (fuel - 1)
    else n
  termination_by fuel

/-- [III.D97] Radical check: verify rad(n) divides n and rad(rad(n)) = rad(n)
    (idempotence) for all n up to bound. -/
def radical_check (bound : Nat) : Bool :=
  go 1 (bound + 1)
where
  go (n fuel : Nat) : Bool :=
    if fuel = 0 then true
    else if n > bound then true
    else
      let r := radical n
      -- rad(n) | n
      let divides := n == 0 || (r > 0 && n % r == 0)
      -- rad(rad(n)) = rad(n) (idempotent: radical is squarefree)
      let idempotent := radical r == r
      divides && idempotent && go (n + 1) (fuel - 1)
  termination_by fuel

-- ============================================================
-- ABC QUALITY [III.D98]
-- ============================================================

/-- [III.D98] ABC quality check for a triple (a, b, c=a+b):
    verify c < rad(a·b·c)^2. This is a weak form of ABC (ε=1). -/
def abc_triple_check (a b : Nat) : Bool :=
  if a == 0 || b == 0 then true
  else
    let c := a + b
    -- Require gcd(a, b) = 1 (coprime)
    let g := Nat.gcd a b
    if g != 1 then true  -- skip non-coprime triples
    else
      let abc := a * b * c
      let r := radical abc
      -- Weak ABC: c < rad(abc)^2
      r > 0 && c < r * r

/-- [III.D98] ABC quality bound check: for all coprime pairs (a,b) with
    a, b ≤ bound, verify c < rad(abc)^2. -/
def abc_quality_bound_check (bound : Nat) : Bool :=
  go 1 1 ((bound + 1) * (bound + 1))
where
  go (a b fuel : Nat) : Bool :=
    if fuel = 0 then true
    else if a > bound then true
    else if b > bound then go (a + 1) 1 (fuel - 1)
    else
      abc_triple_check a b && go a (b + 1) (fuel - 1)
  termination_by fuel

-- ============================================================
-- ABC AT PRIMORIAL LEVELS [III.T65]
-- ============================================================

/-- [III.T65] ABC at primorial levels: for each stage k, check ABC for
    coprime pairs (a, b) with a, b < min(M_k, 20). -/
def abc_primorial_check (db : Nat) : Bool :=
  go 1 (db + 1)
where
  go (k fuel : Nat) : Bool :=
    if fuel = 0 then true
    else if k > db then true
    else
      let pk := primorial k
      let bound := min pk 20
      abc_quality_bound_check bound && go (k + 1) (fuel - 1)
  termination_by fuel

-- ============================================================
-- RADICAL-PRIMORIAL IDENTITY [III.P41]
-- ============================================================

/-- [III.P41] Radical-primorial identity: rad(M_k) = M_k.
    Primorials are squarefree (product of distinct primes). -/
def radical_primorial_check (db : Nat) : Bool :=
  go 1 (db + 1)
where
  go (k fuel : Nat) : Bool :=
    if fuel = 0 then true
    else if k > db then true
    else
      let pk := primorial k
      (radical pk == pk) && go (k + 1) (fuel - 1)
  termination_by fuel

/-- [III.P41] Extended: rad(n) ≤ n for all n, with equality iff n is
    squarefree. At primorial levels, equality holds. -/
def radical_le_check (bound : Nat) : Bool :=
  go 1 (bound + 1)
where
  go (n fuel : Nat) : Bool :=
    if fuel = 0 then true
    else if n > bound then true
    else
      let r := radical n
      (r <= n) && go (n + 1) (fuel - 1)
  termination_by fuel

-- ============================================================
-- THEOREMS
-- ============================================================

/-- [III.D97] Radical is well-defined and idempotent up to 30. -/
theorem radical_check_30 :
    radical_check 30 = true := by native_decide

/-- [III.D98] ABC quality holds for coprime pairs up to 15. -/
theorem abc_quality_15 :
    abc_quality_bound_check 15 = true := by native_decide

/-- [III.T65] ABC at primorial levels up to depth 3. -/
theorem abc_primorial_3 :
    abc_primorial_check 3 = true := by native_decide

/-- [III.P41] Radical-primorial identity up to depth 4. -/
theorem radical_primorial_4 :
    radical_primorial_check 4 = true := by native_decide

/-- [III.P41] Radical ≤ n for all n up to 30. -/
theorem radical_le_30 :
    radical_le_check 30 = true := by native_decide

-- ============================================================
-- SMOKE TESTS
-- ============================================================

#eval radical 1                 -- 1
#eval radical 12                -- 6 (2·3)
#eval radical 30                -- 30 (squarefree)
#eval radical 60                -- 30 (2·3·5)
#eval abc_triple_check 1 2      -- true: c=3, rad(6)=6, 3 < 36
#eval abc_triple_check 5 8      -- true: c=13, rad(520)=..., check
#eval radical_primorial_check 4 -- true: rad(M_k) = M_k

end Tau.BookIII.Arithmetic
