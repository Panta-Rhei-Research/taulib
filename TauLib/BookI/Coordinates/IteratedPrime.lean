import TauLib.BookI.Coordinates.PrimeEnumeration

/-!
# TauLib.BookI.Coordinates.IteratedPrime

The iterated prime tower: k-fold composition of the prime enumeration
function nthPrime. Each generator's orbit carries a natural scalar
projection via iterated prime enumeration.

## Registry Cross-References

- [I.D94] Orbit-Set Map — connection to semantic projection

## Mathematical Content

### The Iterated Prime Tower

Define P^(k)(n) = k-fold iterated nthPrime:
  - P^(0)(n) = n                           (identity, α-orbit)
  - P^(1)(n) = nthPrime(n)                 (primes, π-orbit)
  - P^(2)(n) = nthPrime(nthPrime(n))       (super-primes, γ-orbit)
  - P^(3)(n) = nthPrime^3(n)               (η-orbit)
  - P^(4)(n) = nthPrime^4(n)               (ω-orbit)

Key values:
  γ₁ = P^(2)(1) = 3,   γ₂ = P^(2)(2) = 5,   γ₃ = P^(2)(3) = 11
  η₁ = P^(3)(1) = 5,   η₂ = P^(3)(2) = 11,  η₃ = P^(3)(3) = 31
  ω₁ = P^(4)(1) = 11,  ω₂ = P^(4)(2) = 31,  ω₃ = P^(4)(3) = 127

### Connection to α Formula

The fine-structure constant is expressed entirely in tower values:
  α = (ω₁ / (γ₁ · γ₂))² · ι_τ⁴ = (11/15)² · ι_τ⁴

The Euler sieve factor:
  8/15 = (1 - 1/γ₁)(1 - 1/η₁) = (2/3)(4/5)

The S₅ correction:
  (8/15) · (1 + 1/η₁!) = (8/15) · (121/120) = 121/225 = (11/15)²

### Tower Nesting

ω-values ⊂ η-values ⊂ γ-values ⊂ π-values (as value sets).
Cross-level shift: η_n = γ_{π_n} for all n.

## Ground Truth Sources
- Book I ch83: Orbit-set correspondence, semantic projection
- Book IV ch11: Dimensionless cascade, Route C tower formula
- Book IV ch29: Fine-structure constant derivation
-/

namespace Tau.Coordinates

-- ============================================================
-- FACTORIAL (minimal definition for S₅ connection)
-- ============================================================

/-- Simple factorial function for tower connections. -/
def factorial : Nat → Nat
  | 0 => 1
  | n + 1 => (n + 1) * factorial n

-- ============================================================
-- ITERATED PRIME FUNCTION
-- ============================================================

/-- The k-fold iterated prime function P^(k)(n).
    iteratedPrime 0 n = n (identity).
    iteratedPrime (k+1) n = nthPrime(iteratedPrime k n).

    NOTE: nthPrime is 0-indexed in Lean (nthPrime 0 = 2),
    but the tower convention uses 1-indexed input:
    val(α_n) = n, val(π_n) = p_n where p_1 = 2.
    We use the RAW function here; users apply the index
    shift when mapping to generator orbits. -/
def iteratedPrime : Nat → Nat → Nat
  | 0, n => n
  | k + 1, n => nthPrime (iteratedPrime k n)

-- ============================================================
-- TOWER VALUE VERIFICATION (0-indexed nthPrime)
-- ============================================================

-- Level 0 (α-orbit): identity
example : iteratedPrime 0 1 = 1 := by native_decide
example : iteratedPrime 0 2 = 2 := by native_decide
example : iteratedPrime 0 5 = 5 := by native_decide

-- Level 1 (π-orbit): nthPrime (0-indexed)
-- nthPrime 0 = 2, nthPrime 1 = 3, nthPrime 2 = 5, nthPrime 4 = 11
example : iteratedPrime 1 0 = 2 := by native_decide
example : iteratedPrime 1 1 = 3 := by native_decide
example : iteratedPrime 1 2 = 5 := by native_decide
example : iteratedPrime 1 3 = 7 := by native_decide
example : iteratedPrime 1 4 = 11 := by native_decide

-- Level 2 (γ-orbit): nthPrime ∘ nthPrime (0-indexed)
-- γ₁ = P^(2)(0) = nthPrime(nthPrime 0) = nthPrime 2 = 5
-- γ₂ = P^(2)(1) = nthPrime(nthPrime 1) = nthPrime 3 = 7? No...
-- With 0-indexed: P^(2)(0) = nthPrime(nthPrime 0) = nthPrime 2 = 5

-- For the PHYSICAL tower (1-indexed), we need a shift.
-- γ_n (physics) = P^(2)(n) with 1-indexed primes.
-- 1-indexed p_n: p_1=2, p_2=3, p_3=5, p_4=7, p_5=11
-- So γ_1 = p_{p_1} = p_2 = 3, which is nthPrime(nthPrime(0))
--                              = nthPrime(2) = 5. WRONG!

-- The issue: nthPrime is 0-indexed but physics uses 1-indexed.
-- p_1 (physics) = 2 = nthPrime(0), so physics index k = Lean index k-1.
-- γ_n (physics) = nthPrime(nthPrime(n-1) - 1)?  No, that's wrong too.

-- CORRECT approach: define towerVal that takes 1-indexed input
-- and converts to 0-indexed nthPrime calls.

/-- Tower value with 1-indexed input (physics convention).
    towerVal 0 n = n (identity, α-orbit).
    towerVal 1 n = nthPrime(n-1) (primes, π-orbit, 1-indexed).
    towerVal 2 n = nthPrime(nthPrime(n-1) - 1) (super-primes, γ-orbit).
    The index shift accounts for nthPrime being 0-indexed. -/
def towerVal : Nat → Nat → Nat
  | 0, n => n
  | k + 1, n => nthPrime (towerVal k n - 1)

-- ============================================================
-- TOWER VALUE VERIFICATION (1-indexed, physics convention)
-- ============================================================

-- Level 0 (α-orbit): val(α_n) = n
example : towerVal 0 1 = 1 := by native_decide
example : towerVal 0 5 = 5 := by native_decide

-- Level 1 (π-orbit): val(π_n) = p_n (1-indexed)
-- p_1 = 2, p_2 = 3, p_3 = 5, p_4 = 7, p_5 = 11
example : towerVal 1 1 = 2 := by native_decide
example : towerVal 1 2 = 3 := by native_decide
example : towerVal 1 3 = 5 := by native_decide
example : towerVal 1 4 = 7 := by native_decide
example : towerVal 1 5 = 11 := by native_decide

-- Level 2 (γ-orbit): val(γ_n) = p_{p_n}
-- γ_1 = p_{p_1} = p_2 = 3
-- γ_2 = p_{p_2} = p_3 = 5
-- γ_3 = p_{p_3} = p_5 = 11
-- γ_4 = p_{p_4} = p_7 = 17
-- γ_5 = p_{p_5} = p_11 = 31
example : towerVal 2 1 = 3 := by native_decide
example : towerVal 2 2 = 5 := by native_decide
example : towerVal 2 3 = 11 := by native_decide
example : towerVal 2 4 = 17 := by native_decide
example : towerVal 2 5 = 31 := by native_decide

-- Level 3 (η-orbit): val(η_n) = p_{p_{p_n}}
-- η_1 = p_{p_{p_1}} = p_{p_2} = p_3 = 5
-- η_2 = p_{p_{p_2}} = p_{p_3} = p_5 = 11
-- η_3 = p_{p_{p_3}} = p_{p_5} = p_11 = 31
-- η_4 = p_{p_{p_4}} = p_{p_7} = p_17 = 59
-- η_5 = p_{p_{p_5}} = p_{p_11} = p_31 = 127
example : towerVal 3 1 = 5 := by native_decide
example : towerVal 3 2 = 11 := by native_decide
example : towerVal 3 3 = 31 := by native_decide
example : towerVal 3 4 = 59 := by native_decide
example : towerVal 3 5 = 127 := by native_decide

-- Level 4 (ω-orbit): val(ω_n) = p_{p_{p_{p_n}}}
-- ω_1 = 11, ω_2 = 31, ω_3 = 127
example : towerVal 4 1 = 11 := by native_decide
example : towerVal 4 2 = 31 := by native_decide
example : towerVal 4 3 = 127 := by native_decide

-- ============================================================
-- KEY TOWER VALUES FOR α FORMULA
-- ============================================================

/-- γ₁ = 3 (first value of γ-orbit). -/
theorem gamma_1_eq : towerVal 2 1 = 3 := by native_decide

/-- γ₂ = 5 (second value of γ-orbit). -/
theorem gamma_2_eq : towerVal 2 2 = 5 := by native_decide

/-- γ₃ = 11 (third value of γ-orbit). -/
theorem gamma_3_eq : towerVal 2 3 = 11 := by native_decide

/-- η₁ = 5 (first value of η-orbit). -/
theorem eta_1_eq : towerVal 3 1 = 5 := by native_decide

/-- η₂ = 11 (second value of η-orbit). -/
theorem eta_2_eq : towerVal 3 2 = 11 := by native_decide

/-- η₃ = 31 (third value of η-orbit). -/
theorem eta_3_eq : towerVal 3 3 = 31 := by native_decide

/-- ω₁ = 11 (first value of ω-orbit). -/
theorem omega_1_eq : towerVal 4 1 = 11 := by native_decide

/-- ω₂ = 31 (second value of ω-orbit). -/
theorem omega_2_eq : towerVal 4 2 = 31 := by native_decide

/-- ω₃ = 127 (third value of ω-orbit). -/
theorem omega_3_eq : towerVal 4 3 = 127 := by native_decide

-- ============================================================
-- TOWER FORMULA CONNECTIONS
-- ============================================================

/-- γ₁ · γ₂ = 15 (denominator of α). -/
theorem gamma_product_15 :
    towerVal 2 1 * towerVal 2 2 = 15 := by native_decide

/-- ω₁² = 121 (numerator of α). -/
theorem omega_1_squared :
    towerVal 4 1 * towerVal 4 1 = 121 := by native_decide

/-- ω₁ / (γ₁ · γ₂) = 11/15 as cross-multiplied identity:
    ω₁ · 15 = 11 · (γ₁ · γ₂). -/
theorem tower_ratio_identity :
    towerVal 4 1 * 15 = 11 * (towerVal 2 1 * towerVal 2 2) := by native_decide

/-- (ω₁)² / (γ₁ · γ₂)² = 121/225 = (11/15)² as cross-multiplied:
    (ω₁)² · 225 = 121 · (γ₁ · γ₂)². -/
theorem tower_alpha_ratio :
    (towerVal 4 1)^2 * 225 = 121 * (towerVal 2 1 * towerVal 2 2)^2 := by native_decide

-- ============================================================
-- EULER SIEVE: (1 - 1/γ₁)(1 - 1/η₁) = 8/15
-- ============================================================

/-- The Euler sieve factor: (1 - 1/γ₁)(1 - 1/η₁) = 8/15.
    Cross-multiplied: (γ₁ - 1)(η₁ - 1) · 15 = 8 · γ₁ · η₁. -/
theorem euler_sieve_tower :
    (towerVal 2 1 - 1) * (towerVal 3 1 - 1) * 15 =
    8 * towerVal 2 1 * towerVal 3 1 := by native_decide

-- ============================================================
-- S₅ CONNECTION: η₁ = 5 = |generators|
-- ============================================================

/-- η₁ = 5 = number of generators {α, π, γ, η, ω}. -/
theorem eta_1_is_generator_count : towerVal 3 1 = 5 := by native_decide

/-- η₁! = 120 = |S₅|. -/
theorem eta_1_factorial : factorial (towerVal 3 1) = 120 := by native_decide

/-- The S₅ correction: (8/15)(1 + 1/η₁!) = 121/225.
    Cross-multiplied: 8 · (η₁! + 1) · 225 = 121 · 15 · η₁!. -/
theorem s5_correction_yields_tower :
    8 * (factorial (towerVal 3 1) + 1) * 225 =
    121 * 15 * factorial (towerVal 3 1) := by native_decide

-- ============================================================
-- TOWER NESTING (partial verification)
-- ============================================================

/-- Cross-level shift: η_n = γ_{π_n} for n = 1..5.
    towerVal 3 n = towerVal 2 (towerVal 1 n). -/
theorem cross_level_1 : towerVal 3 1 = towerVal 2 (towerVal 1 1) := by native_decide
theorem cross_level_2 : towerVal 3 2 = towerVal 2 (towerVal 1 2) := by native_decide
theorem cross_level_3 : towerVal 3 3 = towerVal 2 (towerVal 1 3) := by native_decide
theorem cross_level_4 : towerVal 3 4 = towerVal 2 (towerVal 1 4) := by native_decide
theorem cross_level_5 : towerVal 3 5 = towerVal 2 (towerVal 1 5) := by native_decide

/-- ω₃ = 127 = 2⁷ - 1 (Mersenne prime). -/
theorem omega_3_mersenne : towerVal 4 3 = 2^7 - 1 := by native_decide

-- ============================================================
-- PERFECT SQUARE UNIQUENESS (N = 5)
-- ============================================================

/-- factorial 5 = 120. -/
theorem factorial_5 : factorial 5 = 120 := by native_decide

/-- factorial 3 = 6. -/
theorem factorial_3 : factorial 3 = 6 := by native_decide

/-- factorial 4 = 24. -/
theorem factorial_4 : factorial 4 = 24 := by native_decide

/-- factorial 6 = 720. -/
theorem factorial_6 : factorial 6 = 720 := by native_decide

/-- factorial 7 = 5040. -/
theorem factorial_7 : factorial 7 = 5040 := by native_decide

/-- For N = 5: 8·(N!+1) / (15·N!) = 121/225 = 11²/15².
    We verify: 8·121 = 968, 15·120 = 1800, gcd = 8, giving 121/225. -/
theorem perfect_square_at_5 :
    8 * (120 + 1) = 121 * 8 ∧
    15 * 120 = 225 * 8 ∧
    121 = 11 * 11 ∧
    225 = 15 * 15 := by omega

/-- For N = 3: 8·(3!+1) = 56 is NOT a perfect square.
    Verified: no m ∈ {0,...,7} satisfies m² = 56 (and m ≥ 8 ⟹ m² ≥ 64 > 56). -/
theorem not_perfect_square_at_3 :
    (List.range 8).all (fun m => m * m != 56) = true := by native_decide

/-- For N = 4: 8·(4!+1) = 200 is NOT a perfect square.
    Verified: no m ∈ {0,...,14} satisfies m² = 200 (and m ≥ 15 ⟹ m² ≥ 225 > 200). -/
theorem not_perfect_square_at_4 :
    (List.range 15).all (fun m => m * m != 200) = true := by native_decide

/-- For N = 6: 8·(6!+1) = 5768 is NOT a perfect square.
    Verified: no m ∈ {0,...,75} satisfies m² = 5768 (and m ≥ 76 ⟹ m² ≥ 5776 > 5768). -/
theorem not_perfect_square_at_6 :
    (List.range 76).all (fun m => m * m != 5768) = true := by native_decide

/-- For N = 7: 15·7! = 75600 is NOT a perfect square.
    Verified: no m ∈ {0,...,274} satisfies m² = 75600 (and m ≥ 275 ⟹ m² ≥ 75625 > 75600). -/
theorem denom_not_square_at_7 :
    (List.range 275).all (fun m => m * m != 75600) = true := by native_decide

-- ============================================================
-- SOLENOIDAL BALANCE
-- ============================================================

-- The user discovered (2026-02-18) that replacing ω₁ = η₂ = 11 and
-- introducing π₁ = 2 with a factor 1/2, ALL THREE solenoidal generators
-- {π, γ, η} become visible in the α formula:
--
--   α = (1/2 · (π₁ · η₂) / (γ₁ · γ₂))² · ι_τ⁴
--     = (1/2 · 22/15)² · ι_τ⁴
--     = (11/15)² · ι_τ⁴
--
-- The structure (π · η)/γ² is a geometric mean deviation test:
-- if the tower were a geometric progression, π_n · η_n = γ_n² for all n.
-- The departure from this encodes physical coupling constants.

/-- π₁ = 2 (first value of π-orbit). -/
theorem pi_1_eq : towerVal 1 1 = 2 := by native_decide

/-- Solenoidal balance identity: π₁ · η₂ = 2 · ω₁.
    The product of the first π-value and second η-value equals twice
    the first ω-value, connecting all three solenoidal generators to ω. -/
theorem solenoidal_balance_identity :
    towerVal 1 1 * towerVal 3 2 = 2 * towerVal 4 1 := by native_decide

/-- Solenoidal half-normalization: (π₁ · η₂) / 2 = ω₁.
    This is the Nat division form: 22 / 2 = 11. -/
theorem solenoidal_half_normalization :
    (towerVal 1 1 * towerVal 3 2) / 2 = towerVal 4 1 := by native_decide

/-- The solenoidal balance form of α: (π₁ · η₂)² · 225 = 4 · 121 · (γ₁ · γ₂)².
    Cross-multiplied identity encoding
    ((π₁ · η₂) / (2 · γ₁ · γ₂))² = 121/225 = (11/15)². -/
theorem solenoidal_alpha_form :
    (towerVal 1 1 * towerVal 3 2)^2 * 225 =
    4 * 121 * (towerVal 2 1 * towerVal 2 2)^2 := by native_decide

-- ============================================================
-- GEOMETRIC MEAN DEPARTURE
-- ============================================================

-- If the tower were a geometric progression in the level direction,
-- γ_n² = π_n · η_n for all n (γ being level 2, the middle of 1-2-3).
-- The actual values depart systematically:

/-- Geometric mean departure at n=1: π₁ · η₁ = 2 · 5 = 10 (vs γ₁² = 9). -/
theorem geometric_mean_departure_1 :
    towerVal 1 1 * towerVal 3 1 = 10 := by native_decide

/-- Geometric mean departure at n=2: π₂ · η₂ = 3 · 11 = 33 (vs γ₂² = 25). -/
theorem geometric_mean_departure_2 :
    towerVal 1 2 * towerVal 3 2 = 33 := by native_decide

/-- Geometric mean departure at n=3: π₃ · η₃ = 5 · 31 = 155 (vs γ₃² = 121). -/
theorem geometric_mean_departure_3 :
    towerVal 1 3 * towerVal 3 3 = 155 := by native_decide

/-- γ₁² = 9, for comparison with π₁ · η₁ = 10. -/
theorem gamma_1_squared : (towerVal 2 1)^2 = 9 := by native_decide

/-- γ₂² = 25, for comparison with π₂ · η₂ = 33. -/
theorem gamma_2_squared : (towerVal 2 2)^2 = 25 := by native_decide

/-- γ₃² = 121, for comparison with π₃ · η₃ = 155. -/
theorem gamma_3_squared : (towerVal 2 3)^2 = 121 := by native_decide

-- ============================================================
-- SMOKE TESTS
-- ============================================================

-- Tower values (1-indexed)
#eval towerVal 0 5    -- 5 (α₅ = 5)
#eval towerVal 1 5    -- 11 (π₅ = p_5 = 11)
#eval towerVal 2 5    -- 31 (γ₅ = p_{p_5} = p_11 = 31)
#eval towerVal 3 5    -- 127 (η₅ = p_{p_{p_5}} = p_{p_11} = p_31 = 127)
#eval towerVal 4 3    -- 127 (ω₃ = P^(4)(3) = 127)

-- Key formula values
#eval towerVal 2 1 * towerVal 2 2    -- 15 (γ₁ · γ₂)
#eval (towerVal 4 1)^2               -- 121 (ω₁²)
#eval factorial (towerVal 3 1)    -- 120 (η₁! = 5!)

-- Tower table for display
#eval (List.range 6).map fun n => (n, towerVal 2 (n+1))  -- γ orbit
#eval (List.range 6).map fun n => (n, towerVal 3 (n+1))  -- η orbit
#eval (List.range 4).map fun n => (n, towerVal 4 (n+1))  -- ω orbit

-- Solenoidal balance
#eval towerVal 1 1 * towerVal 3 2          -- 22 (π₁ · η₂)
#eval (towerVal 1 1 * towerVal 3 2) / 2    -- 11 (= ω₁)

-- Geometric mean departures: π_n · η_n vs γ_n²
#eval (List.range 5).map fun i =>
  let n := i + 1
  (n, towerVal 1 n * towerVal 3 n, (towerVal 2 n)^2)

end Tau.Coordinates
