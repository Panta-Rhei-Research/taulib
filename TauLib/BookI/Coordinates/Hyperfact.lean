import TauLib.BookI.Coordinates.NoTie
import TauLib.BookI.Coordinates.Descent
import TauLib.BookI.Coordinates.ABCD

/-!
# TauLib.BookI.Coordinates.Hyperfact

Hyperfactorization: existence and uniqueness of the ABCD decomposition.

## Registry Cross-References

- [I.T04] Hyperfactorization Theorem — `hyperfact_check`, No-Tie + Descent
- [I.C01] Constructive Encoding Corollary — `encoding_check`

## Ground Truth Sources
- chunk_0241_M002280: Existence-uniqueness (Thm 2.14), constructive encoding
- chunk_0310_M002679: No-tie (Lemma 2.1) as uniqueness ingredient

## Mathematical Content

The Hyperfactorization Theorem states: every X ≥ 2 has a unique decomposition
X = T(A,B,C) · D where A is the largest prime divisor, C is the maximal
tetration height for the A-adic valuation, B = v_A(X) / A↑↑(C-1), and
D = X / T(A,B,C).

Uniqueness follows from the No-Tie Lemma (I.L03): the pair (B,C) is forced
by the maximality of C. Descent (I.L04) ensures D < X, so iteration terminates.

The constructive encoding corollary (I.C01) states: Φ is an injection from
τ-Idx ≥ 2 to the set of quadruples satisfying the ABCD constraints.
-/

namespace Tau.Coordinates

open Tau.Denotation Tau.Orbit

-- ============================================================
-- HYPERFACTORIZATION CONSTRAINTS
-- ============================================================

/-- Predicate: (A,B,C,D) is a valid ABCD decomposition of X. -/
def ValidABCD (x a b c d : TauIdx) : Prop :=
  a ≥ 2 ∧ b ≥ 1 ∧ c ≥ 1 ∧
  tower_atom a b c * d = x ∧
  (d = 0 ∨ ¬(a ∣ d))  -- D is A-free (or zero)

/-- Computable check for valid ABCD constraints. -/
def valid_abcd_check (x a b c d : TauIdx) : Bool :=
  a ≥ 2 && b ≥ 1 && c ≥ 1 &&
  tower_atom a b c * d == x &&
  (d ≤ 1 || d % a != 0)

-- ============================================================
-- HYPERFACTORIZATION THEOREM [I.T04] (computable verification)
-- ============================================================

/-- [I.T04] Verify hyperfactorization for a single X:
    - Greedy peel produces valid ABCD
    - Reconstruction is exact
    - Descent holds -/
def hyperfact_check (x : TauIdx) : Bool :=
  if x ≤ 1 then true
  else
    let (a, b, c, d) := greedy_peel x
    -- Valid constraints
    valid_abcd_check x a b c d &&
    -- Descent
    (d < x) &&
    -- Maximality of C (no-tie precondition)
    (b * tetration a (c - 1) % (tetration a c) != 0 || c ≤ 1)

-- ============================================================
-- CONSTRUCTIVE ENCODING [I.C01]
-- ============================================================

/-- [I.C01] Encoding: map X to its (spine, final remainder) pair.
    This is injective by the Hyperfactorization Theorem. -/
def tau_encode (x : TauIdx) : List (TauIdx × TauIdx × TauIdx) × TauIdx :=
  (spine x, if x ≤ 1 then x else 1)

/-- Decoding: reconstruct X from its spine encoding. -/
def tau_decode (enc : List (TauIdx × TauIdx × TauIdx) × TauIdx) : TauIdx :=
  list_tower_prod enc.1 * enc.2

/-- Check that encoding is a left inverse of decoding. -/
def encoding_check (x : TauIdx) : Bool :=
  tau_decode (tau_encode x) == x

-- ============================================================
-- INJECTIVITY CHECK
-- ============================================================

/-- Check Φ is injective on [2..n]: no two distinct X values share coordinates. -/
def injectivity_check_go (i n : Nat) (fuel : Nat) : Bool :=
  if fuel = 0 then true
  else if i > n then true
  else
    let ok := hyperfact_check i && encoding_check i
    ok && injectivity_check_go (i + 1) n (fuel - 1)
termination_by fuel

def injectivity_check (n : TauIdx) : Bool := injectivity_check_go 2 n n

-- ============================================================
-- SMOKE TESTS
-- ============================================================

-- Hyperfactorization checks
#eval hyperfact_check 12     -- true
#eval hyperfact_check 64     -- true
#eval hyperfact_check 360    -- true
#eval hyperfact_check 7      -- true
#eval hyperfact_check 1000   -- true

-- Encoding round-trip
#eval tau_encode 64          -- ([(2, 3, 2)], 1)
#eval tau_encode 360         -- ([(5, 1, 1), (3, 2, 1), (2, 3, 1)], 1)
#eval tau_decode (tau_encode 64)   -- 64
#eval tau_decode (tau_encode 360)  -- 360
#eval encoding_check 64      -- true
#eval encoding_check 360     -- true

-- Batch verification: all X from 2 to 500
#eval injectivity_check 500  -- true

end Tau.Coordinates
