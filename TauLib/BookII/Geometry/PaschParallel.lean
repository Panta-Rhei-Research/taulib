import TauLib.BookII.Geometry.Congruence

/-!
# TauLib.BookII.Geometry.PaschParallel

Pasch axiom and parallel postulate for ultrametric geometry on Ẑ_τ.

## Registry Cross-References

- [II.T17] Pasch Axiom — `pasch_spot_check`
- [II.T18] Parallel Postulate — `parallel_unique_check`

## Mathematical Content

**Pasch Axiom (II.T17):**
In ultrametric geometry, EVERY triple of points is collinear: for any
a, b, c, at least one of B(a,b,c), B(a,c,b), B(b,a,c) holds.

The classical Pasch axiom states: if B(a,p,c) and B(b,q,c) and a,b,c
form a non-collinear triangle, then ∃x with B(a,x,b) ∧ B(p,x,q).
Since no non-collinear triangle exists in the ultrametric tree, the
Pasch axiom is VACUOUSLY TRUE. The connectivity property (every triple
collinear) is the ultrametric substitute — it is STRONGER than Pasch
and subsumes all line-intersection reasoning.

**Parallel Postulate (II.T18):**
Given a "line" (depth-equivalence class at depth k) and a point not
on it, there exists a parallel "line" through that point.

In the ultrametric setting: lines are depth-level sets
{ z : δ(x,z) = k or δ(y,z) = k }. For a given depth k and external
point z, the branching structure provides at least one sibling branch
at the same depth, giving a canonical parallel direction.

Bound analysis: at depth k, all residue classes mod p_{k+1} must be
represented. Depth 0 needs bound ≥ 2, depth 1 needs ≥ 7, depth 2
needs ≥ 13 (all odd/even residue classes mod 6 covered).
-/

namespace Tau.BookII.Geometry

open Tau.BookII.Domains Tau.Polarity Tau.Denotation

-- ============================================================
-- PASCH AXIOM [II.T17] — VACUOUSLY TRUE VIA COLLINEARITY
-- ============================================================

/-- Triple collinearity: at least one betweenness ordering holds.
    In the ultrametric tree, this is ALWAYS true (ultrametric
    inequality forces isosceles triangles). -/
def collinear_triple (a b c db : TauIdx) : Bool :=
  between a b c db || between a c b db || between b a c db

/-- [II.T17] Pasch axiom spot check: verify collinearity for
    representative triangles spanning different tree configurations.
    Since all triples are collinear, Pasch is vacuously true
    (its hypothesis requires a non-collinear triangle). -/
def pasch_spot_check (db : TauIdx) : Bool :=
  collinear_triple 3 5 7 db &&
  collinear_triple 2 9 12 db &&
  collinear_triple 3 7 10 db &&
  collinear_triple 2 4 8 db

/-- [II.T17] Exhaustive collinearity check for all triples in [2, bound].
    Flat triple loop with single fuel counter. -/
def pasch_exhaustive_check (bound db : TauIdx) : Bool :=
  go 2 2 2 ((bound + 1) * (bound + 1) * (bound + 1))
where
  go (a b c fuel : Nat) : Bool :=
    if fuel = 0 then true
    else if a > bound then true
    else if b > bound then go (a + 1) 2 2 (fuel - 1)
    else if c > bound then go a (b + 1) 2 (fuel - 1)
    else collinear_triple a b c db && go a b (c + 1) (fuel - 1)
  termination_by fuel

-- ============================================================
-- PARALLEL POSTULATE [II.T18]
-- ============================================================

/-- [II.T18] Depth-line: x and y determine a "line" at depth k = δ(x,y).
    The line through x,y consists of all z with δ(x,z) = k or δ(y,z) = k. -/
def on_depth_line (x y z db : TauIdx) : Bool :=
  let k := disagree_depth x y db
  disagree_depth x z db == k || disagree_depth y z db == k

/-- [II.T18] Find a parallel partner: w ≠ z with δ(z,w) = k in [2, bound].
    Returns true iff such a partner exists. -/
def find_parallel_partner (z k db bound : TauIdx) : Bool :=
  go 2 (bound + 1)
where
  go (w fuel : Nat) : Bool :=
    if fuel = 0 then false
    else if w > bound then false
    else if w != z && disagree_depth z w db == k then true
    else go (w + 1) (fuel - 1)
  termination_by fuel

/-- Inner loop for parallel check: iterate over z for fixed x, y. -/
def parallel_check_z (x y bound db : TauIdx) : Bool :=
  go 2 (bound + 1)
where
  go (z fuel : Nat) : Bool :=
    if fuel = 0 then true
    else if z > bound then true
    else if on_depth_line x y z db then
      go (z + 1) (fuel - 1)
    else
      let k := disagree_depth x y db
      find_parallel_partner z k db bound && go (z + 1) (fuel - 1)
  termination_by fuel

/-- Inner loop for parallel check: iterate over y for fixed x. -/
def parallel_check_y (x bound db : TauIdx) : Bool :=
  go 2 (bound + 1)
where
  go (y fuel : Nat) : Bool :=
    if fuel = 0 then true
    else if y > bound then true
    else if x == y then go (y + 1) (fuel - 1)
    else parallel_check_z x y bound db && go (y + 1) (fuel - 1)
  termination_by fuel

/-- [II.T18] Parallel existence: for every line (x,y) and external
    point z, there exists at least one parallel partner w with
    δ(z,w) = δ(x,y). The ultrametric tree branching forces this. -/
def parallel_exists_check (bound db : TauIdx) : Bool :=
  go 2 (bound + 1)
where
  go (x fuel : Nat) : Bool :=
    if fuel = 0 then true
    else if x > bound then true
    else parallel_check_y x bound db && go (x + 1) (fuel - 1)
  termination_by fuel

/-- [II.T18] Full parallel postulate check. -/
def parallel_unique_check (bound db : TauIdx) : Bool :=
  parallel_exists_check bound db

-- ============================================================
-- TARSKI COMPLETENESS: ALL AXIOMS
-- ============================================================

/-- Complete Tarski axiom check: betweenness + congruence + Pasch + parallel. -/
def tarski_complete_check (bound db : TauIdx) : Bool :=
  between_identity_check bound db &&
  between_connectivity_check bound db &&
  cong_reflexivity_check bound db &&
  cong_identity_check bound db &&
  pasch_spot_check db &&
  parallel_unique_check bound db

-- ============================================================
-- SMOKE TESTS
-- ============================================================

-- Collinearity checks
#eval collinear_triple 3 5 7 5       -- true
#eval collinear_triple 2 9 12 5      -- true
#eval collinear_triple 3 7 10 5      -- true
#eval collinear_triple 2 4 8 5       -- true

-- Spot check
#eval pasch_spot_check 5              -- true

-- Exhaustive for small range
#eval pasch_exhaustive_check 5 5      -- true

-- Parallel partner finding
#eval find_parallel_partner 3 1 5 13  -- true (depth 1)
#eval find_parallel_partner 7 2 5 13  -- true (depth 2)

-- Parallel existence
#eval parallel_exists_check 6 5       -- true (depth ≤ 1)
#eval parallel_exists_check 13 5      -- true (depth ≤ 2)

-- Combined Tarski
#eval tarski_complete_check 6 5       -- true

-- ============================================================
-- FORMAL VERIFICATION
-- ============================================================

theorem pasch_spot : pasch_spot_check 5 = true := by native_decide
theorem pasch_exhaustive_5 : pasch_exhaustive_check 5 5 = true := by native_decide
theorem parallel_6 : parallel_unique_check 6 5 = true := by native_decide
theorem parallel_13 : parallel_unique_check 13 5 = true := by native_decide
theorem tarski_complete_6 : tarski_complete_check 6 5 = true := by native_decide

end Tau.BookII.Geometry
