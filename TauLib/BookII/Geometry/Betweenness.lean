import TauLib.BookII.Domains.Ultrametric

/-!
# TauLib.BookII.Geometry.Betweenness

Betweenness relation from ultrametric distance, executing the Tarski program.

## Registry Cross-References

- [II.D19] Betweenness Relation — `between`
- [II.T15] Betweenness Axioms — `between_identity_check`, `between_connectivity_check`

## Mathematical Content

B(x,y,z) ⟺ δ(x,z) = min(δ(x,y), δ(y,z))

Equivalently: y lies "between" x and z in the ultrametric tree if
y agrees with both endpoints up to their mutual divergence depth.

Tarski axioms:
- T1 (Identity): B(x,y,x) ⟹ x = y
- T2 (Transitivity): B(x,y,z) ∧ B(y,z,w) ⟹ B(x,y,w)
- T3 (Connectivity): For any triple, at least one betweenness holds
  (stronger than Tarski: ALL triples, not just collinear)
-/

namespace Tau.BookII.Geometry

open Tau.BookII.Domains Tau.Polarity Tau.Denotation

-- ============================================================
-- BETWEENNESS RELATION [II.D19]
-- ============================================================

/-- [II.D19] Ultrametric betweenness: B(x,y,z) iff
    δ(x,z) = min(δ(x,y), δ(y,z)).
    y lies on the geodesic from x to z in the profinite tree. -/
def between (x y z db : TauIdx) : Bool :=
  let dxz := disagree_depth x z db
  let dxy := disagree_depth x y db
  let dyz := disagree_depth y z db
  dxz == min dxy dyz

-- ============================================================
-- BETWEENNESS AXIOMS [II.T15]
-- ============================================================

/-- [II.T15, T1] Identity: B(x,y,x) ⟹ x = y.
    If δ(x,x) = min(δ(x,y), δ(y,x)), then δ(x,y) = ∞, so x = y.
    Check: B(x,y,x) is true only when x = y. -/
def between_identity_check (bound db : TauIdx) : Bool :=
  go 2 2 ((bound + 1) * (bound + 1))
where
  go (x y fuel : Nat) : Bool :=
    if fuel = 0 then true
    else if x > bound then true
    else if y > bound then go (x + 1) 2 (fuel - 1)
    else
      let ok := !between x y x db || x == y
      ok && go x (y + 1) (fuel - 1)
  termination_by fuel

/-- [II.T15, T3] Connectivity: for any x, y, z, at least one of
    B(x,y,z), B(y,x,z), B(x,z,y) holds.
    Ultrametric isosceles property guarantees this. -/
def between_connectivity_check (bound db : TauIdx) : Bool :=
  go 2 2 2 ((bound + 1) * (bound + 1) * (bound + 1))
where
  go (x y z fuel : Nat) : Bool :=
    if fuel = 0 then true
    else if x > bound then true
    else if y > bound then go (x + 1) 2 2 (fuel - 1)
    else if z > bound then go x (y + 1) 2 (fuel - 1)
    else
      (between x y z db || between y x z db || between x z y db) &&
      go x y (z + 1) (fuel - 1)
  termination_by fuel

/-- [II.T15, T2] Outer transitivity: B(x,y,z) ∧ B(x,z,w) ⟹ B(x,y,w).
    If y is between x and z, and z is between x and w,
    then y is between x and w (monotonic along rays from x).
    Verified exhaustively for small range. -/
def between_transitivity_check (bound db : TauIdx) : Bool :=
  go 2 2 2 2 ((bound + 1) * (bound + 1) * (bound + 1) * (bound + 1))
where
  go (x y z w fuel : Nat) : Bool :=
    if fuel = 0 then true
    else if x > bound then true
    else if y > bound then go (x + 1) 2 2 2 (fuel - 1)
    else if z > bound then go x (y + 1) 2 2 (fuel - 1)
    else if w > bound then go x y (z + 1) 2 (fuel - 1)
    else
      let ok := !(between x y z db && between x z w db) || between x y w db
      ok && go x y z (w + 1) (fuel - 1)
  termination_by fuel

-- ============================================================
-- SMOKE TESTS
-- ============================================================

-- B(2, 4, 6): check betweenness
#eval between 2 4 6 5
-- B(x, x, z) should always hold (degenerate case)
#eval between 3 3 7 5    -- true (δ(3,7) = min(∞, δ(3,7)))
-- Connectivity
#eval between 3 5 7 5 || between 5 3 7 5 || between 3 7 5 5  -- true

-- Axiom checks
#eval between_identity_check 10 5        -- true
#eval between_connectivity_check 8 5     -- true
#eval between_transitivity_check 6 5     -- true

-- Formal verification
theorem identity_10 : between_identity_check 10 5 = true := by native_decide
theorem connectivity_8 : between_connectivity_check 8 5 = true := by native_decide
theorem transitivity_6 : between_transitivity_check 6 5 = true := by native_decide

end Tau.BookII.Geometry
