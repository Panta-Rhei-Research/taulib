import TauLib.BookII.Domains.Cylinders

/-!
# TauLib.BookII.Domains.Ultrametric

First disagreement depth and ultrametric structure on Ẑ_τ.

## Registry Cross-References

- [II.D12] First Disagreement Depth — `disagree_depth`
- [II.D13] Ultrametric Distance — `ultra_dist` (encoded as depth)
- [II.T05] Ultrametric Inequality — `triangle_check`
- [II.P04] Cylinders = Balls — `cyl_eq_ball_check`

## Mathematical Content

δ(x, y) = max { k : π_k(x) = π_k(y) }
d(x, y) = 2^{-δ(x,y)}, d(x, x) = 0

Ultrametric: d(x,z) ≤ max(d(x,y), d(y,z))
Equivalently: δ(x,z) ≥ min(δ(x,y), δ(y,z))

Cylinder-ball correspondence: C_k(x) = { y : δ(x,y) ≥ k }
-/

namespace Tau.BookII.Domains

open Tau.Polarity Tau.Denotation

-- ============================================================
-- FIRST DISAGREEMENT DEPTH [II.D12]
-- ============================================================

/-- [II.D12] First disagreement depth δ(x, y).
    Returns max { k : π_k(x) = π_k(y) } for k ≤ bound.
    If they agree for all k ≤ bound, returns bound + 1 (∞ proxy).
    Stage 0 always agrees (primorial 0 = 1), so δ ≥ 0. -/
def disagree_depth (x y bound : TauIdx) : TauIdx :=
  go 0 (bound + 2)
where
  go (k fuel : Nat) : TauIdx :=
    if fuel = 0 then k
    else if k > bound then bound + 1
    else if reduce x (k + 1) ≠ reduce y (k + 1) then k
    else go (k + 1) (fuel - 1)
  termination_by fuel

-- ============================================================
-- ULTRAMETRIC DISTANCE [II.D13]
-- ============================================================

/-- [II.D13] Ultrametric distance encoded as agreement depth.
    Higher depth = closer (smaller distance).
    d(x,y) = 2^{-disagree_depth(x,y)}, d(x,x) = 0.
    Convention: depth = bound + 1 represents d = 0 (identity). -/
def ultra_dist (x y bound : TauIdx) : TauIdx :=
  disagree_depth x y bound

/-- Symmetry: δ(x,y) = δ(y,x). Flat double loop. -/
def symmetry_check (bound : TauIdx) : Bool :=
  go 2 2 ((bound + 1) * (bound + 1))
where
  go (x y fuel : Nat) : Bool :=
    if fuel = 0 then true
    else if x > bound then true
    else if y > bound then go (x + 1) 2 (fuel - 1)
    else (disagree_depth x y 5 == disagree_depth y x 5) &&
         go x (y + 1) (fuel - 1)
  termination_by fuel

/-- Non-degeneracy: δ(x,x) = ∞ and δ(x,y) < ∞ for x ≠ y. -/
def nondegen_check (bound : TauIdx) : Bool :=
  go 2 (bound + 1)
where
  go (x fuel : Nat) : Bool :=
    if fuel = 0 then true
    else if x > bound then true
    else
      (disagree_depth x x 5 == 6) &&
      (x + 1 > bound || disagree_depth x (x + 1) 5 < 6) &&
      go (x + 1) (fuel - 1)
  termination_by fuel

-- ============================================================
-- ULTRAMETRIC TRIANGLE INEQUALITY [II.T05]
-- ============================================================

/-- [II.T05] Ultrametric triangle inequality:
    δ(x,z) ≥ min(δ(x,y), δ(y,z)) for all x, y, z ∈ [2, bound].
    Equivalent to d(x,z) ≤ max(d(x,y), d(y,z)).
    Uses a flat triple loop with single fuel counter. -/
def triangle_check (bound db : TauIdx) : Bool :=
  go 2 2 2 ((bound + 1) * (bound + 1) * (bound + 1))
where
  go (x y z fuel : Nat) : Bool :=
    if fuel = 0 then true
    else if x > bound then true
    else if y > bound then go (x + 1) 2 2 (fuel - 1)
    else if z > bound then go x (y + 1) 2 (fuel - 1)
    else
      let dxz := disagree_depth x z db
      let dxy := disagree_depth x y db
      let dyz := disagree_depth y z db
      (dxz ≥ min dxy dyz) && go x y (z + 1) (fuel - 1)
  termination_by fuel

-- ============================================================
-- CYLINDERS = BALLS [II.P04]
-- ============================================================

/-- [II.P04] C_k(x) = B(x, 2^{-k}) = { y : δ(x,y) ≥ k }.
    Cylinder membership and ultrametric ball membership coincide. -/
def cyl_eq_ball_check (k center bound db : TauIdx) : Bool :=
  go 2 (bound + 1)
where
  go (y fuel : Nat) : Bool :=
    if fuel = 0 then true
    else if y > bound then true
    else
      let in_cyl := cylinder_mem k center y
      let in_ball := disagree_depth center y db ≥ k
      (in_cyl == in_ball) && go (y + 1) (fuel - 1)
  termination_by fuel

-- ============================================================
-- SMOKE TESTS
-- ============================================================

#eval disagree_depth 3 5 5    -- 1 (agree mod 2, differ mod 6)
#eval disagree_depth 3 9 5    -- 2 (agree mod 6, differ mod 30)
#eval disagree_depth 7 7 5    -- 6 (equal → ∞ proxy)
#eval disagree_depth 2 3 5    -- 0 (differ mod 2)

#eval symmetry_check 15       -- true
#eval nondegen_check 15        -- true
#eval triangle_check 8 5       -- true

#eval cyl_eq_ball_check 1 3 20 5    -- true
#eval cyl_eq_ball_check 2 7 30 5    -- true

-- Formal verification
theorem sym_15 : symmetry_check 15 = true := by native_decide
theorem nondegen_15 : nondegen_check 15 = true := by native_decide
theorem triangle_8_5 : triangle_check 8 5 = true := by native_decide
theorem cyl_ball_k1 : cyl_eq_ball_check 1 3 20 5 = true := by native_decide
theorem cyl_ball_k2 : cyl_eq_ball_check 2 7 30 5 = true := by native_decide

end Tau.BookII.Domains
