import TauLib.BookI.Coordinates.TowerAtoms

/-!
# TauLib.BookI.Coordinates.NormalForm

Normal form encoding and spine decomposition on τ-Idx.

## Registry Cross-References

- [I.D16] Normal Form Encoding — `NFStep`, `NFStep.ofPeel`
- [I.D23] Spine Decomposition — `spine`, `list_tower_prod`, `spine_reconstruction`

## Ground Truth Sources
- chunk_0241_M002280: NF peel-off term definition (Def 2.12), spine decomposition

## Mathematical Content

Every X ≥ 2 in τ-Idx decomposes as T(A,B,C) · D via the greedy peel.
Iterating this peel until D = 1 produces the **spine**: an ordered list of
tower atom triples (Aᵢ, Bᵢ, Cᵢ) whose product equals X.

The spine is computable. Its correctness (product = X) is verified
computationally here; formal descent (D < X) is proved in the
Descent module.
-/

namespace Tau.Coordinates

open Tau.Denotation Tau.Orbit

-- ============================================================
-- NORMAL FORM STEP [I.D16]
-- ============================================================

/-- [I.D16] A normal form step: (A, B, C, D) decomposing X = T(A,B,C) · D. -/
structure NFStep where
  A : TauIdx
  B : TauIdx
  C : TauIdx
  D : TauIdx
  deriving Repr, DecidableEq

/-- Convert greedy_peel output to NFStep. -/
def NFStep.ofPeel (x : TauIdx) : NFStep :=
  let (a, b, c, d) := greedy_peel x
  { A := a, B := b, C := c, D := d }

/-- The tower atom of an NF step. -/
def NFStep.atom (s : NFStep) : TauIdx := tower_atom s.A s.B s.C

/-- NF step reconstruction value: T(A,B,C) * D. -/
def NFStep.value (s : NFStep) : TauIdx := s.atom * s.D

-- ============================================================
-- LIST TOWER PRODUCT
-- ============================================================

/-- Product of a list of tower atoms. -/
def list_tower_prod : List (TauIdx × TauIdx × TauIdx) → TauIdx
  | [] => 1
  | (a, b, c) :: rest => tower_atom a b c * list_tower_prod rest

theorem list_tower_prod_nil : list_tower_prod [] = 1 := rfl

theorem list_tower_prod_cons (a b c : TauIdx) (rest : List (TauIdx × TauIdx × TauIdx)) :
    list_tower_prod ((a, b, c) :: rest) = tower_atom a b c * list_tower_prod rest := rfl

-- ============================================================
-- SPINE [I.D23]
-- ============================================================

/-- [I.D23] Iterated greedy peel producing a spine of (A,B,C) triples.
    Fuel-bounded; formal descent proved in the Descent module. -/
def spine (x : TauIdx) : List (TauIdx × TauIdx × TauIdx) :=
  if x ≤ 1 then []
  else go x x
where
  go (x fuel : TauIdx) : List (TauIdx × TauIdx × TauIdx) :=
    if fuel = 0 then []
    else if x ≤ 1 then []
    else
      let (a, b, c, d) := greedy_peel x
      (a, b, c) :: go d (fuel - 1)
  termination_by fuel
  decreasing_by simp_wf; simp only [TauIdx] at *; omega

/-- Length of a spine. -/
def spine_length (x : TauIdx) : Nat := (spine x).length

-- ============================================================
-- COMPUTABLE RECONSTRUCTION CHECK
-- ============================================================

/-- Check that spine(x) reconstructs to x. Computable boolean test. -/
def spine_check (x : TauIdx) : Bool := list_tower_prod (spine x) == x

-- ============================================================
-- SMOKE TESTS
-- ============================================================

-- Spine decompositions
#eval spine 12       -- [(3, 1, 1), (2, 1, 2)]: 3 * 4 = 12
#eval spine 64       -- [(2, 3, 2)]: 4^3 = 64
#eval spine 360      -- [(5, 1, 1), (3, 2, 1), (2, 3, 1)]: 5 * 9 * 8 = 360
#eval spine 7        -- [(7, 1, 1)]
#eval spine 1        -- []
#eval spine 16       -- [(2, 1, 3)]: 16
#eval spine 256      -- [(2, 2, 3)]: 16^2 = 256
#eval spine 100      -- should factor: 100 = 5^2 * 4

-- Reconstruction check
#eval spine_check 12     -- true
#eval spine_check 64     -- true
#eval spine_check 360    -- true
#eval spine_check 7      -- true
#eval spine_check 100    -- true
#eval spine_check 256    -- true
#eval spine_check 1000   -- true

-- Products
#eval list_tower_prod (spine 12)   -- 12
#eval list_tower_prod (spine 64)   -- 64
#eval list_tower_prod (spine 360)  -- 360

-- Spine lengths
#eval spine_length 12    -- 2
#eval spine_length 64    -- 1
#eval spine_length 360   -- 3
#eval spine_length 7     -- 1

-- NFStep
#eval (NFStep.ofPeel 64).A   -- 2
#eval (NFStep.ofPeel 64).B   -- 3
#eval (NFStep.ofPeel 64).C   -- 2
#eval (NFStep.ofPeel 64).D   -- 1

end Tau.Coordinates
