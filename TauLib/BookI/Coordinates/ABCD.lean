import TauLib.BookI.Coordinates.NormalForm

/-!
# TauLib.BookI.Coordinates.ABCD

ABCD coordinate chart, address DAG, and complexity metrics.

## Registry Cross-References

- [I.D17] ABCD Coordinate Chart — `abcd_chart`, `coord_A/B/C/D`
- [I.D24] Address DAG — `dag_indices`, `dag_size`
- [I.P08] Dimension (dim τ = 4) — `dim_tau_eq_four` (structural)
- [I.P09] Metric Inequality — `metric_inequality_check`

## Ground Truth Sources
- chunk_0241_M002280: ABCD coordinate chart Φ(X), address DAG structure

## Mathematical Content

The ABCD chart Φ(X) = (A, B, C, D) maps each X ≥ 2 to its greedy peel
decomposition. The four coordinates are:
- A = largest prime divisor (generator π-coordinate)
- B = maximal exponent quotient (generator γ-coordinate)
- C = maximal tetration height (generator η-coordinate)
- D = remainder after tower atom extraction (generator α-coordinate)

Recursing into all four coordinates produces a DAG (not a tree, since
distinct coordinates may coincide). Three complexity metrics satisfy
ℓ_spine(X) ≤ ℓ_DAG(X) ≤ ℓ_occ(X).
-/

namespace Tau.Coordinates

open Tau.Denotation Tau.Orbit

-- ============================================================
-- ABCD COORDINATE CHART [I.D17]
-- ============================================================

/-- [I.D17] ABCD coordinate chart: Φ(X) = (A, B, C, D). -/
def abcd_chart (x : TauIdx) : TauIdx × TauIdx × TauIdx × TauIdx := greedy_peel x

/-- A-coordinate (largest prime divisor). -/
def coord_A (x : TauIdx) : TauIdx := (abcd_chart x).1

/-- B-coordinate (exponent quotient). -/
def coord_B (x : TauIdx) : TauIdx := (abcd_chart x).2.1

/-- C-coordinate (tetration height). -/
def coord_C (x : TauIdx) : TauIdx := (abcd_chart x).2.2.1

/-- D-coordinate (remainder). -/
def coord_D (x : TauIdx) : TauIdx := (abcd_chart x).2.2.2

/-- Reconstruction: T(A,B,C) * D. -/
def chart_value (x : TauIdx) : TauIdx :=
  tower_atom (coord_A x) (coord_B x) (coord_C x) * coord_D x

-- ============================================================
-- ADDRESS DAG [I.D24]
-- ============================================================

/-- [I.D24] Collect all distinct indices reachable by recursing into ABCD
    coordinates. Uses a visited set for deduplication (DAG, not tree). -/
def dag_indices_go (worklist visited : List TauIdx) (fuel : Nat) : List TauIdx :=
  if fuel = 0 then visited
  else match worklist with
  | [] => visited
  | y :: rest =>
    if visited.contains y then dag_indices_go rest visited (fuel - 1)
    else if y ≤ 1 then dag_indices_go rest (y :: visited) (fuel - 1)
    else
      let a := coord_A y
      let b := coord_B y
      let c := coord_C y
      let d := coord_D y
      dag_indices_go (a :: b :: c :: d :: rest) (y :: visited) (fuel - 1)
termination_by fuel

def dag_indices (x : TauIdx) : List TauIdx := dag_indices_go [x] [] x

/-- DAG size: number of distinct indices reachable from x. -/
def dag_size (x : TauIdx) : Nat := (dag_indices x).length

-- ============================================================
-- OCCURRENCE SIZE (NAIVE TREE)
-- ============================================================

/-- Occurrence size: total node count in the ABCD tree (without deduplication). -/
def occ_size_go (x : TauIdx) (fuel : Nat) : TauIdx :=
  if fuel = 0 then 1
  else if x ≤ 1 then 1
  else
    let a := coord_A x
    let b := coord_B x
    let c := coord_C x
    let d := coord_D x
    1 + occ_size_go a (fuel - 1) + occ_size_go b (fuel - 1)
      + occ_size_go c (fuel - 1) + occ_size_go d (fuel - 1)
termination_by fuel

def occ_size (x : TauIdx) : TauIdx :=
  if x ≤ 1 then 1
  else occ_size_go x x

-- ============================================================
-- METRIC INEQUALITY [I.P09] (computable check)
-- ============================================================

/-- [I.P09] Check: spine_length ≤ dag_size ≤ occ_size. -/
def metric_inequality_check (x : TauIdx) : Bool :=
  spine_length x ≤ dag_size x && dag_size x ≤ occ_size x

-- ============================================================
-- DIMENSION [I.P08] (structural witness)
-- ============================================================

/-- [I.P08] Four-dimensionality witness: exhibit X values where each
    coordinate varies independently. Computable certificate. -/
def dim_tau_witnesses : List (TauIdx × TauIdx × TauIdx × TauIdx × TauIdx) :=
  -- (X, A, B, C, D): examples showing coordinate independence
  [ (12, 3, 1, 1, 4)     -- A = 3
  , (18, 3, 2, 1, 2)     -- same A, different B
  , (16, 2, 1, 3, 1)     -- different A, C = 3
  , (64, 2, 3, 2, 1)     -- same A as 16, different B and C
  ]

/-- Check that dim_tau_witnesses are consistent with the chart. -/
def dim_tau_check : Bool :=
  dim_tau_witnesses.all fun (x, a, b, c, d) =>
    coord_A x == a && coord_B x == b && coord_C x == c && coord_D x == d

-- ============================================================
-- SMOKE TESTS
-- ============================================================

-- Coordinate projections
#eval coord_A 64     -- 2
#eval coord_B 64     -- 3
#eval coord_C 64     -- 2
#eval coord_D 64     -- 1

#eval coord_A 360    -- 5
#eval coord_B 360    -- 1
#eval coord_C 360    -- 1
#eval coord_D 360    -- 72

-- Reconstruction
#eval chart_value 64     -- 64
#eval chart_value 360    -- 360
#eval chart_value 12     -- 12

-- DAG
#eval dag_indices 12     -- indices reachable from 12
#eval dag_size 12        -- number of distinct indices
#eval dag_size 64        -- should be small (64 → 2,3,2,1)

-- Occurrence size
#eval occ_size 12
#eval occ_size 64

-- Metric inequality
#eval metric_inequality_check 12     -- true
#eval metric_inequality_check 64     -- true
#eval metric_inequality_check 360    -- true
#eval metric_inequality_check 1000   -- true

-- Dimension witnesses
#eval dim_tau_check      -- true

end Tau.Coordinates
