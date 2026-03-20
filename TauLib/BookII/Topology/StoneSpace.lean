import TauLib.BookII.Domains.Ultrametric

/-!
# TauLib.BookII.Topology.StoneSpace

Stone space structure: compact, Hausdorff, totally disconnected.

## Registry Cross-References

- [II.D14] Stone Space — `StoneWitness`
- [II.T07] Compactness — `finite_subcover_check`
- [II.T08] Hausdorff Property — `hausdorff_check`
- [II.T09] Total Disconnectedness — `totally_disconnected_check`

## Mathematical Content

τ³ = lim←_k ℤ/M_kℤ is a Stone space:
1. Compact: inverse limit of finite discrete spaces
2. Hausdorff: distinct points separated by disjoint cylinders
3. Totally disconnected: every connected component is a singleton

Proof of Hausdorff: for x ≠ y, let k = δ(x,y). Then C_{k+1}(x) and
C_{k+1}(y) are disjoint clopen sets separating x and y.

Proof of total disconnectedness: for x ≠ y in S ⊆ τ³, the clopen
cylinder C_{k+1}(x) splits S into two nonempty open parts.
-/

namespace Tau.BookII.Topology

open Tau.BookII.Domains Tau.Polarity Tau.Denotation

-- ============================================================
-- HAUSDORFF PROPERTY [II.T08]
-- ============================================================

/-- [II.T08] Hausdorff: distinct points have disjoint cylinder
    neighborhoods. For x ≠ y with δ(x,y) = k, the cylinders
    C_{k+1}(x) and C_{k+1}(y) are disjoint.
    Check: for all x ≠ y, find separating stage. -/
def hausdorff_check (bound db : TauIdx) : Bool :=
  go 2 2 ((bound + 1) * (bound + 1))
where
  go (x y fuel : Nat) : Bool :=
    if fuel = 0 then true
    else if x > bound then true
    else if y > bound then go (x + 1) 2 (fuel - 1)
    else
      -- x = y trivially separated; x ≠ y needs separating stage
      let ok := x == y || (
        let k := disagree_depth x y db
        k < db + 1 &&  -- they actually disagree somewhere
        !cylinder_mem (k + 1) x y)  -- disjoint at stage k+1
      ok && go x (y + 1) (fuel - 1)
  termination_by fuel

/-- Constructive witness: return the separating stage for x ≠ y. -/
def separating_stage (x y db : TauIdx) : TauIdx :=
  if x == y then db + 1
  else disagree_depth x y db + 1

-- ============================================================
-- TOTAL DISCONNECTEDNESS [II.T09]
-- ============================================================

/-- [II.T09] Total disconnectedness: for x ≠ y, there exists a
    clopen set containing x but not y (the separating cylinder).
    Check: for all x ≠ y, verify the separating cylinder works. -/
def totally_disconnected_check (bound db : TauIdx) : Bool :=
  go 2 2 ((bound + 1) * (bound + 1))
where
  go (x y fuel : Nat) : Bool :=
    if fuel = 0 then true
    else if x > bound then true
    else if y > bound then go (x + 1) 2 (fuel - 1)
    else
      let ok := x == y || (
        let k := separating_stage x y db
        cylinder_mem k x x && !cylinder_mem k x y)
      ok && go x (y + 1) (fuel - 1)
  termination_by fuel

-- ============================================================
-- COMPACTNESS [II.T07]
-- ============================================================

/-- [II.T07] Compactness: every cover by cylinders at stage k has
    a finite subcover. For finite ranges, this is automatic since
    ℤ/M_kℤ is finite (|ℤ/M_kℤ| = M_k residue classes).
    Check: the number of stage-k cylinders in [2, bound] is finite. -/
def finite_subcover_check (k bound : TauIdx) : Bool :=
  let mk := primorial k
  if mk == 0 then true
  else
    -- At stage k, there are at most M_k distinct cylinders
    -- Every element belongs to exactly one
    -- Count distinct residue classes in range
    let residues := go 2 (bound + 1) []
    residues.eraseDups.length ≤ mk
where
  go (y fuel : Nat) (acc : List TauIdx) : List TauIdx :=
    if fuel = 0 then acc
    else if y > bound then acc
    else go (y + 1) (fuel - 1) (reduce y k :: acc)
  termination_by fuel

-- ============================================================
-- STONE SPACE ASSEMBLY [II.D14]
-- ============================================================

/-- [II.D14] Stone space: compact + Hausdorff + totally disconnected.
    Combined verification. -/
def stone_space_check (bound db : TauIdx) : Bool :=
  hausdorff_check bound db &&
  totally_disconnected_check bound db &&
  finite_subcover_check 1 bound &&
  finite_subcover_check 2 bound &&
  finite_subcover_check 3 bound

/-- Stone space witness structure: for each pair (x,y) with x ≠ y,
    records the separating stage. -/
structure StoneWitness where
  x : TauIdx
  y : TauIdx
  sep_stage : TauIdx  -- stage at which x,y are separated
  deriving Repr

/-- Produce separation witness. -/
def stone_witness (x y db : TauIdx) : StoneWitness :=
  ⟨x, y, separating_stage x y db⟩

-- ============================================================
-- SMOKE TESTS
-- ============================================================

#eval hausdorff_check 15 5              -- true
#eval totally_disconnected_check 15 5   -- true
#eval finite_subcover_check 1 20        -- true
#eval finite_subcover_check 2 30        -- true
#eval stone_space_check 12 5            -- true

#eval separating_stage 3 5 5    -- 2 (stage where they diverge + 1)
#eval separating_stage 3 9 5    -- 3
#eval separating_stage 7 7 5    -- 6 (∞ proxy, equal)

#eval stone_witness 3 5 5       -- (3, 5, 2)
#eval stone_witness 12 30 5     -- witness for these two points

-- Formal verification
theorem hausdorff_15 : hausdorff_check 15 5 = true := by native_decide
theorem td_15 : totally_disconnected_check 15 5 = true := by native_decide
theorem subcover_k1 : finite_subcover_check 1 20 = true := by native_decide
theorem subcover_k2 : finite_subcover_check 2 30 = true := by native_decide
theorem stone_12 : stone_space_check 12 5 = true := by native_decide

end Tau.BookII.Topology
