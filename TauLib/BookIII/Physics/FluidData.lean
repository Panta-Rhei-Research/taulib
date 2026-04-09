import TauLib.BookIII.Doors.MasterSchema

/-!
# TauLib.BookIII.Physics.FluidData

τ-Admissible Fluid Data, Cylinder Assignment, ABCD Extraction, and Defect Functional.

## Registry Cross-References

- [III.D36] τ-Admissible Fluid Data — `FluidData`, `fluid_data_check`
- [III.D37] Cylinder Assignment — `cylinder_assignment`, `cylinder_assignment_check`
- [III.D38] ABCD Extraction — `abcd_extract`, `abcd_check`
- [III.D39] Defect Functional — `defect_functional`, `defect_monotone_check`

## Mathematical Content

**III.D36 (τ-Admissible Fluid Data):** An ω-germ assignment on clopen cylinders
of ℤ̂_τ. At primorial level k, a fluid datum is a function assigning to each
cylinder [a mod Prim(k)] an ω-germ value, with ABCD extraction bounded.

**III.D37 (Cylinder Assignment):** The assignment map: each residue class
mod Prim(k) receives its boundary normal form, which carries B/C/X components.

**III.D38 (ABCD Extraction):** From a cylinder assignment, extract 4 components:
A = time-sector (primorial depth), B = B-lobe contribution, C = C-lobe contribution,
D = crossing-type contribution. Each is bounded by the primorial.

**III.D39 (Defect Functional):** Δ(f, k) = max over all cylinders at level k of
|BNF sum − original residue|. Measures deviation from canonical form. A good
fluid datum has Δ → 0 as k → ∞.
-/

namespace Tau.BookIII.Physics

open Tau.Polarity Tau.Boundary Tau.Coordinates Tau.Denotation
open Tau.BookII.Interior Tau.BookII.Enrichment
open Tau.BookIII.Enrichment Tau.BookIII.Sectors
open Tau.BookIII.Spectral Tau.BookIII.Doors

-- ============================================================
-- τ-ADMISSIBLE FLUID DATA [III.D36]
-- ============================================================

/-- [III.D36] Fluid data at primorial level k: for each cylinder [a mod Prim(k)],
    we store the boundary normal form (B, C, X components). -/
structure FluidData where
  depth : TauIdx           -- primorial depth k
  values : List TauIdx     -- residue values at each cylinder
  deriving Repr, DecidableEq, BEq

/-- [III.D36] Construct fluid data at depth k from bound: assigns each
    residue class its own value (the canonical assignment). -/
def make_fluid_data (k : TauIdx) : FluidData :=
  let pk := primorial k
  if pk == 0 then ⟨k, []⟩
  else ⟨k, List.range pk⟩

/-- [III.D36] τ-admissibility check: each cylinder value has a valid BNF
    decomposition at this depth. -/
def fluid_data_check (db : TauIdx) : Bool :=
  go 1 (db + 1)
where
  go (k fuel : Nat) : Bool :=
    if fuel = 0 then true
    else if k > db then true
    else
      let _fd := make_fluid_data k
      let pk := primorial k
      let valid := if pk > 0 then
        go_inner 0 pk k
      else true
      valid && go (k + 1) (fuel - 1)
  termination_by fuel
  go_inner (x pk k : Nat) : Bool :=
    if x >= pk then true
    else
      let nf := boundary_normal_form x k
      let sum := (nf.b_part + nf.c_part + nf.x_part) % pk
      sum == x && go_inner (x + 1) pk k

-- ============================================================
-- CYLINDER ASSIGNMENT [III.D37]
-- ============================================================

/-- [III.D37] Cylinder assignment: residue class x mod Prim(k) receives
    its boundary normal form. -/
def cylinder_assignment (x k : TauIdx) : BoundaryNF :=
  let pk := primorial k
  if pk == 0 then ⟨0, 0, 0, k⟩
  else boundary_normal_form (x % pk) k

/-- [III.D37] Cylinder assignment check: every cylinder has a valid
    BNF that sums correctly. -/
def cylinder_assignment_check (bound db : TauIdx) : Bool :=
  go 0 1 ((bound + 1) * (db + 1))
where
  go (x k fuel : Nat) : Bool :=
    if fuel = 0 then true
    else if x > bound then true
    else if k > db then go (x + 1) 1 (fuel - 1)
    else
      let nf := cylinder_assignment x k
      let pk := primorial k
      let ok := if pk > 0 then
        (nf.b_part + nf.c_part + nf.x_part) % pk == x % pk
      else true
      ok && go x (k + 1) (fuel - 1)
  termination_by fuel

-- ============================================================
-- ABCD EXTRACTION [III.D38]
-- ============================================================

/-- [III.D38] ABCD components of a fluid datum at a cylinder.
    A = depth (time/scale), B = B-lobe, C = C-lobe, D = crossing. -/
structure ABCDComponents where
  a_comp : TauIdx    -- depth (time component)
  b_comp : TauIdx    -- B-lobe contribution
  c_comp : TauIdx    -- C-lobe contribution
  d_comp : TauIdx    -- crossing (X-type) contribution
  deriving Repr, DecidableEq, BEq

/-- [III.D38] Extract ABCD components from a cylinder assignment. -/
def abcd_extract (x k : TauIdx) : ABCDComponents :=
  let nf := cylinder_assignment x k
  ⟨nf.depth, nf.b_part, nf.c_part, nf.x_part⟩

/-- [III.D38] ABCD extraction check: components are bounded by primorial,
    and B + C + D ≡ x (mod Prim(k)). -/
def abcd_check (bound db : TauIdx) : Bool :=
  go 0 1 ((bound + 1) * (db + 1))
where
  go (x k fuel : Nat) : Bool :=
    if fuel = 0 then true
    else if x > bound then true
    else if k > db then go (x + 1) 1 (fuel - 1)
    else
      let comp := abcd_extract x k
      let pk := primorial k
      let bounded := if pk > 0 then
        comp.b_comp < pk && comp.c_comp < pk && comp.d_comp < pk
      else true
      let consistent := if pk > 0 then
        (comp.b_comp + comp.c_comp + comp.d_comp) % pk == x % pk
      else true
      bounded && consistent && go x (k + 1) (fuel - 1)
  termination_by fuel

-- ============================================================
-- DEFECT FUNCTIONAL [III.D39]
-- ============================================================

/-- [III.D39] Defect at a single cylinder: |BNF sum − x| mod Prim(k).
    Zero defect means the BNF decomposition is exact. -/
def cylinder_defect (x k : TauIdx) : TauIdx :=
  let pk := primorial k
  if pk == 0 then 0
  else
    let nf := boundary_normal_form (x % pk) k
    let sum := (nf.b_part + nf.c_part + nf.x_part) % pk
    if sum >= x % pk then sum - x % pk else x % pk - sum

/-- [III.D39] Defect functional at primorial level k: maximum defect
    over all cylinders. -/
def defect_functional (k : TauIdx) : TauIdx :=
  let pk := primorial k
  if pk == 0 then 0
  else go 0 pk k 0
where
  go (x pk k max_def : Nat) : TauIdx :=
    if x >= pk then max_def
    else
      let d := cylinder_defect x k
      let new_max := if d > max_def then d else max_def
      go (x + 1) pk k new_max

/-- [III.D39] Defect monotonicity check: defect is zero at every level
    (because BNF decomposition is exact by construction). -/
def defect_monotone_check (db : TauIdx) : Bool :=
  go 1 (db + 1)
where
  go (k fuel : Nat) : Bool :=
    if fuel = 0 then true
    else if k > db then true
    else
      defect_functional k == 0 && go (k + 1) (fuel - 1)
  termination_by fuel

-- ============================================================
-- SMOKE TESTS
-- ============================================================

#eval fluid_data_check 4                     -- true
#eval cylinder_assignment_check 15 4         -- true
#eval abcd_check 15 4                        -- true
#eval defect_functional 3                    -- 0
#eval defect_monotone_check 5                -- true
#eval (abcd_extract 7 3).b_comp              -- B-component of 7 mod 30
#eval (abcd_extract 7 3).c_comp              -- C-component of 7 mod 30

-- ============================================================
-- FORMAL VERIFICATION (native_decide)
-- ============================================================

theorem fluid_data_4 :
    fluid_data_check 4 = true := by native_decide

theorem cylinder_assign_15_4 :
    cylinder_assignment_check 15 4 = true := by native_decide

theorem abcd_15_4 :
    abcd_check 15 4 = true := by native_decide

theorem defect_zero_3 :
    defect_functional 3 = 0 := by native_decide

theorem defect_zero_4 :
    defect_functional 4 = 0 := by native_decide

theorem defect_monotone_5 :
    defect_monotone_check 5 = true := by native_decide

-- ============================================================
-- STRUCTURAL THEOREMS
-- ============================================================

/-- [III.D36] Structural: canonical fluid data at depth 3 has 30 values. -/
theorem fluid_data_depth_3 :
    (make_fluid_data 3).values.length = 30 := by native_decide

/-- [III.D37] Structural: cylinder assignment at depth 0 is trivial. -/
theorem cylinder_assign_0 :
    cylinder_assignment 42 0 = ⟨0, 0, 0, 0⟩ := by native_decide

/-- [III.D38] Structural: ABCD of 0 is always zero. -/
theorem abcd_zero_3 :
    abcd_extract 0 3 = ⟨3, 0, 0, 0⟩ := by native_decide

/-- [III.D39] Structural: defect at depth 1 is zero. -/
theorem defect_zero_1 :
    defect_functional 1 = 0 := by native_decide

end Tau.BookIII.Physics
