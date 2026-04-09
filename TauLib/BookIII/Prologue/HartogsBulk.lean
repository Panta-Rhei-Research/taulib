import TauLib.BookII.Closure.ForwardBook3

/-!
# TauLib.BookIII.Prologue.HartogsBulk

Hartogs Bulk Projection and E₁ as Gluing Principle.

## Registry Cross-References

- [III.D01] Hartogs Bulk Projection — `HartogsBulk`, `hartogs_bulk_check`
- [III.D03] E₁ as Gluing Principle — `e1_gluing_check`

## Mathematical Content

**III.D01 (Hartogs Bulk Projection):** 3D Cartesian space = Hartogs-projected
bulk of the local T² fiber at each worldline point. Solenoidal surface
coordinates (γ, η) carry boundary data; Hartogs extension fills the interior
with genuine linear coordinates.

**III.D03 (E₁ as Gluing Principle):** Self-enrichment (E₁) is precisely the
statement that local Hartogs bulk projections glue globally. Morphisms between
local patches carry the same split-complex bipolar structure as the patches
themselves. Physics IS E₁.

Book III starts at E₁ (verified by ForwardBook3.lean). These two definitions
set the stage: Hartogs bulk = local spatial structure, E₁ gluing = global
coherence.
-/

namespace Tau.BookIII.Prologue

open Tau.Polarity Tau.Boundary Tau.Coordinates Tau.Denotation
open Tau.BookII.Closure Tau.BookII.Enrichment

-- ============================================================
-- HARTOGS BULK PROJECTION [III.D01]
-- ============================================================

/-- [III.D01] Hartogs Bulk Projection: at each stage k, the bulk coordinate
    is the interior value obtained by Hartogs extension from boundary data.
    Concretely: given boundary values at stage k (the reduce-compatible map),
    the bulk value is the unique Hartogs extension = reduce(x, k).

    The "3D space" perceived at a point is the Hartogs-filled interior of
    the local T² fiber. We model this as: for each pair (boundary_val, stage),
    the bulk projection is the reduce of their sum (combining solenoidal
    coordinates into a single interior coordinate). -/
structure HartogsBulk where
  boundary_b : TauIdx  -- B-channel boundary value
  boundary_c : TauIdx  -- C-channel boundary value
  stage : TauIdx       -- primorial stage
  deriving Repr, DecidableEq

/-- [III.D01] Compute the bulk coordinate from boundary data.
    The bulk projection combines two boundary channels via addition
    mod primorial (Hartogs fill = summation of boundary contributions). -/
def bulk_coordinate (hb : HartogsBulk) : TauIdx :=
  reduce (hb.boundary_b + hb.boundary_c) hb.stage

/-- [III.D01] Hartogs bulk coherence: the bulk coordinate at stage k+1
    projects correctly to stage k. This is the local version of tower
    coherence applied to the spatial (Hartogs-filled) interior. -/
def hartogs_bulk_coherent (hb : HartogsBulk) (k : TauIdx) : Bool :=
  if k >= hb.stage then true
  else
    let bulk_at_stage := reduce (hb.boundary_b + hb.boundary_c) hb.stage
    let projected := reduce bulk_at_stage k
    let direct := reduce (hb.boundary_b + hb.boundary_c) k
    projected == direct

/-- [III.D01] Full Hartogs bulk check: for all boundary pairs in range,
    verify tower coherence of the bulk projection. -/
def hartogs_bulk_check (bound db : TauIdx) : Bool :=
  go 0 0 1 ((bound + 1) * (bound + 1) * (db + 1))
where
  go (b c k fuel : Nat) : Bool :=
    if fuel = 0 then true
    else if b > bound then true
    else if c > bound then go (b + 1) 0 1 (fuel - 1)
    else if k >= db then go b (c + 1) 1 (fuel - 1)
    else
      let hb : HartogsBulk := ⟨b, c, db⟩
      hartogs_bulk_coherent hb k && go b c (k + 1) (fuel - 1)
  termination_by fuel

-- ============================================================
-- E₁ AS GLUING PRINCIPLE [III.D03]
-- ============================================================

/-- [III.D03] E₁ gluing check: verify that Book II is complete (all 6
    export components verified) and that the Hartogs bulk projection
    is tower-coherent. E₁ = "local patches glue" = "physics exists".

    This combines the ForwardBook3 export with local Hartogs coherence. -/
def e1_gluing_check (bound db k_max : TauIdx) : Bool :=
  full_export_check db bound k_max &&
  hartogs_bulk_check bound db

/-- [III.D03] The entry point for Book III: E₁ is established.
    Book III begins at E₁ and constructs the full enrichment ladder. -/
def book3_e1_established (bound db k_max : TauIdx) : Bool :=
  book3_starts_at_e1 db bound k_max && e1_gluing_check bound db k_max

-- ============================================================
-- SMOKE TESTS
-- ============================================================

-- Bulk coordinate
#eval bulk_coordinate ⟨3, 5, 2⟩     -- reduce(8, 2) = 2
#eval bulk_coordinate ⟨0, 0, 3⟩     -- reduce(0, 3) = 0
#eval bulk_coordinate ⟨10, 7, 2⟩    -- reduce(17, 2) = 5

-- Hartogs bulk coherence
#eval hartogs_bulk_coherent ⟨5, 3, 3⟩ 1    -- true
#eval hartogs_bulk_coherent ⟨5, 3, 3⟩ 2    -- true

-- Hartogs bulk check
#eval hartogs_bulk_check 8 3               -- true

-- E₁ gluing
#eval e1_gluing_check 8 3 3               -- true

-- Book III entry established
#eval book3_e1_established 8 3 3          -- true

-- ============================================================
-- FORMAL VERIFICATION (native_decide)
-- ============================================================

-- Hartogs bulk coherence [III.D01]
theorem hartogs_bulk_8_3 :
    hartogs_bulk_check 8 3 = true := by native_decide

-- E₁ gluing [III.D03]
theorem e1_gluing_8_3_3 :
    e1_gluing_check 8 3 3 = true := by native_decide

-- Book III entry [III.D03]
theorem book3_entry_8_3_3 :
    book3_e1_established 8 3 3 = true := by native_decide

-- ============================================================
-- STRUCTURAL THEOREMS
-- ============================================================

/-- [III.D01] Structural proof: Hartogs bulk projection is tower-coherent.
    reduce(reduce(b + c, stage), k) = reduce(b + c, k) for k ≤ stage.
    This is reduction_compat from Book I. -/
theorem bulk_tower_coherent (b c : TauIdx) {k stage : TauIdx} (h : k ≤ stage) :
    reduce (reduce (b + c) stage) k = reduce (b + c) k :=
  reduction_compat (b + c) h

/-- [III.D01] Bulk projection is reduce-stable:
    reduce(bulk_coordinate(hb), hb.stage) = bulk_coordinate(hb). -/
theorem bulk_reduce_stable (hb : HartogsBulk) :
    reduce (bulk_coordinate hb) hb.stage = bulk_coordinate hb := by
  simp only [bulk_coordinate, reduce]
  exact Nat.mod_mod_of_dvd _ (dvd_refl (primorial hb.stage))

end Tau.BookIII.Prologue
