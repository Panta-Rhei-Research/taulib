import TauLib.BookIV.Arena.CoherenceKernel

/-!
# TauLib.BookIV.Arena.RefinementTower

Refinement tower and profinite structure of Category τ at E₁.

## Registry Cross-References

- [IV.D249] Refinement Tower R — `RefinementTower`
- [IV.D250] Profinite Limit α̂ — `ProfiniteLimit`
- [IV.P147] Subsystem Horizon — `subsystem_horizon`
- [IV.D251] Proto-Time t_p — `ProtoTime`
- [IV.P148] NNO from α-Orbit — `nno_from_alpha`
- [IV.T95] Structural Arrow of Time — `structural_arrow`

## Mathematical Content

The refinement tower R = lim←_n (τ/τ_n) of finite quotients provides the
microscopic structure. The completion α̂ of the α-orbit defines proto-time
as a directed ordering. The natural numbers object is recovered from orbit
depth indexing, and the irreversible arrow of time from the tower's directedness.

## Ground Truth Sources
- Chapter 3 of Book IV (2nd Edition)
-/

namespace Tau.BookIV.Arena

open Tau.Kernel Tau.Boundary

-- ============================================================
-- REFINEMENT TOWER [IV.D249]
-- ============================================================

/-- [IV.D249] A level in the refinement tower: quotient at depth n.
    Each level captures the observable physics up to that resolution. -/
structure TowerLevel where
  /-- Depth index (positive natural). -/
  depth : Nat
  /-- Depth is positive (meaningful orbit level). -/
  depth_pos : depth > 0
  deriving Repr

/-- [IV.D249] The refinement tower R: a sequence of levels ordered by depth.
    R = lim←_n (τ/τ_n) — the profinite inverse limit. -/
structure RefinementTower where
  /-- Level accessor. -/
  level : Nat → TowerLevel
  /-- Levels are indexed consecutively starting at 1. -/
  level_depth : ∀ n : Nat, n > 0 → (level n).depth = n

/-- Canonical refinement tower: level n has depth n. -/
def canonical_tower : RefinementTower where
  level := fun n => ⟨if n > 0 then n else 1, by split <;> omega⟩
  level_depth := by
    intro n hn; simp [show n > 0 from hn]

-- ============================================================
-- PROFINITE LIMIT [IV.D250]
-- ============================================================

/-- [IV.D250] The profinite limit α̂ = lim←_n α_n: completion of
    the α-orbit providing the temporal substrate. Structurally,
    α̂ is the sequence of all orbit levels. -/
structure ProfiniteLimit where
  /-- The generating generator (always α for temporal). -/
  seed : Generator
  /-- Seed is alpha. -/
  seed_is_alpha : seed = .alpha
  /-- The tower providing the levels. -/
  tower : RefinementTower

/-- The canonical profinite limit of the α-orbit. -/
def alpha_profinite : ProfiniteLimit where
  seed := .alpha
  seed_is_alpha := rfl
  tower := canonical_tower

-- ============================================================
-- SUBSYSTEM HORIZON [IV.P147]
-- ============================================================

/-- [IV.P147] Subsystem horizon: every finite subsystem can only
    observe finitely many orbit levels. The profinite limit captures all.
    Formalized as: for any finite bound B, there exist levels beyond B. -/
theorem subsystem_horizon (B : Nat) : ∃ n : Nat, n > B := ⟨B + 1, by omega⟩

-- ============================================================
-- PROTO-TIME [IV.D251]
-- ============================================================

/-- [IV.D251] Proto-time: the ordering on α-orbit levels that defines
    temporal succession before any metric. Earlier levels (smaller depth)
    precede later levels (larger depth). -/
structure ProtoTime where
  /-- Current depth in the tower. -/
  tick : Nat
  /-- Tick is positive. -/
  tick_pos : tick > 0
  deriving Repr, DecidableEq

/-- Proto-time ordering: earlier ticks precede later ticks. -/
instance : LT ProtoTime where
  lt a b := a.tick < b.tick

instance : DecidableRel (α := ProtoTime) (· < ·) :=
  fun a b => inferInstanceAs (Decidable (a.tick < b.tick))

-- ============================================================
-- NNO FROM α-ORBIT [IV.P148]
-- ============================================================

/-- [IV.P148] The natural numbers object ℕ is recovered from α-orbit
    depth indexing: depth 1 ↦ 0, depth 2 ↦ 1, ... -/
def prototime_to_nat (t : ProtoTime) : Nat := t.tick - 1

/-- The map is surjective onto ℕ. -/
theorem nno_from_alpha (n : Nat) : ∃ t : ProtoTime, prototime_to_nat t = n :=
  ⟨⟨n + 1, by omega⟩, by simp [prototime_to_nat]⟩

-- ============================================================
-- STRUCTURAL ARROW OF TIME [IV.T95]
-- ============================================================

/-- [IV.T95] Structural arrow of time: the refinement tower is directed,
    meaning deeper levels always refine shallower ones. This gives an
    irreversible arrow: once at depth n, you cannot "un-refine" to n-1. -/
theorem structural_arrow (t1 t2 : ProtoTime) (h : t1 < t2) :
    t2.tick > t1.tick := h

/-- Transitivity of the arrow. -/
theorem arrow_transitive (t1 t2 t3 : ProtoTime)
    (h12 : t1 < t2) (h23 : t2 < t3) : t1 < t3 :=
  Nat.lt_trans h12 h23

/-- Irreflexivity: no time tick precedes itself. -/
theorem arrow_irreflexive (t : ProtoTime) : ¬(t < t) := Nat.lt_irrefl _

-- ============================================================
-- SMOKE TESTS
-- ============================================================

#eval (canonical_tower.level 1).depth  -- 1
#eval (canonical_tower.level 5).depth  -- 5
#eval prototime_to_nat ⟨1, by omega⟩  -- 0
#eval prototime_to_nat ⟨5, by omega⟩  -- 4

end Tau.BookIV.Arena
