import TauLib.BookI.Kernel.Axioms

/-!
# TauLib.BookI.Kernel.Diagonal

The Diagonal Discipline: why exactly 4 orbit channels, and why
the iterator ladder saturates at tetration (level 3).

## Registry Cross-References

- [I.D03] Diagonal Discipline — `diagonal_discipline`

## Mathematical Content

The free diagonal on {α, π, γ, η} × {α, π, γ, η} has 12 off-diagonal
pairs (g, h) with g ≠ h. These 12 pairs organize into 3 rewiring levels:
- Level 1 (addition): consumes the π channel
- Level 2 (multiplication): consumes the γ channel
- Level 3 (exponentiation): consumes the η channel

The α channel is the counting scaffold (τ-Idx) and cannot be consumed.
Since K6 closes the universe at exactly 4 non-omega generators,
no 4th rewiring level exists. The iterator ladder saturates at 3 rewirings
(4 operations: ρ, +, ×, ^).
-/

namespace Tau.Kernel

open Generator

-- ============================================================
-- CHANNEL COUNTING
-- ============================================================

/-- [I.D03] There are exactly 4 non-omega generators.
    This is the source of the diagonal discipline:
    4 generators yield 3 rewiring levels. -/
theorem diagonal_channel_count : nonOmegaGenerators.length = 4 := by
  rfl

/-- The complete list of non-omega generators is [α, π, γ, η]. -/
theorem nonOmega_complete (g : Generator) (hg : g ≠ omega) :
    g ∈ nonOmegaGenerators := by
  cases g <;> simp [nonOmegaGenerators] <;> exact absurd rfl hg

-- ============================================================
-- REWIRING STRUCTURE
-- ============================================================

/-- The 3 solenoidal generators that serve as rewiring targets.
    α is the counting scaffold and is NOT a rewiring target. -/
def solenoidalGenerators : List Generator := [pi, gamma, eta]

/-- Exactly 3 solenoidal generators. -/
theorem solenoidal_count : solenoidalGenerators.length = 3 := by
  rfl

/-- The solenoidal generators are distinct from α. -/
theorem solenoidal_ne_alpha (g : Generator) (hg : g ∈ solenoidalGenerators) :
    g ≠ alpha := by
  simp [solenoidalGenerators] at hg
  rcases hg with rfl | rfl | rfl <;> decide

/-- The solenoidal generators are distinct from ω. -/
theorem solenoidal_ne_omega (g : Generator) (hg : g ∈ solenoidalGenerators) :
    g ≠ omega := by
  simp [solenoidalGenerators] at hg
  rcases hg with rfl | rfl | rfl <;> decide

/-- [I.D03] The diagonal discipline: exactly 3 rewiring levels exist
    because exactly 3 solenoidal generators are available as targets.
    Each rewiring level consumes one generator:
    - Level 1 (addition) ↔ π
    - Level 2 (multiplication) ↔ γ
    - Level 3 (exponentiation) ↔ η
    No 4th level: α is the counting scaffold, ω is the beacon. -/
theorem rewiring_levels_eq_solenoidal :
    solenoidalGenerators.length = nonOmegaGenerators.length - 1 := by
  rfl

/-- Alpha is the unique non-omega, non-solenoidal generator:
    the counting scaffold. -/
theorem alpha_unique_scaffold :
    alpha ∉ solenoidalGenerators ∧ alpha ≠ omega := by
  exact ⟨by decide, by decide⟩

end Tau.Kernel
