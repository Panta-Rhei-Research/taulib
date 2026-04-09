import TauLib.BookI.Kernel.Diagonal

/-!
# TauLib.BookI.MetaLogic.Substrate

The meta-logical substrate: CIC structural rules and their status in τ.

## Registry Cross-References

- [I.D77] Meta-Logical Substrate — `MetaLogicalSubstrate`
- [I.R15] Structural Rules Inventory — structural rule classification

## Mathematical Content

CIC provides three structural rules: contraction, weakening, exchange.
K5's diagonal discipline refuses contraction and weakening at the object level
while preserving exchange. This module formalizes that classification.
-/

namespace Tau.MetaLogic

open Tau.Kernel Generator

-- ============================================================
-- STRUCTURAL RULES
-- ============================================================

/-- The three structural rules of classical sequent calculus. -/
inductive StructuralRule where
  | contraction   -- Γ, A, A ⊢ B  →  Γ, A ⊢ B  (use a resource twice)
  | weakening     -- Γ ⊢ B  →  Γ, A ⊢ B  (discard a resource)
  | exchange      -- Γ, A, B, Δ ⊢ C  →  Γ, B, A, Δ ⊢ C  (reorder)
  deriving DecidableEq, Repr

open StructuralRule

-- ============================================================
-- OBJECT-LEVEL STATUS
-- ============================================================

/-- The object-level status of a structural rule under K5's diagonal discipline. -/
inductive ObjectLevelStatus where
  | refused    -- Rule is refused at the object level
  | preserved  -- Rule is preserved at the object level
  deriving DecidableEq, Repr

open ObjectLevelStatus

/-- K5's classification: contraction and weakening are refused,
    exchange is preserved. -/
def k5_status : StructuralRule → ObjectLevelStatus
  | .contraction => .refused
  | .weakening   => .refused
  | .exchange    => .preserved

-- ============================================================
-- CLASSIFICATION THEOREMS
-- ============================================================

/-- Contraction is refused at the object level. -/
theorem contraction_refused : k5_status .contraction = .refused := rfl

/-- Weakening is refused at the object level. -/
theorem weakening_refused : k5_status .weakening = .refused := rfl

/-- Exchange is preserved at the object level. -/
theorem exchange_preserved : k5_status .exchange = .preserved := rfl

-- ============================================================
-- ALL RULES ENUMERATION
-- ============================================================

/-- The complete list of structural rules. -/
def allRules : List StructuralRule := [.contraction, .weakening, .exchange]

/-- There are exactly 3 structural rules. -/
theorem allRules_length : allRules.length = 3 := by rfl

/-- The rules refused by K5 at the object level. -/
def refusedRules : List StructuralRule :=
  allRules.filter (fun r => k5_status r == .refused)

/-- The rules preserved by K5 at the object level. -/
def preservedRules : List StructuralRule :=
  allRules.filter (fun r => k5_status r == .preserved)

/-- Exactly 2 rules are refused. -/
theorem refused_count : refusedRules.length = 2 := by native_decide

/-- Exactly 1 rule is preserved. -/
theorem preserved_count : preservedRules.length = 1 := by native_decide

/-- The refused rules are contraction and weakening. -/
theorem refused_are : refusedRules = [.contraction, .weakening] := by native_decide

/-- The preserved rule is exchange. -/
theorem preserved_is : preservedRules = [.exchange] := by native_decide

/-- Count consistency: refused + preserved = total. -/
theorem count_partition :
    refusedRules.length + preservedRules.length = allRules.length := by native_decide

-- ============================================================
-- CONNECTION TO DIAGONAL DISCIPLINE
-- ============================================================

/-- The 3 solenoidal generators correspond to 3 controlled rewiring levels.
    Free contraction would require unbounded rewiring. Since K6 bounds
    the universe at 4 non-omega generators, free contraction is structurally
    impossible: there are fewer rewiring targets (3) than total channels (4),
    so at least one channel (α) is NEVER a rewiring target and serves as
    the scaffold. -/
theorem diagonal_discipline_refuses_contraction :
    solenoidalGenerators.length < nonOmegaGenerators.length := by
  native_decide

/-- Every generator in `nonOmegaGenerators` is reachable by construction.
    No generator can be discarded — each participates in the orbit structure.
    The list is complete: every non-omega generator appears. -/
theorem diagonal_discipline_refuses_weakening :
    ∀ g : Generator, g ≠ omega → g ∈ nonOmegaGenerators :=
  nonOmega_complete

/-- The scaffold invariant: α is not a solenoidal generator.
    It is the unique channel that is never consumed by rewiring. -/
theorem scaffold_invariant : alpha ∉ solenoidalGenerators := by decide

/-- The rewiring budget is exactly 3 = 4 - 1.
    This means 3 levels of rewiring (addition, multiplication, exponentiation)
    and no room for a 4th. -/
theorem rewiring_budget :
    solenoidalGenerators.length = nonOmegaGenerators.length - 1 :=
  rewiring_levels_eq_solenoidal

-- ============================================================
-- SMOKE TESTS
-- ============================================================

#eval k5_status .contraction    -- refused
#eval k5_status .weakening      -- refused
#eval k5_status .exchange       -- preserved
#eval refusedRules              -- [contraction, weakening]
#eval preservedRules            -- [exchange]
#eval solenoidalGenerators.length   -- 3
#eval nonOmegaGenerators.length     -- 4

end Tau.MetaLogic
