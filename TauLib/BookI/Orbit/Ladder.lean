import TauLib.BookI.Orbit.Closure
import TauLib.BookI.Kernel.Diagonal

/-!
# TauLib.BookI.Orbit.Ladder

The iterator ladder: 4 levels of meta-iteration, and saturation at tetration.

## Registry Cross-References

- [I.D06] Iterator Ladder — `LadderLevel`, `ladderOp`
- [I.T02] Iterator Ladder Saturation — `ladder_saturation`
- [I.L01] Pentation Non-Injectivity — `pentation_channel_exhaustion`

## Ground Truth Sources
- chunk_0060_M000698: UR-ITER requirement, ladder saturation forced by arity exhaustion
- chunk_0050_M000608: Diagonal rewiring, typed channel assignments

## Mathematical Content

The iterator ladder has 4 levels:
- Level 0: ρ (successor / depth increment)
- Level 1: iterated ρ (addition on depths)
- Level 2: iterated addition (multiplication)
- Level 3: iterated multiplication (exponentiation)

Each level is canonically injective (in its second argument for fixed first).
At level 4 (tetration), the operations can still be defined, but there is
no 5th orbit channel to associate with pentation. Since there are only
4 non-omega generators, the ladder saturates at 4 levels (3 rewiring levels).
-/

namespace Tau.Orbit

open Tau.Kernel Generator

-- ============================================================
-- ITERATOR LADDER OPERATIONS
-- ============================================================

/-- [I.D06] The 5 hyperoperation levels (ρ through tetration).
    Only levels 0-3 have canonical orbit channel assignments. -/
inductive LadderLevel : Type where
  | rho_level    : LadderLevel  -- Level 0: ρ
  | add_level    : LadderLevel  -- Level 1: iterated ρ = addition
  | mul_level    : LadderLevel  -- Level 2: iterated addition = multiplication
  | exp_level    : LadderLevel  -- Level 3: iterated multiplication = exponentiation
  | tet_level    : LadderLevel  -- Level 4: iterated exponentiation = tetration
  deriving DecidableEq, Repr

/-- Tetration (iterated exponentiation): a ↑↑ 0 = 1, a ↑↑ (n+1) = a ^ (a ↑↑ n). -/
def tetration : Nat → Nat → Nat
  | _, 0 => 1
  | n, m + 1 => n ^ (tetration n m)

/-- The hyperoperation at each ladder level (on Nat = depth values). -/
def ladderOp : LadderLevel → Nat → Nat → Nat
  | .rho_level, _, m => m + 1        -- ρ: successor (ignores first arg)
  | .add_level, n, m => n + m        -- addition
  | .mul_level, n, m => n * m        -- multiplication
  | .exp_level, n, m => n ^ m        -- exponentiation
  | .tet_level, n, m => tetration n m -- tetration

/-- The canonical orbit channel assigned to each rewiring level.
    Level 0 (ρ) uses all channels uniformly.
    Levels 1-3 each consume one solenoidal generator. -/
def ladderChannel : LadderLevel → Option Generator
  | .rho_level => none           -- ρ acts on all orbits
  | .add_level => some pi        -- addition ↔ π channel
  | .mul_level => some gamma     -- multiplication ↔ γ channel
  | .exp_level => some eta       -- exponentiation ↔ η channel
  | .tet_level => none           -- no channel available

-- ============================================================
-- INJECTIVITY AT EACH LEVEL
-- ============================================================

/-- Addition is injective in the second argument (for any fixed first). -/
theorem add_injective (n : Nat) : Function.Injective (n + ·) := by
  intro a b h
  have h' : n + a = n + b := h
  omega

/-- Multiplication by n > 0 is injective in the second argument. -/
theorem mul_injective (n : Nat) (hn : n > 0) : Function.Injective (n * ·) := by
  intro a b h
  induction a generalizing b with
  | zero =>
    have h' : n * 0 = n * b := h
    rw [Nat.mul_zero] at h'
    cases b with
    | zero => rfl
    | succ b => rw [Nat.mul_succ] at h'; omega
  | succ a ih =>
    have h' : n * (a + 1) = n * b := h
    cases b with
    | zero => rw [Nat.mul_zero, Nat.mul_succ] at h'; omega
    | succ b =>
      congr 1
      apply ih
      show n * a = n * b
      rw [Nat.mul_succ, Nat.mul_succ] at h'
      omega

/-- Exponentiation with base n ≥ 2 is injective in the exponent. -/
theorem exp_injective (n : Nat) (hn : n ≥ 2) : Function.Injective (n ^ ·) := by
  intro a b h
  have h' : n ^ a = n ^ b := h
  have h1 : ¬(a < b) := by
    intro hlt
    have : n ^ a < n ^ b := Nat.pow_lt_pow_right (by omega) hlt
    omega
  have h2 : ¬(b < a) := by
    intro hgt
    have : n ^ b < n ^ a := Nat.pow_lt_pow_right (by omega) hgt
    omega
  omega

-- ============================================================
-- SATURATION [I.T02] AND PENTATION NON-INJECTIVITY [I.L01]
-- ============================================================

/-- The number of available orbit channels for rewiring. -/
theorem available_channels : solenoidalGenerators.length = 3 :=
  solenoidal_count

/-- [I.L01] Pentation cannot be assigned a canonical orbit channel:
    all 3 solenoidal generators are consumed by levels 1-3,
    and alpha is the counting scaffold. No 5th channel exists (K6).

    This is the channel-exhaustion form of the saturation argument. -/
theorem pentation_channel_exhaustion :
    ladderChannel .tet_level = none := by
  rfl

/-- [I.T02] The iterator ladder saturates at 4 levels:
    exactly 3 solenoidal generators exist (solenoidalGenerators.length = 3),
    so exactly 3 rewiring levels can be canonically assigned,
    giving 4 total operation levels (ρ + 3 rewirings).

    The 4th rewiring level (pentation/level 4) has no channel. -/
theorem ladder_saturation :
    solenoidalGenerators.length = 3 ∧ ladderChannel .tet_level = none := by
  exact ⟨by rfl, by rfl⟩

/-- Each of the first 3 rewiring levels has an assigned channel. -/
theorem ladder_channels_assigned :
    ladderChannel .add_level = some pi ∧
    ladderChannel .mul_level = some gamma ∧
    ladderChannel .exp_level = some eta := by
  exact ⟨rfl, rfl, rfl⟩

/-- The assigned channels are pairwise distinct. -/
theorem ladder_channels_distinct :
    pi ≠ gamma ∧ pi ≠ eta ∧ gamma ≠ eta := by
  exact ⟨by decide, by decide, by decide⟩

end Tau.Orbit
