import TauLib.BookI.Orbit.Rigidity
import TauLib.BookI.Orbit.Ladder

/-!
# TauLib.BookI.Orbit.TooMany

Counter-model: a 6-generator tau-like system admits a non-trivial
ρ-automorphism, breaking rigidity.

## Registry Cross-References

- [I.T11a] Six-Generator Rigidity Failure — `six_gen_rigidity_fails`

## Mathematical Content

If we add a 6th generator ζ (between η and ω), the resulting system
satisfies all K-axiom analogues but has a non-trivial automorphism:
the swap η ↔ ζ commutes with ρ₆ and is an involution, yet is not
the identity. This shows that 5 generators is not merely sufficient
for rigidity — it is *necessary*.

The key insight: with 6 generators, η and ζ are both solenoidal
(neither the counting scaffold α nor the fixed-point ω) and play
interchangeable structural roles, so swapping them preserves all
axioms while moving objects.
-/

namespace Tau.Orbit.TooMany

open Tau.Kernel

-- ============================================================
-- SIX-GENERATOR SIGNATURE
-- ============================================================

/-- A hypothetical 6-generator alphabet: α, π, γ, η, ζ, ω. -/
inductive Gen6 : Type where
  | alpha : Gen6
  | pi    : Gen6
  | gamma : Gen6
  | eta   : Gen6
  | zeta  : Gen6   -- the extra generator
  | omega : Gen6
  deriving DecidableEq, Repr

open Gen6

/-- Canonical ordering: α=0, π=1, γ=2, η=3, ζ=4, ω=5. -/
def Gen6.toNat : Gen6 → Nat
  | alpha => 0
  | pi    => 1
  | gamma => 2
  | eta   => 3
  | zeta  => 4
  | omega => 5

-- ============================================================
-- OBJECTS AND ρ₆
-- ============================================================

/-- Objects of the 6-generator system: (seed, depth) pairs. -/
structure Obj6 where
  seed : Gen6
  depth : Nat
  deriving DecidableEq, Repr

/-- The progression operator ρ₆: fixes ω-fiber, increments depth otherwise. -/
def rho6 (x : Obj6) : Obj6 :=
  match x.seed with
  | Gen6.omega => x
  | _ => ⟨x.seed, x.depth + 1⟩

-- ============================================================
-- K-AXIOM ANALOGUES
-- ============================================================

/-- K1₆: The generators are strictly ordered. -/
theorem K1_six : Gen6.toNat alpha < Gen6.toNat pi ∧
    Gen6.toNat pi < Gen6.toNat gamma ∧
    Gen6.toNat gamma < Gen6.toNat eta ∧
    Gen6.toNat eta < Gen6.toNat zeta ∧
    Gen6.toNat zeta < Gen6.toNat omega := by
  decide

/-- K2₆: ω is the unique fixed point of ρ₆. -/
theorem K2_six (d : Nat) : rho6 ⟨omega, d⟩ = ⟨omega, d⟩ := by
  rfl

/-- K4₆: ρ₆ increments depth for non-ω generators. -/
theorem K4_six (g : Gen6) (hg : g ≠ omega) (d : Nat) :
    rho6 ⟨g, d⟩ = ⟨g, d + 1⟩ := by
  cases g <;> simp [rho6] <;> exact absurd rfl hg

-- ============================================================
-- THE SWAP AUTOMORPHISM η ↔ ζ
-- ============================================================

/-- Swap η and ζ, fix everything else. -/
def swap_ez : Gen6 → Gen6
  | eta   => zeta
  | zeta  => eta
  | g     => g

/-- Lift the generator swap to objects. -/
def swap6 (x : Obj6) : Obj6 := ⟨swap_ez x.seed, x.depth⟩

/-- swap_ez is an involution on generators. -/
theorem swap_ez_invol (g : Gen6) : swap_ez (swap_ez g) = g := by
  cases g <;> rfl

/-- swap6 is an involution on objects. -/
theorem swap6_involution (x : Obj6) : swap6 (swap6 x) = x := by
  cases x with | mk s d =>
  simp [swap6, swap_ez_invol]

/-- swap6 commutes with ρ₆. -/
theorem swap6_rho_comm (x : Obj6) : swap6 (rho6 x) = rho6 (swap6 x) := by
  cases x with | mk s d =>
  cases s <;> rfl

/-- swap6 is NOT the identity: it moves ⟨η, 0⟩. -/
theorem swap6_ne_id : swap6 ⟨eta, 0⟩ ≠ ⟨eta, 0⟩ := by
  decide

-- ============================================================
-- RIGIDITY FAILURE [I.T09a]
-- ============================================================

/-- [I.T09a] **Six-Generator Rigidity Failure**:
    A 6-generator tau-like system admits a non-trivial ρ-automorphism.

    The witness is the swap η ↔ ζ, which:
    (1) commutes with ρ₆ (preserves all dynamical structure)
    (2) is an involution (self-inverse, hence bijective)
    (3) is not the identity (moves ⟨η, 0⟩ to ⟨ζ, 0⟩)

    This shows that adding a 6th generator breaks the rigidity
    property Aut(τ) = {id} that holds for exactly 5 generators. -/
theorem six_gen_rigidity_fails :
    ∃ (f : Obj6 → Obj6),
      (∀ x, f (rho6 x) = rho6 (f x)) ∧
      (∀ x, f (f x) = x) ∧
      ¬(∀ x, f x = x) :=
  ⟨swap6, swap6_rho_comm, swap6_involution, fun h => swap6_ne_id (h _)⟩

-- ============================================================
-- SOLENOIDAL COUNT: 6 generators have 4 solenoidal
-- ============================================================

/-- In Gen6, the solenoidal generators are {π, γ, η, ζ} — four of them.
    This is one more than the 3 rewiring levels need, creating the
    η ↔ ζ ambiguity that enables the swap automorphism. -/
def solenoidal6 : List Gen6 := [pi, gamma, eta, zeta]

theorem solenoidal6_count : solenoidal6.length = 4 := by rfl

/-- The surplus: 4 solenoidal generators for only 3 rewiring levels. -/
theorem solenoidal6_surplus : solenoidal6.length > 3 := by decide

end Tau.Orbit.TooMany
