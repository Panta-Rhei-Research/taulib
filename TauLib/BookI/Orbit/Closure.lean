import TauLib.BookI.Orbit.Countability

/-!
# TauLib.BookI.Orbit.Closure

The Ontic Closure Theorem: Obj(τ) = O_α ∪ O_π ∪ O_γ ∪ O_η ∪ Ω.

## Registry Cross-References

- [I.T01] Ontic Closure Theorem — `ontic_closure`

## Mathematical Content

The Ontic Closure Theorem is the central result of Part II.
It asserts that the universe of τ is:
1. Exhaustive: every object is in some orbit ray or is omega
2. Disjoint: the five components are pairwise disjoint
3. Countable: the universe is countably infinite
4. Sealed: no object exists outside these five components

In our Lean representation, property (4) is definitional:
`TauObj` is constructed from `Generator × Nat`, so it is
impossible to create objects outside the orbit structure.
-/

namespace Tau.Orbit

open Tau.Kernel Generator

-- ============================================================
-- ONTIC CLOSURE THEOREM [I.T01]
-- ============================================================

/-- [I.T01] Ontic Closure: every TauObj is either in an orbit ray
    or has seed omega. -/
theorem ontic_closure (x : TauObj) :
    (∃ g, g ≠ omega ∧ OrbitRay g x) ∨ x.seed = omega := by
  cases h : x.seed with
  | omega => exact Or.inr rfl
  | alpha => exact Or.inl ⟨alpha, by decide, h, by decide⟩
  | pi => exact Or.inl ⟨pi, by decide, h, by decide⟩
  | gamma => exact Or.inl ⟨gamma, by decide, h, by decide⟩
  | eta => exact Or.inl ⟨eta, by decide, h, by decide⟩

/-- Ontic closure: five-way decomposition. -/
theorem ontic_closure_five_way (x : TauObj) :
    OrbitRay alpha x ∨ OrbitRay pi x ∨
    OrbitRay gamma x ∨ OrbitRay eta x ∨
    x.seed = omega := by
  cases h : x.seed with
  | alpha => exact Or.inl ⟨h, by decide⟩
  | pi => exact Or.inr (Or.inl ⟨h, by decide⟩)
  | gamma => exact Or.inr (Or.inr (Or.inl ⟨h, by decide⟩))
  | eta => exact Or.inr (Or.inr (Or.inr (Or.inl ⟨h, by decide⟩)))
  | omega => exact Or.inr (Or.inr (Or.inr (Or.inr rfl)))

-- ============================================================
-- DISJOINTNESS (orbit vs omega)
-- ============================================================

/-- Orbit rays and the omega fiber are disjoint. -/
theorem orbit_omega_disjoint (g : Generator) (hg : g ≠ omega) (x : TauObj) :
    ¬(OrbitRay g x ∧ OmegaFiber x) := by
  intro ⟨⟨hseed, _⟩, homega⟩
  exact hg (hseed.symm.trans homega)

-- ============================================================
-- SEALED UNIVERSE
-- ============================================================

/-- The universe is sealed: the seed of any TauObj is one of the 5 generators.
    This is K6, restated at the orbit level. -/
theorem universe_sealed (x : TauObj) :
    x.seed = alpha ∨ x.seed = pi ∨ x.seed = gamma ∨
    x.seed = eta ∨ x.seed = omega :=
  K6_object_closure x

/-- Every non-omega TauObj is reached by iterated ρ from a generator. -/
theorem universe_generated (x : TauObj) (hx : x.seed ≠ omega) :
    ∃ g, g ≠ omega ∧ x = iter_rho x.depth (TauObj.ofGen g) := by
  exact ⟨x.seed, hx, by
    simp [TauObj.ofGen, iter_rho_depth x.seed hx 0 x.depth]⟩

-- ============================================================
-- RHO-EQUIVALENCE ON OMEGA FIBER
-- ============================================================

/-- All objects in the omega fiber are ρ-fixed. -/
theorem omega_fiber_rho_fixed (n : Nat) :
    rho ⟨omega, n⟩ = ⟨omega, n⟩ :=
  K2_omega_fixed n

/-- The canonical omega representative. -/
def omega_obj : TauObj := ⟨omega, 0⟩

end Tau.Orbit
