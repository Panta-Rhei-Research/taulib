import TauLib.BookI.Kernel.Axioms

/-!
# TauLib.BookI.Orbit.Generation

Orbit rays, iterated ρ, and the generative act.

## Registry Cross-References

- [I.X01] The Generative Act — `generative_act`
- [I.D05] Orbit Rays — `OrbitRay`
- [I.P03] Pairwise Disjointness — `orbit_disjoint`

## Mathematical Content

The generative act applies ρ to each non-omega generator g,
producing the orbit ray O_g = {g, ρ(g), ρ²(g), ...}.
The four orbit rays are pairwise disjoint (different seeds),
and ω sits alone as a fixed point.

NOTE: We use predicates (TauObj → Prop) rather than Mathlib's `Set`,
since we import Mathlib for tactics only.
-/

namespace Tau.Orbit

open Tau.Kernel Generator

-- ============================================================
-- ITERATED RHO
-- ============================================================

/-- Iterated application of ρ: ρⁿ(x). -/
def iter_rho : Nat → TauObj → TauObj
  | 0, x => x
  | n + 1, x => rho (iter_rho n x)

@[simp]
theorem iter_rho_zero (x : TauObj) : iter_rho 0 x = x := rfl

@[simp]
theorem iter_rho_succ (n : Nat) (x : TauObj) :
    iter_rho (n + 1) x = rho (iter_rho n x) := rfl

/-- iter_rho on a non-omega object increments depth. -/
theorem iter_rho_depth (g : Generator) (hg : g ≠ omega) (d n : Nat) :
    iter_rho n ⟨g, d⟩ = ⟨g, d + n⟩ := by
  induction n with
  | zero => simp
  | succ n ih =>
    simp only [iter_rho_succ, ih]
    have h := K4_no_jump g hg (d + n)
    rw [h]
    exact congrArg (TauObj.mk g) (by omega)

/-- iter_rho on omega is the identity. -/
@[simp]
theorem iter_rho_omega (n d : Nat) :
    iter_rho n ⟨omega, d⟩ = ⟨omega, d⟩ := by
  induction n with
  | zero => simp
  | succ n ih => simp [ih, K2_omega_fixed]

/-- iter_rho preserves the seed for non-omega generators. -/
theorem iter_rho_seed (g : Generator) (hg : g ≠ omega) (d n : Nat) :
    (iter_rho n ⟨g, d⟩).seed = g := by
  rw [iter_rho_depth g hg d n]

/-- iter_rho composes: ρⁿ⁺ᵐ(x) = ρⁿ(ρᵐ(x)). -/
theorem iter_rho_add (n m : Nat) (x : TauObj) :
    iter_rho (n + m) x = iter_rho n (iter_rho m x) := by
  induction n with
  | zero => simp
  | succ n ih =>
    simp only [Nat.succ_add, iter_rho_succ, ih]

-- ============================================================
-- ORBIT RAYS (as predicates)
-- ============================================================

/-- [I.D05] Orbit ray membership predicate: x ∈ O_g iff x has seed g
    and g is not omega. -/
def OrbitRay (g : Generator) (x : TauObj) : Prop :=
  x.seed = g ∧ g ≠ omega

/-- The omega fiber: all TauObj with seed omega. -/
def OmegaFiber (x : TauObj) : Prop :=
  x.seed = omega

/-- Each non-omega generator belongs to its own orbit ray. -/
theorem orbit_ray_contains_gen (g : Generator) (hg : g ≠ omega) :
    OrbitRay g (TauObj.ofGen g) :=
  ⟨rfl, hg⟩

/-- Orbit rays are closed under ρ. -/
theorem orbit_ray_rho_closed (g : Generator) (hg : g ≠ omega)
    (x : TauObj) (hx : OrbitRay g x) :
    OrbitRay g (rho x) := by
  obtain ⟨hseed, _⟩ := hx
  refine ⟨?_, hg⟩
  rw [show x = ⟨g, x.depth⟩ from by cases x; simp at hseed; simp [hseed]]
  exact K5_beacon_non_succ g hg x.depth

/-- Every element of an orbit ray is ⟨g, n⟩ for some n. -/
theorem orbit_ray_characterize (g : Generator) (hg : g ≠ omega) (x : TauObj) :
    OrbitRay g x ↔ ∃ n, x = ⟨g, n⟩ := by
  constructor
  · intro ⟨hseed, _⟩
    exact ⟨x.depth, by cases x; simp at hseed; simp [hseed]⟩
  · intro ⟨_, hx⟩
    exact ⟨by rw [hx], hg⟩

-- ============================================================
-- PAIRWISE DISJOINTNESS [I.P03]
-- ============================================================

/-- [I.P03] Orbit rays are pairwise disjoint: if g ≠ h, no object
    belongs to both O_g and O_h. -/
theorem orbit_disjoint (g h : Generator) (hgh : g ≠ h)
    (x : TauObj) : ¬(OrbitRay g x ∧ OrbitRay h x) := by
  intro ⟨⟨hsg, _⟩, ⟨hsh, _⟩⟩
  exact hgh (hsg.symm.trans hsh)

/-- Omega is not in any orbit ray. -/
theorem omega_not_in_orbit (g : Generator) (hg : g ≠ omega) (n : Nat) :
    ¬ OrbitRay g ⟨omega, n⟩ := by
  intro ⟨hseed, _⟩
  simp at hseed
  exact hg hseed.symm

/-- Orbit ray elements have seed equal to the generator. -/
theorem orbit_ray_seed (g : Generator) (x : TauObj) (hx : OrbitRay g x) :
    x.seed = g := hx.1

-- ============================================================
-- THE GENERATIVE ACT [I.X01]
-- ============================================================

/-- [I.X01] The generative act: every non-omega TauObj is reachable by
    iterated ρ from a generator. -/
theorem generative_act (x : TauObj) (hx : x.seed ≠ omega) :
    ∃ g n, g ≠ omega ∧ iter_rho n (TauObj.ofGen g) = x := by
  refine ⟨x.seed, x.depth, hx, ?_⟩
  simp [TauObj.ofGen, iter_rho_depth x.seed hx 0 x.depth]

end Tau.Orbit
