import TauLib.BookI.Denotation.TauIdx

/-!
# TauLib.BookI.Denotation.RankTransfer

Rank transfer maps: canonical bijections TauIdx ↔ OrbitRay g.

## Registry Cross-References

- [I.D08] Rank Transfer — `RT`, `RT_inv`

## Mathematical Content

Since every orbit ray O_g has the form {⟨g, 0⟩, ⟨g, 1⟩, ⟨g, 2⟩, ...},
there is a canonical bijection with TauIdx (= Nat) via depth.
The rank transfer RT_g : TauIdx → O_g maps n ↦ ⟨g, n⟩.

This gives each orbit ray the same arithmetic structure as the alpha orbit:
any operation on TauIdx can be "transferred" to any orbit ray.
-/

namespace Tau.Denotation

open Tau.Kernel Tau.Orbit Generator

-- ============================================================
-- RANK TRANSFER [I.D08]
-- ============================================================

/-- [I.D08] Rank transfer: TauIdx → orbit ray O_g, mapping n ↦ ⟨g, n⟩. -/
def RT (g : Generator) (n : TauIdx) : TauObj := ⟨g, n⟩

/-- Rank transfer inverse: orbit ray element → TauIdx (extracts depth). -/
def RT_inv (x : TauObj) : TauIdx := x.depth

/-- RT is injective. -/
theorem RT_injective (g : Generator) (n m : TauIdx) (h : RT g n = RT g m) :
    n = m := by
  simp [RT] at h
  exact h

/-- RT hits every orbit ray element. -/
theorem RT_surjective (g : Generator) (_hg : g ≠ omega) (x : TauObj)
    (hx : OrbitRay g x) : ∃ n, RT g n = x := by
  obtain ⟨hseed, _⟩ := hx
  exact ⟨x.depth, by cases x; simp [RT] at hseed ⊢; exact hseed.symm⟩

/-- Round-trip: RT_inv ∘ RT = id. -/
theorem RT_inv_left (g : Generator) (n : TauIdx) :
    RT_inv (RT g n) = n := by
  rfl

/-- Round-trip: RT ∘ RT_inv = id (on orbit ray elements). -/
theorem RT_inv_right (g : Generator) (x : TauObj) (h : x.seed = g) :
    RT g (RT_inv x) = x := by
  cases x with | mk s d =>
  simp [RT, RT_inv] at h ⊢
  exact h.symm

/-- RT commutes with ρ: RT_g(n+1) = ρ(RT_g(n)) for g ≠ ω. -/
theorem RT_rho_comm (g : Generator) (hg : g ≠ omega) (n : TauIdx) :
    RT g (n + 1) = rho (RT g n) := by
  simp [RT]
  exact (K4_no_jump g hg n).symm

/-- RT lands in the orbit ray. -/
theorem RT_in_orbit (g : Generator) (hg : g ≠ omega) (n : TauIdx) :
    OrbitRay g (RT g n) := by
  exact ⟨rfl, hg⟩

/-- RT for alpha is the same as toAlphaOrbit. -/
theorem RT_alpha_eq (n : TauIdx) :
    RT alpha n = toAlphaOrbit n := by
  rfl

/-- Rank transfer is natural: σ_{g,h} ∘ RT_g = RT_h. -/
theorem RT_sigma (g h : Generator) (_hg : g ≠ h) (n : TauIdx) :
    sigma g h (RT g n) = RT h n := by
  simp [RT, sigma]

end Tau.Denotation
