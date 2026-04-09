import TauLib.BookI.Orbit.Closure

/-!
# TauLib.BookI.Denotation.TauIdx

τ-Idx: the alpha orbit IS the natural numbers. The swap operator σ
permutes seeds between orbits.

## Registry Cross-References

- [I.D07] τ-Idx — `TauIdx`, `toAlphaOrbit`
- [I.D09] Swap Operator — `sigma`, `sigma_involutive`

## Mathematical Content

The alpha orbit O_α = {⟨α, 1⟩, ⟨α, 2⟩, ⟨α, 3⟩, ...} is in canonical
bijection with ℕ⁺ = {1, 2, 3, ...} via n ↦ ⟨α, n⟩. We define TauIdx
as a transparent alias for Nat, emphasizing that the natural numbers
are *discovered* as the depth values of the alpha orbit — not imported.

**Convention**: Semantically, τ-Idx = ℕ⁺ (positive naturals). Lean uses
`TauIdx = Nat` for convenience; orbit-meaningful indices are ≥ 1.
The element ⟨α, 0⟩ = α is the **generator itself** (depth 0 = no ρ
applied), not an orbit element α_0. Zero only enters as an arithmetic
value when ring structures are built (Part VIII).

The swap operator σ_{s,t} exchanges the seeds s and t, providing
canonical bijections between orbit rays.
-/

namespace Tau.Denotation

open Tau.Kernel Tau.Orbit Generator

-- ============================================================
-- τ-IDX [I.D07]
-- ============================================================

/-- [I.D07] τ-Idx: the natural number system discovered as the alpha orbit.
    Using `abbrev` makes this definitionally equal to Nat.

    Semantically, τ-Idx = ℕ⁺. Orbit indices start at 1:
    α_1 = ⟨α, 1⟩, α_2 = ⟨α, 2⟩, etc. The Lean type is Nat
    for convenience; orbit-meaningful theorems carry nonzero guards. -/
abbrev TauIdx := Nat

/-- Canonical embedding: TauIdx → TauObj (into the alpha orbit). -/
def toAlphaOrbit (n : TauIdx) : TauObj := ⟨alpha, n⟩

/-- Extraction: TauObj (alpha orbit) → TauIdx. -/
def fromAlphaOrbit (x : TauObj) : TauIdx := x.depth

/-- The embedding is injective. -/
theorem toAlpha_injective (n m : TauIdx) (h : toAlphaOrbit n = toAlphaOrbit m) :
    n = m := by
  simp [toAlphaOrbit] at h
  exact h

/-- Round-trip: fromAlpha ∘ toAlpha = id. -/
theorem toAlpha_fromAlpha (n : TauIdx) :
    fromAlphaOrbit (toAlphaOrbit n) = n := by
  rfl

/-- The embedding lands in the alpha orbit ray. -/
theorem toAlpha_in_orbit (n : TauIdx) :
    OrbitRay alpha (toAlphaOrbit n) := by
  exact ⟨rfl, by decide⟩

/-- The embedding commutes with ρ: toAlpha(n+1) = ρ(toAlpha(n)). -/
theorem toAlpha_rho (n : TauIdx) :
    toAlphaOrbit (n + 1) = rho (toAlphaOrbit n) := by
  simp [toAlphaOrbit, rho]

-- ============================================================
-- SWAP OPERATOR [I.D09]
-- ============================================================

/-- [I.D09] The swap operator σ_{s,t}: exchanges seeds s and t,
    leaving all other seeds unchanged. Preserves depth. -/
def sigma (s t : Generator) (x : TauObj) : TauObj :=
  if x.seed = s then ⟨t, x.depth⟩
  else if x.seed = t then ⟨s, x.depth⟩
  else x

/-- σ is an involution: σ_{s,t}(σ_{s,t}(x)) = x. -/
theorem sigma_involutive (s t : Generator) (x : TauObj) :
    sigma s t (sigma s t x) = x := by
  cases x with | mk seed depth =>
  cases seed <;> cases s <;> cases t <;> simp [sigma]

/-- σ preserves depth. -/
theorem sigma_preserves_depth (s t : Generator) (x : TauObj) :
    (sigma s t x).depth = x.depth := by
  cases x with | mk seed depth =>
  cases seed <;> cases s <;> cases t <;> simp [sigma]

/-- σ with s = t is the identity. -/
theorem sigma_self (s : Generator) (x : TauObj) :
    sigma s s x = x := by
  cases x with | mk seed depth =>
  cases seed <;> cases s <;> simp [sigma]

/-- σ is symmetric in its arguments. -/
theorem sigma_comm (s t : Generator) (x : TauObj) :
    sigma s t x = sigma t s x := by
  cases x with | mk seed depth =>
  cases seed <;> cases s <;> cases t <;> simp [sigma]

end Tau.Denotation
