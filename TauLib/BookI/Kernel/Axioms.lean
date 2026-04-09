import TauLib.BookI.Kernel.Signature

/-!
# TauLib.BookI.Kernel.Axioms

The six structural axioms K1–K6 of Category τ.

The zeroth axiom K0 (Universe Postulate) is implicit in Lean's type system:
the declarations `Generator : Type` and `TauObj : Type` postulate the
existence of the universe of discourse. See `TauLib.Kernel.Signature` for
the K0 documentation.

## Registry Cross-References

- [I.K1] Strict Order — `K1_strict_order`
- [I.K2] Omega Fixed Point — `K2_omega_fixed`
- [I.K3] Orbit-Seeded Generation — `K3_orbit_seeded`
- [I.K4] No-Jump / Cover — `K4_no_jump`
- [I.K5] Beacon Non-Successor — `K5_beacon_non_succ`
- [I.K6] Object Closure — `K6_object_closure`

## Mathematical Content

The 2nd Edition compresses the 1st Edition's 9 axioms into 6 structural axioms
(K1–K6), plus the zeroth axiom K0 (Universe Postulate).
K1–K6 are purely about generation and closure. All structural consequences
are deferred to Parts II–III.

These axioms operate on the `TauObj` type, which represents all objects of τ
(generators + orbit elements produced by ρ).
-/

namespace Tau.Kernel

open Generator

/-- Objects of Category τ: either a generator or an orbit element ρⁿ(g).
    This is the type AFTER the generative act (Part II).

    An object is represented by its seed generator and the number of ρ-applications.
    The generator ω with n=0 is the beacon; ω with n>0 collapses to ω (K2).

    **Depth convention**: depth 0 = the generator itself (no ρ applied).
    Orbit elements start at depth 1: α_1 = ⟨α, 1⟩ = ρ(α).
    The generator α = ⟨α, 0⟩ is the seed, NOT an orbit element "α_0".

    NOTE: This representation makes K6 (object closure) definitional rather than axiomatic:
    every TauObj is by construction in some orbit ray or is ω. -/
structure TauObj where
  /-- The seed generator of this object's orbit ray -/
  seed : Generator
  /-- Number of ρ-applications (0 = the generator itself, ≥1 = orbit element) -/
  depth : Nat
  deriving DecidableEq, Repr

/-- Construct a TauObj from a generator (depth 0). -/
def TauObj.ofGen (g : Generator) : TauObj := ⟨g, 0⟩

/-- [I.D02] The progression operator ρ: sole primitive iterator.
    ρ(ω) = ω (K2 omega fixed point); otherwise increments depth. -/
def rho (x : TauObj) : TauObj :=
  match x.seed with
  | omega => x  -- K2: ω is a fixed point
  | _ => ⟨x.seed, x.depth + 1⟩

-- ============================================================
-- STRUCTURAL AXIOMS K1–K6
-- (K0 Universe Postulate is implicit in the type declarations above)
-- ============================================================

/-- [I.K1] **Strict Order**: α < π < γ < η < ω is a strict total order
    on the 5 generators.

    In our representation, this holds definitionally via `Generator.toNat`. -/
theorem K1_strict_order :
    alpha.toNat < pi.toNat ∧
    pi.toNat < gamma.toNat ∧
    gamma.toNat < eta.toNat ∧
    eta.toNat < omega.toNat := by
  exact ⟨by decide, by decide, by decide, by decide⟩

/-- [I.K2] **Omega Fixed Point**: ρ(ω) = ω; ω absorbs all operations.

    This holds definitionally from our `rho` definition. -/
theorem K2_omega_fixed (n : Nat) :
    rho ⟨omega, n⟩ = ⟨omega, n⟩ := by
  simp [rho]

/-- [I.K3] **Orbit-Seeded Generation**: Each non-omega generator g seeds
    its orbit ray O_g = {ρⁿ(g) : n ≥ 0}.

    We define the orbit ray predicate. -/
def inOrbitRay (g : Generator) (x : TauObj) : Prop :=
  x.seed = g ∧ g ≠ omega

/-- [I.K3] Every non-omega generator seeds an orbit ray containing itself. -/
theorem K3_orbit_seeded (g : Generator) (h : g ≠ omega) :
    inOrbitRay g (TauObj.ofGen g) := by
  exact ⟨rfl, h⟩

/-- [I.K4] **No-Jump / Cover**: ρ acts as a successor within each orbit
    (no skipping). The cover relation is immediate: ρⁿ(g) covers ρⁿ⁻¹(g). -/
theorem K4_no_jump (g : Generator) (hg : g ≠ omega) (n : Nat) :
    rho ⟨g, n⟩ = ⟨g, n + 1⟩ := by
  cases g <;> simp [rho] <;> exact absurd rfl hg

/-- [I.K5] **Beacon Non-Successor**: ω is NOT in the image of ρ restricted
    to any orbit ray. No finite iteration of ρ on a non-omega generator reaches ω. -/
theorem K5_beacon_non_succ (g : Generator) (hg : g ≠ omega) (n : Nat) :
    (rho ⟨g, n⟩).seed = g := by
  cases g <;> simp [rho] <;> exact absurd rfl hg

/-- [I.K5 corollary] ω is unreachable: no orbit element has seed = omega
    (except ω itself with depth 0). -/
theorem K5_omega_unreachable (g : Generator) (hg : g ≠ omega) (n : Nat) :
    ⟨g, n⟩ ≠ (⟨omega, 0⟩ : TauObj) := by
  intro h
  have : g = omega := by
    cases h
    rfl
  exact hg this

/-- [I.K6] **Object Closure**: Obj(τ) = {ω} ∪ O_α ∪ O_π ∪ O_γ ∪ O_η.
    No other objects exist.

    In our representation, this is definitional: every `TauObj` is constructed
    from a `Generator` seed, and `Generator` has exactly 5 constructors. -/
theorem K6_object_closure (x : TauObj) :
    x.seed = alpha ∨ x.seed = pi ∨ x.seed = gamma ∨ x.seed = eta ∨ x.seed = omega := by
  cases x.seed with
  | alpha => exact Or.inl rfl
  | pi => exact Or.inr (Or.inl rfl)
  | gamma => exact Or.inr (Or.inr (Or.inl rfl))
  | eta => exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))
  | omega => exact Or.inr (Or.inr (Or.inr (Or.inr rfl)))

-- ============================================================
-- BASIC DERIVED FACTS
-- ============================================================

/-- [I.P01] Generator distinctness: all five generators are pairwise distinct. -/
theorem gen_distinct : ∀ (a b : Generator), a ≠ b → a.toNat ≠ b.toNat := by
  intro a b hab
  intro heq
  apply hab
  cases a <;> cases b <;> simp [Generator.toNat] at heq <;> try rfl

/-- [I.P02] ρ is injective on each orbit ray. -/
theorem rho_injective (g : Generator) (hg : g ≠ omega) (n m : Nat) :
    rho ⟨g, n⟩ = rho ⟨g, m⟩ → n = m := by
  intro h
  have h1 := K4_no_jump g hg n
  have h2 := K4_no_jump g hg m
  rw [h1, h2] at h
  cases h
  rfl

end Tau.Kernel
