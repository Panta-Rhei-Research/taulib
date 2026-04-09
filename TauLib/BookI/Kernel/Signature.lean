/-!
# TauLib.BookI.Kernel.Signature

The foundational signature of Category τ: five generators in strict total order,
and the sole primitive iterator ρ.

## Registry Cross-References

- [I.K0] Universe Postulate — implicit in Lean's type system (see below)
- [I.D01] Five Generators — `Generator` inductive type
- [I.D02] Progression Operator ρ — `rho` function
- [I.D04] Static Kernel τ₀ — `TauZero` structure

## Axiom K0: Universe Postulate

The zeroth axiom K0 postulates the existence of τ as a universe of discourse —
the ambient totality that contains all five generators and all orbit elements.
In Lean 4, K0 is realized by the type system itself:

  `inductive Generator : Type`  — declares the generator type exists
  `structure TauObj : Type`     — declares the object universe exists

K0 distinguishes τ (the ambient type/universe) from ω (the fixed-point element
*within* τ). τ is not an element of itself; ω is. τ is the Type; ω is a term.
This distinction is foundational: ω lives inside the system as an algebraic
citizen (the unique ρ-fixed point, K2), while τ is the ground that makes the
system possible.

## Mathematical Content

τ begins with exactly five generators in strict total order:
  α < π < γ < η < ω

Each generator has a canonical role:
- α: radial seed (its orbit O_α becomes τ-Idx, the internal natural numbers)
- π: prime base / multiplicative spine
- γ: exponent / outer-power channel
- η: tetration / inner-power channel
- ω: fixed-point absorber / closure beacon

## Notation (2nd Edition)

The 1st Edition used π, π', π'' for the three solenoidal generators.
The 2nd Edition replaces π' → γ, π'' → η for cleaner typesetting and
robust Lean identifiers. The solenoidal triple is {π, γ, η}.
-/

namespace Tau.Kernel

-- ============================================================
-- AXIOM K0: UNIVERSE POSTULATE
-- ============================================================
-- [I.K0] The zeroth axiom postulates the existence of the totality τ
-- as a universe of discourse. In Lean 4, this is implicit:
-- the `inductive Generator : Type` declaration below asserts that
-- Generator exists as a type, and `structure TauObj : Type` (in
-- Axioms.lean) asserts the object universe exists.
--
-- K0 distinguishes τ (the ambient type/universe) from ω (the
-- fixed-point element *within* τ). τ is not an element of itself;
-- ω is. This distinction is foundational: τ is the Type, ω is a term.
-- ============================================================

/-- [I.D01] The five generators of Category τ.
    These are the ONLY primitive objects. All other objects are orbit elements
    produced by applying ρ to these generators. -/
inductive Generator : Type where
  | alpha : Generator  -- α: radial seed
  | pi    : Generator  -- π: prime base
  | gamma : Generator  -- γ: exponent channel (1st Ed: π')
  | eta   : Generator  -- η: tetration channel (1st Ed: π'')
  | omega : Generator  -- ω: fixed-point absorber
  deriving DecidableEq, Repr

open Generator

/-- Canonical ordering index for generators: α=0, π=1, γ=2, η=3, ω=4. -/
def Generator.toNat : Generator → Nat
  | alpha => 0
  | pi    => 1
  | gamma => 2
  | eta   => 3
  | omega => 4

/-- [I.K1 prerequisite] Strict ordering on generators derived from their indices. -/
instance : LT Generator where
  lt a b := a.toNat < b.toNat

/-- The ordering on generators is decidable. -/
instance (a b : Generator) : Decidable (a < b) :=
  inferInstanceAs (Decidable (a.toNat < b.toNat))

/-- [I.D01] The four non-omega generators that seed orbit rays. -/
def nonOmegaGenerators : List Generator := [alpha, pi, gamma, eta]

/-- [I.D04] The static kernel τ₀: the 5 generators before the generative act.
    This is the complete specification — ρ has not yet been applied. -/
structure TauZero where
  /-- The five generators are present -/
  generators : Fin 5 → Generator
  /-- They are listed in canonical order -/
  canonical_order : ∀ i j : Fin 5, i < j → (generators i).toNat < (generators j).toNat

end Tau.Kernel
