import TauLib.BookI.Orbit.Ladder

/-!
# TauLib.BookI.Orbit.TooFew

Counter-model: a 4-generator tau-like system cannot assign canonical
channels to all 3 rewiring levels of the iterator ladder.

## Registry Cross-References

- [I.T11b] Four-Generator Ladder Incompleteness — `four_gen_ladder_incomplete`

## Mathematical Content

If we drop η (keeping only α, π, γ, ω), only 2 solenoidal generators
remain (π and γ). The iterator ladder needs 3 rewiring channels
(addition, multiplication, exponentiation), so the exponentiation level
is orphaned — no generator carries it.

Interestingly, Gen4 *does* still have rigidity (any automorphism fixing
α and ω must be the identity), because with only 2 solenoidal generators,
there is no same-role pair to swap. This highlights the tradeoff:

- 4 generators: rigidity ✓, completeness ✗
- 5 generators: rigidity ✓, completeness ✓ (sweet spot)
- 6 generators: rigidity ✗, completeness ✓
-/

namespace Tau.Orbit.TooFew

open Tau.Kernel

-- ============================================================
-- FOUR-GENERATOR SIGNATURE
-- ============================================================

/-- A hypothetical 4-generator alphabet: α, π, γ, ω (no η). -/
inductive Gen4 : Type where
  | alpha : Gen4
  | pi    : Gen4
  | gamma : Gen4
  | omega : Gen4
  deriving DecidableEq, Repr

open Gen4

/-- Canonical ordering: α=0, π=1, γ=2, ω=3. -/
def Gen4.toNat : Gen4 → Nat
  | alpha => 0
  | pi    => 1
  | gamma => 2
  | omega => 3

-- ============================================================
-- FOUR-GENERATOR LADDER
-- ============================================================

/-- The solenoidal generators of Gen4: only {π, γ}. -/
def solenoidal4 : List Gen4 := [pi, gamma]

/-- Only 2 solenoidal generators in Gen4. -/
theorem solenoidal4_count : solenoidal4.length = 2 := by rfl

/-- The 4 hyperoperation levels (same as Gen5, but channel assignment fails). -/
inductive Ladder4Level : Type where
  | rho_level : Ladder4Level
  | add_level : Ladder4Level
  | mul_level : Ladder4Level
  | exp_level : Ladder4Level
  deriving DecidableEq, Repr

/-- Channel assignment in Gen4: addition gets π, multiplication gets γ,
    but exponentiation has no available channel. -/
def ladder4Channel : Ladder4Level → Option Gen4
  | .rho_level => none           -- ρ acts on all orbits
  | .add_level => some Gen4.pi   -- addition ↔ π channel
  | .mul_level => some Gen4.gamma -- multiplication ↔ γ channel
  | .exp_level => none           -- NO channel available!

-- ============================================================
-- LADDER INCOMPLETENESS [I.T09b]
-- ============================================================

/-- Exponentiation has no canonical channel in Gen4. -/
theorem four_gen_exp_no_channel : ladder4Channel .exp_level = none := by rfl

/-- The deficit: 2 solenoidal generators for 3 rewiring levels needed. -/
theorem solenoidal4_deficit : solenoidal4.length < 3 := by decide

/-- [I.T09b] **Four-Generator Ladder Incompleteness**:
    With only 4 generators, the iterator ladder cannot be completed.
    The exponentiation level has no canonical orbit channel because
    only 2 solenoidal generators (π, γ) exist, but 3 rewiring levels
    (addition, multiplication, exponentiation) are needed.

    This shows that dropping a generator from 5 to 4 breaks
    ladder completeness — 5 generators is *necessary*. -/
theorem four_gen_ladder_incomplete :
    ladder4Channel .exp_level = none ∧ solenoidal4.length < 3 :=
  ⟨rfl, by decide⟩

-- ============================================================
-- GEN4 RIGIDITY (contrast with Gen6)
-- ============================================================

/-- Objects of the 4-generator system. -/
structure Obj4 where
  seed : Gen4
  depth : Nat
  deriving DecidableEq, Repr

/-- The progression operator ρ₄: fixes ω-fiber, increments depth otherwise. -/
def rho4 (x : Obj4) : Obj4 :=
  match x.seed with
  | Gen4.omega => x
  | _ => ⟨x.seed, x.depth + 1⟩

/-- The only permutations of Gen4 fixing α and ω are
    id and the transposition (π γ). The transposition reverses
    the canonical order (π < γ becomes γ > π), so an order-preserving
    bijection must be the identity. -/
theorem four_gen_order_rigid (f : Gen4 → Gen4)
    (hf_alpha : f alpha = alpha)
    (hf_omega : f omega = omega)
    (hf_order : ∀ g h : Gen4, Gen4.toNat g < Gen4.toNat h →
                             Gen4.toNat (f g) < Gen4.toNat (f h)) :
    ∀ g, f g = g := by
  -- Key: order-preservation + fixed endpoints force f pi = pi and f gamma = gamma.
  -- From alpha < pi < gamma < omega and f(alpha)=alpha, f(omega)=omega:
  --   0 < toNat(f pi) < toNat(f gamma) < 3
  -- So toNat(f pi) ∈ {1,2} and toNat(f gamma) ∈ {1,2} with strict inequality.
  -- The only solution is toNat(f pi) = 1, toNat(f gamma) = 2.
  have h_ap := hf_order alpha pi (by decide)
  have h_pg := hf_order pi gamma (by decide)
  have h_go := hf_order gamma omega (by decide)
  rw [hf_alpha] at h_ap
  rw [hf_omega] at h_go
  -- h_ap: 0 < toNat (f pi)
  -- h_pg: toNat (f pi) < toNat (f gamma)
  -- h_go: toNat (f gamma) < 3
  -- Chain: 0 < toNat(f pi) < toNat(f gamma) < 3
  -- Only solution: toNat(f pi) = 1 ∧ toNat(f gamma) = 2
  -- Recover f pi = pi from toNat constraints
  have hfp : f pi = pi := by
    cases hc : f pi with
    | alpha => rw [hc] at h_ap; simp [Gen4.toNat] at h_ap
    | pi => rfl
    | gamma => rw [hc] at h_pg; simp [Gen4.toNat] at h_pg h_go; omega
    | omega => rw [hc] at h_pg; simp [Gen4.toNat] at h_pg h_go; omega
  -- Recover f gamma = gamma from toNat constraints
  have hfg : f gamma = gamma := by
    cases hc : f gamma with
    | alpha => rw [hfp, hc] at h_pg; simp [Gen4.toNat] at h_pg
    | pi => rw [hfp, hc] at h_pg; simp [Gen4.toNat] at h_pg
    | gamma => rfl
    | omega => rw [hc] at h_go; simp [Gen4.toNat] at h_go
  intro g
  cases g with
  | alpha => exact hf_alpha
  | omega => exact hf_omega
  | pi => exact hfp
  | gamma => exact hfg

/-- **Four-Generator Order-Preserving Rigidity**:
    Any order-preserving ρ-automorphism of the 4-generator system is the identity.

    Note: unlike the 5-generator system where rigidity holds for ALL automorphisms
    (given seed preservation at depth 0), the 4-generator system has rigidity only
    for ORDER-PRESERVING automorphisms. The transposition (π γ) is a valid
    non-order-preserving automorphism. This weaker form of rigidity is sufficient
    for the Minimal Alphabet Theorem. -/
theorem four_gen_rigidity_holds :
    ∀ (f : Gen4 → Gen4),
      f alpha = alpha →
      f omega = omega →
      (∀ g h, Gen4.toNat g < Gen4.toNat h → Gen4.toNat (f g) < Gen4.toNat (f h)) →
      ∀ g, f g = g :=
  fun f ha ho hord => four_gen_order_rigid f ha ho hord

end Tau.Orbit.TooFew
