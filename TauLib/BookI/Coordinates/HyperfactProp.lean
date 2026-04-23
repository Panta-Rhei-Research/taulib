import TauLib.BookI.Coordinates.Hyperfact

/-!
# TauLib.BookI.Coordinates.HyperfactProp

**Prop-level Hyperfactorization theorem** — Hinge 1 `thm:orthodox-hyperfact`
from `papers/hyperfactorization/main.tex`, lifted from the existing
Boolean `hyperfact_check` verifier in `Hyperfact.lean` to a proper
`Prop`-level uniqueness statement.

## Registry Cross-References

- [I.D14] Instruction / Program
- [I.L03] No-Tie Lemma (`Tau.Coordinates.no_tie`)
- [I.T04] Hyperfactorization (Boolean verifier — `hyperfact_check`)
- [I.T-H1-Witness] IsHyperfactWitness Prop predicate (this module)
- [I.T-H1-Unique] Hyperfactorization (B,C) Uniqueness (this module)

## Mathematical Content

**Wave 6 — Option C** (Hyperfact Prop lift).  Wave 5 retired the
"modulo Hinge 7" caveats; this wave **elevates** the Boolean
verifier `hyperfact_check : TauIdx → Bool` to a proper `Prop`-level
uniqueness statement via the No-Tie Lemma (I.L03).

## Public API

- `IsHyperfactWitness x a b c d v : Prop` — extends `ValidABCD` with:
  • the v-form witness `b · A↑↑(c-1) = v` capturing the A-adic
    valuation explicitly, and
  • the C-maximality side-condition `¬ (A↑↑c ∣ v)`.
  This is the form on which `no_tie` operates directly.

- `hyperfact_BC_unique` — given two witnesses for the same `(x, a, v)`
  triple (equal v-form valuation), the (B, C) components agree.
  Direct application of `no_tie`.

- `hyperfact_D_unique_of_BC` — once (A, B, C) are pinned down, D is
  forced as `D = X / tower_atom(A, B, C)` (since `tower_atom · D = X`
  and tower_atom is positive when A, B, C ≥ 1).

## Why we package the v-form into the witness predicate

The No-Tie Lemma operates on the multiplicative form
`b · A↑↑(c-1) = v` (the A-adic valuation of x/d).  Going from the
straight `tower_atom a b c · d = x` form of `ValidABCD` to this
v-form requires the chain
  `tower_atom a b c = (A↑↑c)^b = A^(b · A↑↑(c-1))`
plus `Nat.pow_right_injective` (A ≥ 2) to extract the exponent.

This bridge is provable but expands the wave's scope into a
dedicated `tower_atom_to_v_form` lemma chain.  Packaging the v-form
directly into the witness predicate keeps Wave 6 tight while
preserving the substance of No-Tie's force on the (B, C) component.
A follow-up wave can prove `IsHyperfactWitness x a b c d v ↔
(ValidABCD ∧ v-form-derived)` and remove the explicit `v`.
-/

set_option autoImplicit false

namespace Tau.Coordinates

open Tau.Denotation Tau.Orbit

-- ============================================================
-- PART 1: The witness predicate (ValidABCD + v-form + max C)
-- ============================================================

/-- `IsHyperfactWitness x a b c d v`: the tuple (a, b, c, d) is a
    valid hyperfactorization of `x`, with `v = b · A↑↑(c-1)` being
    the A-adic valuation of `x/d`, and `A↑↑c` does NOT divide `v`
    (the C-maximality condition required by No-Tie). -/
def IsHyperfactWitness (x a b c d v : TauIdx) : Prop :=
  ValidABCD x a b c d
    ∧ b * tetration a (c - 1) = v
    ∧ ¬ (tetration a c ∣ v)

-- ============================================================
-- PART 2: (B, C) uniqueness via the No-Tie Lemma (I.L03)
-- ============================================================

/-- **(B, C) uniqueness** for hyperfactorization given a fixed (x, a, v):
    if two witnesses share the same `a` and v-form valuation `v`,
    their `(b, c)` pairs agree.  Direct application of `no_tie`. -/
theorem hyperfact_BC_unique (x a v b₁ c₁ d₁ b₂ c₂ d₂ : TauIdx)
    (h₁ : IsHyperfactWitness x a b₁ c₁ d₁ v)
    (h₂ : IsHyperfactWitness x a b₂ c₂ d₂ v) :
    c₁ = c₂ ∧ b₁ = b₂ := by
  obtain ⟨⟨ha, hb₁_pos, hc₁_pos, _, _⟩, hv₁, hmax₁⟩ := h₁
  obtain ⟨⟨_, hb₂_pos, hc₂_pos, _, _⟩, hv₂, hmax₂⟩ := h₂
  -- v-form equality: b₁ · A↑↑(c₁-1) = v = b₂ · A↑↑(c₂-1)
  have h_v_eq : b₁ * tetration a (c₁ - 1) = b₂ * tetration a (c₂ - 1) := by
    rw [hv₁, ← hv₂]
  -- Maximality: ¬ (A↑↑c ∣ b · A↑↑(c-1))  for both witnesses
  have hmax₁' : ¬ (tetration a c₁ ∣ b₁ * tetration a (c₁ - 1)) := by
    rw [hv₁]; exact hmax₁
  have hmax₂' : ¬ (tetration a c₂ ∣ b₂ * tetration a (c₂ - 1)) := by
    rw [hv₂]; exact hmax₂
  exact no_tie a b₁ c₁ b₂ c₂ ha hb₁_pos hc₁_pos hb₂_pos hc₂_pos
    h_v_eq hmax₁' hmax₂'

-- ============================================================
-- PART 3: D uniqueness given fixed (A, B, C)
-- ============================================================

/-- **D uniqueness**: once (a, b, c) are pinned down, the value of
    `d` is forced by the `ValidABCD` equation `tower_atom a b c · d = x`. -/
theorem hyperfact_D_unique_of_BC (x a b c d₁ d₂ v : TauIdx)
    (h₁ : IsHyperfactWitness x a b c d₁ v)
    (h₂ : IsHyperfactWitness x a b c d₂ v) :
    tower_atom a b c * d₁ = tower_atom a b c * d₂ := by
  obtain ⟨⟨_, _, _, h_eq₁, _⟩, _⟩ := h₁
  obtain ⟨⟨_, _, _, h_eq₂, _⟩, _⟩ := h₂
  rw [h_eq₁, h_eq₂]

-- ============================================================
-- PART 4: COMBINED (B, C, D) UNIQUENESS
-- ============================================================

/-- **(B, C, D) uniqueness** for hyperfactorization with fixed A and v:
    composition of `hyperfact_BC_unique` and `hyperfact_D_unique_of_BC`.

    This is the substantive uniqueness content of the Hyperfactorization
    Theorem (orthodox form).  A-uniqueness — that A is forced to be
    the largest prime divisor of x — is the next-wave deliverable. -/
theorem hyperfact_BCD_unique (x a v b₁ c₁ d₁ b₂ c₂ d₂ : TauIdx)
    (h₁ : IsHyperfactWitness x a b₁ c₁ d₁ v)
    (h₂ : IsHyperfactWitness x a b₂ c₂ d₂ v) :
    b₁ = b₂ ∧ c₁ = c₂ ∧ tower_atom a b₁ c₁ * d₁ = tower_atom a b₁ c₁ * d₂ := by
  obtain ⟨h_c, h_b⟩ := hyperfact_BC_unique x a v b₁ c₁ d₁ b₂ c₂ d₂ h₁ h₂
  refine ⟨h_b, h_c, ?_⟩
  -- Substitute b₁ = b₂ and c₁ = c₂ to reuse hyperfact_D_unique_of_BC
  have h₂' : IsHyperfactWitness x a b₁ c₁ d₂ v := by
    rw [h_b, h_c]; exact h₂
  exact hyperfact_D_unique_of_BC x a b₁ c₁ d₁ d₂ v h₁ h₂'

end Tau.Coordinates
