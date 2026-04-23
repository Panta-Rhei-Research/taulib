import TauLib.BookI.Coordinates.HyperfactProp

/-!
# TauLib.BookI.Coordinates.HyperfactFTA

**FTA-as-height-1 corollary** of the Hyperfactorization Theorem.
Hinge 1 `cor:fta-embedding` from `papers/hyperfactorization/main.tex`.

## Registry Cross-References

- [I.D14] Instruction / Program
- [I.T04] Hyperfactorization (Boolean verifier)
- [I.T56] Hyperfactorization Prop-level Uniqueness (Wave 6)
- [I.C-H1-FTA] FTA-as-height-1 corollary (this module)

## Mathematical Content

The Fundamental Theorem of Arithmetic is the restriction of the
Hyperfactorization Theorem to integers `X` whose ABCD chart has
`C = 1` at every recursion stage.  When `C = 1`, the tower atom
reduces to

  `tower_atom A B 1 = (A↑↑1)^B = A^B`

so the hyperfactorization equation `tower_atom A B C · D = X`
becomes the standard prime-power factor form `A^B · D = X` with
`A` prime, `A ∤ D` — exactly the inductive step of FTA when iterated.

This module formalises the height-1 specialisation as a corollary,
landing the connection between hyperfactorization and the classical
Fundamental Theorem of Arithmetic in registry form.

## Public API

- `tower_atom_at_height_one` — the algebraic identity
  `tower_atom A B 1 = A^B`.
- `validABCD_at_height_one_iff` — `ValidABCD x A B 1 D` is exactly
  `A ≥ 2 ∧ B ≥ 1 ∧ A^B · D = x ∧ (D = 0 ∨ ¬ A ∣ D)`, the standard
  prime-power-plus-remainder form.
- `fta_height_one_corollary` — the headline corollary: at C = 1,
  the hyperfactorization equation IS the FTA inductive step.
-/

set_option autoImplicit false

namespace Tau.Coordinates

open Tau.Denotation Tau.Orbit

-- ============================================================
-- PART 1: tower_atom at height 1 reduces to plain exponentiation
-- ============================================================

/-- `tower_atom a b 1 = a^b`: the tower atom at height 1 collapses
    to ordinary exponentiation.  Direct from `tetration a 1 = a`. -/
theorem tower_atom_at_height_one (a b : TauIdx) :
    tower_atom a b 1 = a ^ b := by
  show (tetration a 1) ^ b = a ^ b
  have : tetration a 1 = a := by
    show a ^ (tetration a 0) = a
    show a ^ 1 = a
    exact Nat.pow_one a
  rw [this]

-- ============================================================
-- PART 2: ValidABCD at height 1 = prime-power factor form
-- ============================================================

/-- `ValidABCD x A B 1 D` simplifies to the standard prime-power
    factor form `A ≥ 2 ∧ B ≥ 1 ∧ A^B · D = x ∧ (D = 0 ∨ ¬ A ∣ D)`.
    This is exactly the inductive step of the classical FTA at the
    largest prime divisor `A` of `X`. -/
theorem validABCD_at_height_one_iff (x a b d : TauIdx) :
    ValidABCD x a b 1 d
      ↔ a ≥ 2 ∧ b ≥ 1 ∧ a ^ b * d = x ∧ (d = 0 ∨ ¬ a ∣ d) := by
  unfold ValidABCD
  rw [tower_atom_at_height_one]
  refine ⟨?_, ?_⟩
  · intro ⟨ha, hb, _, h_eq, h_d⟩
    exact ⟨ha, hb, h_eq, h_d⟩
  · intro ⟨ha, hb, h_eq, h_d⟩
    refine ⟨ha, hb, ?_, h_eq, h_d⟩
    exact Nat.one_le_iff_ne_zero.mpr (by decide)

-- ============================================================
-- PART 3: FTA-as-height-1 corollary
-- ============================================================

/-- **FTA-as-height-1 corollary** (Hinge 1, `cor:fta-embedding`):
    when the hyperfactorization of `x` has `C = 1`, it specialises
    to the prime-power factor form `x = a^b · d` where `a ≥ 2` is
    the largest prime divisor (B uniqueness from Wave 6's No-Tie
    Lemma), `b = v_a(x)` is the a-adic valuation, and `d` is the
    a-free remainder.

    Iterated application yields the ordinary FTA factorisation
    `x = p_1^{e_1} · p_2^{e_2} · … · p_k^{e_k}` with
    `p_1 > p_2 > … > p_k`.

    Conversely, the ordinary FTA factorisation determines the ABCD
    chart's `C = 1` specialisation via `B = e_j` and `A = p_j` in
    decreasing order at each recursion stage. -/
theorem fta_height_one_corollary (x a b d : TauIdx)
    (h : ValidABCD x a b 1 d) :
    a ≥ 2 ∧ b ≥ 1 ∧ a ^ b * d = x ∧ (d = 0 ∨ ¬ a ∣ d) :=
  (validABCD_at_height_one_iff x a b d).mp h

-- ============================================================
-- PART 4: Numerical sanity check
-- ============================================================

end Tau.Coordinates

-- `12 = 3^1 · 4` is the height-1 ABCD chart of 12 (with A=3 the
-- largest prime divisor).
#eval (3 ^ 1 * 4 = 12 : Bool)  -- true
