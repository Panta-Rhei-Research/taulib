import TauLib.BookI.Sets.Operations

/-!
# TauLib.BookI.Sets.Powerset

Well-foundedness of strict τ-membership and the powerset hierarchy.

## Registry Cross-References

- [I.D33] Strict Membership — `tau_strict_mem`
- [I.P12] Well-Foundedness — `tau_strict_mem_wf`

## Ground Truth Sources
- chunk_0360_M003055: Well-foundedness of the divisibility order on Nat

## Mathematical Content

In the τ-arithmetic encoding, strict membership a ∈^strict_τ b means
a | b with a ≠ b. For b ≠ 0, this implies a < b, so strict membership
is well-founded (no infinite descending chains).

This well-foundedness is the arithmetic analogue of the Foundation Axiom
(Regularity) in ZF set theory: there is no infinite chain
... ∈_τ x₂ ∈_τ x₁ ∈_τ x₀ (unless 0 is involved).

The restriction to nonzero sets is essential: 0 is the universal set
(everything divides 0), so chains through 0 are degenerate.
-/

namespace Tau.Sets

open Tau.Denotation Tau.Coordinates

-- ============================================================
-- STRICT MEMBERSHIP [I.D33]
-- ============================================================

/-- [I.D33] Strict τ-membership: a properly divides b (a | b and a ≠ b). -/
def tau_strict_mem (a b : TauIdx) : Prop := tau_mem a b ∧ a ≠ b

/-- Strict membership is irreflexive. -/
theorem tau_strict_mem_irrefl (a : TauIdx) : ¬ tau_strict_mem a a :=
  fun ⟨_, h⟩ => h rfl

/-- Strict membership is transitive. -/
theorem tau_strict_mem_trans {a b c : TauIdx}
    (h1 : tau_strict_mem a b) (h2 : tau_strict_mem b c) :
    tau_strict_mem a c :=
  ⟨tau_mem_trans h1.1 h2.1, fun h => by
    subst h; exact h1.2 (tau_mem_antisymm h1.1 h2.1)⟩

-- ============================================================
-- STRICT MEMBERSHIP AND ORDERING
-- ============================================================

/-- Strict membership with nonzero target implies strict inequality.
    If a | b, a ≠ b, and b ≠ 0, then a < b. -/
theorem tau_strict_mem_lt {a b : TauIdx} (h : tau_strict_mem a b) (hb : b ≠ 0) :
    a < b := by
  have hle : a ≤ b := tau_mem_le h.1 hb
  exact Nat.lt_of_le_of_ne hle h.2

/-- 1 is a strict member of any n ≥ 2. -/
theorem tau_strict_mem_one {n : TauIdx} (hn : n ≥ 2) : tau_strict_mem 1 n :=
  ⟨tau_mem_one n, Nat.ne_of_lt (Nat.lt_of_lt_of_le (by decide : (1 : Nat) < 2) hn)⟩

/-- If a is a strict member of b, and b > 0, then a is strictly smaller. -/
theorem tau_strict_mem_bound {a b : TauIdx} (h : tau_strict_mem a b) (hb : b > 0) :
    a < b :=
  tau_strict_mem_lt h (fun heq => by subst heq; exact Nat.lt_irrefl 0 hb)

-- ============================================================
-- WELL-FOUNDEDNESS [I.P12]
-- ============================================================

/-- Strict membership restricted to nonzero targets is a subrelation of Nat.lt.
    This is the key step for well-foundedness. -/
private theorem strict_mem_sub_lt {a b : TauIdx} (hb : b ≠ 0) (h : tau_strict_mem a b) :
    a < b :=
  tau_strict_mem_lt h hb

/-- The "nonzero strict membership" relation: a strictly divides b and b ≠ 0. -/
def tau_strict_mem_nz (a b : TauIdx) : Prop := tau_strict_mem a b ∧ b ≠ 0

/-- Nonzero strict membership is a subrelation of Nat.lt via the identity map. -/
private theorem strict_mem_nz_sub_lt {a b : TauIdx} (h : tau_strict_mem_nz a b) :
    a < b :=
  tau_strict_mem_lt h.1 h.2

/-- [I.P12] Well-foundedness of nonzero strict τ-membership:
    there is no infinite descending chain
    ... ∈^strict_τ x₂ ∈^strict_τ x₁ ∈^strict_τ x₀
    when all elements are nonzero.

    Proof: tau_strict_mem_nz is a subrelation of Nat.lt (via identity),
    and Nat.lt is well-founded. -/
theorem tau_strict_mem_wf : WellFounded tau_strict_mem_nz :=
  Subrelation.wf
    (fun h => strict_mem_nz_sub_lt h)
    (InvImage.wf id Nat.lt_wfRel.wf)

/-- From well-foundedness: strong induction on τ-membership.
    For nonzero indices, if P holds for all strict τ-members of n,
    then P holds for n. -/
theorem tau_strict_mem_induction {P : TauIdx → Prop}
    (h : ∀ n : TauIdx, (∀ m : TauIdx, tau_strict_mem_nz m n → P m) → P n)
    (n : TauIdx) : P n :=
  tau_strict_mem_wf.induction n h

-- ============================================================
-- FINITENESS OF DIVISOR SETS
-- ============================================================

/-- For nonzero b, the set of τ-members is bounded: every member is ≤ b. -/
theorem tau_mem_bounded {b : TauIdx} (hb : b ≠ 0) (a : TauIdx) (h : tau_mem a b) :
    a ≤ b :=
  tau_mem_le h hb

/-- For nonzero b, strict membership decreases: if a ∈^strict_τ b then a < b.
    Combined with a ≥ 1 (since 0 divides nothing nonzero), this bounds
    the length of any descending chain to at most b steps. -/
theorem strict_mem_chain_bound {a b : TauIdx} (hb : b > 0)
    (h : tau_strict_mem a b) : a < b :=
  tau_strict_mem_bound h hb

-- ============================================================
-- SMOKE TESTS
-- ============================================================

-- 3 is a strict member of 12 (3 | 12, 3 ≠ 12)
example : tau_strict_mem 3 12 :=
  ⟨(tau_mem_iff_dvd 3 12).mpr ⟨4, rfl⟩, by decide⟩

-- 12 is NOT a strict member of 12 (irreflexive)
example : ¬ tau_strict_mem 12 12 := tau_strict_mem_irrefl 12

-- 1 is a strict member of 7
example : tau_strict_mem 1 7 :=
  tau_strict_mem_one (by decide : (7 : Nat) ≥ 2)

end Tau.Sets
