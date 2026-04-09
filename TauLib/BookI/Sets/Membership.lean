import TauLib.BookI.Coordinates.Primes

/-!
# TauLib.BookI.Sets.Membership

τ-Membership: divisibility as the internal membership relation on τ-Idx.

## Registry Cross-References

- [I.D31] τ-Membership — `tau_mem`, `tau_mem_iff_dvd`
- [I.P10] Membership Decidability — `instDecidableTauMem`

## Ground Truth Sources
- chunk_0350_M003012: Membership = divisibility in τ-Idx arithmetic

## Mathematical Content

In Category τ, the membership relation a ∈_τ b is identified with
index divisibility: a ∈_τ b iff a | b. This encodes set-membership
arithmetically, where each natural number IS a set (its divisor set).

**Convention**: τ-Idx semantically represents ℕ⁺ = {1, 2, 3, ...},
the positive natural numbers discovered as the α-orbit O_α.
Zero is NOT a valid orbit index — it first appears in ring
structures (Part VIII, boundary ring). Lean uses `TauIdx = Nat`
for convenience; all orbit-meaningful results carry nonzero guards.

**τ as class**: τ is a proper class (a category), not a set.
"x belongs to τ" means x is an object of the category — class
membership, not set membership. The internal set theory developed
here lives INSIDE τ, encoded arithmetically on the α-orbit.

Under this encoding:
- 1 is the unit (α_1 represents {α_1}, the minimal singleton)
- Primes are atoms (only 1 and themselves as members)
- The orbit-set of ω gives the universal collection O_α ∪ {ω}
-/

namespace Tau.Sets

open Tau.Denotation Tau.Coordinates

-- ============================================================
-- τ-MEMBERSHIP [I.D31]
-- ============================================================

/-- [I.D31] τ-membership: a ∈_τ b iff a divides b.
    Every natural number IS its divisor set. -/
def tau_mem (a b : TauIdx) : Prop := idx_divides a b

/-- Bridge: τ-membership is Nat divisibility. -/
theorem tau_mem_iff_dvd (a b : TauIdx) : tau_mem a b ↔ a ∣ b :=
  idx_divides_iff_nat_dvd a b

/-- [I.P10] τ-membership is decidable. -/
instance instDecidableTauMem (a b : TauIdx) : Decidable (tau_mem a b) :=
  instDecidableIdxDivides a b

-- ============================================================
-- MEMBERSHIP PROPERTIES
-- ============================================================

/-- Reflexivity: every τ-set is a member of itself. -/
theorem tau_mem_refl (a : TauIdx) : tau_mem a a :=
  idx_divides_refl a

/-- Antisymmetry: mutual membership implies equality. -/
theorem tau_mem_antisymm {a b : TauIdx} (h1 : tau_mem a b) (h2 : tau_mem b a) : a = b :=
  idx_divides_antisymm h1 h2

/-- Transitivity: membership is transitive. -/
theorem tau_mem_trans {a b c : TauIdx} (h1 : tau_mem a b) (h2 : tau_mem b c) : tau_mem a c :=
  idx_divides_trans h1 h2

/-- 1 (the empty set) is a member of every τ-set. -/
theorem tau_mem_one (b : TauIdx) : tau_mem 1 b :=
  idx_one_divides b

/-- Membership is bounded: a ∈_τ b with b ≠ 0 implies a ≤ b. -/
theorem tau_mem_le {a b : TauIdx} (h : tau_mem a b) (hb : b ≠ 0) : a ≤ b :=
  idx_divides_le h hb

-- ============================================================
-- EMPTY SET AND SINGLETONS
-- ============================================================

/-- The unit element in τ-arithmetic is 1 (α_1): its only τ-member is 1 itself.
    (The only divisor of 1 is 1.) This is the minimal τ-set — not truly
    "empty" since α_1 ∈_τ α_1 by reflexivity of divisibility. -/
def tau_unit : TauIdx := 1

/-- The unit has no members other than itself: if a ∈_τ 1, then a = 1. -/
theorem tau_unit_char (a : TauIdx) (h : tau_mem a tau_unit) : a = 1 := by
  unfold tau_unit at h
  unfold tau_mem at h
  rw [idx_divides_iff_nat_dvd] at h
  exact Nat.eq_one_of_dvd_one h

/-- A nonzero τ-set p is a singleton (only 1 and p are τ-members) iff p = 1 or p is prime. -/
theorem singleton_char (p : TauIdx) (hp0 : p ≠ 0) :
    (∀ d : TauIdx, tau_mem d p → d = 1 ∨ d = p) ↔ (p = 1 ∨ idx_prime p) := by
  constructor
  · intro h
    by_cases hp1 : p = 1
    · exact Or.inl hp1
    · right
      constructor
      · rcases p with _ | _ | n
        · exact absurd rfl hp0
        · exact absurd rfl hp1
        · exact Nat.le_add_left 2 n
      · intro d hd
        exact h d ((idx_divides_iff_nat_dvd d p).mpr hd)
  · intro h d hd
    rcases h with rfl | hp
    · -- p = 1
      exact Or.inl (Nat.eq_one_of_dvd_one ((idx_divides_iff_nat_dvd d 1).mp hd))
    · -- p is prime
      exact hp.2 d ((idx_divides_iff_nat_dvd d p).mp hd)

-- ============================================================
-- MEMBERSHIP INTERACTIONS
-- ============================================================

/-- Product membership: if a ∈_τ b, then a ∈_τ b*c. -/
theorem tau_mem_mul_right {a b : TauIdx} (h : tau_mem a b) (c : TauIdx) :
    tau_mem a (idx_mul b c) := by
  rw [tau_mem_iff_dvd] at h ⊢
  rw [idx_mul_eq_nat_mul]
  exact Nat.dvd_trans h (Nat.dvd_mul_right b c)

/-- Product membership (left): if a ∈_τ c, then a ∈_τ b*c. -/
theorem tau_mem_mul_left {a c : TauIdx} (h : tau_mem a c) (b : TauIdx) :
    tau_mem a (idx_mul b c) := by
  rw [tau_mem_iff_dvd] at h ⊢
  rw [idx_mul_eq_nat_mul]
  exact Nat.dvd_trans h (Nat.dvd_mul_left c b)

-- ============================================================
-- SMOKE TESTS
-- ============================================================

-- 3 ∈_τ 12 (3 | 12)
#eval (instDecidableTauMem 3 12 : Decidable _)
-- 5 ∉_τ 12 (5 ∤ 12)
#eval (instDecidableTauMem 5 12 : Decidable _)
-- 1 ∈_τ 7 (1 | 7)
#eval (instDecidableTauMem 1 7 : Decidable _)
-- 1 ∈_τ 1 (unit is self-member)
#eval (instDecidableTauMem 1 1 : Decidable _)

end Tau.Sets
