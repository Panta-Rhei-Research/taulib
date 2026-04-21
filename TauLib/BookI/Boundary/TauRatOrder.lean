import TauLib.BookI.Boundary.TauRatField
import Mathlib.Tactic.Ring
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum

/-!
# TauLib.BookI.Boundary.TauRatOrder

Ordering on TauRat: strict less-than, less-than-or-equal, and their
properties (transitivity, trichotomy, equiv-preservation).

## Registry Cross-References

- [I.D35] Number Tower — TauRat is the field-of-fractions layer defined in
  `TauLib.Boundary.NumberTower`
- [I.D84] Constructive Reals — Wave 2 will lift this ordering to `TauReal`

New declarations in this module are not yet registered (pending the
medium-PR registry-bookkeeping pass): `TauRat.lt`, `TauRat.le`, and the
ordering / trichotomy / equiv-preservation lemmas built on them.

## Mathematical Content

This module is **Wave 1b** of the four-wave TauReal infrastructure build
(see `ROADMAP-3-HINGES.md`).  It adds the ordering layer:

1. **`TauRat.lt`** and **`TauRat.le`** via the `toRat` semantic bridge
   (Wave 1a) routed through Lean core's `Rat.lt`/`Rat.le`.
2. **Properties**: irreflexivity, transitivity, trichotomy, antisymmetry.
3. **Equiv preservation**: lt and le are well-defined modulo TauRat.equiv.

All proofs route through `equiv_iff_toRat_eq` (Wave 1a) and Lean core's
`Rat` ordering.  No mathlib content imports needed — only the available
tactic budget (`ring`, `linear_combination`, `norm_num`, `push_cast`,
`omega`, `decide`, `native_decide`).

Naming convention: namespace lemmas explicitly use `_root_.lt_irrefl`,
`_root_.le_refl`, etc. to avoid recursive name resolution against
`TauRat.lt_irrefl` and friends being defined here.
-/

set_option autoImplicit false

namespace Tau.Boundary

open Tau.Denotation

-- ============================================================
-- PART 1: STRICT LESS-THAN
-- ============================================================

/-- TauRat strict less-than via toRat comparison. -/
def TauRat.lt (a b : TauRat) : Prop := a.toRat < b.toRat

/-- lt is irreflexive. -/
theorem TauRat.lt_irrefl (a : TauRat) : ¬ TauRat.lt a a :=
  _root_.lt_irrefl a.toRat

/-- lt is transitive. -/
theorem TauRat.lt_trans {a b c : TauRat}
    (hab : TauRat.lt a b) (hbc : TauRat.lt b c) : TauRat.lt a c :=
  _root_.lt_trans hab hbc

/-- lt is asymmetric (if a < b then ¬b < a). -/
theorem TauRat.lt_asymm {a b : TauRat}
    (hab : TauRat.lt a b) : ¬ TauRat.lt b a :=
  fun hba => TauRat.lt_irrefl a (TauRat.lt_trans hab hba)

-- ============================================================
-- PART 2: LESS-THAN-OR-EQUAL
-- ============================================================

/-- TauRat less-than-or-equal via toRat comparison. -/
def TauRat.le (a b : TauRat) : Prop := a.toRat ≤ b.toRat

/-- le is reflexive. -/
theorem TauRat.le_refl (a : TauRat) : TauRat.le a a := _root_.le_refl a.toRat

/-- le is transitive. -/
theorem TauRat.le_trans {a b c : TauRat}
    (hab : TauRat.le a b) (hbc : TauRat.le b c) : TauRat.le a c :=
  _root_.le_trans hab hbc

/-- le is antisymmetric up to TauRat.equiv:
    if a ≤ b and b ≤ a then a is equiv to b. -/
theorem TauRat.le_antisymm {a b : TauRat}
    (hab : TauRat.le a b) (hba : TauRat.le b a) : TauRat.equiv a b := by
  rw [equiv_iff_toRat_eq]
  exact _root_.le_antisymm hab hba

-- ============================================================
-- PART 3: lt-le BRIDGE LEMMAS
-- ============================================================

/-- lt implies le. -/
theorem TauRat.le_of_lt {a b : TauRat} (h : TauRat.lt a b) : TauRat.le a b :=
  _root_.le_of_lt h

/-- lt iff le and not equiv. -/
theorem TauRat.lt_iff_le_and_not_equiv (a b : TauRat) :
    TauRat.lt a b ↔ TauRat.le a b ∧ ¬ TauRat.equiv a b := by
  constructor
  · intro h
    refine ⟨_root_.le_of_lt h, ?_⟩
    intro h_eq
    rw [equiv_iff_toRat_eq] at h_eq
    -- Now h_eq : a.toRat = b.toRat; h : TauRat.lt a b ↔ a.toRat < b.toRat
    unfold TauRat.lt at h
    exact _root_.lt_irrefl _ (h_eq ▸ h)
  · intro ⟨hle, hne⟩
    rw [equiv_iff_toRat_eq] at hne
    exact lt_of_le_of_ne hle hne

-- ============================================================
-- PART 4: TRICHOTOMY
-- ============================================================

/-- Trichotomy: for any two TauRats, exactly one of lt, equiv, gt holds. -/
theorem TauRat.trichotomy (a b : TauRat) :
    TauRat.lt a b ∨ TauRat.equiv a b ∨ TauRat.lt b a := by
  rcases _root_.lt_trichotomy a.toRat b.toRat with h | h | h
  · exact Or.inl h
  · exact Or.inr (Or.inl ((equiv_iff_toRat_eq a b).mpr h))
  · exact Or.inr (Or.inr h)

-- ============================================================
-- PART 5: EQUIV PRESERVATION (well-definedness)
-- ============================================================

/-- lt is preserved by equiv on the left. -/
theorem TauRat.lt_of_equiv_left {a a' b : TauRat}
    (h_equiv : TauRat.equiv a a') (h_lt : TauRat.lt a b) : TauRat.lt a' b := by
  unfold TauRat.lt at *
  rw [← (equiv_iff_toRat_eq a a').mp h_equiv]
  exact h_lt

/-- lt is preserved by equiv on the right. -/
theorem TauRat.lt_of_equiv_right {a b b' : TauRat}
    (h_equiv : TauRat.equiv b b') (h_lt : TauRat.lt a b) : TauRat.lt a b' := by
  unfold TauRat.lt at *
  rw [← (equiv_iff_toRat_eq b b').mp h_equiv]
  exact h_lt

/-- le is preserved by equiv on the left. -/
theorem TauRat.le_of_equiv_left {a a' b : TauRat}
    (h_equiv : TauRat.equiv a a') (h_le : TauRat.le a b) : TauRat.le a' b := by
  unfold TauRat.le at *
  rw [← (equiv_iff_toRat_eq a a').mp h_equiv]
  exact h_le

/-- le is preserved by equiv on the right. -/
theorem TauRat.le_of_equiv_right {a b b' : TauRat}
    (h_equiv : TauRat.equiv b b') (h_le : TauRat.le a b) : TauRat.le a b' := by
  unfold TauRat.le at *
  rw [← (equiv_iff_toRat_eq b b').mp h_equiv]
  exact h_le

-- ============================================================
-- PART 6: COMPATIBILITY WITH ARITHMETIC
-- ============================================================

/-- Adding the same value preserves lt.
    (Note: mathlib's `add_lt_add_left` is the lemma that actually
    yields `a + c < b + c` despite the misleading name.) -/
theorem TauRat.add_lt_add_right {a b : TauRat} (h : TauRat.lt a b) (c : TauRat) :
    TauRat.lt (a.add c) (b.add c) := by
  unfold TauRat.lt at *
  rw [toRat_add, toRat_add]
  exact _root_.add_lt_add_left h c.toRat

/-- Adding the same value preserves le. -/
theorem TauRat.add_le_add_right {a b : TauRat} (h : TauRat.le a b) (c : TauRat) :
    TauRat.le (a.add c) (b.add c) := by
  unfold TauRat.le at *
  rw [toRat_add, toRat_add]
  exact _root_.add_le_add_left h c.toRat

/-- Adding the same value on the left preserves lt. -/
theorem TauRat.add_lt_add_left (c : TauRat) {a b : TauRat} (h : TauRat.lt a b) :
    TauRat.lt (c.add a) (c.add b) := by
  unfold TauRat.lt at *
  rw [toRat_add, toRat_add]
  exact _root_.add_lt_add_right h c.toRat

-- ============================================================
-- PART 7: SMOKE TESTS
-- ============================================================

-- 1/3 < 1/2
example : TauRat.lt (⟨⟨1, 0⟩, 3, by norm_num⟩ : TauRat) ⟨⟨1, 0⟩, 2, by norm_num⟩ := by
  unfold TauRat.lt
  simp [TauRat.toRat, TauInt.toInt]
  norm_num

-- 1/2 ≤ 1/2
example : TauRat.le (⟨⟨1, 0⟩, 2, by norm_num⟩ : TauRat) ⟨⟨1, 0⟩, 2, by norm_num⟩ :=
  TauRat.le_refl _

-- Trichotomy applied: not (1/2 < 1/2)
example : ¬ TauRat.lt (⟨⟨1, 0⟩, 2, by norm_num⟩ : TauRat) ⟨⟨1, 0⟩, 2, by norm_num⟩ :=
  TauRat.lt_irrefl _

-- Transitivity: 1/4 < 1/3 < 1/2 ⟹ 1/4 < 1/2
example :
    TauRat.lt (⟨⟨1, 0⟩, 4, by norm_num⟩ : TauRat) ⟨⟨1, 0⟩, 2, by norm_num⟩ := by
  apply TauRat.lt_trans (b := ⟨⟨1, 0⟩, 3, by norm_num⟩)
  · unfold TauRat.lt
    simp [TauRat.toRat, TauInt.toInt]
    norm_num
  · unfold TauRat.lt
    simp [TauRat.toRat, TauInt.toInt]
    norm_num

end Tau.Boundary
