import TauLib.BookI.Boundary.NumberTower
import Mathlib.Tactic.Ring
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum

/-!
# TauLib.BookI.Boundary.TauRatField

Field extensions for TauRat: the missing pieces needed to make
TauRat a constructive ordered field (up to equiv).

## Registry Cross-References

- [I.D35] Number Tower — TauRat is the field-of-fractions layer defined in
  `TauLib.Boundary.NumberTower`; this module extends it with the missing
  `equiv_trans` and a semantic bridge to Lean's built-in `Rat`
- [I.D107] TauRat Semantic Bridge — `TauRat.toRat` (this module's main
  new definition; parallels `TauInt.toInt`)
- [I.P48] TauRat Ordered Field Structure — collective proposition that
  TauRat satisfies ordered-field axioms up to equiv (proved across
  Wave 1a/1b/1c/1d)
- [I.D84] Constructive Reals — the eventual consumer of these helpers
  (Wave 2 will rebuild `TauReal` on top of true Cauchy semantics)

## Mathematical Content

This module is **Wave 1a** of the four-wave TauReal infrastructure build
(see `ROADMAP-3-HINGES.md`).  It adds the essential foundational pieces:

1. **Equivalence transitivity** (the missing piece in NumberTower).
2. **Semantic bridge `toRat`** to Lean's built-in `Rat`, paralleling the
   existing `toInt` bridge for TauInt.  Enables proofs by `push_cast; ring`
   over rationals.
3. **toRat homomorphism properties** (preserves +, ·, -, 0, 1).
4. **TauRat.is_nonzero** predicate.

Wave 1b (separate file) will add: ordering (lt, le), absolute value (abs),
multiplicative inverse (inv with nonzero hypothesis), and division (div).
The split is for compile-time isolation given TauLib's restricted
mathlib-tactic set (no `field_simp`, no `linarith`, no `Int.natAbs_of_pos`).
-/

set_option autoImplicit false

namespace Tau.Boundary

open Tau.Denotation

-- ============================================================
-- PART 1: TauRat.equiv_trans (THE MISSING PIECE)
-- ============================================================

/-- TauRat equivalence is transitive.  This was missing from NumberTower.lean
    where only `equiv_refl` and `equiv_symm` were proved.

    Strategy: convert all three TauInt-equivs to integer equalities via
    `equiv_iff_toInt_eq`, then use the cross-multiplication identity
    via `linear_combination`. -/
theorem TauRat.equiv_trans {a b c : TauRat}
    (hab : TauRat.equiv a b) (hbc : TauRat.equiv b c) :
    TauRat.equiv a c := by
  -- Unfold and convert to Int equalities
  simp only [TauRat.equiv] at *
  rw [equiv_iff_toInt_eq] at *
  simp only [toInt_mul, toInt_fromNat] at *
  -- Now: hab: a.num.toInt * b.den = b.num.toInt * a.den
  --      hbc: b.num.toInt * c.den = c.num.toInt * b.den
  -- Goal: a.num.toInt * c.den = c.num.toInt * a.den
  -- Cancel b.den (which is positive).
  have hb_pos : (b.den : Int) > 0 := by exact_mod_cast b.den_pos
  have hb_ne : (b.den : Int) ≠ 0 := ne_of_gt hb_pos
  have key :
      (a.num.toInt * (c.den : Int)) * (b.den : Int) =
      (c.num.toInt * (a.den : Int)) * (b.den : Int) := by
    linear_combination (c.den : Int) * hab + (a.den : Int) * hbc
  exact mul_right_cancel₀ hb_ne key

/-- TauRat.equiv as a fully-fledged equivalence relation. -/
theorem TauRat.equivalence : Equivalence TauRat.equiv :=
  ⟨TauRat.equiv_refl, TauRat.equiv_symm, TauRat.equiv_trans⟩

-- ============================================================
-- PART 2: SEMANTIC BRIDGE TauRat.toRat
-- ============================================================

/-- Semantic bridge from TauRat to Lean's built-in `Rat`.  Computes the
    rational number represented by a TauRat structure.  Parallels
    `TauInt.toInt`. -/
def TauRat.toRat (q : TauRat) : Rat :=
  (q.num.toInt : Rat) / (q.den : Rat)

/-- The denominator is positive when cast to Rat. -/
theorem TauRat.den_pos_rat (q : TauRat) : (q.den : Rat) > 0 := by
  exact_mod_cast q.den_pos

/-- The denominator is nonzero when cast to Rat. -/
theorem TauRat.den_ne_zero_rat (q : TauRat) : (q.den : Rat) ≠ 0 :=
  ne_of_gt q.den_pos_rat

/-- Convert TauRat.equiv to a clean cross-multiplication identity in ℤ.
    This is the workhorse lemma. -/
theorem TauRat.equiv_iff_int_cross (a b : TauRat) :
    TauRat.equiv a b ↔
    a.num.toInt * (b.den : Int) = b.num.toInt * (a.den : Int) := by
  constructor
  · intro h
    have := (equiv_iff_toInt_eq _ _).mp h
    simpa [toInt_mul, toInt_fromNat] using this
  · intro h
    simp only [TauRat.equiv]
    rw [equiv_iff_toInt_eq, toInt_mul, toInt_mul, toInt_fromNat, toInt_fromNat]
    exact h

/-- TauRat.equiv is equivalent to Rat equality of toRat values. -/
theorem equiv_iff_toRat_eq (a b : TauRat) :
    TauRat.equiv a b ↔ a.toRat = b.toRat := by
  rw [TauRat.equiv_iff_int_cross]
  constructor
  · intro h
    simp only [TauRat.toRat]
    have ha_ne : (a.den : Rat) ≠ 0 := a.den_ne_zero_rat
    have hb_ne : (b.den : Rat) ≠ 0 := b.den_ne_zero_rat
    rw [div_eq_div_iff ha_ne hb_ne]
    have h_rat : (a.num.toInt : Rat) * (b.den : Rat) =
                 (b.num.toInt : Rat) * (a.den : Rat) := by
      exact_mod_cast h
    linear_combination h_rat
  · intro h
    simp only [TauRat.toRat] at h
    have ha_ne : (a.den : Rat) ≠ 0 := a.den_ne_zero_rat
    have hb_ne : (b.den : Rat) ≠ 0 := b.den_ne_zero_rat
    rw [div_eq_div_iff ha_ne hb_ne] at h
    exact_mod_cast h

-- ============================================================
-- PART 3: toRat HOMOMORPHISM PROPERTIES
-- ============================================================

/-- toRat preserves zero. -/
theorem toRat_zero : TauRat.zero.toRat = 0 := by
  simp [TauRat.toRat, TauRat.zero, toInt_zero]

/-- toRat preserves one. -/
theorem toRat_one : TauRat.one.toRat = 1 := by
  simp [TauRat.toRat, TauRat.one, toInt_one]

/-- toRat preserves addition.  Proof reduces to a ℚ-level identity. -/
theorem toRat_add (a b : TauRat) :
    (a.add b).toRat = a.toRat + b.toRat := by
  simp only [TauRat.toRat, TauRat.add, toInt_add, toInt_mul, toInt_fromNat]
  have ha_ne : (a.den : Rat) ≠ 0 := a.den_ne_zero_rat
  have hb_ne : (b.den : Rat) ≠ 0 := b.den_ne_zero_rat
  rw [div_add_div _ _ ha_ne hb_ne]
  push_cast
  congr 1
  ring

/-- toRat preserves multiplication. -/
theorem toRat_mul (a b : TauRat) :
    (a.mul b).toRat = a.toRat * b.toRat := by
  simp only [TauRat.toRat, TauRat.mul, toInt_mul]
  push_cast
  rw [div_mul_div_comm]

/-- toRat preserves negation. -/
theorem toRat_negate (a : TauRat) :
    a.negate.toRat = -a.toRat := by
  simp only [TauRat.toRat, TauRat.negate, toInt_negate]
  push_cast
  rw [neg_div]

/-- toRat preserves subtraction. -/
theorem toRat_sub (a b : TauRat) :
    (a.sub b).toRat = a.toRat - b.toRat := by
  simp only [TauRat.sub, toRat_add, toRat_negate]
  ring

-- ============================================================
-- PART 4: NONZERO PREDICATE
-- ============================================================

/-- TauRat is non-equiv-zero iff its numerator is nonzero in ℤ. -/
def TauRat.is_nonzero (q : TauRat) : Prop := q.num.toInt ≠ 0

/-- is_nonzero iff toRat is nonzero. -/
theorem TauRat.is_nonzero_iff_toRat_ne_zero (q : TauRat) :
    q.is_nonzero ↔ q.toRat ≠ 0 := by
  unfold TauRat.is_nonzero
  simp only [TauRat.toRat, ne_eq, div_eq_zero_iff]
  constructor
  · intro h_int
    push_neg
    refine ⟨?_, q.den_ne_zero_rat⟩
    intro h_zero
    apply h_int
    exact_mod_cast h_zero
  · intro h
    push_neg at h
    intro h_int
    apply h.1
    exact_mod_cast h_int

/-- is_nonzero is preserved by equiv. -/
theorem TauRat.is_nonzero_of_equiv {a b : TauRat}
    (h_equiv : TauRat.equiv a b) (h_nz : a.is_nonzero) : b.is_nonzero := by
  rw [TauRat.is_nonzero_iff_toRat_ne_zero] at *
  rw [← (equiv_iff_toRat_eq a b).mp h_equiv]
  exact h_nz

-- ============================================================
-- PART 5: SMOKE TESTS
-- ============================================================

-- toRat semantic bridge sanity
example : (⟨⟨1, 0⟩, 2, by norm_num⟩ : TauRat).toRat = 1/2 := by
  simp [TauRat.toRat, TauInt.toInt]

-- is_nonzero sanity
example : (⟨⟨2, 0⟩, 3, by norm_num⟩ : TauRat).is_nonzero := by
  unfold TauRat.is_nonzero TauInt.toInt
  norm_num

-- equiv_trans smoke test: 1/2 ~ 2/4, 2/4 ~ 3/6, so 1/2 ~ 3/6
example :
    TauRat.equiv (⟨⟨1, 0⟩, 2, by norm_num⟩ : TauRat) ⟨⟨3, 0⟩, 6, by norm_num⟩ := by
  apply TauRat.equiv_trans (b := ⟨⟨2, 0⟩, 4, by norm_num⟩)
  · rw [equiv_iff_toRat_eq]; native_decide
  · rw [equiv_iff_toRat_eq]; native_decide

end Tau.Boundary
