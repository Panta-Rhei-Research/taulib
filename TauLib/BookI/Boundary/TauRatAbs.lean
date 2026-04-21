import TauLib.BookI.Boundary.TauRatOrder
import Mathlib.Tactic.Ring
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push

/-!
# TauLib.BookI.Boundary.TauRatAbs

Absolute value on `TauRat`.

## Registry Cross-References

- [I.D35] Number Tower — TauRat is the field-of-fractions layer
- [I.D107] TauRat Semantic Bridge — `TauRat.toRat`
- [I.D109] TauRat Absolute Value — `TauRat.abs` (this module's subject)
- [I.P48] TauRat Ordered Field Structure — abs is a component
- [I.D84] Constructive Reals — Wave 2 will lift `abs` to `TauReal`

## Mathematical Content

This module is **Wave 1c** of the four-wave TauReal infrastructure build
(see `ROADMAP-3-HINGES.md`).  It adds the absolute-value layer on
`TauRat` via a structural if/else on the sign of the numerator,
paralleling Lean core's `Int.natAbs`.

Deliberate design choice: all properties are stated in terms of
`toRat` comparisons and the two cases (nonneg / neg), **not** via
Lean's `|·|` / `Abs` notation on `Rat`.  This avoids any dependence
on Mathlib's `Abs` instance chain — which would pull in forbidden
content modules — while still giving consumers a clean API:

```
TauRat.abs : TauRat → TauRat
toRat_abs_of_nonneg : 0 ≤ q.toRat → q.abs.toRat = q.toRat
toRat_abs_of_neg    : q.toRat < 0 → q.abs.toRat = -q.toRat
TauRat.abs_nonneg   : 0 ≤ q.abs.toRat
```

Wave 1d (`TauRatInv.lean`) will use `abs` implicitly through its
handling of the sign-of-numerator case split in the inverse
construction.
-/

set_option autoImplicit false

namespace Tau.Boundary

open Tau.Denotation

-- ============================================================
-- PART 1: DEFINITION
-- ============================================================

/-- Absolute value on `TauRat`: a structural if/else that returns the
    TauRat itself if its numerator is nonneg (i.e. `q.toRat ≥ 0`), and
    the TauRat-level negation otherwise.

    The decidability lives at the `Int` level via `q.num.toInt < 0`
    (Lean core's `Int.decLt`).  No Mathlib content is imported. -/
def TauRat.abs (q : TauRat) : TauRat :=
  if q.num.toInt < 0 then q.negate else q

-- ============================================================
-- PART 2: SIGN-OF-NUMERATOR vs SIGN-OF-toRat
-- ============================================================

/-- `q.toRat ≥ 0` iff `q.num.toInt ≥ 0`.  The denominator is positive,
    so the sign of `q.toRat = q.num.toInt / q.den` is controlled
    entirely by the numerator. -/
theorem TauRat.toRat_nonneg_iff_num_nonneg (q : TauRat) :
    0 ≤ q.toRat ↔ 0 ≤ q.num.toInt := by
  unfold TauRat.toRat
  have hp : (0 : Rat) < (q.den : Rat) := q.den_pos_rat
  constructor
  · intro h
    have h_rat : (0 : Rat) ≤ (q.num.toInt : Rat) := by
      have hmul := mul_nonneg h (_root_.le_of_lt hp)
      rwa [div_mul_cancel₀ _ (ne_of_gt hp)] at hmul
    exact_mod_cast h_rat
  · intro h
    have h_rat : (0 : Rat) ≤ (q.num.toInt : Rat) := by exact_mod_cast h
    exact div_nonneg h_rat (_root_.le_of_lt hp)

/-- `q.toRat < 0` iff `q.num.toInt < 0`. -/
theorem TauRat.toRat_neg_iff_num_neg (q : TauRat) :
    q.toRat < 0 ↔ q.num.toInt < 0 := by
  have := q.toRat_nonneg_iff_num_nonneg
  constructor
  · intro h
    by_contra h_not
    push_neg at h_not
    exact absurd (this.mpr h_not) (not_le.mpr h)
  · intro h
    by_contra h_not
    push_neg at h_not
    exact absurd (this.mp h_not) (not_le.mpr h)

-- ============================================================
-- PART 3: toRat(abs) IDENTITIES
-- ============================================================

/-- If `q.toRat ≥ 0`, `abs q` leaves the toRat value unchanged. -/
theorem toRat_abs_of_nonneg {q : TauRat} (h : 0 ≤ q.toRat) :
    q.abs.toRat = q.toRat := by
  unfold TauRat.abs
  rw [(q.toRat_nonneg_iff_num_nonneg).mp h |> not_lt.mpr |> if_neg]

/-- If `q.toRat < 0`, `abs q` flips the sign. -/
theorem toRat_abs_of_neg {q : TauRat} (h : q.toRat < 0) :
    q.abs.toRat = -q.toRat := by
  unfold TauRat.abs
  rw [if_pos ((q.toRat_neg_iff_num_neg).mp h), toRat_negate]

-- ============================================================
-- PART 4: NONNEGATIVITY
-- ============================================================

/-- `abs q` is always nonneg in toRat. -/
theorem TauRat.abs_nonneg (q : TauRat) : 0 ≤ q.abs.toRat := by
  by_cases h : 0 ≤ q.toRat
  · rw [toRat_abs_of_nonneg h]; exact h
  · push_neg at h
    rw [toRat_abs_of_neg h]
    linarith

-- ============================================================
-- PART 5: abs IS ZERO IFF equiv ZERO
-- ============================================================

/-- `abs q` is equiv to zero iff `q` is equiv to zero. -/
theorem TauRat.abs_equiv_zero_iff_equiv_zero (q : TauRat) :
    TauRat.equiv q.abs TauRat.zero ↔ TauRat.equiv q TauRat.zero := by
  rw [equiv_iff_toRat_eq, equiv_iff_toRat_eq, toRat_zero]
  by_cases h : 0 ≤ q.toRat
  · rw [toRat_abs_of_nonneg h]
  · push_neg at h
    rw [toRat_abs_of_neg h]
    constructor
    · intro h_neg_zero
      linarith
    · intro h_zero
      rw [h_zero, neg_zero]

-- ============================================================
-- PART 6: EQUIV PRESERVATION
-- ============================================================

/-- `abs` respects `TauRat.equiv`. -/
theorem TauRat.abs_of_equiv {a b : TauRat} (h : TauRat.equiv a b) :
    TauRat.equiv a.abs b.abs := by
  rw [equiv_iff_toRat_eq] at h
  rw [equiv_iff_toRat_eq]
  by_cases ha : 0 ≤ a.toRat
  · have hb : 0 ≤ b.toRat := h ▸ ha
    rw [toRat_abs_of_nonneg ha, toRat_abs_of_nonneg hb, h]
  · push_neg at ha
    have hb : b.toRat < 0 := h ▸ ha
    rw [toRat_abs_of_neg ha, toRat_abs_of_neg hb, h]

-- ============================================================
-- PART 7: SMOKE TESTS
-- ============================================================

-- abs of a positive TauRat is the identity
example :
    (⟨⟨3, 0⟩, 5, by norm_num⟩ : TauRat).abs.toRat =
      (⟨⟨3, 0⟩, 5, by norm_num⟩ : TauRat).toRat := by
  apply toRat_abs_of_nonneg
  simp [TauRat.toRat, TauInt.toInt]
  norm_num

-- abs of a negative TauRat flips the sign
example :
    (⟨⟨0, 3⟩, 5, by norm_num⟩ : TauRat).abs.toRat =
      -(⟨⟨0, 3⟩, 5, by norm_num⟩ : TauRat).toRat := by
  apply toRat_abs_of_neg
  simp [TauRat.toRat, TauInt.toInt]
  norm_num

-- abs is always nonneg
example : 0 ≤ (⟨⟨0, 7⟩, 2, by norm_num⟩ : TauRat).abs.toRat :=
  TauRat.abs_nonneg _

end Tau.Boundary
