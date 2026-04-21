import TauLib.BookI.Boundary.TauRatAbs
import Mathlib.Tactic.Ring
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push

/-!
# TauLib.BookI.Boundary.TauRatInv

Multiplicative inverse and division on `TauRat`.

## Registry Cross-References

- [I.D35] Number Tower — TauRat is the field-of-fractions layer
- [I.D107] TauRat Semantic Bridge — `TauRat.toRat`
- [I.D110] TauRat Inverse and Division — `TauRat.inv`, `TauRat.div`
  (this module's subject)
- [I.P48] TauRat Ordered Field Structure — collective ordered-field
  proposition proved across Wave 1
- [I.D84] Constructive Reals — Wave 2 will lift `inv` and `div` to `TauReal`

## Mathematical Content

This module is **Wave 1d** of the four-wave TauReal infrastructure build
(see `ROADMAP-3-HINGES.md`).  It adds the multiplicative-inverse layer
on `TauRat`:

1. **`TauRat.inv`** — inverse as a structure-level case split on the
   sign of the numerator, using `Int.natAbs` (Lean core) for the
   magnitude.  The positivity of the new denominator falls out of
   `Int.natAbs_pos` + the `is_nonzero` hypothesis.
2. **`TauRat.div`** — division defined as multiplication by the inverse.
3. **Homomorphism**: `toRat_inv`, `toRat_div` reduce to Lean core's
   `Rat.inv` and `Rat.div`.
4. **Cancellation**: `inv_mul_cancel` and `mul_inv_cancel` up to
   `TauRat.equiv`.

The sign case split mirrors the one in `TauRatAbs.lean`: if
`q.num.toInt > 0`, the inverse is the obvious swap `⟨den, 0⟩ / |num|`;
if `q.num.toInt < 0`, both signs flip to keep the denominator positive:
`⟨0, den⟩ / |num|`.
-/

set_option autoImplicit false

namespace Tau.Boundary

open Tau.Denotation

-- ============================================================
-- PART 1: DEFINITION
-- ============================================================

/-- Multiplicative inverse on `TauRat`.  Requires a nonzero hypothesis
    (see `TauRat.is_nonzero`).

    Structure: the new numerator is either `⟨den, 0⟩` (when `q.num > 0`)
    or `⟨0, den⟩` (when `q.num < 0`), so the sign is carried in the
    TauInt representation.  The new denominator is `q.num.toInt.natAbs`,
    which is strictly positive by `Int.natAbs_pos.mpr h`. -/
def TauRat.inv (q : TauRat) (h : q.is_nonzero) : TauRat :=
  { num := if 0 < q.num.toInt then ⟨q.den, 0⟩ else ⟨0, q.den⟩,
    den := q.num.toInt.natAbs,
    den_pos := Int.natAbs_pos.mpr h }

/-- Division on `TauRat`: `a / b = a · b⁻¹`, with a nonzero hypothesis
    on `b`. -/
def TauRat.div (a b : TauRat) (hb : b.is_nonzero) : TauRat :=
  a.mul (b.inv hb)

-- ============================================================
-- PART 2: toRat(inv) IDENTITY
-- ============================================================

/-- Helper: `(⟨q.den, 0⟩ : TauInt).toInt = q.den`. -/
private theorem TauRat.inv_num_toInt_pos (q : TauRat) :
    (⟨q.den, 0⟩ : TauInt).toInt = (q.den : Int) := by
  show (q.den : Int) - 0 = (q.den : Int); ring

/-- Helper: `(⟨0, q.den⟩ : TauInt).toInt = -q.den`. -/
private theorem TauRat.inv_num_toInt_neg (q : TauRat) :
    (⟨0, q.den⟩ : TauInt).toInt = -(q.den : Int) := by
  show (0 : Int) - q.den = -(q.den : Int); ring

/-- `toRat` is a homomorphism with respect to inverses: the toRat of
    `q.inv h` equals `q.toRat⁻¹`.

    Strategy: route `Int.natAbs` through the `|·|` notation on `Rat` via
    `Int.cast_natAbs` (which says `((n.natAbs : Nat) : α) = |(n : α)|` on a
    suitable ordered type).  Then close each sign branch with
    `abs_of_pos` / `abs_of_neg`. -/
theorem toRat_inv (q : TauRat) (h : q.is_nonzero) :
    (q.inv h).toRat = q.toRat⁻¹ := by
  have h_num_ne : (q.num.toInt : Rat) ≠ 0 := by
    intro hcontra
    apply h
    exact_mod_cast hcontra
  have h_den_ne : (q.den : Rat) ≠ 0 := q.den_ne_zero_rat
  -- Route natAbs through the Int-level `|·|` via `Nat.cast_natAbs`
  -- (which gives `(n.natAbs : α) = ((|n| : Int) : α)`), then resolve
  -- `|q.num.toInt|` by sign case at the Int level.
  by_cases hpos : 0 < q.num.toInt
  · -- Positive branch
    have h_abs_int : |q.num.toInt| = q.num.toInt := abs_of_pos hpos
    have h_natAbs_rat : ((q.num.toInt.natAbs : Nat) : Rat) = (q.num.toInt : Rat) := by
      rw [Nat.cast_natAbs, h_abs_int]
    have hLHS : (q.inv h).toRat =
                ((q.den : Int) : Rat) / ((q.num.toInt.natAbs : Nat) : Rat) := by
      show (((if 0 < q.num.toInt then (⟨q.den, 0⟩ : TauInt)
              else ⟨0, q.den⟩).toInt : Int) : Rat)
             / ((q.num.toInt.natAbs : Nat) : Rat) = _
      rw [if_pos hpos, TauRat.inv_num_toInt_pos]
    rw [hLHS, h_natAbs_rat, TauRat.toRat, inv_div]
    push_cast; ring
  · -- Nonpositive (hence negative by nonzero) branch
    push_neg at hpos
    have hneg : q.num.toInt < 0 := lt_of_le_of_ne hpos h
    have h_abs_int : |q.num.toInt| = -q.num.toInt := abs_of_neg hneg
    have h_natAbs_rat : ((q.num.toInt.natAbs : Nat) : Rat) = -(q.num.toInt : Rat) := by
      rw [Nat.cast_natAbs, h_abs_int]
      push_cast; ring
    have hLHS : (q.inv h).toRat =
                (-(q.den : Int) : Rat) / ((q.num.toInt.natAbs : Nat) : Rat) := by
      show (((if 0 < q.num.toInt then (⟨q.den, 0⟩ : TauInt)
              else ⟨0, q.den⟩).toInt : Int) : Rat)
             / ((q.num.toInt.natAbs : Nat) : Rat) = _
      rw [if_neg (not_lt.mpr hpos), TauRat.inv_num_toInt_neg]
      push_cast; ring
    rw [hLHS, h_natAbs_rat, TauRat.toRat, inv_div]
    push_cast; ring

/-- `toRat` is a homomorphism with respect to division. -/
theorem toRat_div (a b : TauRat) (hb : b.is_nonzero) :
    (a.div b hb).toRat = a.toRat / b.toRat := by
  unfold TauRat.div
  rw [toRat_mul, toRat_inv]
  rw [div_eq_mul_inv]

-- ============================================================
-- PART 3: CANCELLATION LEMMAS (up to TauRat.equiv)
-- ============================================================

/-- `q⁻¹ · q ≡ 1` up to `TauRat.equiv`, assuming `q` is nonzero. -/
theorem TauRat.inv_mul_cancel (q : TauRat) (h : q.is_nonzero) :
    TauRat.equiv ((q.inv h).mul q) TauRat.one := by
  rw [equiv_iff_toRat_eq, toRat_mul, toRat_inv, toRat_one]
  rw [(TauRat.is_nonzero_iff_toRat_ne_zero q).mp h
      |> inv_mul_cancel₀]

/-- `q · q⁻¹ ≡ 1` up to `TauRat.equiv`, assuming `q` is nonzero. -/
theorem TauRat.mul_inv_cancel (q : TauRat) (h : q.is_nonzero) :
    TauRat.equiv (q.mul (q.inv h)) TauRat.one := by
  rw [equiv_iff_toRat_eq, toRat_mul, toRat_inv, toRat_one]
  rw [(TauRat.is_nonzero_iff_toRat_ne_zero q).mp h
      |> mul_inv_cancel₀]

-- ============================================================
-- PART 4: DIVISION BY SELF IS ONE (up to equiv)
-- ============================================================

/-- `q / q ≡ 1` up to `TauRat.equiv`, assuming `q` is nonzero. -/
theorem TauRat.div_self (q : TauRat) (h : q.is_nonzero) :
    TauRat.equiv (q.div q h) TauRat.one := by
  rw [equiv_iff_toRat_eq, toRat_div, toRat_one]
  exact _root_.div_self ((TauRat.is_nonzero_iff_toRat_ne_zero q).mp h)

-- ============================================================
-- PART 5: SMOKE TESTS
-- ============================================================

-- 1/(2/3) = 3/2
example :
    let q : TauRat := ⟨⟨2, 0⟩, 3, by norm_num⟩
    have h : q.is_nonzero := by unfold TauRat.is_nonzero TauInt.toInt; norm_num
    (q.inv h).toRat = 3/2 := by
  intro q h
  rw [toRat_inv]
  simp [TauRat.toRat, TauInt.toInt, q]

-- (2/3) / (4/5) = 5/6
example :
    let a : TauRat := ⟨⟨2, 0⟩, 3, by norm_num⟩
    let b : TauRat := ⟨⟨4, 0⟩, 5, by norm_num⟩
    have hb : b.is_nonzero := by unfold TauRat.is_nonzero TauInt.toInt; norm_num
    (a.div b hb).toRat = 5/6 := by
  intro a b hb
  rw [toRat_div]
  simp [TauRat.toRat, TauInt.toInt, a, b]
  norm_num

-- Negative: 1/(-2/3) = -3/2
example :
    let q : TauRat := ⟨⟨0, 2⟩, 3, by norm_num⟩
    have h : q.is_nonzero := by unfold TauRat.is_nonzero TauInt.toInt; norm_num
    (q.inv h).toRat = -3/2 := by
  intro q h
  rw [toRat_inv]
  simp [TauRat.toRat, TauInt.toInt, q]
  norm_num

end Tau.Boundary
