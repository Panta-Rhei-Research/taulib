import TauLib.BookI.Boundary.Bridge.TauIntQuotient
import Mathlib.Algebra.Order.Ring.Defs
import Mathlib.Algebra.Order.Ring.Int
import Mathlib.Tactic.Linarith

/-!
# TauLib.BookI.Boundary.Bridge.TauIntQTransport

**Wave 43 — Mathlib structure transport along TauIntQ ≃+* ℤ**.

Wave 39 established `TauIntQ.ringEquivInt : TauIntQ ≃+* ℤ`. This module
**transports** Mathlib's full classical structure on `Int` to `TauIntQ`
using the ring isomorphism, unlocking essentially all of Mathlib's
elementary number theory at the τ-integer level.

This is a **transport** module, not a constructive bridge: every
instance is derived by pulling back the corresponding `Int` instance
through the bijection. No new mathematical content is introduced; we
are stating "TauIntQ has the same structure as ℤ as a ring", which is
exactly what `≃+*` already says. Mathlib's classical reasoning on `ℤ`
is accepted as-is on the receiving side.

## What this module delivers

| Mathlib instance         | Source              | Role |
|--------------------------|---------------------|------|
| `DecidableEq TauIntQ`    | `Int`'s DecidableEq | Decidable equality |
| `LinearOrder TauIntQ`    | `Int`'s LinearOrder | Trichotomy |
| `IsOrderedAddMonoid`     | `Int`               | Add-monotone order |
| `ZeroLEOneClass`         | `Int`               | `0 ≤ 1` |
| `Nontrivial TauIntQ`     | `Int`               | `0 ≠ 1` |
| `IsOrderedRing TauIntQ`  | `of_mul_nonneg`     | Ordered ring |
| `IsStrictOrderedRing`    | `of_mul_pos`        | Strict ordered ring |
| `NoZeroDivisors TauIntQ` | `Int`               | No zero divisors |

## Methodology check

- Mathlib usage: typeclass instances + transport. Module sits in
  `Boundary/Bridge/` per Wave 39 CI policy.
- No new types or operations — pure structure transport.
- Companion to Waves 39, 40, 41a–41e.

## Registry Cross-References

- [I.T208]   TauIntQ ≃+* ℤ ring isomorphism (Wave 39)
- [I.T246+]  This module's instances
-/

set_option autoImplicit false

namespace Tau.Boundary

open Tau.Denotation

-- ============================================================
-- PART 0: Typeclass-form simp lemmas for `toInt`
-- ============================================================
-- The existing `TauIntQ.toInt_add` etc. in `Bridge/TauIntQuotient.lean`
-- are stated as `(TauIntQ.add x y).toInt = ...`. After the typeclass
-- `Add TauIntQ` resolves `x + y` to `TauIntQ.add x y`, these are
-- definitionally equal, but `simp` matches syntactically. We expose the
-- typeclass-form lemmas explicitly so `simp` can chain through them.

@[simp] theorem TauIntQ.toInt_add' (x y : TauIntQ) :
    (x + y).toInt = x.toInt + y.toInt := TauIntQ.toInt_add x y

@[simp] theorem TauIntQ.toInt_mul' (x y : TauIntQ) :
    (x * y).toInt = x.toInt * y.toInt := TauIntQ.toInt_mul x y

@[simp] theorem TauIntQ.toInt_neg' (x : TauIntQ) : (-x).toInt = -x.toInt :=
  TauIntQ.toInt_neg x

@[simp] theorem TauIntQ.toInt_zero' : ((0 : TauIntQ).toInt) = 0 := TauIntQ.toInt_zero

@[simp] theorem TauIntQ.toInt_one' : ((1 : TauIntQ).toInt) = 1 := TauIntQ.toInt_one

-- ============================================================
-- PART 1: DecidableEq + LinearOrder via the bijection
-- ============================================================

/-- **DecidableEq via `toInt` injectivity**.

    Decidable equality on `TauIntQ` reduces to decidable equality on
    `ℤ` through the bijection `toInt` (which is injective by
    `eq_iff_toInt_eq`). -/
instance : DecidableEq TauIntQ := fun x y =>
  decidable_of_iff (TauIntQ.toInt x = TauIntQ.toInt y) (TauIntQ.eq_iff_toInt_eq x y).symm

/-- **LE on TauIntQ via `toInt`**. -/
instance : LE TauIntQ := ⟨fun x y => TauIntQ.toInt x ≤ TauIntQ.toInt y⟩

/-- **LT on TauIntQ via `toInt`**. -/
instance : LT TauIntQ := ⟨fun x y => TauIntQ.toInt x < TauIntQ.toInt y⟩

@[simp] theorem TauIntQ.le_iff (x y : TauIntQ) : x ≤ y ↔ x.toInt ≤ y.toInt := Iff.rfl
@[simp] theorem TauIntQ.lt_iff (x y : TauIntQ) : x < y ↔ x.toInt < y.toInt := Iff.rfl

/-- **LinearOrder TauIntQ** — full trichotomy via `Int`'s LinearOrder. -/
instance : LinearOrder TauIntQ where
  le_refl x := by simp [TauIntQ.le_iff]
  le_trans x y z hxy hyz := by
    simp only [TauIntQ.le_iff] at hxy hyz ⊢; linarith
  le_antisymm x y hxy hyx := by
    apply (TauIntQ.eq_iff_toInt_eq x y).mpr
    simp only [TauIntQ.le_iff] at hxy hyx
    linarith
  le_total x y := by simp only [TauIntQ.le_iff]; exact le_total _ _
  toDecidableLE x y := inferInstanceAs (Decidable (x.toInt ≤ y.toInt))
  lt_iff_le_not_ge x y := by
    simp only [TauIntQ.lt_iff, TauIntQ.le_iff]
    exact lt_iff_le_not_ge

-- ============================================================
-- PART 2: Ordered-ring structure via toInt
-- ============================================================

/-- **IsOrderedAddMonoid TauIntQ** — addition is monotone. -/
instance : IsOrderedAddMonoid TauIntQ where
  add_le_add_left a b h c := by
    simp only [TauIntQ.le_iff, TauIntQ.toInt_add'] at *
    linarith

/-- **ZeroLEOneClass TauIntQ**. -/
instance : ZeroLEOneClass TauIntQ where
  zero_le_one := by
    simp only [TauIntQ.le_iff, TauIntQ.toInt_zero', TauIntQ.toInt_one']
    norm_num

instance : Nontrivial TauIntQ := ⟨0, 1, by
  intro h
  have : TauIntQ.toInt 0 = TauIntQ.toInt 1 := congrArg _ h
  simp only [TauIntQ.toInt_zero', TauIntQ.toInt_one'] at this
  exact zero_ne_one this⟩

/-- **IsOrderedRing TauIntQ** via `of_mul_nonneg`. -/
instance : IsOrderedRing TauIntQ :=
  IsOrderedRing.of_mul_nonneg (fun a b ha hb => by
    simp only [TauIntQ.le_iff, TauIntQ.toInt_zero', TauIntQ.toInt_mul'] at *
    exact mul_nonneg ha hb)

/-- **IsStrictOrderedRing TauIntQ** via `of_mul_pos`. -/
instance : IsStrictOrderedRing TauIntQ :=
  IsStrictOrderedRing.of_mul_pos (fun a b ha hb => by
    simp only [TauIntQ.lt_iff, TauIntQ.toInt_zero', TauIntQ.toInt_mul'] at *
    exact mul_pos ha hb)

-- ============================================================
-- PART 3: NoZeroDivisors via the bijection
-- ============================================================

instance : NoZeroDivisors TauIntQ where
  eq_zero_or_eq_zero_of_mul_eq_zero {a b} h := by
    have h_int : a.toInt * b.toInt = 0 := by
      have := congrArg TauIntQ.toInt h
      simp only [TauIntQ.toInt_mul', TauIntQ.toInt_zero'] at this
      exact this
    rcases mul_eq_zero.mp h_int with ha | hb
    · left
      exact (TauIntQ.eq_iff_toInt_eq a 0).mpr (by simp [ha])
    · right
      exact (TauIntQ.eq_iff_toInt_eq b 0).mpr (by simp [hb])

-- ============================================================
-- PART 4: Wave 43 synthesis theorem
-- ============================================================

/-- **Wave 43 synthesis: structural-significance packaging**.

    Five-clause structural significance:
    1. `DecidableEq TauIntQ`     (decidable equality)
    2. `LinearOrder TauIntQ`     (full trichotomy)
    3. `IsStrictOrderedRing`     (strict ordered-ring structure)
    4. `NoZeroDivisors TauIntQ`  (no zero divisors)
    5. The RingEquiv `TauIntQ ≃+* ℤ` (Wave 39) is also an
       order-preserving bijection (immediate from `toInt` definitions).

    Every Mathlib theorem stated for `[CommRing K] [LinearOrder K]
    [IsStrictOrderedRing K]` (i.e., the modern unbundled form of
    `LinearOrderedCommRing`) now applies to TauIntQ. -/
theorem h8_tauintq_mathlib_transport_synthesis :
    Nonempty (DecidableEq TauIntQ) ∧
    Nonempty (LinearOrder TauIntQ) ∧
    Nonempty (IsStrictOrderedRing TauIntQ) ∧
    Nonempty (NoZeroDivisors TauIntQ) ∧
    -- Order-preservation of the bijection (immediate from definitions)
    (∀ x y : TauIntQ, x ≤ y ↔ x.toInt ≤ y.toInt) :=
  ⟨⟨inferInstance⟩, ⟨inferInstance⟩, ⟨inferInstance⟩, ⟨inferInstance⟩,
   fun x y => Iff.rfl⟩

end Tau.Boundary
