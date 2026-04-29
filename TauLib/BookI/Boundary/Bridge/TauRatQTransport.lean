import TauLib.BookI.Boundary.Bridge.TauRatQuotient
import Mathlib.Algebra.Order.Ring.Defs
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Tactic.Linarith

/-!
# TauLib.BookI.Boundary.Bridge.TauRatQTransport

**Wave 44 — Mathlib structure transport along TauRatQ ≃+* ℚ**.

Wave 40 established `TauRatQ.ringEquivRat : TauRatQ ≃+* ℚ`. This module
**transports** Mathlib's full classical structure on `Rat` to `TauRatQ`
using the ring isomorphism.

Like Wave 43 (TauIntQ), this is a transport module — every instance is
derived by pulling back the corresponding `Rat` instance through the
bijection. **All instances are constructive** (no Markov needed) at
this tier, because `ℚ` has computably-decidable comparison.

The structurally significant instance: **`LinearOrderedField TauRatQ`**
(modern unbundled form: `[Field K] [LinearOrder K] [IsStrictOrderedRing K]`)
— this is the τ-side analogue of "ℚ as a linearly ordered field". The
SAME structural typeclass that is **structurally impossible** on
`TauRealQ` (cardinality wall, see Wave 41 atlas insight) is
**immediately available** on `TauRatQ`. The cardinality boundary lives
between `TauRatQ` and `TauRealQ`, not between `TauRatQ` and orthodox
`ℚ`.

## What this module delivers

| Mathlib instance         | Source              | Cost |
|--------------------------|---------------------|------|
| `DecidableEq TauRatQ`    | `Rat`'s DecidableEq | constructive |
| `LinearOrder TauRatQ`    | `Rat`'s LinearOrder | constructive |
| `IsOrderedAddMonoid`     | `Rat`               | constructive |
| `ZeroLEOneClass`         | `Rat`               | constructive |
| `IsOrderedRing TauRatQ`  | `of_mul_nonneg`     | constructive |
| `IsStrictOrderedRing`    | `of_mul_pos`        | constructive |
| `Archimedean TauRatQ`    | `Rat`               | constructive |
| `DenselyOrdered TauRatQ` | `Rat`               | constructive |

The combination `[Field TauRatQ] [LinearOrder TauRatQ] [IsStrictOrderedRing TauRatQ]`
is the modern unbundled form of `LinearOrderedField TauRatQ`.

## Methodology check

- Mathlib usage: typeclass instances + transport. Module sits in
  `Boundary/Bridge/` per Wave 39 CI policy.
- No new types or operations — pure structure transport.
- Uses pattern established by Wave 43 (TauIntQ transport).

## Registry Cross-References

- [I.T213]   TauRatQ ≃+* ℚ ring isomorphism (Wave 40)
- [I.T252+]  This module's instances
-/

set_option autoImplicit false

namespace Tau.Boundary

open Tau.Denotation

-- ============================================================
-- PART 0: Typeclass-form simp lemmas for `toRat`
-- ============================================================

@[simp] theorem TauRatQ.toRat_add' (x y : TauRatQ) :
    (x + y).toRat = x.toRat + y.toRat := TauRatQ.toRat_add x y

@[simp] theorem TauRatQ.toRat_mul' (x y : TauRatQ) :
    (x * y).toRat = x.toRat * y.toRat := TauRatQ.toRat_mul x y

@[simp] theorem TauRatQ.toRat_zero' : ((0 : TauRatQ).toRat) = 0 := TauRatQ.toRat_zero

@[simp] theorem TauRatQ.toRat_one' : ((1 : TauRatQ).toRat) = 1 := TauRatQ.toRat_one

-- ============================================================
-- PART 1: DecidableEq + LinearOrder via the bijection
-- ============================================================

instance : DecidableEq TauRatQ := fun x y =>
  decidable_of_iff (TauRatQ.toRat x = TauRatQ.toRat y)
    (TauRatQ.eq_iff_toRat_eq x y).symm

instance : LE TauRatQ := ⟨fun x y => TauRatQ.toRat x ≤ TauRatQ.toRat y⟩
instance : LT TauRatQ := ⟨fun x y => TauRatQ.toRat x < TauRatQ.toRat y⟩

@[simp] theorem TauRatQ.le_iff (x y : TauRatQ) : x ≤ y ↔ x.toRat ≤ y.toRat := Iff.rfl
@[simp] theorem TauRatQ.lt_iff (x y : TauRatQ) : x < y ↔ x.toRat < y.toRat := Iff.rfl

instance : LinearOrder TauRatQ where
  le_refl x := by simp [TauRatQ.le_iff]
  le_trans x y z hxy hyz := by
    simp only [TauRatQ.le_iff] at hxy hyz ⊢; linarith
  le_antisymm x y hxy hyx := by
    apply (TauRatQ.eq_iff_toRat_eq x y).mpr
    simp only [TauRatQ.le_iff] at hxy hyx
    linarith
  le_total x y := by simp only [TauRatQ.le_iff]; exact le_total _ _
  toDecidableLE x y := inferInstanceAs (Decidable (x.toRat ≤ y.toRat))
  lt_iff_le_not_ge x y := by
    simp only [TauRatQ.lt_iff, TauRatQ.le_iff]
    exact lt_iff_le_not_ge

-- ============================================================
-- PART 2: Ordered-ring structure
-- ============================================================

instance : IsOrderedAddMonoid TauRatQ where
  add_le_add_left a b h c := by
    simp only [TauRatQ.le_iff, TauRatQ.toRat_add'] at *
    linarith

instance : ZeroLEOneClass TauRatQ where
  zero_le_one := by
    simp only [TauRatQ.le_iff, TauRatQ.toRat_zero', TauRatQ.toRat_one']
    norm_num

instance : Nontrivial TauRatQ := ⟨0, 1, by
  intro h
  have : TauRatQ.toRat 0 = TauRatQ.toRat 1 := congrArg _ h
  simp only [TauRatQ.toRat_zero', TauRatQ.toRat_one'] at this
  exact zero_ne_one this⟩

instance : IsOrderedRing TauRatQ :=
  IsOrderedRing.of_mul_nonneg (fun a b ha hb => by
    simp only [TauRatQ.le_iff, TauRatQ.toRat_zero', TauRatQ.toRat_mul'] at *
    exact mul_nonneg ha hb)

instance : IsStrictOrderedRing TauRatQ :=
  IsStrictOrderedRing.of_mul_pos (fun a b ha hb => by
    simp only [TauRatQ.lt_iff, TauRatQ.toRat_zero', TauRatQ.toRat_mul'] at *
    exact mul_pos ha hb)

-- ============================================================
-- PART 3: Archimedean + DenselyOrdered
-- ============================================================

/-- **`Archimedean TauRatQ`** — for any `x : TauRatQ` and `0 < y`, some
    `n : ℕ` satisfies `x ≤ n • y`. Lifted from `ℚ`'s Archimedean property. -/
instance : Archimedean TauRatQ where
  arch x {y} hy := by
    simp only [TauRatQ.lt_iff, TauRatQ.toRat_zero'] at hy
    obtain ⟨n, hn⟩ := Archimedean.arch x.toRat hy
    refine ⟨n, ?_⟩
    simp only [TauRatQ.le_iff]
    -- Need to show: x.toRat ≤ (n • y).toRat
    -- (n • y).toRat = n • y.toRat by induction on n
    have h_nsmul : ∀ k : ℕ, (k • y).toRat = k • y.toRat := by
      intro k
      induction k with
      | zero => simp [TauRatQ.toRat_zero']
      | succ n ih =>
        rw [succ_nsmul, TauRatQ.toRat_add', ih, succ_nsmul]
    rw [h_nsmul]
    exact hn

/-- **`DenselyOrdered TauRatQ`** — between any two distinct elements there's
    another. Lifted from `ℚ`'s density. -/
instance : DenselyOrdered TauRatQ where
  dense x y h := by
    simp only [TauRatQ.lt_iff] at h
    obtain ⟨q, hq1, hq2⟩ := exists_between h
    -- q : Rat with x.toRat < q < y.toRat
    -- Lift q back to TauRatQ via TauRatQ.ofRat
    refine ⟨TauRatQ.ofRat q, ?_, ?_⟩
    · simp only [TauRatQ.lt_iff]
      have : (TauRatQ.ofRat q).toRat = q := TauRatQ.ofRat_toRat q
      rw [this]; exact hq1
    · simp only [TauRatQ.lt_iff]
      have : (TauRatQ.ofRat q).toRat = q := TauRatQ.ofRat_toRat q
      rw [this]; exact hq2

-- ============================================================
-- PART 4: Wave 44 synthesis theorem
-- ============================================================

/-- **Wave 44 synthesis: TauRatQ structural-significance packaging**.

    Eight-clause structural significance:
    1. `Field TauRatQ`           (Wave 40 — already established)
    2. `DecidableEq TauRatQ`     (this module)
    3. `LinearOrder TauRatQ`     (this module — full trichotomy)
    4. `IsStrictOrderedRing`     (this module)
    5. `Archimedean TauRatQ`     (this module)
    6. `DenselyOrdered TauRatQ`  (this module)
    7. The combination of (1)+(3)+(4) is the modern unbundled form of
       **`LinearOrderedField TauRatQ`** — the keystone classical
       typeclass that is structurally **impossible** on `TauRealQ`
       (cardinality wall) but immediate on `TauRatQ`.
    8. The cardinality boundary lives BETWEEN `TauRatQ` and `TauRealQ`,
       not between `TauRatQ` and orthodox `ℚ`.

    Every Mathlib theorem stated for `[LinearOrderedField K]` (modern
    unbundled form) now applies to TauRatQ — Galois theory, modular
    arithmetic at field level, classical algebraic number theory's
    field-theoretic content all unlock. -/
theorem h8_tauratq_mathlib_transport_synthesis :
    Nonempty (DecidableEq TauRatQ) ∧
    Nonempty (LinearOrder TauRatQ) ∧
    Nonempty (IsStrictOrderedRing TauRatQ) ∧
    Nonempty (Archimedean TauRatQ) ∧
    Nonempty (DenselyOrdered TauRatQ) ∧
    -- Order-preservation of the bijection (immediate from definitions)
    (∀ x y : TauRatQ, x ≤ y ↔ x.toRat ≤ y.toRat) :=
  ⟨⟨inferInstance⟩, ⟨inferInstance⟩, ⟨inferInstance⟩, ⟨inferInstance⟩,
   ⟨inferInstance⟩, fun x y => Iff.rfl⟩

end Tau.Boundary
