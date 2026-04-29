import TauLib.BookI.Boundary.NumberTower
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Algebra.Ring.Equiv
import Mathlib.Tactic.Ring

/-!
# TauLib.BookI.Boundary.TauIntQuotient

**Wave 39 — Mathlib Ring Bridge for TauInt** (Path C: Quotient + typeclass).

Wraps the τ-native `TauInt` (formal differences over `TauIdx`) into a
`Quotient` type `TauIntQ` and instantiates Mathlib's `CommRing`
typeclass on it, plus a `RingEquiv` to `Int`.

This is the cleanest "bridge into Mathlib" pattern:

- **`TauInt`** stays as the constructive representation — pairs of
  `TauIdx` values with an `equiv` relation. Computable, no Mathlib
  dependency for the construction itself.
- **`TauIntQ`** is the **Mathlib-bridge form** — a true `CommRing`
  with operations Lean-equal on the nose (after the quotient
  collapses `equiv` to `=`).
- **`TauIntQ ≃+* ℤ`** is the ring isomorphism witnessing that our
  τ-native integer construction satisfies all classical ring axioms.

After Wave 39, any Mathlib theorem about `CommRing` automatically
applies to `TauIntQ` — the τ-native side is now a first-class citizen
in the Mathlib algebraic ecosystem.

## Methodology check

Per the foundational-methodology audit (R4 Generation-First):

- **TauInt is τ-native**: built from TauIdx via formal differences, no
  Mathlib dependency in the construction.
- **TauIntQ is τ-native**: a `Quotient` of TauInt by the equiv setoid;
  no comprehension, all operations lifted via `Quotient.lift₂`.
- **The `CommRing` instance is an EARNED bridge**: each ring axiom is
  proven by pulling back through `toInt` to ℤ, where Mathlib's `ring`
  tactic discharges the obligation. The classical structure on ℤ is
  used as a *target*, not as a *source dependency*.
- **The `RingEquiv` to ℤ is a structural-witness theorem**, not a
  classical-existence axiom.

This satisfies the [E] Earned classification per chunk 0122 — the
construction uses only bounded fold + finite quotient + denotational
readout, with Lean proof.

## Registry Cross-References

- [I.D14]   TauInt (existing — formal differences)
- [I.T-W37] embed_int_into_d (Wave 37)
- [I.T-W39-CommRing]   `CommRing TauIntQ`
- [I.T-W39-RingEquiv]  `TauIntQ ≃+* ℤ`
-/

set_option autoImplicit false

namespace Tau.Boundary

open Tau.Denotation

-- ============================================================
-- PART 1: Setoid + Quotient construction
-- ============================================================

/-- The setoid on `TauInt` from the `equiv` relation. -/
def TauInt.setoid : Setoid TauInt where
  r := TauInt.equiv
  iseqv := ⟨TauInt.equiv_refl, TauInt.equiv_symm, TauInt.equiv_trans⟩

/-- The Quotient of `TauInt` by the equivalence relation.

    This is the **Mathlib-bridge form** of τ-native integers. It is
    isomorphic to `Int` and carries a full `CommRing` structure. -/
abbrev TauIntQ : Type := Quotient TauInt.setoid

/-- Canonical projection `TauInt → TauIntQ`. -/
def TauInt.toQ (a : TauInt) : TauIntQ := Quotient.mk TauInt.setoid a

@[simp] theorem TauInt.toQ_eq_iff (a b : TauInt) :
    a.toQ = b.toQ ↔ TauInt.equiv a b :=
  Quotient.eq

-- ============================================================
-- PART 2: toInt lifted to TauIntQ
-- ============================================================

/-- Lift `TauInt.toInt` to the quotient. Well-defined because
    `equiv_iff_toInt_eq` proves equiv classes have unique Int values. -/
def TauIntQ.toInt : TauIntQ → Int :=
  Quotient.lift TauInt.toInt (fun a b h => (equiv_iff_toInt_eq a b).mp h)

@[simp] theorem TauIntQ.toInt_mk (a : TauInt) :
    TauIntQ.toInt a.toQ = a.toInt := rfl

-- ============================================================
-- PART 3: Ring operations on TauIntQ (via Quotient.lift)
-- ============================================================

/-- `add` respects equiv: if `a ≈ a'` and `b ≈ b'`, then `add a b ≈ add a' b'`. -/
theorem TauInt.add_respects_equiv (a₁ a₂ b₁ b₂ : TauInt)
    (ha : TauInt.equiv a₁ a₂) (hb : TauInt.equiv b₁ b₂) :
    TauInt.equiv (a₁.add b₁) (a₂.add b₂) := by
  rw [equiv_iff_toInt_eq] at ha hb ⊢
  rw [toInt_add, toInt_add, ha, hb]

/-- `mul` respects equiv. -/
theorem TauInt.mul_respects_equiv (a₁ a₂ b₁ b₂ : TauInt)
    (ha : TauInt.equiv a₁ a₂) (hb : TauInt.equiv b₁ b₂) :
    TauInt.equiv (a₁.mul b₁) (a₂.mul b₂) := by
  rw [equiv_iff_toInt_eq] at ha hb ⊢
  rw [toInt_mul, toInt_mul, ha, hb]

/-- `negate` respects equiv. -/
theorem TauInt.negate_respects_equiv (a₁ a₂ : TauInt) (h : TauInt.equiv a₁ a₂) :
    TauInt.equiv a₁.negate a₂.negate := by
  rw [equiv_iff_toInt_eq] at h ⊢
  rw [toInt_negate, toInt_negate, h]

/-- Quotient-level addition. -/
def TauIntQ.add : TauIntQ → TauIntQ → TauIntQ :=
  Quotient.lift₂ (fun a b => (a.add b).toQ)
    (fun a₁ b₁ a₂ b₂ ha hb => Quotient.sound (TauInt.add_respects_equiv a₁ a₂ b₁ b₂ ha hb))

/-- Quotient-level multiplication. -/
def TauIntQ.mul : TauIntQ → TauIntQ → TauIntQ :=
  Quotient.lift₂ (fun a b => (a.mul b).toQ)
    (fun a₁ b₁ a₂ b₂ ha hb => Quotient.sound (TauInt.mul_respects_equiv a₁ a₂ b₁ b₂ ha hb))

/-- Quotient-level negation. -/
def TauIntQ.neg : TauIntQ → TauIntQ :=
  Quotient.lift (fun a => a.negate.toQ)
    (fun a b h => Quotient.sound (TauInt.negate_respects_equiv a b h))

/-- Quotient-level zero. -/
def TauIntQ.zero : TauIntQ := TauInt.zero.toQ

/-- Quotient-level one. -/
def TauIntQ.one : TauIntQ := TauInt.one.toQ

@[simp] theorem TauIntQ.add_mk (a b : TauInt) :
    TauIntQ.add a.toQ b.toQ = (a.add b).toQ := rfl

@[simp] theorem TauIntQ.mul_mk (a b : TauInt) :
    TauIntQ.mul a.toQ b.toQ = (a.mul b).toQ := rfl

@[simp] theorem TauIntQ.neg_mk (a : TauInt) :
    TauIntQ.neg a.toQ = a.negate.toQ := rfl

-- ============================================================
-- PART 4: toInt is a ring homomorphism on TauIntQ
-- ============================================================

theorem TauIntQ.toInt_add (x y : TauIntQ) :
    (TauIntQ.add x y).toInt = x.toInt + y.toInt := by
  refine Quotient.inductionOn₂ x y (fun a b => ?_)
  exact Tau.Boundary.toInt_add a b

theorem TauIntQ.toInt_mul (x y : TauIntQ) :
    (TauIntQ.mul x y).toInt = x.toInt * y.toInt := by
  refine Quotient.inductionOn₂ x y (fun a b => ?_)
  exact Tau.Boundary.toInt_mul a b

@[simp] theorem TauIntQ.toInt_neg (x : TauIntQ) :
    (TauIntQ.neg x).toInt = -x.toInt := by
  refine Quotient.inductionOn x (fun a => ?_)
  show a.negate.toInt = -a.toInt
  exact toInt_negate a

@[simp] theorem TauIntQ.toInt_zero : TauIntQ.zero.toInt = 0 := rfl

@[simp] theorem TauIntQ.toInt_one : TauIntQ.one.toInt = 1 := rfl

/-- Two TauIntQ values are equal iff they have the same `toInt`. -/
theorem TauIntQ.eq_iff_toInt_eq (x y : TauIntQ) :
    x = y ↔ x.toInt = y.toInt := by
  refine Quotient.inductionOn₂ x y (fun a b => ?_)
  show (a.toQ = b.toQ) ↔ (a.toInt = b.toInt)
  rw [TauInt.toQ_eq_iff, equiv_iff_toInt_eq]

-- ============================================================
-- PART 5: CommRing instance on TauIntQ (KEYSTONE)
-- ============================================================

/-- Helper: convert a ring axiom on `TauIntQ` to a ring axiom on `Int`
    via the homomorphism `toInt`. -/
private theorem TauIntQ.lift_via_toInt (x y : TauIntQ)
    (h : x.toInt = y.toInt) : x = y :=
  (TauIntQ.eq_iff_toInt_eq x y).mpr h

-- Bare typeclass instances so `nsmulRec` / `zsmulRec` can resolve
-- inside the `CommRing` instance below.
instance : Zero TauIntQ := ⟨TauIntQ.zero⟩
instance : One TauIntQ := ⟨TauIntQ.one⟩
instance : Add TauIntQ := ⟨TauIntQ.add⟩
instance : Mul TauIntQ := ⟨TauIntQ.mul⟩
instance : Neg TauIntQ := ⟨TauIntQ.neg⟩

/-- **Wave 39 KEYSTONE: CommRing instance on TauIntQ**.

    Every ring axiom is proven by:
    1. Lifting the obligation to `toInt` via the homomorphism theorems
    2. Reducing to a Mathlib `Int` ring identity
    3. Discharging via Mathlib's `ring` tactic.

    This makes TauIntQ a first-class citizen of Mathlib's algebraic
    ecosystem. -/
instance : CommRing TauIntQ where
  add := TauIntQ.add
  mul := TauIntQ.mul
  neg := TauIntQ.neg
  zero := TauIntQ.zero
  one := TauIntQ.one
  add_assoc x y z := by
    apply TauIntQ.lift_via_toInt
    change TauIntQ.toInt (TauIntQ.add (TauIntQ.add x y) z) =
           TauIntQ.toInt (TauIntQ.add x (TauIntQ.add y z))
    simp only [TauIntQ.toInt_add]; ring
  zero_add x := by
    apply TauIntQ.lift_via_toInt
    change TauIntQ.toInt (TauIntQ.add TauIntQ.zero x) = TauIntQ.toInt x
    simp only [TauIntQ.toInt_add, TauIntQ.toInt_zero]; ring
  add_zero x := by
    apply TauIntQ.lift_via_toInt
    change TauIntQ.toInt (TauIntQ.add x TauIntQ.zero) = TauIntQ.toInt x
    simp only [TauIntQ.toInt_add, TauIntQ.toInt_zero]; ring
  add_comm x y := by
    apply TauIntQ.lift_via_toInt
    change TauIntQ.toInt (TauIntQ.add x y) = TauIntQ.toInt (TauIntQ.add y x)
    simp only [TauIntQ.toInt_add]; ring
  mul_assoc x y z := by
    apply TauIntQ.lift_via_toInt
    change TauIntQ.toInt (TauIntQ.mul (TauIntQ.mul x y) z) =
           TauIntQ.toInt (TauIntQ.mul x (TauIntQ.mul y z))
    simp only [TauIntQ.toInt_mul]; ring
  one_mul x := by
    apply TauIntQ.lift_via_toInt
    change TauIntQ.toInt (TauIntQ.mul TauIntQ.one x) = TauIntQ.toInt x
    simp only [TauIntQ.toInt_mul, TauIntQ.toInt_one]; ring
  mul_one x := by
    apply TauIntQ.lift_via_toInt
    change TauIntQ.toInt (TauIntQ.mul x TauIntQ.one) = TauIntQ.toInt x
    simp only [TauIntQ.toInt_mul, TauIntQ.toInt_one]; ring
  left_distrib x y z := by
    apply TauIntQ.lift_via_toInt
    change TauIntQ.toInt (TauIntQ.mul x (TauIntQ.add y z)) =
           TauIntQ.toInt (TauIntQ.add (TauIntQ.mul x y) (TauIntQ.mul x z))
    simp only [TauIntQ.toInt_mul, TauIntQ.toInt_add]; ring
  right_distrib x y z := by
    apply TauIntQ.lift_via_toInt
    change TauIntQ.toInt (TauIntQ.mul (TauIntQ.add x y) z) =
           TauIntQ.toInt (TauIntQ.add (TauIntQ.mul x z) (TauIntQ.mul y z))
    simp only [TauIntQ.toInt_mul, TauIntQ.toInt_add]; ring
  zero_mul x := by
    apply TauIntQ.lift_via_toInt
    change TauIntQ.toInt (TauIntQ.mul TauIntQ.zero x) = TauIntQ.toInt TauIntQ.zero
    simp only [TauIntQ.toInt_mul, TauIntQ.toInt_zero]; ring
  mul_zero x := by
    apply TauIntQ.lift_via_toInt
    change TauIntQ.toInt (TauIntQ.mul x TauIntQ.zero) = TauIntQ.toInt TauIntQ.zero
    simp only [TauIntQ.toInt_mul, TauIntQ.toInt_zero]; ring
  mul_comm x y := by
    apply TauIntQ.lift_via_toInt
    change TauIntQ.toInt (TauIntQ.mul x y) = TauIntQ.toInt (TauIntQ.mul y x)
    simp only [TauIntQ.toInt_mul]; ring
  neg_add_cancel x := by
    apply TauIntQ.lift_via_toInt
    change TauIntQ.toInt (TauIntQ.add (TauIntQ.neg x) x) = TauIntQ.toInt TauIntQ.zero
    simp only [TauIntQ.toInt_add, TauIntQ.toInt_neg, TauIntQ.toInt_zero]; ring
  nsmul := nsmulRec
  zsmul := zsmulRec

-- ============================================================
-- PART 6: RingEquiv TauIntQ ≃+* ℤ (the bridge keystone)
-- ============================================================

/-- Embed `Int` into `TauIntQ` via the τ-native fromInt construction. -/
def TauIntQ.ofInt (n : Int) : TauIntQ :=
  if h : n ≥ 0 then (⟨n.toNat, 0⟩ : TauInt).toQ
  else (⟨0, (-n).toNat⟩ : TauInt).toQ

theorem TauIntQ.ofInt_toInt (n : Int) : (TauIntQ.ofInt n).toInt = n := by
  unfold TauIntQ.ofInt
  by_cases h : n ≥ 0
  · simp only [h, ↓reduceDIte, TauIntQ.toInt_mk, TauInt.toInt]
    push_cast
    omega
  · push_neg at h
    have hneg : -n ≥ 0 := by omega
    have hcast : ((-n).toNat : Int) = -n := Int.toNat_of_nonneg hneg
    simp only [show ¬ n ≥ 0 from not_le.mpr h, ↓reduceDIte, TauIntQ.toInt_mk, TauInt.toInt]
    push_cast
    omega

theorem TauIntQ.toInt_ofInt (x : TauIntQ) : TauIntQ.ofInt x.toInt = x := by
  rw [TauIntQ.eq_iff_toInt_eq, TauIntQ.ofInt_toInt]

/-- **Wave 39 keystone-of-keystones: `TauIntQ ≃+* ℤ` ring isomorphism**.

    This is the formal statement that our τ-native integer construction
    is **isomorphic as a ring** to Mathlib's `Int`. Every ring property
    transfers cleanly between the two via this isomorphism. -/
def TauIntQ.ringEquivInt : TauIntQ ≃+* ℤ where
  toFun := TauIntQ.toInt
  invFun := TauIntQ.ofInt
  left_inv := TauIntQ.toInt_ofInt
  right_inv := TauIntQ.ofInt_toInt
  map_add' x y := by
    show TauIntQ.toInt (x + y) = TauIntQ.toInt x + TauIntQ.toInt y
    exact TauIntQ.toInt_add x y
  map_mul' x y := by
    show TauIntQ.toInt (x * y) = TauIntQ.toInt x * TauIntQ.toInt y
    exact TauIntQ.toInt_mul x y

-- ============================================================
-- PART 7: Wave 39 synthesis theorem
-- ============================================================

/-- **Wave 39 H8 Mathlib-Ring-Bridge synthesis (KEYSTONE)**.

    Packages the structural significance of the τ-native integer
    construction satisfying classical ring axioms:

    1. **TauIntQ is a `CommRing`**: full Mathlib typeclass instance
    2. **TauIntQ ≃+* ℤ**: ring isomorphism to Mathlib's `Int`
    3. **toInt homomorphism**: respects +, *, neg, 0, 1
    4. **Round-trip**: `ofInt ∘ toInt = id` and `toInt ∘ ofInt = id`

    Together these establish that the τ-native integer construction
    (formal differences over TauIdx, with explicit equiv quotient) is
    a **bridge into Mathlib's algebraic ecosystem** — every Mathlib
    theorem about CommRings now automatically applies to TauIntQ. -/
theorem h8_tauint_mathlib_bridge_synthesis :
    -- Clause 1: ring isomorphism to ℤ exists
    Nonempty (TauIntQ ≃+* ℤ) ∧
    -- Clause 2: toInt preserves addition
    (∀ x y : TauIntQ, (x + y).toInt = x.toInt + y.toInt) ∧
    -- Clause 3: toInt preserves multiplication
    (∀ x y : TauIntQ, (x * y).toInt = x.toInt * y.toInt) ∧
    -- Clause 4: toInt preserves zero and one
    (TauIntQ.zero.toInt = 0 ∧ TauIntQ.one.toInt = 1) ∧
    -- Clause 5: round-trip
    (∀ n : Int, (TauIntQ.ofInt n).toInt = n) :=
  ⟨⟨TauIntQ.ringEquivInt⟩,
   TauIntQ.toInt_add,
   TauIntQ.toInt_mul,
   ⟨TauIntQ.toInt_zero, TauIntQ.toInt_one⟩,
   TauIntQ.ofInt_toInt⟩

end Tau.Boundary
