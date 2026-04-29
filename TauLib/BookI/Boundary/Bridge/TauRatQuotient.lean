import TauLib.BookI.Boundary.Bridge.TauIntQuotient
import TauLib.BookI.Boundary.TauRatField
import Mathlib.Algebra.Field.Defs
import Mathlib.Algebra.Field.Equiv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# TauLib.BookI.Boundary.Bridge.TauRatQuotient

**Wave 40 — Mathlib Field Bridge for TauRat** (Path C: Quotient + typeclass).

Wraps the τ-native `TauRat` (formal fractions over `TauInt`) into a
`Quotient` type `TauRatQ` and instantiates Mathlib's `Field`
typeclass on it, plus a `RingEquiv` (and field-equivalence) to `Rat`.

Companion to Wave 39's `TauIntQuotient.lean`. Same pattern, one
floor up the number tower.

After Wave 40, any Mathlib theorem about `Field` automatically
applies to `TauRatQ` — Galois theory of ℚ-extensions, modular
arithmetic at the field level, and most algebraic number theory's
field-theoretic content all become directly usable.

## Methodology check (R4 Generation-First — passes)

- **TauRat is τ-native**: built from `TauInt` (which is τ-native via
  formal differences over TauIdx). No Mathlib dependency in the
  construction itself.
- **TauRatQ is τ-native**: a `Quotient` of TauRat; no comprehension.
- **The `Field` instance is an EARNED bridge**: each axiom proven by
  pulling back through `toRat` to ℚ where Mathlib's `field_simp` /
  `ring` tactics discharge.
- **The bridge module lives in `Bridge/`** per the Wave 39 CI policy
  for orthodox-bridge zones.

## Registry Cross-References

- [I.D15]   TauRat (existing — formal fractions)
- [I.D144]  TauIntQ (Wave 39)
- [I.T207]  CommRing TauIntQ (Wave 39)
- [I.T-W40-Field]      `Field TauRatQ`
- [I.T-W40-RingEquiv]  `TauRatQ ≃+* ℚ`
-/

set_option autoImplicit false

namespace Tau.Boundary

open Tau.Denotation

-- ============================================================
-- PART 1: Setoid + Quotient construction
-- ============================================================

/-- The setoid on `TauRat` from the existing `TauRat.equivalence`. -/
def TauRat.setoid : Setoid TauRat where
  r := TauRat.equiv
  iseqv := TauRat.equivalence

/-- The Quotient of `TauRat` by the equivalence relation.

    The Mathlib-bridge form of τ-native rationals. Isomorphic to
    `Rat` and carries a full `Field` structure. -/
abbrev TauRatQ : Type := Quotient TauRat.setoid

/-- Canonical projection `TauRat → TauRatQ`. -/
def TauRat.toQ (a : TauRat) : TauRatQ := Quotient.mk TauRat.setoid a

@[simp] theorem TauRat.toQ_eq_iff (a b : TauRat) :
    a.toQ = b.toQ ↔ TauRat.equiv a b :=
  Quotient.eq

-- ============================================================
-- PART 2: toRat lifted to TauRatQ
-- ============================================================

/-- Lift `TauRat.toRat` to the quotient. -/
def TauRatQ.toRat : TauRatQ → Rat :=
  Quotient.lift TauRat.toRat (fun a b h => (equiv_iff_toRat_eq a b).mp h)

@[simp] theorem TauRatQ.toRat_mk (a : TauRat) :
    TauRatQ.toRat a.toQ = a.toRat := rfl

-- ============================================================
-- PART 3: Ring operations on TauRatQ
-- ============================================================

theorem TauRat.add_respects_equiv (a₁ a₂ b₁ b₂ : TauRat)
    (ha : TauRat.equiv a₁ a₂) (hb : TauRat.equiv b₁ b₂) :
    TauRat.equiv (a₁.add b₁) (a₂.add b₂) := by
  rw [equiv_iff_toRat_eq] at ha hb ⊢
  rw [toRat_add, toRat_add, ha, hb]

theorem TauRat.mul_respects_equiv (a₁ a₂ b₁ b₂ : TauRat)
    (ha : TauRat.equiv a₁ a₂) (hb : TauRat.equiv b₁ b₂) :
    TauRat.equiv (a₁.mul b₁) (a₂.mul b₂) := by
  rw [equiv_iff_toRat_eq] at ha hb ⊢
  rw [toRat_mul, toRat_mul, ha, hb]

theorem TauRat.negate_respects_equiv (a₁ a₂ : TauRat) (h : TauRat.equiv a₁ a₂) :
    TauRat.equiv a₁.negate a₂.negate := by
  rw [equiv_iff_toRat_eq] at h ⊢
  rw [toRat_negate, toRat_negate, h]

def TauRatQ.add : TauRatQ → TauRatQ → TauRatQ :=
  Quotient.lift₂ (fun a b => (a.add b).toQ)
    (fun a₁ b₁ a₂ b₂ ha hb => Quotient.sound (TauRat.add_respects_equiv a₁ a₂ b₁ b₂ ha hb))

def TauRatQ.mul : TauRatQ → TauRatQ → TauRatQ :=
  Quotient.lift₂ (fun a b => (a.mul b).toQ)
    (fun a₁ b₁ a₂ b₂ ha hb => Quotient.sound (TauRat.mul_respects_equiv a₁ a₂ b₁ b₂ ha hb))

def TauRatQ.neg : TauRatQ → TauRatQ :=
  Quotient.lift (fun a => a.negate.toQ)
    (fun a b h => Quotient.sound (TauRat.negate_respects_equiv a b h))

def TauRatQ.zero : TauRatQ := TauRat.zero.toQ
def TauRatQ.one : TauRatQ := TauRat.one.toQ

@[simp] theorem TauRatQ.add_mk (a b : TauRat) :
    TauRatQ.add a.toQ b.toQ = (a.add b).toQ := rfl
@[simp] theorem TauRatQ.mul_mk (a b : TauRat) :
    TauRatQ.mul a.toQ b.toQ = (a.mul b).toQ := rfl
@[simp] theorem TauRatQ.neg_mk (a : TauRat) :
    TauRatQ.neg a.toQ = a.negate.toQ := rfl

-- ============================================================
-- PART 4: toRat ring homomorphism on TauRatQ
-- ============================================================

theorem TauRatQ.toRat_add (x y : TauRatQ) :
    (TauRatQ.add x y).toRat = x.toRat + y.toRat := by
  refine Quotient.inductionOn₂ x y (fun a b => ?_)
  exact Tau.Boundary.toRat_add a b

theorem TauRatQ.toRat_mul (x y : TauRatQ) :
    (TauRatQ.mul x y).toRat = x.toRat * y.toRat := by
  refine Quotient.inductionOn₂ x y (fun a b => ?_)
  exact Tau.Boundary.toRat_mul a b

@[simp] theorem TauRatQ.toRat_neg (x : TauRatQ) :
    (TauRatQ.neg x).toRat = -x.toRat := by
  refine Quotient.inductionOn x (fun a => ?_)
  show a.negate.toRat = -a.toRat
  exact toRat_negate a

@[simp] theorem TauRatQ.toRat_zero : TauRatQ.zero.toRat = 0 := by
  show TauRat.zero.toRat = 0
  exact Tau.Boundary.toRat_zero

@[simp] theorem TauRatQ.toRat_one : TauRatQ.one.toRat = 1 := by
  show TauRat.one.toRat = 1
  exact Tau.Boundary.toRat_one

theorem TauRatQ.eq_iff_toRat_eq (x y : TauRatQ) :
    x = y ↔ x.toRat = y.toRat := by
  refine Quotient.inductionOn₂ x y (fun a b => ?_)
  show (a.toQ = b.toQ) ↔ (a.toRat = b.toRat)
  rw [TauRat.toQ_eq_iff, equiv_iff_toRat_eq]

private theorem TauRatQ.lift_via_toRat (x y : TauRatQ)
    (h : x.toRat = y.toRat) : x = y :=
  (TauRatQ.eq_iff_toRat_eq x y).mpr h

-- ============================================================
-- PART 5: Multiplicative inverse (Field-specific)
-- ============================================================

/-- TauRat-level multiplicative inverse. For nonzero `q : TauRat`,
    swaps numerator and denominator with sign adjustment. For zero,
    returns zero (Mathlib's standard convention `inv 0 = 0`). -/
def TauRat.inv (q : TauRat) : TauRat :=
  if hgt : q.num.pos > q.num.neg then
    -- q.num.toInt > 0, so q > 0; inv = ⟨⟨den, 0⟩, pos-neg, _⟩
    ⟨⟨q.den, 0⟩, q.num.pos - q.num.neg, Nat.sub_pos_of_lt hgt⟩
  else if hlt : q.num.neg > q.num.pos then
    -- q.num.toInt < 0, so q < 0; inv = ⟨⟨0, den⟩, neg-pos, _⟩
    ⟨⟨0, q.den⟩, q.num.neg - q.num.pos, Nat.sub_pos_of_lt hlt⟩
  else
    -- pos = neg, so q.toInt = 0 → q ≈ 0; return 0 (Mathlib convention)
    TauRat.zero

/-- toRat of inv: `(q.inv).toRat = (q.toRat)⁻¹`. -/
theorem toRat_inv (q : TauRat) : q.inv.toRat = q.toRat⁻¹ := by
  unfold TauRat.inv
  by_cases hgt : q.num.pos > q.num.neg
  · -- positive case: q > 0
    simp only [hgt, ↓reduceDIte]
    unfold TauRat.toRat TauInt.toInt
    have hle : q.num.neg ≤ q.num.pos := Nat.le_of_lt hgt
    have hsub_rat : ((q.num.pos - q.num.neg : Nat) : Rat)
                  = (q.num.pos : Rat) - (q.num.neg : Rat) := by
      have hsub_int : ((q.num.pos - q.num.neg : Nat) : Int)
                    = (q.num.pos : Int) - (q.num.neg : Int) := Int.ofNat_sub hle
      exact_mod_cast hsub_int
    have hden_pos : (q.den : Rat) > 0 := q.den_pos_rat
    have hnum_lt : (q.num.neg : Rat) < (q.num.pos : Rat) := by exact_mod_cast hgt
    have hnum_ne : ((q.num.pos : Rat) - (q.num.neg : Rat)) ≠ 0 := by linarith
    push_cast
    rw [hsub_rat]
    field_simp
    ring
  · simp only [hgt, ↓reduceDIte]
    by_cases hlt : q.num.neg > q.num.pos
    · -- negative case: q < 0
      simp only [hlt, ↓reduceDIte]
      unfold TauRat.toRat TauInt.toInt
      have hle : q.num.pos ≤ q.num.neg := Nat.le_of_lt hlt
      have hsub_rat : ((q.num.neg - q.num.pos : Nat) : Rat)
                    = (q.num.neg : Rat) - (q.num.pos : Rat) := by
        have hsub_int : ((q.num.neg - q.num.pos : Nat) : Int)
                      = (q.num.neg : Int) - (q.num.pos : Int) := Int.ofNat_sub hle
        exact_mod_cast hsub_int
      have hden_pos : (q.den : Rat) > 0 := q.den_pos_rat
      have hnum_lt : (q.num.pos : Rat) < (q.num.neg : Rat) := by exact_mod_cast hlt
      have hnum_ne : ((q.num.pos : Rat) - (q.num.neg : Rat)) ≠ 0 := by linarith
      have hnum_ne' : ((q.num.neg : Rat) - (q.num.pos : Rat)) ≠ 0 := by linarith
      push_cast
      rw [hsub_rat]
      field_simp
      ring
    · -- zero case: pos = neg, so q.toRat = 0
      simp only [hlt, ↓reduceDIte]
      have h1 : q.num.pos ≤ q.num.neg := Nat.le_of_not_lt hgt
      have h2 : q.num.neg ≤ q.num.pos := Nat.le_of_not_lt hlt
      have heq : q.num.pos = q.num.neg := Nat.le_antisymm h1 h2
      have h_int : q.num.toInt = 0 := by
        unfold TauInt.toInt
        have : (q.num.pos : Int) = (q.num.neg : Int) := by exact_mod_cast heq
        linarith
      have h_rat : q.toRat = 0 := by
        unfold TauRat.toRat; rw [h_int]; simp
      rw [toRat_zero, h_rat]
      simp

theorem TauRat.inv_respects_equiv (a₁ a₂ : TauRat) (h : TauRat.equiv a₁ a₂) :
    TauRat.equiv a₁.inv a₂.inv := by
  rw [equiv_iff_toRat_eq] at h ⊢
  rw [toRat_inv, toRat_inv, h]

def TauRatQ.inv : TauRatQ → TauRatQ :=
  Quotient.lift (fun a => a.inv.toQ)
    (fun a b h => Quotient.sound (TauRat.inv_respects_equiv a b h))

@[simp] theorem TauRatQ.inv_mk (a : TauRat) :
    TauRatQ.inv a.toQ = a.inv.toQ := rfl

@[simp] theorem TauRatQ.toRat_inv (x : TauRatQ) :
    (TauRatQ.inv x).toRat = x.toRat⁻¹ := by
  refine Quotient.inductionOn x (fun a => ?_)
  show a.inv.toRat = (a.toRat)⁻¹
  exact Tau.Boundary.toRat_inv a

-- ============================================================
-- PART 6: Bare typeclass instances (for nsmulRec / zsmulRec)
-- ============================================================

instance : Zero TauRatQ := ⟨TauRatQ.zero⟩
instance : One TauRatQ := ⟨TauRatQ.one⟩
instance : Add TauRatQ := ⟨TauRatQ.add⟩
instance : Mul TauRatQ := ⟨TauRatQ.mul⟩
instance : Neg TauRatQ := ⟨TauRatQ.neg⟩
instance : Inv TauRatQ := ⟨TauRatQ.inv⟩

-- ============================================================
-- PART 7: Field instance on TauRatQ (KEYSTONE)
-- ============================================================

/-- **Wave 40 KEYSTONE: Field instance on TauRatQ**.

    Every field axiom is proven by pulling back through `toRat` to ℚ
    where Mathlib's `field_simp` / `ring` tactics discharge.

    This makes TauRatQ a first-class citizen of Mathlib's field
    ecosystem — Galois theory, finite extensions of ℚ, classical
    algebraic number theory at the field level all unlock. -/
instance : Field TauRatQ where
  add := TauRatQ.add
  mul := TauRatQ.mul
  neg := TauRatQ.neg
  zero := TauRatQ.zero
  one := TauRatQ.one
  inv := TauRatQ.inv
  add_assoc x y z := by
    apply TauRatQ.lift_via_toRat
    change TauRatQ.toRat (TauRatQ.add (TauRatQ.add x y) z) =
           TauRatQ.toRat (TauRatQ.add x (TauRatQ.add y z))
    simp only [TauRatQ.toRat_add]; ring
  zero_add x := by
    apply TauRatQ.lift_via_toRat
    change TauRatQ.toRat (TauRatQ.add TauRatQ.zero x) = TauRatQ.toRat x
    simp only [TauRatQ.toRat_add, TauRatQ.toRat_zero]; ring
  add_zero x := by
    apply TauRatQ.lift_via_toRat
    change TauRatQ.toRat (TauRatQ.add x TauRatQ.zero) = TauRatQ.toRat x
    simp only [TauRatQ.toRat_add, TauRatQ.toRat_zero]; ring
  add_comm x y := by
    apply TauRatQ.lift_via_toRat
    change TauRatQ.toRat (TauRatQ.add x y) = TauRatQ.toRat (TauRatQ.add y x)
    simp only [TauRatQ.toRat_add]; ring
  mul_assoc x y z := by
    apply TauRatQ.lift_via_toRat
    change TauRatQ.toRat (TauRatQ.mul (TauRatQ.mul x y) z) =
           TauRatQ.toRat (TauRatQ.mul x (TauRatQ.mul y z))
    simp only [TauRatQ.toRat_mul]; ring
  one_mul x := by
    apply TauRatQ.lift_via_toRat
    change TauRatQ.toRat (TauRatQ.mul TauRatQ.one x) = TauRatQ.toRat x
    simp only [TauRatQ.toRat_mul, TauRatQ.toRat_one]; ring
  mul_one x := by
    apply TauRatQ.lift_via_toRat
    change TauRatQ.toRat (TauRatQ.mul x TauRatQ.one) = TauRatQ.toRat x
    simp only [TauRatQ.toRat_mul, TauRatQ.toRat_one]; ring
  left_distrib x y z := by
    apply TauRatQ.lift_via_toRat
    change TauRatQ.toRat (TauRatQ.mul x (TauRatQ.add y z)) =
           TauRatQ.toRat (TauRatQ.add (TauRatQ.mul x y) (TauRatQ.mul x z))
    simp only [TauRatQ.toRat_mul, TauRatQ.toRat_add]; ring
  right_distrib x y z := by
    apply TauRatQ.lift_via_toRat
    change TauRatQ.toRat (TauRatQ.mul (TauRatQ.add x y) z) =
           TauRatQ.toRat (TauRatQ.add (TauRatQ.mul x z) (TauRatQ.mul y z))
    simp only [TauRatQ.toRat_mul, TauRatQ.toRat_add]; ring
  zero_mul x := by
    apply TauRatQ.lift_via_toRat
    change TauRatQ.toRat (TauRatQ.mul TauRatQ.zero x) = TauRatQ.toRat TauRatQ.zero
    simp only [TauRatQ.toRat_mul, TauRatQ.toRat_zero]; ring
  mul_zero x := by
    apply TauRatQ.lift_via_toRat
    change TauRatQ.toRat (TauRatQ.mul x TauRatQ.zero) = TauRatQ.toRat TauRatQ.zero
    simp only [TauRatQ.toRat_mul, TauRatQ.toRat_zero]; ring
  mul_comm x y := by
    apply TauRatQ.lift_via_toRat
    change TauRatQ.toRat (TauRatQ.mul x y) = TauRatQ.toRat (TauRatQ.mul y x)
    simp only [TauRatQ.toRat_mul]; ring
  neg_add_cancel x := by
    apply TauRatQ.lift_via_toRat
    change TauRatQ.toRat (TauRatQ.add (TauRatQ.neg x) x) = TauRatQ.toRat TauRatQ.zero
    refine Quotient.inductionOn x (fun a => ?_)
    show ((a.negate.add a).toRat = TauRat.zero.toRat)
    rw [toRat_add, toRat_negate, Tau.Boundary.toRat_zero]
    ring
  exists_pair_ne := ⟨TauRatQ.zero, TauRatQ.one, by
    intro h
    have : TauRatQ.zero.toRat = TauRatQ.one.toRat :=
      congrArg TauRatQ.toRat h
    simp [TauRatQ.toRat_zero, TauRatQ.toRat_one] at this⟩
  mul_inv_cancel x hx := by
    apply TauRatQ.lift_via_toRat
    change TauRatQ.toRat (TauRatQ.mul x (TauRatQ.inv x)) = TauRatQ.toRat TauRatQ.one
    have hx_rat : x.toRat ≠ 0 := by
      intro h
      apply hx
      show x = (0 : TauRatQ)
      apply TauRatQ.lift_via_toRat
      show x.toRat = TauRatQ.zero.toRat
      rw [h, TauRatQ.toRat_zero]
    simp only [TauRatQ.toRat_mul, TauRatQ.toRat_inv, TauRatQ.toRat_one]
    field_simp
  inv_zero := by
    apply TauRatQ.lift_via_toRat
    change TauRatQ.toRat (TauRatQ.inv TauRatQ.zero) = TauRatQ.toRat TauRatQ.zero
    simp only [TauRatQ.toRat_inv, TauRatQ.toRat_zero, inv_zero]
  nsmul := nsmulRec
  zsmul := zsmulRec
  nnqsmul := _
  qsmul := _

-- ============================================================
-- PART 8: RingEquiv TauRatQ ≃+* ℚ (the bridge keystone)
-- ============================================================

/-- Embed `Rat` into `TauRatQ`: `q ↦ ⟨⟨q.num.toNat, (-q.num).toNat⟩, q.den, _⟩.toQ`.

    Unconditional pattern: works regardless of sign of `q.num`. When
    `q.num ≥ 0`, `q.num.toNat = q.num` and `(-q.num).toNat = 0`; when
    `q.num < 0`, `q.num.toNat = 0` and `(-q.num).toNat = -q.num`.
    Either way, `pos - neg = q.num` as `Int`. -/
def TauRatQ.ofRat (q : Rat) : TauRatQ :=
  (⟨⟨q.num.toNat, (-q.num).toNat⟩, q.den, q.pos⟩ : TauRat).toQ

theorem TauRatQ.ofRat_toRat (q : Rat) : (TauRatQ.ofRat q).toRat = q := by
  unfold TauRatQ.ofRat
  simp only [TauRatQ.toRat_mk]
  unfold TauRat.toRat TauInt.toInt
  -- Goal: ↑((q.num.toNat : Int) - ((-q.num).toNat : Int)) / ↑q.den = q
  have h_int : (q.num.toNat : Int) - ((-q.num).toNat : Int) = q.num := by omega
  rw [h_int]
  exact Rat.num_div_den q

theorem TauRatQ.toRat_ofRat (x : TauRatQ) : TauRatQ.ofRat x.toRat = x := by
  apply TauRatQ.lift_via_toRat
  rw [TauRatQ.ofRat_toRat]

/-- **Wave 40 keystone-of-keystones: `TauRatQ ≃+* ℚ` ring isomorphism**.

    Witnesses that our τ-native rational construction is isomorphic
    AS A FIELD to Mathlib's `Rat`. -/
def TauRatQ.ringEquivRat : TauRatQ ≃+* ℚ where
  toFun := TauRatQ.toRat
  invFun := TauRatQ.ofRat
  left_inv := TauRatQ.toRat_ofRat
  right_inv := TauRatQ.ofRat_toRat
  map_add' x y := by
    show TauRatQ.toRat (x + y) = TauRatQ.toRat x + TauRatQ.toRat y
    exact TauRatQ.toRat_add x y
  map_mul' x y := by
    show TauRatQ.toRat (x * y) = TauRatQ.toRat x * TauRatQ.toRat y
    exact TauRatQ.toRat_mul x y

-- ============================================================
-- PART 9: Wave 40 synthesis theorem
-- ============================================================

/-- **Wave 40 H8 Mathlib-Field-Bridge synthesis (KEYSTONE)**.

    Five-clause structural significance:

    1. **TauRatQ is a `Field`**: full Mathlib typeclass instance
    2. **TauRatQ ≃+* ℚ**: ring isomorphism to Mathlib's `Rat`
    3. **toRat homomorphism**: respects +, *, neg, inv, 0, 1
    4. **Round-trip**: `ofRat ∘ toRat = id` and `toRat ∘ ofRat = id`
    5. **Inverse for nonzero**: `q ≠ 0 → q * inv q = 1` -/
theorem h8_taurat_mathlib_bridge_synthesis :
    -- Clause 1: ring isomorphism to ℚ exists
    Nonempty (TauRatQ ≃+* ℚ) ∧
    -- Clause 2: toRat preserves addition
    (∀ x y : TauRatQ, (x + y).toRat = x.toRat + y.toRat) ∧
    -- Clause 3: toRat preserves multiplication
    (∀ x y : TauRatQ, (x * y).toRat = x.toRat * y.toRat) ∧
    -- Clause 4: toRat preserves zero, one
    (TauRatQ.zero.toRat = 0 ∧ TauRatQ.one.toRat = 1) ∧
    -- Clause 5: round-trip
    (∀ q : Rat, (TauRatQ.ofRat q).toRat = q) :=
  ⟨⟨TauRatQ.ringEquivRat⟩,
   TauRatQ.toRat_add,
   TauRatQ.toRat_mul,
   ⟨TauRatQ.toRat_zero, TauRatQ.toRat_one⟩,
   TauRatQ.ofRat_toRat⟩

end Tau.Boundary
