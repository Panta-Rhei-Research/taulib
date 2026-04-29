import TauLib.BookI.Boundary.Bridge.TauRealCongruence
import Mathlib.Algebra.Ring.Defs
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-!
# TauLib.BookI.Boundary.Bridge.TauRealQuotient

**Wave 41b — Mathlib CommRing bridge for TauReal (Cauchy-quotient form)**.

Builds `CauchyTauReal := {x : TauReal // x.IsCauchy}` and the Cauchy
quotient `TauRealQ := Quotient CauchyTauReal.setoid`. Instantiates
Mathlib's `CommRing TauRealQ` typeclass — the strongest unconditional
classical algebraic structure on a τ-native countable real WITHOUT
invoking Classical reasoning.

Companion to Waves 39 (TauIntQ ≃+* ℤ), 40 (TauRatQ ≃+* ℚ), and 41a
(`TauRealCongruence.lean` kernel).

## Constructive boundary (made visible)

| Typeclass             | Decidability cost           | Wave landed |
|-----------------------|-----------------------------|-------------|
| `CommRing TauRealQ`   | none (constructive)         | **41b** ← this module |
| `Field TauRealQ`      | `Classical.byCases (a = 0)` | 41c (planned) |
| `IsStrictOrderedRing` | `mul_pos` + ordered-add-monoid axioms (constructive) | 41d (planned) |
| `LinearOrderedField`  | Markov's principle          | **structurally impossible** |

The last row is the structural-honesty *feature* of the τ-kernel —
`TauRealQ` is countable; `LinearOrderedField` would imply uncountable
cardinality. See atlas insight
`2026-04-29-constructive-real-cardinality-boundary`.

## Registry Cross-References

- [I.D84/D111/D112]    TauReal infrastructure
- [I.T216–I.T222]      Wave 41a congruence kernel (dependencies)
- [I.D146]             CauchyTauReal + TauRealQ (this module)
- [I.T223]             CommRing TauRealQ Instance (this module)
- [I.T224]             Wave 41b synthesis theorem (this module)
-/

set_option autoImplicit false

namespace Tau.Boundary

open Tau.Denotation

-- ============================================================
-- PART 1: TauReal.zero / TauReal.one are Cauchy
-- ============================================================

theorem TauReal.zero_isCauchy : TauReal.zero.IsCauchy :=
  ⟨fun _ => 0, fun k _ _ _ _ => by
    show TauRat.lt _ _
    unfold TauRat.lt
    rw [TauRat.toRat_abs, toRat_sub]
    show |TauRat.zero.toRat - TauRat.zero.toRat| < (TauRat.ofNatRecip k).toRat
    rw [toRat_zero]
    simp
    exact TauRat.ofNatRecip_pos k⟩

theorem TauReal.one_isCauchy : TauReal.one.IsCauchy :=
  ⟨fun _ => 0, fun k _ _ _ _ => by
    show TauRat.lt _ _
    unfold TauRat.lt
    rw [TauRat.toRat_abs, toRat_sub]
    show |TauRat.one.toRat - TauRat.one.toRat| < (TauRat.ofNatRecip k).toRat
    rw [toRat_one]
    simp
    exact TauRat.ofNatRecip_pos k⟩

-- ============================================================
-- PART 2: CauchyTauReal subtype + operations
-- ============================================================

/-- The **Cauchy subtype** of `TauReal` — pairs of (sequence, Cauchy
    proof). Multiplication on this subtype respects `equiv`
    (Wave 41a `mul_respects_equiv_under_cauchy`), enabling a
    well-defined Quotient ring structure. -/
structure CauchyTauReal where
  val : TauReal
  isCauchy : val.IsCauchy

namespace CauchyTauReal

@[simp] theorem ext {a b : CauchyTauReal} (h : a.val = b.val) : a = b := by
  cases a; cases b; congr

def zero : CauchyTauReal := ⟨TauReal.zero, TauReal.zero_isCauchy⟩
def one  : CauchyTauReal := ⟨TauReal.one,  TauReal.one_isCauchy⟩

def add (a b : CauchyTauReal) : CauchyTauReal :=
  ⟨a.val.add b.val, TauReal.IsCauchy_add a.val b.val a.isCauchy b.isCauchy⟩

def neg (a : CauchyTauReal) : CauchyTauReal :=
  ⟨a.val.negate, TauReal.IsCauchy_negate a.val a.isCauchy⟩

def mul (a b : CauchyTauReal) : CauchyTauReal :=
  ⟨a.val.mul b.val, TauReal.IsCauchy_mul a.val b.val a.isCauchy b.isCauchy⟩

/-- Cauchy-equivalence on the Cauchy subtype: lifted from `TauReal.equiv`. -/
def equiv (a b : CauchyTauReal) : Prop := TauReal.equiv a.val b.val

theorem equiv_refl (a : CauchyTauReal) : equiv a a := TauReal.equiv_refl a.val

theorem equiv_symm {a b : CauchyTauReal} (h : equiv a b) : equiv b a :=
  TauReal.equiv_symm h

theorem equiv_trans {a b c : CauchyTauReal}
    (hab : equiv a b) (hbc : equiv b c) : equiv a c :=
  TauReal.equiv_trans hab hbc

/-- The Setoid on `CauchyTauReal`. -/
def setoid : Setoid CauchyTauReal where
  r := equiv
  iseqv := ⟨equiv_refl, equiv_symm, equiv_trans⟩

end CauchyTauReal

-- ============================================================
-- PART 3: TauRealQ — the Cauchy quotient
-- ============================================================

/-- **TauRealQ — the Cauchy quotient of TauReal**.

    The Mathlib-bridge form of τ-native reals. Multiplication is
    well-defined here (unlike `Quotient TauReal.equiv` over arbitrary
    sequences), and standard ring axioms hold via the Wave 41a
    `mul_respects_equiv_under_cauchy` machinery. -/
abbrev TauRealQ : Type := Quotient CauchyTauReal.setoid

def CauchyTauReal.toQ (a : CauchyTauReal) : TauRealQ :=
  Quotient.mk CauchyTauReal.setoid a

@[simp] theorem CauchyTauReal.toQ_eq_iff (a b : CauchyTauReal) :
    a.toQ = b.toQ ↔ CauchyTauReal.equiv a b :=
  Quotient.eq

-- ============================================================
-- PART 4: Operations lifted to TauRealQ
-- ============================================================

theorem CauchyTauReal.add_respects_equiv (a₁ a₂ b₁ b₂ : CauchyTauReal)
    (ha : equiv a₁ a₂) (hb : equiv b₁ b₂) :
    equiv (a₁.add b₁) (a₂.add b₂) :=
  TauReal.add_respects_equiv a₁.val a₂.val b₁.val b₂.val ha hb

theorem CauchyTauReal.mul_respects_equiv (a₁ a₂ b₁ b₂ : CauchyTauReal)
    (ha : equiv a₁ a₂) (hb : equiv b₁ b₂) :
    equiv (a₁.mul b₁) (a₂.mul b₂) :=
  TauReal.mul_respects_equiv_under_cauchy a₁.val a₂.val b₁.val b₂.val
    a₂.isCauchy b₁.isCauchy ha hb

theorem CauchyTauReal.neg_respects_equiv (a₁ a₂ : CauchyTauReal)
    (h : equiv a₁ a₂) :
    equiv a₁.neg a₂.neg :=
  TauReal.negate_respects_equiv a₁.val a₂.val h

def TauRealQ.add : TauRealQ → TauRealQ → TauRealQ :=
  Quotient.lift₂ (fun a b => (a.add b).toQ)
    (fun a₁ b₁ a₂ b₂ ha hb =>
      Quotient.sound (CauchyTauReal.add_respects_equiv a₁ a₂ b₁ b₂ ha hb))

def TauRealQ.mul : TauRealQ → TauRealQ → TauRealQ :=
  Quotient.lift₂ (fun a b => (a.mul b).toQ)
    (fun a₁ b₁ a₂ b₂ ha hb =>
      Quotient.sound (CauchyTauReal.mul_respects_equiv a₁ a₂ b₁ b₂ ha hb))

def TauRealQ.neg : TauRealQ → TauRealQ :=
  Quotient.lift (fun a => a.neg.toQ)
    (fun a b h => Quotient.sound (CauchyTauReal.neg_respects_equiv a b h))

def TauRealQ.zero : TauRealQ := CauchyTauReal.zero.toQ
def TauRealQ.one  : TauRealQ := CauchyTauReal.one.toQ

@[simp] theorem TauRealQ.add_mk (a b : CauchyTauReal) :
    TauRealQ.add a.toQ b.toQ = (a.add b).toQ := rfl
@[simp] theorem TauRealQ.mul_mk (a b : CauchyTauReal) :
    TauRealQ.mul a.toQ b.toQ = (a.mul b).toQ := rfl
@[simp] theorem TauRealQ.neg_mk (a : CauchyTauReal) :
    TauRealQ.neg a.toQ = a.neg.toQ := rfl

-- ============================================================
-- PART 5: Bare typeclass instances
-- ============================================================

instance : Zero TauRealQ := ⟨TauRealQ.zero⟩
instance : One  TauRealQ := ⟨TauRealQ.one⟩
instance : Add  TauRealQ := ⟨TauRealQ.add⟩
instance : Mul  TauRealQ := ⟨TauRealQ.mul⟩
instance : Neg  TauRealQ := ⟨TauRealQ.neg⟩

-- ============================================================
-- PART 6: CommRing TauRealQ instance (KEYSTONE)
-- ============================================================

/-- Helper: lift an equality of equivalence classes via `Quotient.sound`
    using a TauReal-level `equiv` proof on representatives. -/
private theorem TauRealQ.from_equiv {a b : CauchyTauReal}
    (h : CauchyTauReal.equiv a b) : a.toQ = b.toQ :=
  Quotient.sound h

/-- **Wave 41b KEYSTONE: CommRing instance on TauRealQ**.

    Every ring axiom is proven by `Quotient.inductionOn` on the
    Cauchy reps, then invoking the existing equiv-level ring axioms
    on `TauReal` (`taureal_add_comm`, `taureal_add_assoc`,
    `taureal_mul_comm`, etc.).

    Multiplication is well-defined on the quotient because we
    quotiented the *Cauchy subtype* (Wave 41a `IsCauchy_mul` +
    `mul_respects_equiv_under_cauchy`). -/
instance : CommRing TauRealQ where
  add := TauRealQ.add
  mul := TauRealQ.mul
  neg := TauRealQ.neg
  zero := TauRealQ.zero
  one := TauRealQ.one
  add_assoc x y z := by
    refine Quotient.inductionOn₃ x y z (fun a b c => ?_)
    show ((a.add b).add c).toQ = (a.add (b.add c)).toQ
    apply TauRealQ.from_equiv
    exact taureal_add_assoc a.val b.val c.val
  zero_add x := by
    refine Quotient.inductionOn x (fun a => ?_)
    show (CauchyTauReal.zero.add a).toQ = a.toQ
    apply TauRealQ.from_equiv
    show TauReal.equiv (TauReal.zero.add a.val) a.val
    exact taureal_zero_add a.val
  add_zero x := by
    refine Quotient.inductionOn x (fun a => ?_)
    show (a.add CauchyTauReal.zero).toQ = a.toQ
    apply TauRealQ.from_equiv
    show TauReal.equiv (a.val.add TauReal.zero) a.val
    exact taureal_add_zero a.val
  add_comm x y := by
    refine Quotient.inductionOn₂ x y (fun a b => ?_)
    show (a.add b).toQ = (b.add a).toQ
    apply TauRealQ.from_equiv
    exact taureal_add_comm a.val b.val
  mul_assoc x y z := by
    refine Quotient.inductionOn₃ x y z (fun a b c => ?_)
    show ((a.mul b).mul c).toQ = (a.mul (b.mul c)).toQ
    apply TauRealQ.from_equiv
    exact taureal_mul_assoc a.val b.val c.val
  one_mul x := by
    refine Quotient.inductionOn x (fun a => ?_)
    show (CauchyTauReal.one.mul a).toQ = a.toQ
    apply TauRealQ.from_equiv
    show TauReal.equiv (TauReal.one.mul a.val) a.val
    exact taureal_one_mul a.val
  mul_one x := by
    refine Quotient.inductionOn x (fun a => ?_)
    show (a.mul CauchyTauReal.one).toQ = a.toQ
    apply TauRealQ.from_equiv
    show TauReal.equiv (a.val.mul TauReal.one) a.val
    exact taureal_mul_one a.val
  left_distrib x y z := by
    refine Quotient.inductionOn₃ x y z (fun a b c => ?_)
    show (a.mul (b.add c)).toQ = ((a.mul b).add (a.mul c)).toQ
    apply TauRealQ.from_equiv
    exact taureal_left_distrib a.val b.val c.val
  right_distrib x y z := by
    refine Quotient.inductionOn₃ x y z (fun a b c => ?_)
    show ((a.add b).mul c).toQ = ((a.mul c).add (b.mul c)).toQ
    apply TauRealQ.from_equiv
    exact taureal_right_distrib a.val b.val c.val
  zero_mul x := by
    refine Quotient.inductionOn x (fun a => ?_)
    show (CauchyTauReal.zero.mul a).toQ = CauchyTauReal.zero.toQ
    apply TauRealQ.from_equiv
    show TauReal.equiv (TauReal.zero.mul a.val) TauReal.zero
    exact taureal_zero_mul a.val
  mul_zero x := by
    refine Quotient.inductionOn x (fun a => ?_)
    show (a.mul CauchyTauReal.zero).toQ = CauchyTauReal.zero.toQ
    apply TauRealQ.from_equiv
    -- a*0 ≡ 0 follows from mul_comm + zero_mul
    have h1 : TauReal.equiv (a.val.mul TauReal.zero) (TauReal.zero.mul a.val) :=
      taureal_mul_comm a.val TauReal.zero
    have h2 : TauReal.equiv (TauReal.zero.mul a.val) TauReal.zero :=
      taureal_zero_mul a.val
    exact TauReal.equiv_trans h1 h2
  mul_comm x y := by
    refine Quotient.inductionOn₂ x y (fun a b => ?_)
    show (a.mul b).toQ = (b.mul a).toQ
    apply TauRealQ.from_equiv
    exact taureal_mul_comm a.val b.val
  neg_add_cancel x := by
    refine Quotient.inductionOn x (fun a => ?_)
    show (a.neg.add a).toQ = CauchyTauReal.zero.toQ
    apply TauRealQ.from_equiv
    show TauReal.equiv (a.val.negate.add a.val) TauReal.zero
    exact taureal_negate_add a.val
  nsmul := nsmulRec
  zsmul := zsmulRec

-- ============================================================
-- PART 7: Wave 41b synthesis theorem
-- ============================================================

/-- **Wave 41b H8 Mathlib-CommRing-Bridge synthesis (KEYSTONE)**.

    Five-clause structural significance:

    1. **TauRealQ is a `CommRing`**: full Mathlib typeclass instance
       on the Cauchy-quotient construction.
    2. **Cauchy subtype closed under operations**: the four lifting
       theorems (add, mul, neg, plus IsCauchy preservation) witness
       that ring operations stay within Cauchy reps.
    3. **Multiplication well-defined on quotient**: `mul_respects_equiv`
       at the Cauchy level (Wave 41a's `mul_respects_equiv_under_cauchy`).
    4. **Constructive boundary explicit**: NO `RingEquiv` to Mathlib's
       `Real` (different cardinality). NO `LinearOrderedField` (Markov
       barrier). Field/IsStrictOrderedRing planned for Waves 41c, 41d.
    5. **Bridge cascade ceiling**: every τ-native real-valued
       construction (TauComplex, TauQuaternion in Wave 42) inherits
       this ceiling — countable τ-Real is the structural commitment. -/
theorem h8_taureal_mathlib_commring_bridge_synthesis :
    -- Clause 1: CommRing instance exists on TauRealQ
    Nonempty (CommRing TauRealQ) ∧
    -- Clause 2: Cauchy subtype closed under add (witness)
    (∀ a b : TauReal, a.IsCauchy → b.IsCauchy → (a.add b).IsCauchy) ∧
    -- Clause 3: Cauchy subtype closed under mul (witness)
    (∀ a b : TauReal, a.IsCauchy → b.IsCauchy → (a.mul b).IsCauchy) ∧
    -- Clause 4: Cauchy subtype closed under neg (witness)
    (∀ a : TauReal, a.IsCauchy → a.negate.IsCauchy) ∧
    -- Clause 5: mul respects equiv under Cauchy (witness)
    (∀ a₁ a₂ b₁ b₂ : TauReal, a₂.IsCauchy → b₁.IsCauchy →
      TauReal.equiv a₁ a₂ → TauReal.equiv b₁ b₂ →
      TauReal.equiv (a₁.mul b₁) (a₂.mul b₂)) :=
  ⟨⟨inferInstance⟩,
   TauReal.IsCauchy_add,
   TauReal.IsCauchy_mul,
   TauReal.IsCauchy_negate,
   TauReal.mul_respects_equiv_under_cauchy⟩

end Tau.Boundary
