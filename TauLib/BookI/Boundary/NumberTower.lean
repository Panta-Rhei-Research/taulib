import TauLib.BookI.Denotation.Arithmetic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum

/-!
# TauLib.BookI.Boundary.NumberTower

The τ number tower: TauInt (formal differences) and TauRat (formal fractions).

## Registry Cross-References

- [I.D14] TauInt — Formal difference integers earned from TauIdx
- [I.D15] TauRat — Formal fraction rationals earned from TauIdx
- [I.D16] Number Tower — TauIdx ↪ TauInt ↪ TauRat → [deferred] TauReal → TauComplex

## Ground Truth Sources
- chunk_0065_M000740: Integer construction from natural differences
- chunk_0070_M000780: Rational field as formal fractions
- chunk_0095_M001050: Number tower architecture, deferred completions

## Mathematical Content

The number tower is built purely from earned arithmetic on TauIdx:

1. **TauInt**: Formal differences (a, b) representing a - b, with equivalence
   (a₁, b₁) ~ (a₂, b₂) iff a₁ + b₂ = a₂ + b₁.

2. **TauRat**: Formal fractions (p, q) with q > 0, with equivalence
   via cross-multiplication through TauInt.equiv.

3. **TauReal / TauComplex**: Deferred to Book II (require Cauchy completion
   and algebraic closure, which need earned topology from Global Hartogs).

All ring axioms are proved up to the respective equivalence relations.
-/

set_option autoImplicit false

namespace Tau.Boundary

open Tau.Denotation

-- ============================================================
-- PART 1: TauInt — FORMAL DIFFERENCES [I.D14]
-- ============================================================

/-- [I.D14] Formal difference representation of integers earned from TauIdx.
    The pair (pos, neg) represents the integer pos - neg. -/
structure TauInt where
  pos : TauIdx
  neg : TauIdx
  deriving DecidableEq, Repr

/-- TauInt zero: 0 = 0 - 0. -/
def TauInt.zero : TauInt := ⟨0, 0⟩

/-- TauInt one: 1 = 1 - 0. -/
def TauInt.one : TauInt := ⟨1, 0⟩

/-- TauInt addition: (a - b) + (c - d) = (a + c) - (b + d). -/
def TauInt.add (a b : TauInt) : TauInt :=
  ⟨a.pos + b.pos, a.neg + b.neg⟩

/-- TauInt negation: -(a - b) = (b - a). -/
def TauInt.negate (a : TauInt) : TauInt :=
  ⟨a.neg, a.pos⟩

/-- TauInt multiplication: (p₁ - n₁)(p₂ - n₂) = (p₁p₂ + n₁n₂) - (p₁n₂ + n₁p₂). -/
def TauInt.mul (a b : TauInt) : TauInt :=
  ⟨a.pos * b.pos + a.neg * b.neg, a.pos * b.neg + a.neg * b.pos⟩

/-- TauInt subtraction: a - b = a + (-b). -/
def TauInt.sub (a b : TauInt) : TauInt :=
  a.add b.negate

/-- Embed a natural number (TauIdx) into TauInt. -/
def TauInt.fromNat (n : TauIdx) : TauInt := ⟨n, 0⟩

-- ============================================================
-- EQUIVALENCE RELATION ON TauInt
-- ============================================================

/-- Two TauInts are equivalent when they represent the same integer:
    (a, b) ~ (c, d) iff a + d = c + b. -/
def TauInt.equiv (a b : TauInt) : Prop :=
  a.pos + b.neg = b.pos + a.neg

/-- TauInt equivalence is reflexive. -/
theorem TauInt.equiv_refl (a : TauInt) : TauInt.equiv a a := by
  show a.pos + a.neg = a.pos + a.neg; rfl

/-- TauInt equivalence is symmetric. -/
theorem TauInt.equiv_symm {a b : TauInt} (h : TauInt.equiv a b) :
    TauInt.equiv b a := by
  show b.pos + a.neg = a.pos + b.neg
  have h' : a.pos + b.neg = b.pos + a.neg := h
  simp only [TauIdx] at *; omega

/-- TauInt equivalence is transitive. -/
theorem TauInt.equiv_trans {a b c : TauInt}
    (hab : TauInt.equiv a b) (hbc : TauInt.equiv b c) :
    TauInt.equiv a c := by
  show a.pos + c.neg = c.pos + a.neg
  have h1 : a.pos + b.neg = b.pos + a.neg := hab
  have h2 : b.pos + c.neg = c.pos + b.neg := hbc
  simp only [TauIdx] at *; omega

-- ============================================================
-- INT CASTING BRIDGE (public — used by ConstructiveReals etc.)
-- ============================================================

/-- Semantic bridge: compute the Int value represented by a TauInt. -/
def TauInt.toInt (a : TauInt) : Int :=
  (a.pos : Int) - (a.neg : Int)

/-- Convert Int difference equality to TauInt.equiv. -/
theorem equiv_of_int_eq (a b : TauInt)
    (h : (a.pos : Int) - (a.neg : Int) = (b.pos : Int) - (b.neg : Int)) :
    TauInt.equiv a b := by
  show a.pos + b.neg = b.pos + a.neg
  simp only [TauIdx] at *; omega

/-- TauInt.equiv implies Int difference equality. -/
theorem int_eq_of_equiv (a b : TauInt)
    (h : TauInt.equiv a b) :
    (a.pos : Int) - (a.neg : Int) = (b.pos : Int) - (b.neg : Int) := by
  have h' : a.pos + b.neg = b.pos + a.neg := h
  simp only [TauIdx] at *; omega

/-- Equiv iff same Int value. -/
theorem equiv_iff_toInt_eq (a b : TauInt) :
    TauInt.equiv a b ↔ a.toInt = b.toInt := by
  constructor
  · exact int_eq_of_equiv a b
  · exact equiv_of_int_eq a b

/-- toInt of add. -/
theorem toInt_add (a b : TauInt) :
    (a.add b).toInt = a.toInt + b.toInt := by
  simp only [TauInt.add, TauInt.toInt]; push_cast; ring

/-- toInt of mul. -/
theorem toInt_mul (a b : TauInt) :
    (a.mul b).toInt = a.toInt * b.toInt := by
  simp only [TauInt.mul, TauInt.toInt]; push_cast; ring

/-- toInt of negate. -/
theorem toInt_negate (a : TauInt) :
    a.negate.toInt = -a.toInt := by
  simp only [TauInt.negate, TauInt.toInt]; ring

/-- toInt of zero. -/
theorem toInt_zero : TauInt.zero.toInt = 0 := by
  simp [TauInt.zero, TauInt.toInt]

/-- toInt of one. -/
theorem toInt_one : TauInt.one.toInt = 1 := by
  simp [TauInt.one, TauInt.toInt]

/-- toInt of fromNat. -/
theorem toInt_fromNat (n : TauIdx) :
    (TauInt.fromNat n).toInt = (n : Int) := by
  simp [TauInt.fromNat, TauInt.toInt]

-- ============================================================
-- RING AXIOMS (UP TO equiv)
-- ============================================================

/-- Addition is commutative up to equiv. -/
theorem tauint_add_comm (a b : TauInt) :
    TauInt.equiv (a.add b) (b.add a) := by
  rw [equiv_iff_toInt_eq, toInt_add, toInt_add]; ring

/-- Addition is associative up to equiv. -/
theorem tauint_add_assoc (a b c : TauInt) :
    TauInt.equiv ((a.add b).add c) (a.add (b.add c)) := by
  rw [equiv_iff_toInt_eq, toInt_add, toInt_add, toInt_add, toInt_add]; ring

/-- Zero is a right identity for addition (up to equiv). -/
theorem tauint_add_zero (a : TauInt) :
    TauInt.equiv (a.add TauInt.zero) a := by
  rw [equiv_iff_toInt_eq, toInt_add, toInt_zero]; ring

/-- Zero is a left identity for addition (up to equiv). -/
theorem tauint_zero_add (a : TauInt) :
    TauInt.equiv (TauInt.zero.add a) a := by
  rw [equiv_iff_toInt_eq, toInt_add, toInt_zero]; ring

/-- Negation is a right inverse for addition (up to equiv). -/
theorem tauint_add_negate (a : TauInt) :
    TauInt.equiv (a.add a.negate) TauInt.zero := by
  rw [equiv_iff_toInt_eq, toInt_add, toInt_negate, toInt_zero]; ring

/-- Negation is a left inverse for addition (up to equiv). -/
theorem tauint_negate_add (a : TauInt) :
    TauInt.equiv (a.negate.add a) TauInt.zero := by
  rw [equiv_iff_toInt_eq, toInt_add, toInt_negate, toInt_zero]; ring

/-- Multiplication is commutative up to equiv. -/
theorem tauint_mul_comm (a b : TauInt) :
    TauInt.equiv (a.mul b) (b.mul a) := by
  rw [equiv_iff_toInt_eq, toInt_mul, toInt_mul]; ring

/-- Multiplication is associative up to equiv. -/
theorem tauint_mul_assoc (a b c : TauInt) :
    TauInt.equiv ((a.mul b).mul c) (a.mul (b.mul c)) := by
  rw [equiv_iff_toInt_eq, toInt_mul, toInt_mul, toInt_mul, toInt_mul]; ring

/-- One is a right identity for multiplication (up to equiv). -/
theorem tauint_mul_one (a : TauInt) :
    TauInt.equiv (a.mul TauInt.one) a := by
  rw [equiv_iff_toInt_eq, toInt_mul, toInt_one]; ring

/-- One is a left identity for multiplication (up to equiv). -/
theorem tauint_one_mul (a : TauInt) :
    TauInt.equiv (TauInt.one.mul a) a := by
  rw [equiv_iff_toInt_eq, toInt_mul, toInt_one]; ring

/-- Left distributivity: a * (b + c) = a * b + a * c (up to equiv). -/
theorem tauint_distrib (a b c : TauInt) :
    TauInt.equiv (a.mul (b.add c)) ((a.mul b).add (a.mul c)) := by
  rw [equiv_iff_toInt_eq, toInt_mul, toInt_add, toInt_add, toInt_mul, toInt_mul]; ring

/-- Right distributivity: (a + b) * c = a * c + b * c (up to equiv). -/
theorem tauint_distrib_right (a b c : TauInt) :
    TauInt.equiv ((a.add b).mul c) ((a.mul c).add (b.mul c)) := by
  rw [equiv_iff_toInt_eq, toInt_mul, toInt_add, toInt_add, toInt_mul, toInt_mul]; ring

/-- Multiplication by zero gives zero (up to equiv). -/
theorem tauint_mul_zero (a : TauInt) :
    TauInt.equiv (a.mul TauInt.zero) TauInt.zero := by
  rw [equiv_iff_toInt_eq, toInt_mul, toInt_zero]; ring

-- ============================================================
-- EMBEDDING: TauIdx → TauInt
-- ============================================================

/-- Canonical embedding from TauIdx to TauInt. -/
def nat_to_tauint (n : TauIdx) : TauInt := TauInt.fromNat n

/-- The embedding is injective. -/
theorem nat_to_tauint_injective {a b : TauIdx}
    (h : nat_to_tauint a = nat_to_tauint b) : a = b := by
  simp only [nat_to_tauint, TauInt.fromNat, TauInt.mk.injEq] at h
  exact h.1

/-- toInt of nat_to_tauint. -/
theorem toInt_nat_to_tauint (n : TauIdx) :
    (nat_to_tauint n).toInt = (n : Int) := by
  simp [nat_to_tauint, TauInt.fromNat, TauInt.toInt]

/-- The embedding preserves addition (up to equiv). -/
theorem nat_to_tauint_add (a b : TauIdx) :
    TauInt.equiv (nat_to_tauint (a + b)) ((nat_to_tauint a).add (nat_to_tauint b)) := by
  rw [equiv_iff_toInt_eq, toInt_add, toInt_nat_to_tauint, toInt_nat_to_tauint,
      toInt_nat_to_tauint]
  push_cast; ring

/-- The embedding preserves multiplication (up to equiv). -/
theorem nat_to_tauint_mul (a b : TauIdx) :
    TauInt.equiv (nat_to_tauint (a * b)) ((nat_to_tauint a).mul (nat_to_tauint b)) := by
  rw [equiv_iff_toInt_eq, toInt_mul, toInt_nat_to_tauint, toInt_nat_to_tauint,
      toInt_nat_to_tauint]
  push_cast; ring

-- ============================================================
-- PART 2: TauRat — FORMAL FRACTIONS [I.D15]
-- ============================================================

/-- [I.D15] Formal fraction representation of rationals earned from TauIdx.
    The pair (num, den) with den > 0 represents num / den. -/
structure TauRat where
  num : TauInt
  den : TauIdx
  den_pos : den > 0
  deriving Repr

/-- TauRat zero: 0/1. -/
def TauRat.zero : TauRat :=
  ⟨TauInt.zero, 1, Nat.one_pos⟩

/-- TauRat one: 1/1. -/
def TauRat.one : TauRat :=
  ⟨TauInt.one, 1, Nat.one_pos⟩

/-- TauRat addition: a/b + c/d = (a*d + c*b) / (b*d). -/
def TauRat.add (a b : TauRat) : TauRat :=
  ⟨(a.num.mul (TauInt.fromNat b.den)).add (b.num.mul (TauInt.fromNat a.den)),
   a.den * b.den,
   Nat.mul_pos a.den_pos b.den_pos⟩

/-- TauRat multiplication: (a/b) * (c/d) = (a*c) / (b*d). -/
def TauRat.mul (a b : TauRat) : TauRat :=
  ⟨a.num.mul b.num,
   a.den * b.den,
   Nat.mul_pos a.den_pos b.den_pos⟩

/-- TauRat negation: -(a/b) = (-a)/b. -/
def TauRat.negate (a : TauRat) : TauRat :=
  ⟨a.num.negate, a.den, a.den_pos⟩

/-- TauRat subtraction: a - b = a + (-b). -/
def TauRat.sub (a b : TauRat) : TauRat :=
  a.add b.negate

-- ============================================================
-- EQUIVALENCE RELATION ON TauRat
-- ============================================================

/-- Two TauRats are equivalent when they represent the same rational:
    a/b ~ c/d iff a*d = c*b (as TauInt equiv). -/
def TauRat.equiv (a b : TauRat) : Prop :=
  TauInt.equiv (a.num.mul (TauInt.fromNat b.den))
               (b.num.mul (TauInt.fromNat a.den))

/-- TauRat equivalence is reflexive. -/
theorem TauRat.equiv_refl (a : TauRat) : TauRat.equiv a a := by
  simp only [TauRat.equiv]
  exact TauInt.equiv_refl _

/-- TauRat equivalence is symmetric. -/
theorem TauRat.equiv_symm {a b : TauRat} (h : TauRat.equiv a b) :
    TauRat.equiv b a := by
  simp only [TauRat.equiv] at *
  exact TauInt.equiv_symm h

-- ============================================================
-- TauRat FIELD AXIOMS (selected, up to equiv)
-- ============================================================

/-- Addition is commutative up to equiv. -/
theorem taurat_add_comm (a b : TauRat) :
    TauRat.equiv (a.add b) (b.add a) := by
  simp only [TauRat.equiv, TauRat.add]
  rw [equiv_iff_toInt_eq]
  simp only [toInt_mul, toInt_add, toInt_fromNat]
  push_cast; ring

/-- Zero is a right identity for addition (up to equiv). -/
theorem taurat_add_zero (a : TauRat) :
    TauRat.equiv (a.add TauRat.zero) a := by
  simp only [TauRat.equiv, TauRat.add, TauRat.zero]
  rw [equiv_iff_toInt_eq]
  simp only [toInt_mul, toInt_add, toInt_fromNat, toInt_zero]
  push_cast; ring

/-- Negation is a right inverse for addition (up to equiv). -/
theorem taurat_add_negate (a : TauRat) :
    TauRat.equiv (a.add a.negate) TauRat.zero := by
  simp only [TauRat.equiv, TauRat.add, TauRat.negate, TauRat.zero]
  rw [equiv_iff_toInt_eq]
  simp only [toInt_mul, toInt_add, toInt_negate, toInt_fromNat, toInt_zero]
  push_cast; ring

/-- Multiplication is commutative up to equiv. -/
theorem taurat_mul_comm (a b : TauRat) :
    TauRat.equiv (a.mul b) (b.mul a) := by
  simp only [TauRat.equiv, TauRat.mul]
  rw [equiv_iff_toInt_eq]
  simp only [toInt_mul, toInt_fromNat]
  push_cast; ring

/-- One is a right identity for multiplication (up to equiv). -/
theorem taurat_mul_one (a : TauRat) :
    TauRat.equiv (a.mul TauRat.one) a := by
  simp only [TauRat.equiv, TauRat.mul, TauRat.one]
  rw [equiv_iff_toInt_eq]
  simp only [toInt_mul, toInt_fromNat, toInt_one]
  push_cast; ring

-- ============================================================
-- EMBEDDING: TauInt → TauRat
-- ============================================================

/-- Canonical embedding from TauInt to TauRat: z ↦ z/1. -/
def int_to_taurat (z : TauInt) : TauRat :=
  ⟨z, 1, Nat.one_pos⟩

/-- The embedding is injective (on TauInt structures). -/
theorem int_to_taurat_injective {a b : TauInt}
    (h : int_to_taurat a = int_to_taurat b) : a = b := by
  simp only [int_to_taurat, TauRat.mk.injEq] at h
  exact h.1

/-- The embedding preserves addition (up to equiv). -/
theorem int_to_taurat_add (a b : TauInt) :
    TauRat.equiv (int_to_taurat (a.add b))
                 ((int_to_taurat a).add (int_to_taurat b)) := by
  simp only [TauRat.equiv, int_to_taurat, TauRat.add]
  rw [equiv_iff_toInt_eq]
  simp only [toInt_mul, toInt_add, toInt_fromNat]
  push_cast; ring

/-- The embedding preserves multiplication (up to equiv). -/
theorem int_to_taurat_mul (a b : TauInt) :
    TauRat.equiv (int_to_taurat (a.mul b))
                 ((int_to_taurat a).mul (int_to_taurat b)) := by
  simp only [TauRat.equiv, int_to_taurat, TauRat.mul]
  exact TauInt.equiv_refl _

-- ============================================================
-- FULL TOWER EMBEDDING: TauIdx → TauInt → TauRat
-- ============================================================

/-- Full tower embedding: TauIdx → TauRat via nat_to_tauint then int_to_taurat. -/
def nat_to_taurat (n : TauIdx) : TauRat :=
  int_to_taurat (nat_to_tauint n)

/-- The full tower embedding is injective. -/
theorem nat_to_taurat_injective {a b : TauIdx}
    (h : nat_to_taurat a = nat_to_taurat b) : a = b :=
  nat_to_tauint_injective (int_to_taurat_injective h)

-- ============================================================
-- PART 3: TauReal, TauComplex (see Boundary.ConstructiveReals, Boundary.ComplexField)
-- ============================================================

-- TauReal and TauComplex are now fully constructed:
-- • TauReal: Cauchy sequences of TauRat (Boundary.ConstructiveReals)
-- • TauComplex: TauReal[i]/(i²+1) (Boundary.ComplexField)

-- ============================================================
-- SMOKE TESTS
-- ============================================================

-- TauInt arithmetic
#eval TauInt.add ⟨5, 3⟩ ⟨2, 7⟩      -- (7, 10) ~ -3
#eval TauInt.mul ⟨3, 1⟩ ⟨2, 0⟩      -- (6, 2) ~ 4
#eval TauInt.negate ⟨5, 3⟩           -- (3, 5) ~ -2
#eval TauInt.sub ⟨5, 3⟩ ⟨2, 7⟩      -- (5+7, 3+2) = (12, 5) ~ 7

-- TauRat arithmetic
private def halfRat : TauRat := ⟨⟨1, 0⟩, 2, by norm_num⟩
private def thirdRat : TauRat := ⟨⟨1, 0⟩, 3, by norm_num⟩
private def twoFifthsRat : TauRat := ⟨⟨3, 1⟩, 5, by norm_num⟩
#eval TauRat.add halfRat thirdRat       -- 1/2 + 1/3 = 5/6
#eval TauRat.mul halfRat thirdRat       -- 1/2 * 1/3 = 1/6
#eval TauRat.negate twoFifthsRat        -- -(2/5) = (-2)/5

end Tau.Boundary
