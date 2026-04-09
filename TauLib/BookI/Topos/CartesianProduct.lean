import TauLib.BookI.Topos.EarnedTopos

/-!
# TauLib.BookI.Topos.CartesianProduct

Cartesian product as an earned bi-functor in E_τ.

## Registry Cross-References

- [I.D60] Categorical Product — `cat_product`
- [I.T26] Product Universal Property — `product_universal`
- [I.D61] Cartesian Monoidal Structure — `CartesianMonoidal`

## Mathematical Content

The categorical product in E_τ is the pointwise conjunction of presheaves.
The terminal presheaf is the monoidal unit.
Products satisfy the universal property: any pair of morphisms factors
uniquely through the product.
-/

namespace Tau.Topos

open Tau.Holomorphy Tau.Polarity Tau.Denotation

-- ============================================================
-- CATEGORICAL PRODUCT [I.D60]
-- ============================================================

/-- [I.D60] The categorical product of two presheaves:
    pointwise conjunction of support predicates. -/
def cat_product (P Q : Presheaf) : Presheaf :=
  presheaf_product P Q

/-- First projection: product → first factor. -/
theorem cat_proj1 (P Q : Presheaf) (x : TauIdx)
    (h : (cat_product P Q).support x = true) : P.support x = true := by
  simp [cat_product, presheaf_product] at h; exact h.1

/-- Second projection: product → second factor. -/
theorem cat_proj2 (P Q : Presheaf) (x : TauIdx)
    (h : (cat_product P Q).support x = true) : Q.support x = true := by
  simp [cat_product, presheaf_product] at h; exact h.2

-- ============================================================
-- PRODUCT UNIVERSAL PROPERTY [I.T26]
-- ============================================================

/-- [I.T26] Product universal property: if R maps to both P and Q pointwise,
    then R maps to P × Q. -/
theorem product_universal (P Q R : Presheaf)
    (hP : ∀ x, R.support x = true → P.support x = true)
    (hQ : ∀ x, R.support x = true → Q.support x = true) :
    ∀ x, R.support x = true → (cat_product P Q).support x = true := by
  intro x hr
  simp [cat_product, presheaf_product]
  exact ⟨hP x hr, hQ x hr⟩

/-- Product is commutative up to support equality. -/
theorem product_comm (P Q : Presheaf) :
    (cat_product P Q).support = (cat_product Q P).support := by
  ext x; simp [cat_product, presheaf_product, Bool.and_comm]

/-- Product is associative up to support equality. -/
theorem product_assoc (P Q R : Presheaf) :
    (cat_product (cat_product P Q) R).support =
    (cat_product P (cat_product Q R)).support := by
  ext x; simp [cat_product, presheaf_product, Bool.and_assoc]

/-- Product with terminal is identity. -/
theorem product_terminal (P : Presheaf) :
    (cat_product P ⟨fun _ => true⟩).support = P.support :=
  presheaf_product_terminal P

-- ============================================================
-- CARTESIAN MONOIDAL STRUCTURE [I.D61]
-- ============================================================

/-- [I.D61] The cartesian monoidal structure on E_τ.
    Unit: terminal presheaf. Tensor: pointwise product. -/
structure CartesianMonoidal where
  -- Monoidal unit
  unit : Presheaf := ⟨fun _ => true⟩
  -- Tensor product
  tensor : Presheaf → Presheaf → Presheaf := cat_product

/-- The canonical cartesian monoidal structure. -/
def cartesian_monoidal : CartesianMonoidal where

/-- Left unit law. -/
theorem monoidal_left_unit (P : Presheaf) :
    (cat_product ⟨fun _ => true⟩ P).support = P.support := by
  ext x; simp [cat_product, presheaf_product, Bool.true_and]

/-- Right unit law. -/
theorem monoidal_right_unit (P : Presheaf) :
    (cat_product P ⟨fun _ => true⟩).support = P.support :=
  presheaf_product_terminal P

-- ============================================================
-- PRODUCT VIA CANTOR PAIRING
-- ============================================================

/-- Product encoding at the object level via Cantor pairing. -/
theorem cantor_product_encoding (a b : TauIdx) :
    cantor_pair a b = (a + b) * (a + b + 1) / 2 + b := rfl

/-- Cantor pairing: (1,0) ≠ (0,1). -/
example : cantor_pair 1 0 ≠ cantor_pair 0 1 := by native_decide

-- ============================================================
-- SMOKE TESTS
-- ============================================================

-- Product support
#eval (cat_product ⟨fun n => n % 2 == 0⟩ ⟨fun n => n % 3 == 0⟩).support 6  -- true
#eval (cat_product ⟨fun n => n % 2 == 0⟩ ⟨fun n => n % 3 == 0⟩).support 4  -- false

-- Commutativity witness
#eval (cat_product ⟨fun _ => true⟩ ⟨fun _ => false⟩).support 0  -- false
#eval (cat_product ⟨fun _ => false⟩ ⟨fun _ => true⟩).support 0  -- false

end Tau.Topos
