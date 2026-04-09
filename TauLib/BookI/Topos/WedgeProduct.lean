import TauLib.BookI.Topos.CartesianProduct

/-!
# TauLib.BookI.Topos.WedgeProduct

Wedge product (coproduct) and the bi-monoidal structure of E_τ.

## Registry Cross-References

- [I.D62] Categorical Coproduct — `cat_coproduct`
- [I.T27] Distributivity — `product_distributes_over_coproduct`
- [I.D63] Bi-Monoidal Structure — `BiMonoidal`

## Mathematical Content

The categorical coproduct in E_τ is the pointwise disjunction of presheaves.
The bi-monoidal structure has product (×) distributing over coproduct (∨).
-/

namespace Tau.Topos

open Tau.Holomorphy Tau.Polarity Tau.Denotation

-- ============================================================
-- CATEGORICAL COPRODUCT [I.D62]
-- ============================================================

/-- [I.D62] The categorical coproduct of two presheaves:
    pointwise disjunction of support predicates. -/
def cat_coproduct (P Q : Presheaf) : Presheaf :=
  presheaf_coproduct P Q

/-- Left injection: P → P ∨ Q. -/
theorem coprod_inl (P Q : Presheaf) (x : TauIdx) :
    P.support x = true → (cat_coproduct P Q).support x = true := by
  intro h; simp [cat_coproduct, presheaf_coproduct, h]

/-- Right injection: Q → P ∨ Q. -/
theorem coprod_inr (P Q : Presheaf) (x : TauIdx) :
    Q.support x = true → (cat_coproduct P Q).support x = true := by
  intro h; simp [cat_coproduct, presheaf_coproduct, h, Bool.or_true]

/-- Coproduct is commutative. -/
theorem coproduct_comm (P Q : Presheaf) :
    (cat_coproduct P Q).support = (cat_coproduct Q P).support := by
  ext x; simp [cat_coproduct, presheaf_coproduct, Bool.or_comm]

/-- Coproduct is associative. -/
theorem coproduct_assoc (P Q R : Presheaf) :
    (cat_coproduct (cat_coproduct P Q) R).support =
    (cat_coproduct P (cat_coproduct Q R)).support := by
  ext x; simp [cat_coproduct, presheaf_coproduct, Bool.or_assoc]

/-- Coproduct with initial is identity. -/
theorem coproduct_initial (P : Presheaf) :
    (cat_coproduct P ⟨fun _ => false⟩).support = P.support :=
  presheaf_coproduct_initial P

-- ============================================================
-- DISTRIBUTIVITY [I.T27]
-- ============================================================

/-- [I.T27] Product distributes over coproduct:
    P × (Q ∨ R) = (P × Q) ∨ (P × R). -/
theorem product_distributes_over_coproduct (P Q R : Presheaf) :
    (cat_product P (cat_coproduct Q R)).support =
    (cat_coproduct (cat_product P Q) (cat_product P R)).support := by
  ext x
  simp [cat_product, cat_coproduct, presheaf_product, presheaf_coproduct,
        Bool.and_or_distrib_left]

/-- Right distributivity: (P ∨ Q) × R = (P × R) ∨ (Q × R). -/
theorem product_distributes_right (P Q R : Presheaf) :
    (cat_product (cat_coproduct P Q) R).support =
    (cat_coproduct (cat_product P R) (cat_product Q R)).support := by
  ext x
  simp [cat_product, cat_coproduct, presheaf_product, presheaf_coproduct]
  cases P.support x <;> cases Q.support x <;> cases R.support x <;> simp

-- ============================================================
-- BI-MONOIDAL STRUCTURE [I.D63]
-- ============================================================

/-- [I.D63] The bi-monoidal structure on E_τ:
    product (×) and coproduct (∨) with distributivity. -/
structure BiMonoidal where
  -- Multiplicative tensor
  times : Presheaf → Presheaf → Presheaf := cat_product
  -- Additive tensor
  wedge : Presheaf → Presheaf → Presheaf := cat_coproduct
  -- Multiplicative unit
  one : Presheaf := ⟨fun _ => true⟩
  -- Additive unit
  zero : Presheaf := ⟨fun _ => false⟩

/-- The canonical bi-monoidal structure. -/
def bi_monoidal : BiMonoidal where

/-- Absorption: P × 0 = 0. -/
theorem product_absorb (P : Presheaf) :
    (cat_product P ⟨fun _ => false⟩).support = (⟨fun _ => false⟩ : Presheaf).support := by
  ext x; simp [cat_product, presheaf_product, Bool.and_false]

/-- Coproduct with terminal: P ∨ 1 = 1. -/
theorem coproduct_terminal (P : Presheaf) :
    (cat_coproduct P ⟨fun _ => true⟩).support = (⟨fun _ => true⟩ : Presheaf).support := by
  ext x; simp [cat_coproduct, presheaf_coproduct, Bool.or_true]

-- ============================================================
-- SMOKE TESTS
-- ============================================================

-- Coproduct
#eval (cat_coproduct ⟨fun n => n % 2 == 0⟩ ⟨fun n => n % 3 == 0⟩).support 3  -- true
#eval (cat_coproduct ⟨fun n => n % 2 == 0⟩ ⟨fun n => n % 3 == 0⟩).support 5  -- false

-- Distributivity witness
#eval (cat_product ⟨fun _ => true⟩ (cat_coproduct ⟨fun _ => false⟩ ⟨fun _ => true⟩)).support 0
-- true = (true && (false || true))

end Tau.Topos
