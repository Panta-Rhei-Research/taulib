import TauLib.BookI.Topos.WedgeProduct

/-!
# TauLib.BookI.Topos.InternalHom

Internal hom (exponentials) and the cartesian closed structure of E_τ.

## Registry Cross-References

- [I.D64] Internal Hom — `internal_hom`
- [I.T28] Cartesian Closed — `cartesian_closed_adj`
- [I.P28] Self-Enrichment — `self_enrichment`

## Mathematical Content

The internal hom Q^P in E_τ assigns to each object X the set of
"morphisms P → Q over X". In our Boolean-presheaf model, this simplifies:
Q^P(X) = true iff P(X) = true implies Q(X) = true.

This gives E_τ a cartesian closed structure:
Hom(A × B, C) ≅ Hom(A, C^B).
-/

namespace Tau.Topos

open Tau.Holomorphy Tau.Polarity Tau.Denotation

-- ============================================================
-- INTERNAL HOM [I.D64]
-- ============================================================

/-- [I.D64] The internal hom Q^P: pointwise implication.
    (Q^P)(X) = true iff P(X) implies Q(X). -/
def internal_hom (P Q : Presheaf) : Presheaf :=
  ⟨fun x => !P.support x || Q.support x⟩

/-- Internal hom evaluates correctly when P holds and Q holds. -/
theorem ihom_both_true (P Q : Presheaf) (x : TauIdx)
    (hp : P.support x = true) (hq : Q.support x = true) :
    (internal_hom P Q).support x = true := by
  simp [internal_hom, hp, hq]

/-- Internal hom evaluates correctly when P fails. -/
theorem ihom_p_false (P Q : Presheaf) (x : TauIdx)
    (hp : P.support x = false) :
    (internal_hom P Q).support x = true := by
  simp [internal_hom, hp]

/-- Internal hom evaluates correctly when P holds but Q fails. -/
theorem ihom_p_true_q_false (P Q : Presheaf) (x : TauIdx)
    (hp : P.support x = true) (hq : Q.support x = false) :
    (internal_hom P Q).support x = false := by
  simp [internal_hom, hp, hq]

-- ============================================================
-- CARTESIAN CLOSED [I.T28]
-- ============================================================

/-- [I.T28] Cartesian closed adjunction:
    (A × B)(x) = true → C(x) = true
    iff
    A(x) = true → (C^B)(x) = true

    This is the pointwise version of Hom(A × B, C) ≅ Hom(A, C^B). -/
theorem cartesian_closed_adj (A B C : Presheaf) (x : TauIdx) :
    ((cat_product A B).support x = true → C.support x = true) ↔
    (A.support x = true → (internal_hom B C).support x = true) := by
  simp only [cat_product, presheaf_product, internal_hom]
  constructor
  · intro h ha
    cases hb : B.support x <;> simp_all
  · intro h
    cases ha : A.support x <;> cases hb : B.support x <;> simp_all

/-- Evaluation morphism: (Q^P × P) → Q. -/
theorem eval_morphism (P Q : Presheaf) (x : TauIdx) :
    (cat_product (internal_hom P Q) P).support x = true →
    Q.support x = true := by
  simp only [cat_product, presheaf_product, internal_hom]
  cases hp : P.support x <;> cases hq : Q.support x <;> simp_all

-- ============================================================
-- SELF-ENRICHMENT [I.P28]
-- ============================================================

/-- [I.P28] E_τ is self-enriched: internal hom gives an
    internal presheaf of morphisms.
    Witness: internal_hom P Q is itself a Presheaf. -/
theorem self_enrichment (P Q : Presheaf) :
    ∃ R : Presheaf, R = internal_hom P Q :=
  ⟨internal_hom P Q, rfl⟩

/-- Internal hom with terminal: Q^1 = Q (everything implies Q iff Q). -/
theorem ihom_terminal (Q : Presheaf) :
    (internal_hom ⟨fun _ => true⟩ Q).support = Q.support := by
  ext x; simp [internal_hom]

/-- Internal hom from initial: Q^0 = 1 (false implies anything). -/
theorem ihom_initial (Q : Presheaf) :
    (internal_hom ⟨fun _ => false⟩ Q).support = (⟨fun _ => true⟩ : Presheaf).support := by
  ext x; simp [internal_hom]

/-- Internal hom to terminal: 1^P = 1 (everything implies true). -/
theorem ihom_to_terminal (P : Presheaf) :
    (internal_hom P ⟨fun _ => true⟩).support = (⟨fun _ => true⟩ : Presheaf).support := by
  ext x; simp [internal_hom]

-- ============================================================
-- SMOKE TESTS
-- ============================================================

-- Internal hom
#eval (internal_hom ⟨fun n => n % 2 == 0⟩ ⟨fun n => n % 6 == 0⟩).support 6   -- true
#eval (internal_hom ⟨fun n => n % 2 == 0⟩ ⟨fun n => n % 6 == 0⟩).support 4   -- false
#eval (internal_hom ⟨fun n => n % 2 == 0⟩ ⟨fun n => n % 6 == 0⟩).support 3   -- true (vacuous)

end Tau.Topos
