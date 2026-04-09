import TauLib.BookI.Denotation.ProgramMonoid

/-!
# TauLib.BookI.Denotation.Equality

The three levels of equality in Category τ.

## Registry Cross-References

- [I.D15] Three-Level Equality — `ontic_eq`, `addr_equiv`, `shadow_eq`

## Mathematical Content

Category τ distinguishes three levels of equality:
1. **Ontic identity**: primitive structural equality (x = y as TauObj)
2. **Address equivalence**: two programs compute the same result (NF-equivalent)
3. **Shadow equality**: same coordinates (collapses to ontic for Parts I-III)

All three are decidable. Shadow equality implies ontic equality
(in the current scope; the full ABCD chart in Part IV may distinguish them).
-/

namespace Tau.Denotation

open Tau.Kernel

-- ============================================================
-- THREE-LEVEL EQUALITY [I.D15]
-- ============================================================

/-- [I.D15, Level 1] Ontic identity: primitive structural equality. -/
def ontic_eq (x y : TauObj) : Prop := x = y

/-- [I.D15, Level 2] Address equivalence: two programs yield the same
    result on every input. -/
def addr_equiv (p q : Program) : Prop :=
  ∀ x, execProgram p x = execProgram q x

/-- [I.D15, Level 3] Shadow equality: same coordinates.
    In Parts I-III, this collapses to ontic equality.
    (The full ABCD chart in Part IV may refine this.) -/
def shadow_eq (x y : TauObj) : Prop := x = y

-- ============================================================
-- PROPERTIES
-- ============================================================

/-- Ontic equality is decidable. -/
instance ontic_eq_decidable (x y : TauObj) : Decidable (ontic_eq x y) :=
  inferInstanceAs (Decidable (x = y))

/-- Address equivalence is reflexive. -/
theorem addr_equiv_refl (p : Program) : addr_equiv p p := by
  intro x; rfl

/-- Address equivalence is symmetric. -/
theorem addr_equiv_symm {p q : Program} (h : addr_equiv p q) : addr_equiv q p := by
  intro x; exact (h x).symm

/-- Address equivalence is transitive. -/
theorem addr_equiv_trans {p q r : Program} (h1 : addr_equiv p q) (h2 : addr_equiv q r) :
    addr_equiv p r := by
  intro x; exact (h1 x).trans (h2 x)

/-- The empty program is addr_equiv to itself. -/
theorem addr_equiv_nil : addr_equiv [] [] :=
  addr_equiv_refl []

/-- Shadow equality implies ontic equality (trivially, in current scope). -/
theorem shadow_implies_ontic (x y : TauObj) (h : shadow_eq x y) : ontic_eq x y :=
  h

/-- Composition preserves address equivalence (left). -/
theorem addr_equiv_compose_left {p₁ p₂ : Program} (h : addr_equiv p₁ p₂) (q : Program) :
    addr_equiv (Program.compose p₁ q) (Program.compose p₂ q) := by
  intro x
  rw [exec_compose, exec_compose, h x]

/-- Composition preserves address equivalence (right). -/
theorem addr_equiv_compose_right (p : Program) {q₁ q₂ : Program} (h : addr_equiv q₁ q₂) :
    addr_equiv (Program.compose p q₁) (Program.compose p q₂) := by
  intro x
  rw [exec_compose, exec_compose, h (execProgram p x)]

end Tau.Denotation
