import TauLib.BookI.Denotation.Equality

/-!
# TauLib.BookI.Denotation.Order

Denotational ordering on Obj(τ): lexicographic on (seed.toNat, depth).

## Registry Cross-References

- [I.D16a] Denotational Order — `denotational_lt`
- [I.P07] Well-Ordering — `denotational_lt_wf`

## Mathematical Content

The denotational order is lexicographic:
- First compare seed indices (α=0 < π=1 < γ=2 < η=3 < ω=4)
- Then compare depths within the same seed

This gives a well-ordering of type ω·4 + ω (four copies of ω for the
orbit rays, plus one copy for the omega fiber).
-/

namespace Tau.Denotation

open Tau.Kernel Generator

-- ============================================================
-- HELPER
-- ============================================================

/-- Generator.toNat is injective. -/
private theorem Generator.toNat_injective (a b : Generator) (h : a.toNat = b.toNat) : a = b := by
  cases a <;> cases b <;> simp [Generator.toNat] at h <;> rfl

-- ============================================================
-- DENOTATIONAL ORDER [I.D16a]
-- ============================================================

/-- [I.D16a] Denotational strict order: lexicographic on (seed.toNat, depth). -/
def denotational_lt (x y : TauObj) : Prop :=
  x.seed.toNat < y.seed.toNat ∨
  (x.seed = y.seed ∧ x.depth < y.depth)

/-- Decidability of the denotational order. -/
instance denotational_lt_decidable (x y : TauObj) : Decidable (denotational_lt x y) :=
  inferInstanceAs (Decidable (_ ∨ _))

-- ============================================================
-- ORDER PROPERTIES
-- ============================================================

/-- Irreflexivity. -/
theorem denotational_lt_irrefl (x : TauObj) : ¬ denotational_lt x x := by
  intro h
  cases h with
  | inl h => exact Nat.lt_irrefl _ h
  | inr h => exact Nat.lt_irrefl _ h.2

/-- Transitivity. -/
theorem denotational_lt_trans {x y z : TauObj}
    (h1 : denotational_lt x y) (h2 : denotational_lt y z) :
    denotational_lt x z := by
  cases h1 with
  | inl h1 =>
    cases h2 with
    | inl h2 => exact Or.inl (Nat.lt_trans h1 h2)
    | inr h2 => exact Or.inl (h2.1 ▸ h1)
  | inr h1 =>
    cases h2 with
    | inl h2 => exact Or.inl (h1.1 ▸ h2)
    | inr h2 => exact Or.inr ⟨h1.1.trans h2.1, Nat.lt_trans h1.2 h2.2⟩

/-- Trichotomy: for any two TauObj, exactly one of <, =, > holds. -/
theorem denotational_lt_trichotomy (x y : TauObj) :
    denotational_lt x y ∨ x = y ∨ denotational_lt y x := by
  cases x with | mk sx dx =>
  cases y with | mk sy dy =>
  simp only [denotational_lt]
  by_cases h_seed : sx.toNat < sy.toNat
  · exact Or.inl (Or.inl h_seed)
  · by_cases h_seed_eq : sx = sy
    · subst h_seed_eq
      by_cases h_depth : dx < dy
      · exact Or.inl (Or.inr ⟨rfl, h_depth⟩)
      · by_cases h_depth_eq : dx = dy
        · subst h_depth_eq; exact Or.inr (Or.inl rfl)
        · have : dy < dx := by omega
          exact Or.inr (Or.inr (Or.inr ⟨rfl, this⟩))
    · by_cases h_seed2 : sy.toNat < sx.toNat
      · exact Or.inr (Or.inr (Or.inl h_seed2))
      · exfalso
        have : sx.toNat = sy.toNat := by omega
        exact h_seed_eq (Generator.toNat_injective sx sy this)

-- ============================================================
-- EXTREMAL ELEMENTS
-- ============================================================

/-- ⟨α, 0⟩ is the minimum element. -/
theorem alpha_zero_minimum (x : TauObj) (hx : x ≠ ⟨alpha, 0⟩) :
    denotational_lt ⟨alpha, 0⟩ x := by
  cases x with | mk sx dx =>
  simp only [denotational_lt]
  cases sx with
  | alpha =>
    right; constructor; · rfl
    · cases dx with
      | zero => exact absurd rfl hx
      | succ d => omega
  | pi => left; decide
  | gamma => left; decide
  | eta => left; decide
  | omega => left; decide

/-- Within each orbit ray, depth gives a total order. -/
theorem orbit_depth_order (g : Generator) (n m : Nat) (h : n < m) :
    denotational_lt ⟨g, n⟩ ⟨g, m⟩ :=
  Or.inr ⟨rfl, h⟩

/-- Different seeds have a definite order. -/
theorem seed_order_alpha_pi : denotational_lt ⟨alpha, 0⟩ ⟨pi, 0⟩ :=
  Or.inl (by decide)

theorem seed_order_pi_gamma : denotational_lt ⟨pi, 0⟩ ⟨gamma, 0⟩ :=
  Or.inl (by decide)

theorem seed_order_gamma_eta : denotational_lt ⟨gamma, 0⟩ ⟨eta, 0⟩ :=
  Or.inl (by decide)

theorem seed_order_eta_omega : denotational_lt ⟨eta, 0⟩ ⟨omega, 0⟩ :=
  Or.inl (by decide)

-- ============================================================
-- WELL-ORDERING [I.P07]
-- ============================================================

/-- The lexicographic measure for well-foundedness: (seed.toNat, depth). -/
private def lex_measure (x : TauObj) : Nat × Nat := (x.seed.toNat, x.depth)

/-- denotational_lt is a subrelation of Prod.Lex on the measure. -/
private theorem denotational_lt_sub_lex {a b : TauObj} (h : denotational_lt a b) :
    Prod.Lex (· < ·) (· < ·) (lex_measure a) (lex_measure b) := by
  cases h with
  | inl h => exact Prod.Lex.left _ _ h
  | inr h =>
    have hs : a.seed.toNat = b.seed.toNat := congrArg Generator.toNat h.1
    simp only [lex_measure]
    rw [hs]
    exact Prod.Lex.right _ h.2

/-- [I.P07] Well-foundedness of the denotational order:
    denotational_lt is a subrelation of the lexicographic order on (Nat, Nat),
    which is well-founded since Nat is well-ordered. -/
theorem denotational_lt_wf : WellFounded denotational_lt :=
  Subrelation.wf
    (fun h => denotational_lt_sub_lex h)
    (InvImage.wf lex_measure WellFoundedRelation.wf)

end Tau.Denotation
