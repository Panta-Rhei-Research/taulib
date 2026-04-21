import TauLib.BookI.Boundary.TauRealOrder
import Mathlib.Tactic.Ring
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push

/-!
# TauLib.BookI.Boundary.TauRealAbs

Absolute value on `TauReal`: pointwise `TauRat.abs` on the approximation
sequence.

## Registry Cross-References

- [I.D84] TauReal — the Cauchy completion of TauRat
- [I.D109] TauRat Absolute Value — `TauRat.abs` (Wave 1c), lifted pointwise
- [I.D112] TauReal.equiv — the Cauchy equivalence relation

New declarations (pending Wave 2 registry commit): `TauReal.abs`,
`TauReal.abs_nonneg`, `TauReal.abs_of_equiv`, `TauReal.abs_triangle`,
`TauReal.abs_preserves_cauchy`.

## Mathematical Content

**Wave 2c** of the TauReal infrastructure (see `ROADMAP-3-HINGES.md`).

- `TauReal.abs a := ⟨fun n => (a.approx n).abs⟩` — pointwise `TauRat.abs`.
- `abs` preserves `IsCauchy`: the reverse triangle inequality
  `||x| − |y|| ≤ |x − y|` transfers the Cauchy bound from `a` to `a.abs`
  without changing the modulus.
- `abs` is nonneg in the constructive `TauReal.le` sense.
- `abs` respects `TauReal.equiv` (well-defined on the quotient).
- Triangle inequality `(a + b).abs ≤ a.abs + b.abs` at the approximation
  level lifts to the Cauchy ordering.
-/

set_option autoImplicit false

namespace Tau.Boundary

open Tau.Denotation

-- ============================================================
-- PART 1: DEFINITION
-- ============================================================

/-- Absolute value on `TauReal`: pointwise `TauRat.abs` on the
    approximation sequence. -/
def TauReal.abs (a : TauReal) : TauReal :=
  ⟨fun n => (a.approx n).abs⟩

-- ============================================================
-- PART 2: POINTWISE BEHAVIOR AT toRat LEVEL
-- ============================================================

/-- The `n`th approximation of `a.abs` is the TauRat abs of the `n`th
    approximation of `a`. -/
@[simp] theorem TauReal.abs_approx (a : TauReal) (n : Nat) :
    (a.abs).approx n = (a.approx n).abs := rfl

-- ============================================================
-- PART 3: abs IS NONNEG (in TauReal.le)
-- ============================================================

/-- `0 ≤ a.abs` under `TauReal.le` — at every tolerance level, zero is
    strictly less than `|a.approx n| + 1/(k+1)` regardless of `n`. -/
theorem TauReal.abs_nonneg (a : TauReal) : TauReal.le TauReal.zero a.abs := by
  intro k
  refine ⟨0, fun n _ => ?_⟩
  -- Goal: TauRat.lt ((zero.approx n)) ((a.abs.approx n).add (ofNatRecip k))
  unfold TauRat.lt
  rw [toRat_add, TauRat.ofNatRecip_toRat]
  -- (zero.approx n).toRat = 0, (a.abs.approx n).toRat = (a.approx n).abs.toRat ≥ 0
  show (TauReal.zero.approx n).toRat < (a.abs.approx n).toRat + 1 / ((k : Rat) + 1)
  have h_zero : (TauReal.zero.approx n).toRat = 0 := by
    show ((TauRat.zero).toRat) = 0
    exact toRat_zero
  have h_abs_nonneg : 0 ≤ (a.abs.approx n).toRat := by
    show 0 ≤ ((a.approx n).abs).toRat
    exact TauRat.abs_nonneg (a.approx n)
  have h_recip : (0 : Rat) < 1 / ((k : Rat) + 1) := by
    have : (0 : Rat) < (k : Rat) + 1 := by
      have : (0 : Rat) ≤ (k : Rat) := by exact_mod_cast Nat.zero_le k
      linarith
    exact div_pos (by norm_num) this
  rw [h_zero]
  linarith

-- ============================================================
-- PART 4: EQUIV PRESERVATION (well-definedness)
-- ============================================================

/-- Reverse triangle inequality at the TauRat toRat level:
    `||a.toRat| - |b.toRat|| ≤ |a.toRat - b.toRat|`. -/
private theorem TauRat.abs_sub_abs_le_abs_sub_toRat (a b : TauRat) :
    |a.abs.toRat - b.abs.toRat| ≤ |a.toRat - b.toRat| := by
  rw [TauRat.toRat_abs, TauRat.toRat_abs]
  exact abs_abs_sub_abs_le_abs_sub (a.toRat) (b.toRat)

/-- `abs` is well-defined modulo `TauReal.equiv`: if `a ≡ b` then
    `a.abs ≡ b.abs`. -/
theorem TauReal.abs_of_equiv {a b : TauReal} (h : TauReal.equiv a b) :
    TauReal.equiv a.abs b.abs := by
  obtain ⟨μ, h_mod⟩ := h
  refine ⟨μ, fun k n hn => ?_⟩
  have h_orig := h_mod k n hn
  unfold TauRat.lt at h_orig ⊢
  rw [TauRat.toRat_abs, toRat_sub] at h_orig
  rw [TauRat.toRat_abs, toRat_sub]
  have h_rev := TauRat.abs_sub_abs_le_abs_sub_toRat (a.approx n) (b.approx n)
  -- Normalize `a.abs.approx n` to `(a.approx n).abs` for linarith
  show |((a.approx n).abs).toRat - ((b.approx n).abs).toRat| < (TauRat.ofNatRecip k).toRat
  linarith

-- ============================================================
-- PART 5: abs PRESERVES IsCauchy
-- ============================================================

/-- `abs` preserves the Cauchy property: if `a` is Cauchy with modulus
    `μ`, so is `a.abs` with the same modulus. -/
theorem TauReal.abs_preserves_cauchy {a : TauReal}
    (h : TauReal.IsCauchy a) : TauReal.IsCauchy a.abs := by
  obtain ⟨μ, h_mod⟩ := h
  refine ⟨μ, fun k m n hm hn => ?_⟩
  have h_orig := h_mod k m n hm hn
  unfold TauRat.lt at h_orig ⊢
  rw [TauRat.toRat_abs, toRat_sub] at h_orig
  rw [TauRat.toRat_abs, toRat_sub]
  have h_rev := TauRat.abs_sub_abs_le_abs_sub_toRat (a.approx m) (a.approx n)
  show |((a.approx m).abs).toRat - ((a.approx n).abs).toRat| < (TauRat.ofNatRecip k).toRat
  linarith

-- ============================================================
-- PART 6: TRIANGLE INEQUALITY
-- ============================================================

/-- Triangle inequality on TauReal: `(a + b).abs ≤ a.abs + b.abs` in the
    `TauReal.le` sense.

    At each index, `TauRat.abs_triangle` (Wave 1c) gives the pointwise
    bound `(a.approx n + b.approx n).abs.toRat
      ≤ (a.approx n).abs.toRat + (b.approx n).abs.toRat`.
    The difference is therefore ≤ 0 pointwise, hence strictly less than
    any positive tolerance. -/
theorem TauReal.abs_triangle (a b : TauReal) :
    TauReal.le ((a.add b).abs) ((a.abs).add (b.abs)) := by
  intro k
  refine ⟨0, fun n _ => ?_⟩
  -- Goal: ((a.add b).abs.approx n) .lt  ((a.abs.add b.abs).approx n + 1/(k+1))
  unfold TauRat.lt
  rw [toRat_add, TauRat.ofNatRecip_toRat]
  -- LHS.toRat = ((a.approx n).add (b.approx n)).abs.toRat
  -- The inner structural `.add` on TauReal unfolds to TauRat.add at each n.
  show ((a.add b).abs.approx n).toRat
         < ((a.abs.add b.abs).approx n).toRat + 1 / ((k : Rat) + 1)
  have h_LHS : ((a.add b).abs.approx n).toRat
                 = ((a.approx n).add (b.approx n)).abs.toRat := rfl
  have h_RHS : ((a.abs.add b.abs).approx n).toRat
                 = (a.approx n).abs.toRat + (b.approx n).abs.toRat := by
    show ((a.approx n).abs.add (b.approx n).abs).toRat = _
    rw [toRat_add]
  rw [h_LHS, h_RHS]
  have h_tri := TauRat.abs_triangle (a.approx n) (b.approx n)
  have h_recip : (0 : Rat) < 1 / ((k : Rat) + 1) := by
    have : (0 : Rat) < (k : Rat) + 1 := by
      have : (0 : Rat) ≤ (k : Rat) := by exact_mod_cast Nat.zero_le k
      linarith
    exact div_pos (by norm_num) this
  linarith

end Tau.Boundary
