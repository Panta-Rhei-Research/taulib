import TauLib.BookI.Boundary.TauRealAnalyticalHelpers
import Mathlib.Tactic.Ring
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity

/-!
# TauLib.BookI.Boundary.TauRealE

The constructive real `TauReal.e` as the Cauchy sequence of partial
sums `Σ_{k=0}^{n-1} 1/k!`, proven Cauchy with explicit modulus `k + 3`.

## Registry Cross-References

- [I.D84] TauReal, [I.D111] TauReal.IsCauchy
- [I.D115] TauRat partial sum helpers (Wave 3a)
- [I.D116] TauRealAnalyticalHelpers (Wave 3 helpers)

## Mathematical Content

**Wave 3b** of the TauReal infrastructure (see `ROADMAP-3-HINGES.md`).

Proof chain for `TauReal.e.IsCauchy`:

1. `1/k! ≤ 1/2^(k−1)` for `k ≥ 1`  (from `Nat.factorial_ge_two_pow`).
2. Telescoping geometric bound: `sumFromTo e_term n m ≤ 4/2^n − 4/2^m`
   (the `−4/2^m` tail term is essential for the induction to close).
3. `|e_partial m − e_partial n| ≤ 4/2^n` for `1 ≤ n ≤ m`.
4. `4/2^n < 1/(k+1)` for `n ≥ k + 3`  (via `Rat.four_div_two_pow_lt_recip`).
5. `modulus k := k + 3` closes `IsCauchy`.
-/

set_option autoImplicit false

namespace Tau.Boundary

open Tau.Denotation

-- ============================================================
-- PART 1: DEFINITIONS
-- ============================================================

/-- The k-th term of the exponential series at 1: `1/k!`. -/
def TauRat.e_term (k : Nat) : TauRat :=
  ⟨⟨1, 0⟩, Nat.factorial k, Nat.factorial_pos k⟩

theorem TauRat.e_term_toRat (k : Nat) :
    (TauRat.e_term k).toRat = 1 / (Nat.factorial k : Rat) := by
  unfold TauRat.e_term TauRat.toRat TauInt.toInt
  push_cast; ring

theorem TauRat.e_term_pos (k : Nat) : 0 < (TauRat.e_term k).toRat := by
  rw [TauRat.e_term_toRat]
  have h : (0 : Rat) < (Nat.factorial k : Rat) := by
    have := Nat.factorial_pos k; exact_mod_cast this
  exact div_pos (by norm_num) h

theorem TauRat.abs_e_term_toRat (k : Nat) :
    ((TauRat.e_term k).abs).toRat = (TauRat.e_term k).toRat := by
  rw [TauRat.toRat_abs, abs_of_pos (TauRat.e_term_pos k)]

/-- Partial sum of the exponential series. -/
def TauRat.e_partial (n : Nat) : TauRat := TauRat.sum TauRat.e_term n

/-- The constructive real `e`. -/
def TauReal.e : TauReal := ⟨TauRat.e_partial⟩

-- ============================================================
-- PART 2: BOUND ON INDIVIDUAL TERMS
-- ============================================================

/-- `1/k! ≤ 1/2^(k−1)` for `k ≥ 1`, at the Rat level. -/
theorem TauRat.e_term_le_geom (k : Nat) (hk : 1 ≤ k) :
    (TauRat.e_term k).toRat ≤ 1 / (2 ^ (k - 1) : Rat) := by
  rw [TauRat.e_term_toRat]
  have h_fact : (2 ^ (k - 1) : Nat) ≤ Nat.factorial k :=
    Nat.factorial_ge_two_pow k hk
  have h_fact_rat : ((2 : Rat) ^ (k - 1)) ≤ (Nat.factorial k : Rat) := by
    have h_cast : ((2 ^ (k - 1) : Nat) : Rat) ≤ (Nat.factorial k : Rat) := by
      exact_mod_cast h_fact
    have h_pow_cast : ((2 ^ (k - 1) : Nat) : Rat) = (2 : Rat) ^ (k - 1) := by
      push_cast; ring
    linarith
  have h_pos_pow : (0 : Rat) < 2 ^ (k - 1) := by positivity
  have h_pos_fact : (0 : Rat) < (Nat.factorial k : Rat) := by
    have := Nat.factorial_pos k; exact_mod_cast this
  rw [div_le_div_iff₀ h_pos_fact h_pos_pow]
  linarith

-- ============================================================
-- PART 3: TELESCOPING GEOMETRIC BOUND ON sumFromTo e_term
-- ============================================================

/-- Strengthened bound with telescoping tail: the `−4/2^m` term is what
    lets the induction close. -/
theorem TauReal.sumFromTo_e_term_bound (n : Nat) (hn : 1 ≤ n) :
    ∀ m, n ≤ m →
    (TauRat.sumFromTo TauRat.e_term n m).toRat
      ≤ 4 / (2 ^ n : Rat) - 4 / (2 ^ m : Rat) := by
  intro m hnm
  induction m with
  | zero => omega
  | succ m ih =>
    by_cases h_eq : n = m + 1
    · subst h_eq
      rw [TauRat.sumFromTo_self, toRat_zero]
      linarith
    · have hnm' : n ≤ m := by omega
      have h_m_ge_one : 1 ≤ m := by omega
      have ih' := ih hnm'
      have h_rec : TauRat.sumFromTo TauRat.e_term n (m + 1) =
                   (TauRat.sumFromTo TauRat.e_term n m).add (TauRat.e_term m) := by
        show (if n ≤ m then _ else _) = _; rw [if_pos hnm']
      rw [h_rec, toRat_add]
      have h_term_bound : (TauRat.e_term m).toRat ≤ 1 / (2 ^ (m - 1) : Rat) :=
        TauRat.e_term_le_geom m h_m_ge_one
      have h_rewrite_term : (1 : Rat) / 2 ^ (m - 1) = 2 / 2 ^ m :=
        Rat.one_div_two_pow_pred_eq_two_div_two_pow m h_m_ge_one
      have h_rewrite_goal : (4 : Rat) / 2 ^ (m + 1) = 2 / 2 ^ m :=
        Rat.four_div_two_pow_succ_eq_two_div_two_pow m
      rw [h_rewrite_term] at h_term_bound
      rw [h_rewrite_goal]
      -- Tell linarith that `4/2^m = 2 * (2/2^m)` so it can chain ih' through.
      have h_BC : (4 : Rat) / 2 ^ m = 2 * (2 / 2 ^ m) := by ring
      rw [h_BC] at ih'
      linarith [ih', h_term_bound]

-- ============================================================
-- PART 4: MAIN Cauchy BOUND  |e_partial m − e_partial n| ≤ 4/2^n
-- ============================================================

theorem TauReal.e_partial_cauchy_bound (m n : Nat) (hn : 1 ≤ n) (hnm : n ≤ m) :
    |((TauRat.e_partial m).toRat - (TauRat.e_partial n).toRat)|
      ≤ 4 / (2 ^ n : Rat) := by
  unfold TauRat.e_partial
  rw [TauRat.sum_sub_toRat_eq_sumFromTo TauRat.e_term n m hnm]
  have h_tri := TauRat.sumFromTo_abs_le TauRat.e_term n m
  have h_strong := TauReal.sumFromTo_e_term_bound n hn m hnm
  -- |e_term k| = e_term k at toRat, so sumFromTo |e_term| n m = sumFromTo e_term n m.
  have h_abs_eq : (TauRat.sumFromTo (fun k => (TauRat.e_term k).abs) n m).toRat
                    = (TauRat.sumFromTo TauRat.e_term n m).toRat := by
    clear h_tri h_strong hnm hn
    induction m with
    | zero => simp [TauRat.sumFromTo_zero, toRat_zero]
    | succ m ih =>
      by_cases h : n ≤ m
      · have h_abs_rec :
            TauRat.sumFromTo (fun k => (TauRat.e_term k).abs) n (m + 1) =
              (TauRat.sumFromTo (fun k => (TauRat.e_term k).abs) n m).add
                ((TauRat.e_term m).abs) := by
          show (if n ≤ m then _ else _) = _; rw [if_pos h]
        have h_f_rec : TauRat.sumFromTo TauRat.e_term n (m + 1) =
              (TauRat.sumFromTo TauRat.e_term n m).add (TauRat.e_term m) := by
          show (if n ≤ m then _ else _) = _; rw [if_pos h]
        rw [h_abs_rec, h_f_rec, toRat_add, toRat_add, ih, TauRat.abs_e_term_toRat]
      · have h_abs_rec :
            TauRat.sumFromTo (fun k => (TauRat.e_term k).abs) n (m + 1) = TauRat.zero := by
          show (if n ≤ m then _ else _) = _; rw [if_neg h]
        have h_f_rec : TauRat.sumFromTo TauRat.e_term n (m + 1) = TauRat.zero := by
          show (if n ≤ m then _ else _) = _; rw [if_neg h]
        rw [h_abs_rec, h_f_rec]
  have h_pos_m : (0 : Rat) < 2 ^ m := by positivity
  have h_pos_4_2m : (0 : Rat) ≤ 4 / 2 ^ m := by
    have h_pos : (0 : Rat) < 2 ^ m := by positivity
    have h4 : (0 : Rat) ≤ 4 := by norm_num
    exact div_nonneg h4 (_root_.le_of_lt h_pos)
  rw [h_abs_eq] at h_tri
  linarith

-- ============================================================
-- PART 5: IsCauchy FOR TauReal.e  (modulus λ k => k + 3)
-- ============================================================

/-- `TauReal.e` is Cauchy with explicit modulus `λ k => k + 3`. -/
theorem TauReal.e_isCauchy : TauReal.e.IsCauchy := by
  refine ⟨fun k => k + 3, ?_⟩
  intro k m n hm hn
  -- After beta-reduction, hm : k + 3 ≤ m and hn : k + 3 ≤ n
  change k + 3 ≤ m at hm
  change k + 3 ≤ n at hn
  unfold TauRat.lt
  rw [TauRat.toRat_abs, toRat_sub, TauRat.ofNatRecip_toRat]
  show |((TauRat.e_partial m).toRat - (TauRat.e_partial n).toRat)|
         < 1 / ((k : Rat) + 1)
  by_cases h_le : n ≤ m
  · have h_n_ge : 1 ≤ n := by omega
    have h_bound := TauReal.e_partial_cauchy_bound m n h_n_ge h_le
    have h_lt_final : (4 : Rat) / (2 : Rat) ^ n < 1 / ((k : Rat) + 1) :=
      Rat.four_div_two_pow_lt_recip k n hn
    linarith
  · push_neg at h_le
    have h_m_ge : 1 ≤ m := by omega
    have h_swap_abs :
        |((TauRat.e_partial m).toRat - (TauRat.e_partial n).toRat)|
          = |((TauRat.e_partial n).toRat - (TauRat.e_partial m).toRat)| := by
      rw [show (TauRat.e_partial m).toRat - (TauRat.e_partial n).toRat
            = -((TauRat.e_partial n).toRat - (TauRat.e_partial m).toRat) from by ring,
          abs_neg]
    rw [h_swap_abs]
    have h_bound := TauReal.e_partial_cauchy_bound n m h_m_ge (Nat.le_of_lt h_le)
    have h_lt_final : (4 : Rat) / (2 : Rat) ^ m < 1 / ((k : Rat) + 1) :=
      Rat.four_div_two_pow_lt_recip k m hm
    linarith

end Tau.Boundary
