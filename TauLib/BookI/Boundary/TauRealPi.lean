import TauLib.BookI.Boundary.TauRealAnalyticalHelpers
import Mathlib.Tactic.Ring
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity

/-!
# TauLib.BookI.Boundary.TauRealPi

The constructive real `TauReal.pi` as the Cauchy sequence of partial
sums of the **Leibniz-pairs** representation:

  π = 8 · Σ_{k=0}^∞ 1 / ((4k+1)(4k+3))

This is algebraically the alternating Leibniz series with adjacent
terms paired into single positive rationals:

  4·(1 − 1/3) + 4·(1/5 − 1/7) + 4·(1/9 − 1/11) + ...
  = 4·Σ (1/(4k+1) − 1/(4k+3))
  = 8·Σ 1/((4k+1)(4k+3))                                (cross-multiply each pair)

Same TauReal equivalence class as alternating Leibniz (provable in
ZFC); the all-positive form lets us prove `IsCauchy` via the triangle
inequality alone, without invoking the alternating-series estimation
test.  Choice of representative motivated by proof-engineering economy
under the tactics-only Mathlib budget — see Wave 3 brainstorm in PR
discussion.

## Registry Cross-References

- [I.D84] TauReal, [I.D111] TauReal.IsCauchy
- [I.D115] TauRat partial sum helpers (Wave 3a)
- [I.D116] TauRealAnalyticalHelpers (Wave 3 helpers)
- [I.D117] TauReal.e (Wave 3b, parallel proof structure)

## Mathematical Content

**Wave 3c** of the TauReal infrastructure (see `ROADMAP-3-HINGES.md`).

Proof chain for `TauReal.pi.IsCauchy`:

1. `pi_pair_term k = 8/((4k+1)(4k+3))` — all-positive TauRat term.
2. Bound: `pi_pair_term k ≤ (1/2) · (1/k − 1/(k+1))` for `k ≥ 1`,
   using `(4k+1)(4k+3) ≥ 16·k·(k+1)`.
3. Telescoping: `Σ_{k=n}^{m-1} (1/k − 1/(k+1)) = 1/n − 1/m`.
4. Combined: `sumFromTo pi_pair_term n m ≤ (1/(2n) − 1/(2m))` for
   `1 ≤ n ≤ m` — telescoping is **clean** (no geometric scaling
   needed, unlike Wave 3b's e), because the bound is an exact
   `1/k − 1/(k+1)` partial-fraction.
5. `|pi_partial m − pi_partial n| ≤ 1/(2n)` for `1 ≤ n ≤ m`.
6. `1/(2n) < 1/(k+1)` for `n ≥ k + 3` (in fact `n ≥ k + 1` suffices,
   but `k + 3` matches Wave 3b's modulus shape for visual parallelism).
7. `modulus k := k + 3` closes `IsCauchy`.
-/

set_option autoImplicit false

namespace Tau.Boundary

open Tau.Denotation

-- ============================================================
-- PART 1: DEFINITIONS
-- ============================================================

/-- The k-th paired Leibniz term: `8 / ((4k+1)(4k+3))`. -/
def TauRat.pi_pair_term (k : Nat) : TauRat :=
  ⟨⟨8, 0⟩, (4 * k + 1) * (4 * k + 3), by positivity⟩

theorem TauRat.pi_pair_term_toRat (k : Nat) :
    (TauRat.pi_pair_term k).toRat = 8 / (((4 * k + 1) * (4 * k + 3) : Nat) : Rat) := by
  unfold TauRat.pi_pair_term TauRat.toRat TauInt.toInt
  push_cast; ring

theorem TauRat.pi_pair_term_pos (k : Nat) : 0 < (TauRat.pi_pair_term k).toRat := by
  rw [TauRat.pi_pair_term_toRat]
  have h_pos : (0 : Rat) < (((4 * k + 1) * (4 * k + 3) : Nat) : Rat) := by
    have : 0 < (4 * k + 1) * (4 * k + 3) := by positivity
    exact_mod_cast this
  exact div_pos (by norm_num) h_pos

theorem TauRat.abs_pi_pair_term_toRat (k : Nat) :
    ((TauRat.pi_pair_term k).abs).toRat = (TauRat.pi_pair_term k).toRat := by
  rw [TauRat.toRat_abs, abs_of_pos (TauRat.pi_pair_term_pos k)]

/-- Partial sum of the Leibniz-pairs series. -/
def TauRat.pi_partial (n : Nat) : TauRat := TauRat.sum TauRat.pi_pair_term n

/-- The constructive real `π`. -/
def TauReal.pi : TauReal := ⟨TauRat.pi_partial⟩

-- ============================================================
-- PART 2: PER-TERM BOUND  pi_pair_term k ≤ (1/2)(1/k − 1/(k+1))
-- ============================================================

/-- `(4k+1)(4k+3) ≥ 16 · k · (k+1)`, since
    `(4k+1)(4k+3) = 16k² + 16k + 3 = 16k(k+1) + 3`. -/
theorem Nat.four_k_plus_one_three_ge (k : Nat) :
    16 * k * (k + 1) ≤ (4 * k + 1) * (4 * k + 3) := by
  have : (4 * k + 1) * (4 * k + 3) = 16 * k * (k + 1) + 3 := by ring
  omega

/-- `pi_pair_term k ≤ (1/2) · (1/k − 1/(k+1))` for `k ≥ 1`, at Rat level. -/
theorem TauRat.pi_pair_term_le_telescope (k : Nat) (hk : 1 ≤ k) :
    (TauRat.pi_pair_term k).toRat ≤ (1 / 2) * (1 / (k : Rat) - 1 / ((k : Rat) + 1)) := by
  rw [TauRat.pi_pair_term_toRat]
  have h_k_pos : (0 : Rat) < (k : Rat) := by
    have : (1 : Rat) ≤ (k : Rat) := by exact_mod_cast hk
    linarith
  have h_k1_pos : (0 : Rat) < (k : Rat) + 1 := by linarith
  have h_kne : (k : Rat) ≠ 0 := ne_of_gt h_k_pos
  have h_k1ne : ((k : Rat) + 1) ≠ 0 := ne_of_gt h_k1_pos
  -- Step 1: simplify (1/k - 1/(k+1)) = 1/(k(k+1))
  have h_diff : (1 : Rat) / (k : Rat) - 1 / ((k : Rat) + 1)
                  = 1 / ((k : Rat) * ((k : Rat) + 1)) := by
    rw [div_sub_div _ _ h_kne h_k1ne, mul_one, one_mul]
    congr 1; ring
  rw [h_diff]
  -- Goal:  8 / (((4k+1)(4k+3) : Nat) : Rat) ≤ (1/2) * (1 / (k * (k+1)))
  -- Step 2: simplify (1/2) * (1 / (k(k+1))) = 1 / (2·k·(k+1))
  have h_kk1_pos : (0 : Rat) < (k : Rat) * ((k : Rat) + 1) := mul_pos h_k_pos h_k1_pos
  have h_2kk1_pos : (0 : Rat) < 2 * ((k : Rat) * ((k : Rat) + 1)) := by linarith
  have h_rhs_simp : (1 / 2 : Rat) * (1 / ((k : Rat) * ((k : Rat) + 1)))
                       = 1 / (2 * ((k : Rat) * ((k : Rat) + 1))) := by
    rw [div_mul_div_comm]; norm_num
  rw [h_rhs_simp]
  -- Goal:  8 / (((4k+1)(4k+3) : Nat) : Rat) ≤ 1 / (2 * (k * (k+1)))
  have h_prod_pos : (0 : Rat) < (((4 * k + 1) * (4 * k + 3) : Nat) : Rat) := by
    have : 0 < (4 * k + 1) * (4 * k + 3) := by positivity
    exact_mod_cast this
  rw [div_le_div_iff₀ h_prod_pos h_2kk1_pos]
  -- Goal:  8 * (2 * (k * (k+1))) ≤ 1 * (((4k+1)(4k+3) : Nat) : Rat)
  rw [one_mul]
  -- Goal:  8 * (2 * (k * (k+1))) ≤ (((4k+1)(4k+3) : Nat) : Rat)
  -- Use the Nat-level bound  16·k·(k+1) ≤ (4k+1)(4k+3)
  have h_nat := Nat.four_k_plus_one_three_ge k
  have h_rat_cast : ((16 * k * (k + 1) : Nat) : Rat)
                      ≤ (((4 * k + 1) * (4 * k + 3) : Nat) : Rat) := by exact_mod_cast h_nat
  have h_lhs_eq : ((16 * k * (k + 1) : Nat) : Rat)
                    = 8 * (2 * ((k : Rat) * ((k : Rat) + 1))) := by push_cast; ring
  linarith

-- ============================================================
-- PART 3: TELESCOPING SUM BOUND
-- ============================================================

/-- Strengthened telescoping bound on the ranged sum:
    `sumFromTo pi_pair_term n m ≤ 1/(2n) − 1/(2m)` for `1 ≤ n ≤ m`. -/
theorem TauReal.sumFromTo_pi_pair_term_bound (n : Nat) (hn : 1 ≤ n) :
    ∀ m, n ≤ m →
    (TauRat.sumFromTo TauRat.pi_pair_term n m).toRat
      ≤ 1 / (2 * (n : Rat)) - 1 / (2 * (m : Rat)) := by
  intro m hnm
  induction m with
  | zero => omega
  | succ m ih =>
    by_cases h_eq : n = m + 1
    · subst h_eq
      rw [TauRat.sumFromTo_self, toRat_zero]
      have h_pos : (0 : Rat) < (m : Rat) + 1 := by
        have : (0 : Rat) ≤ (m : Rat) := by exact_mod_cast Nat.zero_le m
        linarith
      have h_2pos : (0 : Rat) < 2 * ((m : Rat) + 1) := by linarith
      have h_recip_le : (1 : Rat) / (2 * ((m : Rat) + 1)) ≤ 1 / (2 * ((m : Rat) + 1)) :=
        _root_.le_refl _
      -- Goal: 0 ≤ 1/(2(m+1)) − 1/(2(m+1))
      have : (1 : Rat) / (2 * ((m : Rat) + 1)) - 1 / (2 * ((m : Rat) + 1)) = 0 := by ring
      have h_cast : ((m + 1 : Nat) : Rat) = (m : Rat) + 1 := by push_cast; ring
      rw [h_cast]
      linarith
    · have hnm' : n ≤ m := by omega
      have h_m_ge_one : 1 ≤ m := by omega
      have ih' := ih hnm'
      have h_rec : TauRat.sumFromTo TauRat.pi_pair_term n (m + 1) =
                   (TauRat.sumFromTo TauRat.pi_pair_term n m).add (TauRat.pi_pair_term m) := by
        show (if n ≤ m then _ else _) = _; rw [if_pos hnm']
      rw [h_rec, toRat_add]
      have h_term_bound : (TauRat.pi_pair_term m).toRat ≤
            (1 / 2) * (1 / (m : Rat) - 1 / ((m : Rat) + 1)) :=
        TauRat.pi_pair_term_le_telescope m h_m_ge_one
      -- Goal: SFT.toRat + pi_pair_term m .toRat ≤ 1/(2n) − 1/(2(m+1))
      -- IH:   SFT.toRat ≤ 1/(2n) − 1/(2m)
      -- Term: pi_pair_term m .toRat ≤ (1/2)(1/m − 1/(m+1)) = 1/(2m) − 1/(2(m+1))
      -- Sum:  SFT + term ≤ (1/(2n) − 1/(2m)) + (1/(2m) − 1/(2(m+1))) = 1/(2n) − 1/(2(m+1))  ✓
      -- Prepare cast equality for m + 1
      have h_cast_succ : ((m + 1 : Nat) : Rat) = (m : Rat) + 1 := by push_cast; ring
      rw [h_cast_succ]
      -- Bridge for linarith: (1/2)(1/m − 1/(m+1)) = 1/(2m) − 1/(2(m+1))
      have h_term_rewrite :
          (1 / 2) * (1 / (m : Rat) - 1 / ((m : Rat) + 1))
            = 1 / (2 * (m : Rat)) - 1 / (2 * ((m : Rat) + 1)) := by
        have h_m_pos : (0 : Rat) < (m : Rat) := by exact_mod_cast h_m_ge_one
        have h_m1_pos : (0 : Rat) < (m : Rat) + 1 := by linarith
        field_simp
      rw [h_term_rewrite] at h_term_bound
      linarith [ih']

-- ============================================================
-- PART 4: MAIN Cauchy BOUND  |pi_partial m − pi_partial n| ≤ 1/(2n)
-- ============================================================

theorem TauReal.pi_partial_cauchy_bound (m n : Nat) (hn : 1 ≤ n) (hnm : n ≤ m) :
    |((TauRat.pi_partial m).toRat - (TauRat.pi_partial n).toRat)|
      ≤ 1 / (2 * (n : Rat)) := by
  unfold TauRat.pi_partial
  rw [TauRat.sum_sub_toRat_eq_sumFromTo TauRat.pi_pair_term n m hnm]
  have h_tri := TauRat.sumFromTo_abs_le TauRat.pi_pair_term n m
  have h_strong := TauReal.sumFromTo_pi_pair_term_bound n hn m hnm
  -- |pi_pair_term k| = pi_pair_term k at toRat (positive)
  have h_abs_eq : (TauRat.sumFromTo (fun k => (TauRat.pi_pair_term k).abs) n m).toRat
                    = (TauRat.sumFromTo TauRat.pi_pair_term n m).toRat := by
    clear h_tri h_strong hnm hn
    induction m with
    | zero => simp [TauRat.sumFromTo_zero, toRat_zero]
    | succ m ih =>
      by_cases h : n ≤ m
      · have h_abs_rec :
            TauRat.sumFromTo (fun k => (TauRat.pi_pair_term k).abs) n (m + 1) =
              (TauRat.sumFromTo (fun k => (TauRat.pi_pair_term k).abs) n m).add
                ((TauRat.pi_pair_term m).abs) := by
          show (if n ≤ m then _ else _) = _; rw [if_pos h]
        have h_f_rec : TauRat.sumFromTo TauRat.pi_pair_term n (m + 1) =
              (TauRat.sumFromTo TauRat.pi_pair_term n m).add (TauRat.pi_pair_term m) := by
          show (if n ≤ m then _ else _) = _; rw [if_pos h]
        rw [h_abs_rec, h_f_rec, toRat_add, toRat_add, ih, TauRat.abs_pi_pair_term_toRat]
      · have h_abs_rec :
            TauRat.sumFromTo (fun k => (TauRat.pi_pair_term k).abs) n (m + 1) = TauRat.zero := by
          show (if n ≤ m then _ else _) = _; rw [if_neg h]
        have h_f_rec : TauRat.sumFromTo TauRat.pi_pair_term n (m + 1) = TauRat.zero := by
          show (if n ≤ m then _ else _) = _; rw [if_neg h]
        rw [h_abs_rec, h_f_rec]
  have h_pos_2m : (0 : Rat) < 2 * (m : Rat) := by
    have h_m_ge : 1 ≤ m := by omega
    have : (0 : Rat) < (m : Rat) := by exact_mod_cast h_m_ge
    linarith
  have h_recip_2m_nn : (0 : Rat) ≤ 1 / (2 * (m : Rat)) := by
    have h1 : (0 : Rat) ≤ 1 := by norm_num
    exact div_nonneg h1 (_root_.le_of_lt h_pos_2m)
  rw [h_abs_eq] at h_tri
  linarith

-- ============================================================
-- PART 5: Workhorse  1/(2n) < 1/(k+1)  FROM  k + 3 ≤ n
-- ============================================================

/-- For `n ≥ k + 3`, we have `1/(2n) < 1/(k+1)`.  In fact `n ≥ k + 1`
    suffices, but `k + 3` matches Wave 3b's modulus shape. -/
theorem Rat.one_div_two_n_lt_recip (k n : Nat) (hn : k + 3 ≤ n) :
    (1 : Rat) / (2 * (n : Rat)) < 1 / ((k : Rat) + 1) := by
  have h_n_pos : (0 : Rat) < (n : Rat) := by
    have : 1 ≤ n := by omega
    exact_mod_cast this
  have h_2n_pos : (0 : Rat) < 2 * (n : Rat) := by linarith
  have h_k1_pos : (0 : Rat) < (k : Rat) + 1 := by
    have : (0 : Rat) ≤ (k : Rat) := by exact_mod_cast Nat.zero_le k
    linarith
  rw [div_lt_div_iff₀ h_2n_pos h_k1_pos]
  -- Goal: (k+1) < 2n  for  n ≥ k+3
  have h_cast : ((k + 3 : Nat) : Rat) ≤ (n : Rat) := by exact_mod_cast hn
  have h_cast_eq : ((k + 3 : Nat) : Rat) = (k : Rat) + 3 := by push_cast; ring
  linarith

-- ============================================================
-- PART 6: IsCauchy FOR TauReal.pi  (modulus λ k => k + 3)
-- ============================================================

/-- `TauReal.pi` is Cauchy with explicit modulus `λ k => k + 3`. -/
theorem TauReal.pi_isCauchy : TauReal.pi.IsCauchy := by
  refine ⟨fun k => k + 3, ?_⟩
  intro k m n hm hn
  change k + 3 ≤ m at hm
  change k + 3 ≤ n at hn
  unfold TauRat.lt
  rw [TauRat.toRat_abs, toRat_sub, TauRat.ofNatRecip_toRat]
  show |((TauRat.pi_partial m).toRat - (TauRat.pi_partial n).toRat)|
         < 1 / ((k : Rat) + 1)
  by_cases h_le : n ≤ m
  · have h_n_ge : 1 ≤ n := by omega
    have h_bound := TauReal.pi_partial_cauchy_bound m n h_n_ge h_le
    have h_lt_final : (1 : Rat) / (2 * (n : Rat)) < 1 / ((k : Rat) + 1) :=
      Rat.one_div_two_n_lt_recip k n hn
    linarith
  · push_neg at h_le
    have h_m_ge : 1 ≤ m := by omega
    have h_swap_abs :
        |((TauRat.pi_partial m).toRat - (TauRat.pi_partial n).toRat)|
          = |((TauRat.pi_partial n).toRat - (TauRat.pi_partial m).toRat)| := by
      rw [show (TauRat.pi_partial m).toRat - (TauRat.pi_partial n).toRat
            = -((TauRat.pi_partial n).toRat - (TauRat.pi_partial m).toRat) from by ring,
          abs_neg]
    rw [h_swap_abs]
    have h_bound := TauReal.pi_partial_cauchy_bound n m h_m_ge (Nat.le_of_lt h_le)
    have h_lt_final : (1 : Rat) / (2 * (m : Rat)) < 1 / ((k : Rat) + 1) :=
      Rat.one_div_two_n_lt_recip k m hm
    linarith

end Tau.Boundary
