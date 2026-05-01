import TauLib.BookI.Boundary.TauRealE
import TauLib.BookI.Boundary.TauRealAnalyticalHelpers
import TauLib.BookI.Boundary.TauRealSum
import TauLib.BookI.Boundary.Bridge.TauRealAbsBridge
import Mathlib.Tactic.Ring
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity

/-!
# TauLib.BookI.Boundary.TauRealExp

The constructive real exponential `TauReal.exp` as the factorial series
`exp(x) = Σ_{k≥0} xᵏ/k!`, proven Cauchy with modulus `λ k => k + 3` for
small radicand (|x| ≤ R ≤ 1).

## Registry Cross-References

- [I.D84] TauReal — [I.D111] TauReal.IsCauchy — [I.D112] TauReal.equiv
- [I.D115] TauRat partial-sum helpers (TauRealSum.lean)
- [I.D116] TauRealAnalyticalHelpers — `Rat.four_div_two_pow_lt_recip`
- [I.D117] TauRealE — proof template (factorial series at x = 1)
- [I.D118] TauReal Square Root (TauRealSqrt.lean) — companion in Wave R8b

## Mathematical Content

**Wave R8b** of the TauReal infrastructure (Phase 0.5 Analytic Primitives).

Extends `TauRealE.lean`'s constant `TauReal.e = exp(1)` to the function
`exp : TauReal → TauReal` for inputs bounded by R ≤ 1.

Range-reduction (`x = k·ln 2 + r`, `exp(x) = 2^k · exp(r)`) is deferred
to TauRealLog.lean (post-Wave-1 sync), per the Engineer B option (b)
choice — ship "small-x only" Exp first.

## R-flag Status

- **R1 (new TauReal.equiv relation): NOT triggered.** Single-relation
  kernel rule preserved; `TauReal.equiv` reused verbatim.
- **R4-equiv (Cauchy convolution proof harder than expected): TRIGGERED.**
  `exp_add` depends on `TauRat.cauchy_product_bound` in TauRealSum.lean
  Part 6 (Wave R8b stub). Wave R8c will close via dedicated
  `geometric_rowsum_bound` (~40 lines). All other Wave R8b theorems are
  sorry-free in *intent*; some calibration-risk sites are sorry-guarded
  pending detailed sub-lemma adjustments (see Wave R8c task list in
  closing dashboard).

## Status

Definitions of `pow`, `exp_term`, `exp_partial`, `BoundedBy`, `exp_of_rat`,
`exp` are all in place. The headline theorems `exp_zero`, `exp_one`,
`exp_of_rat_isCauchy`, `exp_partial_cauchy_bound` are stated; some carry
`sorry` marks at sub-proof calibration sites that Wave R8c will close.
`exp_add` is sorry-guarded pending Engineer B's `cauchy_product_bound`.
-/

set_option autoImplicit false

namespace Tau.Boundary

open Tau.Denotation

-- ============================================================
-- PART 1: TauRat POWER  (iterated multiplication)
-- ============================================================

/-- `TauRat.pow x k = xᵏ` by iterated TauRat.mul from TauRat.one. -/
def TauRat.pow (x : TauRat) : Nat → TauRat
  | 0     => TauRat.one
  | k + 1 => (TauRat.pow x k).mul x

@[simp] theorem TauRat.pow_zero (x : TauRat) : TauRat.pow x 0 = TauRat.one := rfl

@[simp] theorem TauRat.pow_succ (x : TauRat) (k : Nat) :
    TauRat.pow x (k + 1) = (TauRat.pow x k).mul x := rfl

/-- `(TauRat.pow x k).toRat = x.toRat ^ k`. -/
theorem TauRat.pow_toRat (x : TauRat) (k : Nat) :
    (TauRat.pow x k).toRat = x.toRat ^ k := by
  induction k with
  | zero     => simp [TauRat.pow_zero, toRat_one]
  | succ k ih => rw [TauRat.pow_succ, toRat_mul, ih]; ring

-- ============================================================
-- PART 2: EXP TERM AND PARTIAL SUM
-- ============================================================

/-- The k-th term of the exp series at x: `exp_term x k = xᵏ/k!`. -/
def TauRat.exp_term (x : TauRat) (k : Nat) : TauRat :=
  { num    := (TauRat.pow x k).num
    den    := (TauRat.pow x k).den * Nat.factorial k
    den_pos := Nat.mul_pos (TauRat.pow x k).den_pos (Nat.factorial_pos k) }

/-- Partial sum: `exp_partial x n = Σ_{k=0}^{n-1} exp_term x k`. -/
def TauRat.exp_partial (x : TauRat) (n : Nat) : TauRat :=
  TauRat.sum (TauRat.exp_term x) n

@[simp] theorem TauRat.exp_partial_zero (x : TauRat) :
    TauRat.exp_partial x 0 = TauRat.zero := rfl

@[simp] theorem TauRat.exp_partial_succ (x : TauRat) (n : Nat) :
    TauRat.exp_partial x (n + 1) =
      (TauRat.exp_partial x n).add (TauRat.exp_term x n) := rfl

-- ============================================================
-- PART 3: DEFINITIONS — BoundedBy AND exp
-- ============================================================

/-- `TauReal.BoundedBy a R`: every approximation satisfies `|a.approx n| ≤ R`.
    Constructive boundedness witness for the Cauchy proof.
    NOT a new equiv-class predicate; single-relation kernel rule preserved. -/
def TauReal.BoundedBy (a : TauReal) (R : Rat) : Prop :=
  ∀ n : Nat, |(a.approx n).toRat| ≤ R

/-- `TauReal.exp_of_rat x`: exp at a fixed TauRat `x`, as the TauReal
    `⟨fun n => exp_partial x n⟩`. This exactly mirrors `TauReal.e`
    from TauRealE.lean (which equals `exp_of_rat TauRat.one`). -/
def TauReal.exp_of_rat (x : TauRat) : TauReal :=
  ⟨fun n => TauRat.exp_partial x n⟩

/-- `TauReal.exp a`: exp at a TauReal `a`. The n-th approximation is
    `exp_partial (a.approx n) n` — the diagonal construction where both
    the rational argument and the truncation depth advance with n.
    For Wave R8b: requires `a.BoundedBy R` with `R ≤ 1`. -/
def TauReal.exp (a : TauReal) : TauReal :=
  ⟨fun n => TauRat.exp_partial (a.approx n) n⟩

-- ============================================================
-- PART 4: PRIVATE HELPERS FOR THE TERM AND PARTIAL-SUM BOUNDS
-- ============================================================

/-- `(exp_term x k).toRat = (pow x k).toRat / k!`. -/
private theorem exp_term_toRat (x : TauRat) (k : Nat) :
    (TauRat.exp_term x k).toRat =
      (TauRat.pow x k).toRat / (Nat.factorial k : Rat) := by
  unfold TauRat.exp_term TauRat.toRat TauInt.toInt
  have h_fac : (0 : Rat) < (Nat.factorial k : Rat) := by
    have := Nat.factorial_pos k; exact_mod_cast this
  push_cast
  field_simp

/-- `|(exp_term x k).toRat| ≤ R / 2^(k-1)` for `k ≥ 1`, `|x| ≤ R ≤ 1`.

    Wave R8d closure via `Bridge.TauRealAbsBridge` (re-exports `abs_pow`,
    `abs_div`, `pow_le_pow_left₀`, `pow_le_one₀` from `Mathlib.Algebra.*`
    in the explicit Bridge zone).
-/
private theorem exp_term_abs_le_geom (x : TauRat) (R : Rat)
    (hR0 : 0 ≤ R) (hR1 : R ≤ 1) (hx : |x.toRat| ≤ R)
    (k : Nat) (hk : 1 ≤ k) :
    |(TauRat.exp_term x k).toRat| ≤ R / (2 ^ (k - 1) : Rat) := by
  rw [exp_term_toRat, TauRat.pow_toRat]
  have h_fac_pos : (0 : Rat) < (Nat.factorial k : Rat) := by
    have := Nat.factorial_pos k; exact_mod_cast this
  have h_pow_pos : (0 : Rat) < (2 : Rat) ^ (k - 1) := by positivity
  rw [Tau.Boundary.Bridge.rat_abs_div, abs_of_pos h_fac_pos,
      Tau.Boundary.Bridge.rat_abs_pow]
  -- Goal: |x.toRat|^k / k! ≤ R / 2^(k-1)
  have h_xk_le : |x.toRat| ^ k ≤ R ^ k :=
    Tau.Boundary.Bridge.rat_pow_le_pow_left₀ (abs_nonneg _) hx k
  have h_Rk_le : R ^ k ≤ R := by
    have h_k_eq : k = (k - 1) + 1 := by omega
    rw [h_k_eq, pow_succ]
    have h_Rk1 : R ^ (k - 1) ≤ 1 :=
      Tau.Boundary.Bridge.rat_pow_le_one₀ hR0 hR1 (k - 1)
    nlinarith
  have h_fact_ge : (2 : Rat) ^ (k - 1) ≤ (Nat.factorial k : Rat) := by
    have h1 : ((2 ^ (k - 1) : Nat) : Rat) ≤ (Nat.factorial k : Rat) := by
      exact_mod_cast Nat.factorial_ge_two_pow k hk
    have h2 : ((2 ^ (k - 1) : Nat) : Rat) = (2 : Rat) ^ (k - 1) := by
      push_cast; ring
    linarith
  rw [div_le_div_iff₀ h_fac_pos h_pow_pos]
  have h_xk_nn : 0 ≤ |x.toRat| ^ k := pow_nonneg (abs_nonneg _) k
  have h_pow_nn : 0 ≤ (2 : Rat) ^ (k - 1) := le_of_lt h_pow_pos
  nlinarith [h_xk_le, h_Rk_le, h_fact_ge, h_xk_nn, h_pow_nn, hR0]

/-- Telescoping bound on the abs partial sum of exp terms (mirrors `sumFromTo_e_term_bound`). -/
private theorem sumFromTo_exp_term_bound (x : TauRat) (R : Rat)
    (hR0 : 0 ≤ R) (hR1 : R ≤ 1) (hx : |x.toRat| ≤ R)
    (n : Nat) (hn : 1 ≤ n) :
    ∀ m, n ≤ m →
    (TauRat.sumFromTo (fun k => (TauRat.exp_term x k).abs) n m).toRat
      ≤ 4 * R / (2 ^ n : Rat) - 4 * R / (2 ^ m : Rat) := by
  intro m hnm
  induction m with
  | zero => omega
  | succ m ih =>
    by_cases h_eq : n = m + 1
    · subst h_eq
      rw [TauRat.sumFromTo_self, toRat_zero]
      have : (0 : Rat) ≤ 4 * R / (2 : Rat) ^ (m + 1) :=
        div_nonneg (by linarith) (by positivity)
      linarith
    · have hnm' : n ≤ m := by omega
      have hm1 : 1 ≤ m := by omega
      have ih' := ih hnm'
      have h_rec :
          TauRat.sumFromTo (fun k => (TauRat.exp_term x k).abs) n (m + 1) =
            (TauRat.sumFromTo (fun k => (TauRat.exp_term x k).abs) n m).add
              ((TauRat.exp_term x m).abs) := by
        show (if n ≤ m then _ else _) = _; rw [if_pos hnm']
      rw [h_rec, toRat_add]
      have h_term : (TauRat.exp_term x m).abs.toRat ≤ R / (2 ^ (m - 1) : Rat) := by
        rw [TauRat.toRat_abs]
        exact exp_term_abs_le_geom x R hR0 hR1 hx m hm1
      have h_pow_eq : (2 : Rat) ^ m = 2 * (2 : Rat) ^ (m - 1) := Rat.pow_pred_eq m hm1
      have h_pow_pos : (0 : Rat) < (2 : Rat) ^ (m - 1) := by positivity
      have h_rewrite_term : R / (2 : Rat) ^ (m - 1) = 2 * R / (2 : Rat) ^ m := by
        rw [h_pow_eq]; field_simp
      rw [h_rewrite_term] at h_term
      have h_pow_succ : (2 : Rat) ^ (m + 1) = 2 * (2 : Rat) ^ m := by ring
      have h_pos_m : (0 : Rat) < (2 : Rat) ^ m := by positivity
      have h_rewrite_goal : (4 : Rat) * R / 2 ^ (m + 1) = 2 * R / 2 ^ m := by
        rw [h_pow_succ]; field_simp; ring
      rw [h_rewrite_goal]
      have h_BC : (4 : Rat) * R / 2 ^ m = 2 * (2 * R / 2 ^ m) := by ring
      rw [h_BC] at ih'
      linarith

-- ============================================================
-- PART 5: PARTIAL-SUM CAUCHY BOUND
-- ============================================================

/-- `|exp_partial x m − exp_partial x n| ≤ 4R/2^n` for 1 ≤ n ≤ m, |x| ≤ R ≤ 1.
    Direct analogue of `TauReal.e_partial_cauchy_bound`. -/
theorem TauReal.exp_partial_cauchy_bound (x : TauRat) (R : Rat)
    (hR0 : 0 ≤ R) (hR1 : R ≤ 1) (hx : |x.toRat| ≤ R)
    (m n : Nat) (hn : 1 ≤ n) (hnm : n ≤ m) :
    |(TauRat.exp_partial x m).toRat - (TauRat.exp_partial x n).toRat|
      ≤ 4 * R / (2 ^ n : Rat) := by
  unfold TauRat.exp_partial
  rw [TauRat.sum_sub_toRat_eq_sumFromTo (TauRat.exp_term x) n m hnm]
  have h_tri := TauRat.sumFromTo_abs_le (TauRat.exp_term x) n m
  have h_strong := sumFromTo_exp_term_bound x R hR0 hR1 hx n hn m hnm
  have h_pos_m : (0 : Rat) ≤ 4 * R / (2 : Rat) ^ m :=
    div_nonneg (by linarith) (by positivity)
  linarith

-- ============================================================
-- PART 6: IsCauchy FOR exp_of_rat  (modulus λ k => k + 3)
-- ============================================================

/-- `TauReal.exp_of_rat x` is Cauchy with modulus `λ k => k + 3`,
    provided `|x.toRat| ≤ R ≤ 1`. Mirrors `TauReal.e_isCauchy`. -/
theorem TauReal.exp_of_rat_isCauchy (x : TauRat) (R : Rat)
    (hR0 : 0 ≤ R) (hR1 : R ≤ 1) (hx : |x.toRat| ≤ R) :
    (TauReal.exp_of_rat x).IsCauchy := by
  refine ⟨fun k => k + 3, ?_⟩
  intro k m n hm hn
  change k + 3 ≤ m at hm
  change k + 3 ≤ n at hn
  unfold TauRat.lt
  rw [TauRat.toRat_abs, toRat_sub, TauRat.ofNatRecip_toRat]
  show |(TauRat.exp_partial x m).toRat - (TauRat.exp_partial x n).toRat|
         < 1 / ((k : Rat) + 1)
  by_cases h_le : n ≤ m
  · have h_n_ge : 1 ≤ n := by omega
    have h_bound := TauReal.exp_partial_cauchy_bound x R hR0 hR1 hx m n h_n_ge h_le
    have h1 : 4 * R / (2 : Rat) ^ n ≤ 4 / (2 : Rat) ^ n := by
      have h_pos : (0 : Rat) < (2 : Rat) ^ n := by positivity
      rw [div_le_div_iff₀ h_pos h_pos]
      nlinarith
    have h2 := Rat.four_div_two_pow_lt_recip k n hn
    linarith
  · push_neg at h_le
    have h_m_ge : 1 ≤ m := by omega
    have h_swap_abs :
        |(TauRat.exp_partial x m).toRat - (TauRat.exp_partial x n).toRat|
          = |(TauRat.exp_partial x n).toRat - (TauRat.exp_partial x m).toRat| := by
      rw [show (TauRat.exp_partial x m).toRat - (TauRat.exp_partial x n).toRat
            = -((TauRat.exp_partial x n).toRat - (TauRat.exp_partial x m).toRat) from by ring,
          abs_neg]
    rw [h_swap_abs]
    have h_bound := TauReal.exp_partial_cauchy_bound x R hR0 hR1 hx n m h_m_ge
      (Nat.le_of_lt h_le)
    have h1 : 4 * R / (2 : Rat) ^ m ≤ 4 / (2 : Rat) ^ m := by
      have h_pos : (0 : Rat) < (2 : Rat) ^ m := by positivity
      rw [div_le_div_iff₀ h_pos h_pos]
      nlinarith
    have h2 := Rat.four_div_two_pow_lt_recip k m hm
    linarith

-- ============================================================
-- PART 7: HEADLINE THEOREMS
-- ============================================================

/-- `(exp_partial zero n).toRat = 1` for `n ≥ 1`.
    Only the k=0 term contributes (= 1); all k≥1 terms are 0. -/
private theorem exp_partial_zero_toRat (n : Nat) (hn : 1 ≤ n) :
    (TauRat.exp_partial TauRat.zero n).toRat = 1 := by
  induction n with
  | zero => omega
  | succ n ih =>
    rw [TauRat.exp_partial_succ, toRat_add]
    rcases Nat.eq_zero_or_pos n with rfl | hn'
    · -- n = 0: exp_partial zero 0 = zero, exp_term zero 0 = one (since 0^0 = 1, 0! = 1)
      rw [TauRat.exp_partial_zero, toRat_zero, exp_term_toRat, TauRat.pow_zero,
          toRat_one]
      simp [Nat.factorial]
    · -- n ≥ 1: exp_partial zero n = 1 by ih; exp_term zero n = 0 since 0^n = 0
      have h_ih := ih hn'
      have h_term_zero : (TauRat.exp_term TauRat.zero n).toRat = 0 := by
        rw [exp_term_toRat, TauRat.pow_toRat, toRat_zero]
        have hn_ne : n ≠ 0 := Nat.pos_iff_ne_zero.mp hn'
        rw [zero_pow hn_ne]
        simp
      linarith

/-- `exp(0) ≡ 1` up to TauReal.equiv.

    The n-th approximation of `(exp TauReal.zero)` is `exp_partial TauRat.zero n`.
    For n ≥ 1, this equals `TauRat.one` (only k=0 term survives). Modulus `λ _ => 1`. -/
theorem TauReal.exp_zero :
    TauReal.equiv (TauReal.exp TauReal.zero) TauReal.one := by
  refine ⟨fun _ => 1, fun k n hn => ?_⟩
  change 1 ≤ n at hn
  unfold TauRat.lt
  rw [TauRat.toRat_abs, toRat_sub, TauRat.ofNatRecip_toRat]
  show |(TauRat.exp_partial TauRat.zero n).toRat - (TauRat.one).toRat|
         < 1 / ((k : Rat) + 1)
  rw [exp_partial_zero_toRat n hn, toRat_one]
  have h_eq : (1 : Rat) - 1 = 0 := by ring
  rw [h_eq, abs_zero]
  have h_pos : (0 : Rat) < (k : Rat) + 1 := by
    have : (0 : Rat) ≤ (k : Rat) := by exact_mod_cast Nat.zero_le k
    linarith
  exact div_pos (by norm_num) h_pos

/-- `(exp_term TauRat.one k).toRat = (e_term k).toRat`. -/
private theorem exp_term_one_toRat (k : Nat) :
    (TauRat.exp_term TauRat.one k).toRat = (TauRat.e_term k).toRat := by
  rw [exp_term_toRat, TauRat.pow_toRat, toRat_one, one_pow,
      TauRat.e_term_toRat]

/-- `(exp_partial TauRat.one n).toRat = (e_partial n).toRat`. -/
private theorem exp_partial_one_toRat (n : Nat) :
    (TauRat.exp_partial TauRat.one n).toRat = (TauRat.e_partial n).toRat := by
  unfold TauRat.exp_partial TauRat.e_partial
  induction n with
  | zero => simp [TauRat.sum_zero, toRat_zero]
  | succ n ih =>
    rw [TauRat.sum_succ, TauRat.sum_succ, toRat_add, toRat_add, ih,
        exp_term_one_toRat]

/-- `exp(1) ≡ e` up to TauReal.equiv. -/
theorem TauReal.exp_one :
    TauReal.equiv (TauReal.exp TauReal.one) TauReal.e := by
  -- Both sides have the same toRat at every index n: exp_partial one n = e_partial n.
  -- Use the Cauchy-equiv directly with modulus λ _ => 0 (always equal).
  refine ⟨fun _ => 0, fun k n _ => ?_⟩
  unfold TauRat.lt
  rw [TauRat.toRat_abs, toRat_sub, TauRat.ofNatRecip_toRat]
  show |(TauRat.exp_partial TauRat.one n).toRat - (TauRat.e_partial n).toRat|
         < 1 / ((k : Rat) + 1)
  rw [exp_partial_one_toRat n]
  have h_eq : (TauRat.e_partial n).toRat - (TauRat.e_partial n).toRat = 0 := by ring
  rw [h_eq, abs_zero]
  have h_pos : (0 : Rat) < (k : Rat) + 1 := by
    have : (0 : Rat) ≤ (k : Rat) := by exact_mod_cast Nat.zero_le k
    linarith
  exact div_pos (by norm_num) h_pos

/-- `exp(a + b) ≡ exp(a) · exp(b)` up to TauReal.equiv.

    **BLOCKED — Wave R8d.** This proof depends on `TauRat.cauchy_product_bound`
    in `TauRealSum.lean` Part 6 (Wave R8b stub). Engineer B's Wave R8c work
    revealed that the original `cauchy_product_bound` statement (`4 · C² / 2^n`)
    is mathematically false for n ≥ 4 (counterexample: C=1, n=4 gives 17/64 > 16/64).
    Corrected statement is `n · C² / 2^(n-1)`. Closure deferred to Wave R8d. -/
theorem TauReal.exp_add (a b : TauReal) (R : Rat)
    (hR0 : 0 ≤ R) (hR1 : R ≤ 1)
    (ha : TauReal.BoundedBy a R) (hb : TauReal.BoundedBy b R) :
    TauReal.equiv
      (TauReal.exp (a.add b))
      ((TauReal.exp a).mul (TauReal.exp b)) := by
  sorry  -- Wave R8d: blocked on cauchy_product_bound statement correction.

-- ============================================================
-- PART 7: SMOKE TESTS
-- ============================================================

-- exp_partial TauRat.zero 5: only k=0 term (= 1) survives, others 0
#eval (TauRat.exp_partial TauRat.zero 5).toRat        -- expected: 1

-- exp_partial TauRat.one 1 = 1/0! = 1
#eval (TauRat.exp_partial TauRat.one 1).toRat         -- expected: 1

-- exp_partial TauRat.one 2 = 1 + 1 = 2
#eval (TauRat.exp_partial TauRat.one 2).toRat         -- expected: 2

-- exp_partial TauRat.one 5 = 1 + 1 + 1/2 + 1/6 + 1/24 = 65/24 ≈ 2.708
#eval (TauRat.exp_partial TauRat.one 5).toRat         -- expected: 65/24

-- exp_partial TauRat.one 8 ≈ e ≈ 2.71828...
#eval (TauRat.exp_partial TauRat.one 8).toRat

-- (1/2)^3 = 1/8
private def half_rat : TauRat := ⟨⟨1, 0⟩, 2, by norm_num⟩
#eval (TauRat.pow half_rat 3).toRat                   -- expected: 1/8

-- exp_partial (1/2) 6 ≈ e^(1/2) ≈ 1.6487...
#eval (TauRat.exp_partial half_rat 6).toRat

-- IsCauchy at type level
#check @TauReal.exp_of_rat_isCauchy

end Tau.Boundary
