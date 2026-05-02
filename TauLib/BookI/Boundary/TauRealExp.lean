import TauLib.BookI.Boundary.TauRealE
import TauLib.BookI.Boundary.TauRealAnalyticalHelpers
import TauLib.BookI.Boundary.TauRealSum
import TauLib.BookI.Boundary.TauRealMulCongr
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
- **R4-equiv (Cauchy convolution proof harder than expected): TRIGGERED then RESOLVED.**
  `exp_add` depends on `TauRat.cauchy_product_bound` in TauRealSum.lean
  (closed Wave R8g with corrected statement `n · C² / 2^(n-1)`). Wave R8h-A
  closes `exp_add` via the binomial identity bridge `add_pow` and modulus
  `k ↦ 2k+6` to absorb the polynomial-in-n factor.

## Status

Definitions of `pow`, `exp_term`, `exp_partial`, `BoundedBy`, `exp_of_rat`,
`exp` are all in place. The headline theorems `exp_zero`, `exp_one`,
`exp_of_rat_isCauchy`, `exp_partial_cauchy_bound`, **`exp_add`** are all
proven sorry-free.

**Wave R9-1a additions** (positivity, monotonicity, injectivity):

- `TauReal.exp_pos_of_quarter` — `0 < exp(a)` (definite gap 1/3 past
  index 1) for `a` BoundedBy `R ≤ 1/4`.
- `TauReal.exp_gt_one_of_pos` — `1 < exp(a)` (definite gap) when `a`
  has a `lt`-positive witness `(k₀, N₀)` AND `BoundedBy R` with
  `R ≤ 1/(2(k₀+1))`.
- `TauReal.exp_strict_mono_of_bounded` — **HEADLINE.**  For `a, b` both
  BoundedBy `R ≤ 1/(4(k₀+1))` with explicit `lt`-witness `(k₀, N₀)` for
  `a < b`: `exp(a) < exp(b)`.
- `TauReal.exp_lt_not_equiv_of_bounded` — injectivity contrapositive:
  same hypotheses give `¬ equiv (exp a) (exp b)`.
- `TauReal.exp_strict_mono_of_lt_bounded` — convenience wrapper that
  takes the `TauReal.lt`-shape gap directly.

The `R ≤ 1/(4(k₀+1))` bound is the trade-off price for our Cauchy
remainder estimate `|exp_partial − (1 + x)| ≤ R`: to ensure the input
gap `1/(k₀+1)` survives the `2R` symmetric truncation noise, we need
`2R ≤ 1/(2(k₀+1))`, equivalently `R ≤ 1/(4(k₀+1))`.

Range-reduction (lifting these results from bounded inputs to all of
TauReal via `exp(x) = exp(k·ln 2) · exp(r)` for small `r`) is deferred
to TauRealLog (R9-1b).
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

/-- **Public re-export of `exp_term_toRat`** (Wave R10-1b).

    Mirrors the private version verbatim — exposed so downstream
    `TauRealLog.exp_log_one_plus_zero` can reduce `exp_partial` on
    structurally-distinct TauRat inputs that share the same `.toRat`
    value (the bridge from `log_partial 0 n` to `TauRat.zero`). -/
theorem TauRat.exp_term_toRat_eq (x : TauRat) (k : Nat) :
    (TauRat.exp_term x k).toRat =
      (TauRat.pow x k).toRat / (Nat.factorial k : Rat) :=
  exp_term_toRat x k

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

/-- **Public re-export of `exp_partial_zero_toRat`** (Wave R10-1b).

    Exposed for downstream `TauRealLog.exp_log_one_plus_zero` use:
    after toRat-invariance reduces `exp_partial (log_partial 0 n) n`
    to `exp_partial TauRat.zero n`, this lemma gives the toRat value `1`. -/
theorem TauRat.exp_partial_zero_toRat_eq (n : Nat) (hn : 1 ≤ n) :
    (TauRat.exp_partial TauRat.zero n).toRat = 1 :=
  exp_partial_zero_toRat n hn

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

-- ============================================================
-- PART 6.5: BINOMIAL IDENTITY  (Wave R8h-A — exp_add support)
--
-- Goal: prove `exp_partial (x.add y) n = cauchyPStar (exp_term x) (exp_term y) n`
-- at the toRat level.  The pointwise identity at term `k` is the binomial
-- theorem `(x+y)^k / k! = Σ_{i ≤ k} (x^i / i!) * (y^(k-i) / (k-i)!)`.
-- ============================================================

section BinomialExp

open BigOperators Tau.Boundary.Bridge

/-- Binomial expansion at `Rat`, divided through by `k!`:
    `(x + y)^k / k! = Σ_{i ≤ k} (x^i / i!) * (y^(k-i) / (k-i)!)`. -/
private theorem rat_exp_term_binomial (x y : Rat) (k : Nat) :
    (x + y) ^ k / (Nat.factorial k : Rat) =
      ∑ i ∈ Finset.range (k + 1),
        x ^ i / (Nat.factorial i : Rat)
          * (y ^ (k - i) / (Nat.factorial (k - i) : Rat)) := by
  have h_fac_pos : (0 : Rat) < (Nat.factorial k : Rat) := by
    have := Nat.factorial_pos k; exact_mod_cast this
  have h_fac_ne : (Nat.factorial k : Rat) ≠ 0 := ne_of_gt h_fac_pos
  -- Multiply both sides by k! and check the resulting polynomial identity.
  rw [div_eq_iff h_fac_ne]
  rw [rat_finset_sum_mul (k + 1)]
  -- Goal: (x + y)^k = ∑ i, (x^i/i! * (y^(k-i)/(k-i)!)) * k!
  rw [rat_add_pow]
  refine rat_finset_sum_congr (k + 1) _ _ ?_
  intro i hi
  have hi' : i ≤ k := Nat.le_of_lt_succ (Finset.mem_range.mp hi)
  have h_fi_pos : (0 : Rat) < (Nat.factorial i : Rat) := by
    have := Nat.factorial_pos i; exact_mod_cast this
  have h_fi_ne : (Nat.factorial i : Rat) ≠ 0 := ne_of_gt h_fi_pos
  have h_fki_pos : (0 : Rat) < (Nat.factorial (k - i) : Rat) := by
    have := Nat.factorial_pos (k - i); exact_mod_cast this
  have h_fki_ne : (Nat.factorial (k - i) : Rat) ≠ 0 := ne_of_gt h_fki_pos
  have h_ch := rat_choose_mul_factorial k i hi'
  -- Goal: x^i * y^(k-i) * (choose k i : Rat) = (x^i/i! * (y^(k-i)/(k-i)!)) * k!
  -- Use h_ch: (choose k i) * i! * (k-i)! = k!
  field_simp
  linear_combination (x ^ i * y ^ (k - i)) * h_ch

/-- The pointwise identity: `(exp_term (x+y) k).toRat = (cauchyDiag (exp_term x) (exp_term y) k).toRat`. -/
private theorem exp_term_add_toRat_eq_cauchyDiag (x y : TauRat) (k : Nat) :
    (TauRat.exp_term (x.add y) k).toRat =
      (TauRat.cauchyDiag (TauRat.exp_term x) (TauRat.exp_term y) k).toRat := by
  rw [exp_term_toRat, TauRat.pow_toRat, toRat_add]
  unfold TauRat.cauchyDiag
  have h_sum_toRat :
      (TauRat.sum (fun i => (TauRat.exp_term x i).mul (TauRat.exp_term y (k - i)))
        (k + 1)).toRat
      = ∑ i ∈ Finset.range (k + 1),
          (TauRat.exp_term x i).toRat * (TauRat.exp_term y (k - i)).toRat := by
    induction (k + 1) with
    | zero => simp [TauRat.sum_zero, toRat_zero]
    | succ m ih =>
      rw [TauRat.sum_succ, toRat_add, ih, toRat_mul, Finset.sum_range_succ]
  rw [h_sum_toRat]
  have h_each :
      ∀ i ∈ Finset.range (k + 1),
        (TauRat.exp_term x i).toRat * (TauRat.exp_term y (k - i)).toRat
        = x.toRat ^ i / (Nat.factorial i : Rat)
          * (y.toRat ^ (k - i) / (Nat.factorial (k - i) : Rat)) := by
    intro i _hi
    rw [exp_term_toRat, exp_term_toRat, TauRat.pow_toRat, TauRat.pow_toRat]
  rw [rat_finset_sum_congr _ _ _ h_each]
  exact rat_exp_term_binomial x.toRat y.toRat k

/-- Lifted to partial sums. -/
private theorem exp_partial_add_toRat_eq_cauchyPStar (x y : TauRat) (n : Nat) :
    (TauRat.exp_partial (x.add y) n).toRat =
      (TauRat.cauchyPStar (TauRat.exp_term x) (TauRat.exp_term y) n).toRat := by
  unfold TauRat.exp_partial TauRat.cauchyPStar
  induction n with
  | zero => simp [TauRat.sum_zero, toRat_zero]
  | succ n ih =>
    rw [TauRat.sum_succ, TauRat.sum_succ, toRat_add, toRat_add, ih,
        exp_term_add_toRat_eq_cauchyDiag]

end BinomialExp

-- ============================================================
-- PART 6.6: Nat-arithmetic helpers for the modulus inequality
-- ============================================================

/-- Polynomial-vs-exponential, Nat form: `4 * n * (k + 1) < 2^(n - 1)` for `n ≥ 2k + 6`.

    Proven by induction on the slack `n - (2k + 6)`. The base case
    `n = 2k + 6` reduces to `4(2k+6)(k+1) < 2^(2k+5)`, i.e.
    `(2k+6)(k+1) < 2^(2k+3)`, a clean polynomial-vs-exponential inequality.
    The step case uses `2 · LHS < RHS_succ` for slack ≥ 1. -/
private theorem nat_exp_add_modulus_ineq (k n : Nat) (hn : 2 * k + 6 ≤ n) :
    4 * n * (k + 1) < 2 ^ (n - 1) := by
  -- Reparametrize via `n = 2k + 6 + m`.
  obtain ⟨m, hm⟩ : ∃ m, n = 2 * k + 6 + m := ⟨n - (2 * k + 6), by omega⟩
  subst hm
  -- Goal: 4 * (2k+6+m) * (k+1) < 2^((2k+6+m) - 1) = 2^(2k+5+m)
  induction m with
  | zero =>
    -- n = 2k + 6: need 4 * (2k + 6) * (k + 1) < 2^(2k + 5)
    -- Inner Nat lemma: `(2*k+6)*(k+1) < 2^(2*k+3)` for all k ≥ 0.
    have h_nat : ∀ k', (2 * k' + 6) * (k' + 1) < 2 ^ (2 * k' + 3) := by
      intro k'
      induction k' with
      | zero => decide
      | succ k' ih =>
        have h_pow : 2 ^ (2 * (k' + 1) + 3) = 4 * 2 ^ (2 * k' + 3) := by
          have h_eq : 2 * (k' + 1) + 3 = (2 * k' + 3) + 2 := by ring
          rw [h_eq, pow_add]; ring
        have h_pos : 0 < 2 ^ (2 * k' + 3) := by positivity
        rw [h_pow]
        nlinarith [ih, h_pos]
    have h_nat_k := h_nat k
    have h_pow_eq : 2 ^ (2 * k + 5) = 4 * 2 ^ (2 * k + 3) := by
      have h_eq : 2 * k + 5 = (2 * k + 3) + 2 := by ring
      rw [h_eq, pow_add]; ring
    have h_idx_eq : 2 * k + 6 + 0 - 1 = 2 * k + 5 := by omega
    rw [h_idx_eq, h_pow_eq]
    nlinarith [h_nat_k]
  | succ m ih =>
    -- Inductive step: assume 4*(2k+6+m)*(k+1) < 2^(2k+5+m).
    -- Need: 4*(2k+6+m+1)*(k+1) < 2^(2k+5+m+1) = 2 * 2^(2k+5+m)
    have h_idx_eq : 2 * k + 6 + (m + 1) - 1 = 2 * k + 6 + m := by omega
    rw [h_idx_eq]
    have h_idx_ih : 2 * k + 6 + m - 1 = 2 * k + 5 + m := by omega
    rw [h_idx_ih] at ih
    have h_pow : 2 ^ (2 * k + 6 + m) = 2 * 2 ^ (2 * k + 5 + m) := by
      have h_eq : 2 * k + 6 + m = (2 * k + 5 + m) + 1 := by omega
      rw [h_eq, pow_succ]; ring
    rw [h_pow]
    have h_pos : 0 < 2 ^ (2 * k + 5 + m) := by positivity
    -- ih is conditional; supply the trivial witness.
    have h_ih : 4 * (2 * k + 6 + m) * (k + 1) < 2 ^ (2 * k + 5 + m) := ih (by omega)
    -- Need: 4 * (2k+6+m+1) * (k+1) < 2 * 2^(2k+5+m)
    -- Have: 4 * (2k+6+m) * (k+1) < 2^(2k+5+m)
    -- So 2 * 4 * (2k+6+m) * (k+1) < 2 * 2^(2k+5+m)
    -- And 4 * (2k+6+m+1) * (k+1) = 4*(2k+6+m)*(k+1) + 4*(k+1)
    --                              ≤ 4*(2k+6+m)*(k+1) + 4*(2k+6+m)*(k+1) since 1 ≤ 2k+6+m.
    have h_M_ge_1 : 1 ≤ 2 * k + 6 + m := by omega
    nlinarith [h_ih, h_pos, h_M_ge_1]

/-- Rat cast of the modulus inequality. -/
private theorem rat_exp_add_modulus_ineq (k n : Nat) (hn : 2 * k + 6 ≤ n) :
    4 * (n : Rat) * ((k : Rat) + 1) < (2 : Rat) ^ (n - 1) := by
  have h_nat := nat_exp_add_modulus_ineq k n hn
  have h_cast : ((4 * n * (k + 1) : Nat) : Rat) < ((2 ^ (n - 1) : Nat) : Rat) := by
    exact_mod_cast h_nat
  have h_lhs : ((4 * n * (k + 1) : Nat) : Rat) = 4 * (n : Rat) * ((k : Rat) + 1) := by
    push_cast; ring
  have h_rhs : ((2 ^ (n - 1) : Nat) : Rat) = (2 : Rat) ^ (n - 1) := by push_cast; ring
  linarith

-- ============================================================
-- PART 6.7: Uniform exp term bound (covers k = 0 and k ≥ 1) at C = 2
-- ============================================================

/-- Uniform geometric bound on `exp_term`: `|exp_term x k| ≤ 2 / 2^k` for all k,
    when `|x| ≤ R ≤ 1`. -/
private theorem exp_term_abs_le_two_geom (x : TauRat) (R : Rat)
    (hR0 : 0 ≤ R) (hR1 : R ≤ 1) (hx : |x.toRat| ≤ R)
    (k : Nat) : |(TauRat.exp_term x k).toRat| ≤ (2 : Rat) / (2 : Rat) ^ k := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · -- k = 0: |exp_term x 0| = |1| = 1 ≤ 2/1 = 2
    rw [exp_term_toRat, TauRat.pow_zero, toRat_one]
    simp [Nat.factorial]
  · -- k ≥ 1: |exp_term x k| ≤ R/2^(k-1) = 2R/2^k ≤ 2/2^k
    have h_geom := exp_term_abs_le_geom x R hR0 hR1 hx k hk
    have h_pow_pos : (0 : Rat) < (2 : Rat) ^ k := by positivity
    have h_pow_pred_pos : (0 : Rat) < (2 : Rat) ^ (k - 1) := by positivity
    have h_pow_eq : (2 : Rat) ^ k = 2 * (2 : Rat) ^ (k - 1) := Rat.pow_pred_eq k hk
    have h_rewrite : R / (2 : Rat) ^ (k - 1) = 2 * R / (2 : Rat) ^ k := by
      rw [h_pow_eq]; field_simp
    rw [h_rewrite] at h_geom
    have h_R2_le : 2 * R ≤ 2 := by linarith
    have h_step : 2 * R / (2 : Rat) ^ k ≤ 2 / (2 : Rat) ^ k := by
      rw [div_le_div_iff₀ h_pow_pos h_pow_pos]
      nlinarith
    linarith

/-- `exp(a + b) ≡ exp(a) · exp(b)` up to TauReal.equiv.

    **Wave R8h-A closure.**  Proof structure:
    (i)  binomial identity:
         `exp_partial (x+y) n .toRat = cauchyPStar (exp_term x) (exp_term y) n .toRat`,
    (ii) `cauchy_product_bound` (R8g) with `C = 2`, term bound
         `|exp_term x k| ≤ 2 / 2^k` for all k,
    (iii) modulus `k ↦ 2k + 6`: at `n ≥ 2k+6`, `4n / 2^(n-1) < 1/(k+1)`. -/
theorem TauReal.exp_add (a b : TauReal) (R : Rat)
    (hR0 : 0 ≤ R) (hR1 : R ≤ 1)
    (ha : TauReal.BoundedBy a R) (hb : TauReal.BoundedBy b R) :
    TauReal.equiv
      (TauReal.exp (a.add b))
      ((TauReal.exp a).mul (TauReal.exp b)) := by
  refine ⟨fun k => 2 * k + 6, fun k n hn => ?_⟩
  change 2 * k + 6 ≤ n at hn
  unfold TauRat.lt
  rw [TauRat.toRat_abs, toRat_sub, TauRat.ofNatRecip_toRat]
  show |(TauRat.exp_partial ((a.approx n).add (b.approx n)) n).toRat
        - ((TauRat.exp_partial (a.approx n) n).mul
            (TauRat.exp_partial (b.approx n) n)).toRat|
       < 1 / ((k : Rat) + 1)
  rw [toRat_mul]
  -- Step (i): binomial identity.
  rw [exp_partial_add_toRat_eq_cauchyPStar (a.approx n) (b.approx n) n]
  -- Sign-swap so the form matches cauchy_product_bound.
  have h_neg_eq :
      (TauRat.cauchyPStar (TauRat.exp_term (a.approx n))
          (TauRat.exp_term (b.approx n)) n).toRat
        - (TauRat.exp_partial (a.approx n) n).toRat
          * (TauRat.exp_partial (b.approx n) n).toRat
      = -((TauRat.exp_partial (a.approx n) n).toRat
            * (TauRat.exp_partial (b.approx n) n).toRat
          - (TauRat.cauchyPStar (TauRat.exp_term (a.approx n))
              (TauRat.exp_term (b.approx n)) n).toRat) := by ring
  rw [h_neg_eq, abs_neg]
  -- exp_partial = sum (exp_term ·) at toRat level (definitional).
  show |(TauRat.sum (TauRat.exp_term (a.approx n)) n).toRat
        * (TauRat.sum (TauRat.exp_term (b.approx n)) n).toRat
        - (TauRat.cauchyPStar (TauRat.exp_term (a.approx n))
            (TauRat.exp_term (b.approx n)) n).toRat|
       < 1 / ((k : Rat) + 1)
  -- Step (ii): apply cauchy_product_bound with C = 2.
  have hn_ge_1 : 1 ≤ n := by omega
  have h_a_term_bound : ∀ i, |(TauRat.exp_term (a.approx n) i).toRat|
                            ≤ (2 : Rat) / (2 : Rat) ^ i :=
    fun i => exp_term_abs_le_two_geom (a.approx n) R hR0 hR1 (ha n) i
  have h_b_term_bound : ∀ j, |(TauRat.exp_term (b.approx n) j).toRat|
                            ≤ (2 : Rat) / (2 : Rat) ^ j :=
    fun j => exp_term_abs_le_two_geom (b.approx n) R hR0 hR1 (hb n) j
  have h_cpb := TauRat.cauchy_product_bound
    (TauRat.exp_term (a.approx n)) (TauRat.exp_term (b.approx n))
    (2 : Rat) (by norm_num) h_a_term_bound h_b_term_bound n hn_ge_1
  -- h_cpb: bound ≤ n * 2^2 / 2^(n-1)  =  4n / 2^(n-1)
  refine lt_of_le_of_lt h_cpb ?_
  -- Step (iii): show n * 4 / 2^(n-1) < 1/(k+1).
  have h_pow_pos : (0 : Rat) < (2 : Rat) ^ (n - 1) := by positivity
  have h_k1_pos : (0 : Rat) < (k : Rat) + 1 := by
    have : (0 : Rat) ≤ (k : Rat) := by exact_mod_cast Nat.zero_le k
    linarith
  -- n * 2^2 = 4n
  have h_simp : (n : Rat) * (2 : Rat) ^ 2 = 4 * (n : Rat) := by ring
  rw [h_simp]
  -- 4n / 2^(n-1) < 1/(k+1)  ⟺  4n(k+1) < 2^(n-1)
  rw [div_lt_div_iff₀ h_pow_pos h_k1_pos]
  have h_main := rat_exp_add_modulus_ineq k n hn
  linarith

-- ============================================================
-- PART 6.8: POSITIVITY INFRASTRUCTURE  (Wave R9-1a)
--
-- Foundation for `exp_strict_mono` / `exp_injectivity` (R9-1a).  We
-- supply the constructive lower bound `(exp_partial x m).toRat ≥ 1 − 2R`
-- (Lemma A) and, for sufficiently small radicand `R ≤ 1/4`, the strict
-- positivity bound `(exp_partial x m).toRat ≥ 1/2` (Lemma B).
--
-- These are the partial-sum-level analogues of `0 < exp(x)`.  Lifting
-- to the TauReal `exp` is straightforward: the n-th approximation of
-- `(TauReal.exp a)` is `exp_partial (a.approx n) n`, so the same lower
-- bound applies pointwise whenever `a` is BoundedBy R with R ≤ 1/4.
-- ============================================================

/-- **Lower bound on the exp partial sum.**

    For `|x| ≤ R ≤ 1` and `n ≥ 1`:
        `(exp_partial x n).toRat ≥ 1 − 2R`.

    Proof: `exp_partial x 1 = 1` (only the k=0 term, which is 1).
    For `n ≥ 1`, the difference
        `(exp_partial x n) − (exp_partial x 1) = sumFromTo (exp_term x) 1 n`
    has absolute value bounded by `sumFromTo |exp_term x| 1 n ≤ 2R`
    (via `sumFromTo_exp_term_bound` with `n = 1`, giving `4R/2 − 4R/2^n`). -/
private theorem exp_partial_lower_bound (x : TauRat) (R : Rat)
    (hR0 : 0 ≤ R) (hR1 : R ≤ 1) (hx : |x.toRat| ≤ R)
    (n : Nat) (hn : 1 ≤ n) :
    (1 : Rat) - 2 * R ≤ (TauRat.exp_partial x n).toRat := by
  -- Step 1: (exp_partial x 1).toRat = 1.
  have h_partial_one : (TauRat.exp_partial x 1).toRat = 1 := by
    -- exp_partial x 1 = sum (exp_term x) 1 = 0 + exp_term x 0 = exp_term x 0
    show (TauRat.sum (TauRat.exp_term x) 1).toRat = 1
    rw [TauRat.sum_succ, TauRat.sum_zero, toRat_add, toRat_zero]
    rw [exp_term_toRat, TauRat.pow_zero, toRat_one]
    simp [Nat.factorial]
  -- Step 2: telescoping difference.
  have h_diff_eq :
      (TauRat.exp_partial x n).toRat - (TauRat.exp_partial x 1).toRat
        = (TauRat.sumFromTo (TauRat.exp_term x) 1 n).toRat := by
    unfold TauRat.exp_partial
    exact TauRat.sum_sub_toRat_eq_sumFromTo (TauRat.exp_term x) 1 n hn
  -- Step 3: triangle inequality on sumFromTo.
  have h_tri := TauRat.sumFromTo_abs_le (TauRat.exp_term x) 1 n
  -- Step 4: telescoping bound.
  have h_strong := sumFromTo_exp_term_bound x R hR0 hR1 hx 1 (le_refl 1) n hn
  -- 4R/2^1 - 4R/2^n = 2R - 4R/2^n ≤ 2R.
  have h_pow_pos_n : (0 : Rat) < (2 : Rat) ^ n := by positivity
  have h_decr_nn : (0 : Rat) ≤ 4 * R / (2 : Rat) ^ n :=
    div_nonneg (by linarith) (le_of_lt h_pow_pos_n)
  have h_pow_one : (2 : Rat) ^ 1 = 2 := by norm_num
  rw [h_pow_one] at h_strong
  -- h_strong : sumFromTo |exp_term x| 1 n .toRat ≤ 4R/2 - 4R/2^n
  have h_4R2 : (4 : Rat) * R / 2 = 2 * R := by ring
  rw [h_4R2] at h_strong
  -- |diff| ≤ sumFromTo |exp_term x| 1 n .toRat ≤ 2R - 4R/2^n ≤ 2R
  have h_abs_diff_le_2R :
      |(TauRat.exp_partial x n).toRat - (TauRat.exp_partial x 1).toRat|
        ≤ 2 * R := by
    rw [h_diff_eq]
    linarith
  -- Step 5: extract lower bound from |partial - 1| ≤ 2R.
  rw [h_partial_one] at h_abs_diff_le_2R
  have h_neg := (abs_le.mp h_abs_diff_le_2R).1
  linarith

/-- **Strict positivity of exp partial sum (R ≤ 1/4).**

    For `|x| ≤ R ≤ 1/4` and `n ≥ 1`:
        `(exp_partial x n).toRat ≥ 1/2 > 0`. -/
private theorem exp_partial_pos_of_quarter (x : TauRat) (R : Rat)
    (hR0 : 0 ≤ R) (hR4 : R ≤ 1 / 4) (hx : |x.toRat| ≤ R)
    (n : Nat) (hn : 1 ≤ n) :
    (1 : Rat) / 2 ≤ (TauRat.exp_partial x n).toRat := by
  have hR1 : R ≤ 1 := by linarith
  have h_lb := exp_partial_lower_bound x R hR0 hR1 hx n hn
  -- 1 - 2R ≥ 1 - 2/4 = 1/2
  linarith

/-- **TauReal.exp is positive when the input is bounded by 1/4.**

    For `a : TauReal` with `BoundedBy a R`, `R ≤ 1/4`:
        `0 < TauReal.exp a`  (in the constructive `TauReal.lt` sense).

    The witness gap is `1/3` — past index `N = 1`, every approximation
    of `exp a` is `≥ 1/2`, so `0 + 1/3 < 1/2 ≤ exp_partial`. -/
theorem TauReal.exp_pos_of_quarter (a : TauReal) (R : Rat)
    (hR0 : 0 ≤ R) (hR4 : R ≤ 1 / 4) (ha : TauReal.BoundedBy a R) :
    TauReal.lt TauReal.zero (TauReal.exp a) := by
  -- We need an explicit gap k and threshold N such that for n ≥ N:
  --   (zero + 1/(k+1)).toRat < (exp a).approx n .toRat
  -- Use k = 2 (giving gap 1/3) and N = 1.
  refine ⟨2, 1, fun n hn => ?_⟩
  unfold TauRat.lt
  rw [toRat_add, TauRat.ofNatRecip_toRat]
  -- (zero.approx n).toRat = 0
  show (TauReal.zero.approx n).toRat + 1 / (((2 : Nat) : Rat) + 1)
        < ((TauReal.exp a).approx n).toRat
  have h_zero : (TauReal.zero.approx n).toRat = 0 := by
    show (TauRat.zero).toRat = 0
    rw [toRat_zero]
  rw [h_zero]
  -- (exp a).approx n = exp_partial (a.approx n) n
  show (0 : Rat) + 1 / (((2 : Nat) : Rat) + 1)
        < (TauRat.exp_partial (a.approx n) n).toRat
  have hx : |(a.approx n).toRat| ≤ R := ha n
  have h_lb := exp_partial_pos_of_quarter (a.approx n) R hR0 hR4 hx n hn
  -- 1/(2+1) = 1/3 < 1/2 ≤ exp_partial
  have h_simp : (1 : Rat) / (((2 : Nat) : Rat) + 1) = 1 / 3 := by push_cast; norm_num
  rw [h_simp]
  linarith

-- ============================================================
-- PART 6.9: GREATER-THAN-ONE FOR DEFINITELY-POSITIVE INPUT  (Wave R9-1a)
--
-- Proves `1 < exp(a)` (definite gap) when `a` has a definite gap from 0
-- AND is BoundedBy R for sufficiently small R.  The second pillar of
-- `exp_strict_mono`.
--
-- Sketch (partial-sum level): for `|x| ≤ R ≤ 1` and `n ≥ 2`,
-- `(exp_partial x n).toRat ≥ 1 + x.toRat − R` (since the k≥2 tail in
-- absolute value is ≤ R, by the same telescoping bound as Part 6.8).
-- ============================================================

/-- Closed form for the n=2 partial sum: `(exp_partial x 2).toRat = 1 + x.toRat`. -/
private theorem exp_partial_two_toRat (x : TauRat) :
    (TauRat.exp_partial x 2).toRat = 1 + x.toRat := by
  show (TauRat.sum (TauRat.exp_term x) 2).toRat = 1 + x.toRat
  rw [TauRat.sum_succ, TauRat.sum_succ, TauRat.sum_zero,
      toRat_add, toRat_add, toRat_zero]
  -- Goal: 0 + (exp_term x 0).toRat + (exp_term x 1).toRat = 1 + x.toRat
  rw [exp_term_toRat, exp_term_toRat,
      TauRat.pow_zero, TauRat.pow_succ, TauRat.pow_zero,
      toRat_one]
  -- Goal: 0 + 1 / (Nat.factorial 0 : Rat) + (TauRat.one.mul x).toRat / (Nat.factorial 1 : Rat)
  --     = 1 + x.toRat
  rw [toRat_mul, toRat_one]
  simp [Nat.factorial]

/-- **Lower bound on exp_partial when k=1 term is included.**

    For `|x| ≤ R ≤ 1` and `n ≥ 2`:
        `(exp_partial x n).toRat ≥ 1 + x.toRat − R`.

    Proof: telescope from `n = 2` onwards.  At n=2 the partial sum is
    exactly `1 + x.toRat`.  The k≥2 tail in absolute value is bounded by
    `sumFromTo |exp_term x| 2 m .toRat ≤ 4R/2² − 4R/2^m ≤ R`. -/
private theorem exp_partial_ge_one_plus_x_sub_R (x : TauRat) (R : Rat)
    (hR0 : 0 ≤ R) (hR1 : R ≤ 1) (hx : |x.toRat| ≤ R)
    (n : Nat) (hn : 2 ≤ n) :
    (1 : Rat) + x.toRat - R ≤ (TauRat.exp_partial x n).toRat := by
  -- Step 1: telescope from index 2.
  have h_diff_eq :
      (TauRat.exp_partial x n).toRat - (TauRat.exp_partial x 2).toRat
        = (TauRat.sumFromTo (TauRat.exp_term x) 2 n).toRat := by
    unfold TauRat.exp_partial
    exact TauRat.sum_sub_toRat_eq_sumFromTo (TauRat.exp_term x) 2 n hn
  -- Step 2: triangle inequality on sumFromTo.
  have h_tri := TauRat.sumFromTo_abs_le (TauRat.exp_term x) 2 n
  -- Step 3: telescoping bound starting at index 2.
  have h_strong :=
    sumFromTo_exp_term_bound x R hR0 hR1 hx 2 (by omega) n hn
  -- 4R/2² - 4R/2^n = R - 4R/2^n.  Show ≤ R.
  have h_pow_two : (2 : Rat) ^ 2 = 4 := by norm_num
  rw [h_pow_two] at h_strong
  have h_pow_pos_n : (0 : Rat) < (2 : Rat) ^ n := by positivity
  have h_decr_nn : (0 : Rat) ≤ 4 * R / (2 : Rat) ^ n :=
    div_nonneg (by linarith) (le_of_lt h_pow_pos_n)
  have h_4R4 : (4 : Rat) * R / 4 = R := by ring
  rw [h_4R4] at h_strong
  -- h_strong : sumFromTo |exp_term x| 2 n .toRat ≤ R - 4R/2^n
  have h_abs_diff_le_R :
      |(TauRat.exp_partial x n).toRat - (TauRat.exp_partial x 2).toRat| ≤ R := by
    rw [h_diff_eq]
    linarith
  -- Step 4: extract lower bound from |partial - (1 + x.toRat)| ≤ R.
  rw [exp_partial_two_toRat] at h_abs_diff_le_R
  have h_neg := (abs_le.mp h_abs_diff_le_R).1
  linarith

/-- **TauReal.exp(a) > 1 (definite gap) when 0 < a and a is bounded suitably.**

    Constructive form: given that `a` is `lt`-positive (with witness gap
    `1/(k₀+1)` past index `N₀`) AND `BoundedBy a R` with `R ≤ 1/(2(k₀+1))`,
    we have `1 < TauReal.exp a` with witness gap `1/(2(k₀+1)+1)` past
    index `max N₀ 2`.

    Proof: at any qualifying n,
      `(exp_partial (a.approx n) n).toRat ≥ 1 + (a.approx n).toRat − R`
      ≥ 1 + 1/(k₀+1) − 1/(2(k₀+1)) = 1 + 1/(2(k₀+1))
      > 1 + 1/(2(k₀+1)+1)
      = (TauReal.one.approx n).toRat + 1/(2(k₀+1)+1).
-/
theorem TauReal.exp_gt_one_of_pos (a : TauReal) (R : Rat) (k₀ N₀ : Nat)
    (hR0 : 0 ≤ R) (hRsmall : R ≤ 1 / (2 * ((k₀ : Rat) + 1)))
    (hR1 : R ≤ 1)
    (ha_bound : TauReal.BoundedBy a R)
    (ha_pos : ∀ n, N₀ ≤ n →
      ((TauReal.zero.approx n).toRat + 1 / (((k₀ : Nat) : Rat) + 1)
        < (a.approx n).toRat)) :
    TauReal.lt TauReal.one (TauReal.exp a) := by
  refine ⟨2 * (k₀ + 1), max N₀ 2, fun n hn => ?_⟩
  have hN : N₀ ≤ n := le_of_max_le_left hn
  have h2 : 2 ≤ n := le_of_max_le_right hn
  unfold TauRat.lt
  rw [toRat_add, TauRat.ofNatRecip_toRat]
  show (TauReal.one.approx n).toRat + 1 / (((2 * (k₀ + 1) : Nat) : Rat) + 1)
        < ((TauReal.exp a).approx n).toRat
  have h_one : (TauReal.one.approx n).toRat = 1 := by
    show (TauRat.one).toRat = 1
    rw [toRat_one]
  rw [h_one]
  show (1 : Rat) + 1 / (((2 * (k₀ + 1) : Nat) : Rat) + 1)
        < (TauRat.exp_partial (a.approx n) n).toRat
  -- Use exp_partial_ge_one_plus_x_sub_R.
  have hx : |(a.approx n).toRat| ≤ R := ha_bound n
  have h_lb := exp_partial_ge_one_plus_x_sub_R (a.approx n) R hR0 hR1 hx n h2
  -- The positivity witness:
  have h_pos := ha_pos n hN
  have h_zero : (TauReal.zero.approx n).toRat = 0 := by
    show (TauRat.zero).toRat = 0; rw [toRat_zero]
  rw [h_zero] at h_pos
  -- h_pos : 0 + 1/(k₀+1) < (a.approx n).toRat,
  -- i.e. (a.approx n).toRat > 1/(k₀+1).
  -- Combine: exp_partial ≥ 1 + (a.approx n).toRat - R > 1 + 1/(k₀+1) - R
  -- and 1/(k₀+1) - R ≥ 1/(k₀+1) - 1/(2(k₀+1)) = 1/(2(k₀+1)).
  -- We need 1 + 1/(2(k+1)+1) < exp_partial, where 2(k+1)+1 (Nat) cast.
  have h_k1_pos : (0 : Rat) < ((k₀ : Nat) : Rat) + 1 := by
    have : (0 : Rat) ≤ ((k₀ : Nat) : Rat) := by exact_mod_cast Nat.zero_le k₀
    linarith
  have h_2k1_pos : (0 : Rat) < 2 * (((k₀ : Nat) : Rat) + 1) := by linarith
  -- Cast Nat-form `2 * (k₀ + 1)` and rewrite.
  have h_cast_2k1 : (((2 * (k₀ + 1) : Nat) : Rat)) = 2 * (((k₀ : Nat) : Rat) + 1) := by
    push_cast; ring
  rw [h_cast_2k1]
  -- Cast hRsmall to match: (k₀ : Rat) appears as ((k₀ : Nat) : Rat).
  -- They are the same term modulo Nat.cast unification.
  have hRsmall' : R ≤ 1 / (2 * (((k₀ : Nat) : Rat) + 1)) := hRsmall
  -- Need: 1 + 1/(2*(k₀+1)+1) < exp_partial.
  -- We have: exp_partial ≥ 1 + (a.approx n).toRat - R, and (a.approx n).toRat > 1/(k₀+1).
  -- Consequently, exp_partial > 1 + 1/(k₀+1) - R ≥ 1 + 1/(k₀+1) - 1/(2(k₀+1))
  --   = 1 + (2 - 1)/(2(k₀+1)) = 1 + 1/(2(k₀+1)).
  -- And 1/(2(k₀+1)+1) < 1/(2(k₀+1)).
  -- Direct linear chain:
  -- Let q = ((k₀ : Nat) : Rat) + 1.
  -- exp_partial ≥ 1 + (a.approx n).toRat - R    [h_lb]
  -- (a.approx n).toRat > 1/q                    [h_pos]
  -- R ≤ 1/(2q)                                  [hRsmall']
  -- Therefore exp_partial > 1 + 1/q - 1/(2q) = 1 + 1/(2q).
  -- And 1/(2q+1) < 1/(2q).
  have h_one_div_2q_pos : (0 : Rat) < 1 / (2 * (((k₀ : Nat) : Rat) + 1)) :=
    div_pos (by norm_num) h_2k1_pos
  have h_two_q_plus_one_pos : (0 : Rat) < 2 * (((k₀ : Nat) : Rat) + 1) + 1 := by
    linarith
  have h_strict_recip :
      1 / (2 * (((k₀ : Nat) : Rat) + 1) + 1)
        < 1 / (2 * (((k₀ : Nat) : Rat) + 1)) := by
    rw [div_lt_div_iff₀ h_two_q_plus_one_pos h_2k1_pos]
    linarith
  -- The key inequality:
  -- exp_partial > 1 + 1/q - R ≥ 1 + 1/q - 1/(2q) = 1 + 1/(2q)
  have h_combine_alg :
      1 / (((k₀ : Nat) : Rat) + 1) - 1 / (2 * (((k₀ : Nat) : Rat) + 1))
        = 1 / (2 * (((k₀ : Nat) : Rat) + 1)) := by
    have h_q_ne : ((k₀ : Nat) : Rat) + 1 ≠ 0 := ne_of_gt h_k1_pos
    field_simp
    ring
  -- Putting it together:
  -- We want: 1 + 1/(2q+1) < exp_partial.
  -- Use chain: 1 + 1/(2q+1) < 1 + 1/(2q) ≤ 1 + (1/q - R)
  --   ≤ 1 + ((a.approx n).toRat - R) [from h_pos: 1/q < (a.approx n).toRat]
  --   ≤ exp_partial [from h_lb].
  linarith [h_combine_alg, h_strict_recip, h_pos, h_lb, hRsmall']

/-- **Upper bound on exp_partial.**

    For `|x| ≤ R ≤ 1` and `n ≥ 2`:
        `(exp_partial x n).toRat ≤ 1 + x.toRat + R`.

    Companion to `exp_partial_ge_one_plus_x_sub_R`. -/
private theorem exp_partial_le_one_plus_x_add_R (x : TauRat) (R : Rat)
    (hR0 : 0 ≤ R) (hR1 : R ≤ 1) (hx : |x.toRat| ≤ R)
    (n : Nat) (hn : 2 ≤ n) :
    (TauRat.exp_partial x n).toRat ≤ (1 : Rat) + x.toRat + R := by
  -- Same telescoping setup as the lower bound, but extract upper bound.
  have h_diff_eq :
      (TauRat.exp_partial x n).toRat - (TauRat.exp_partial x 2).toRat
        = (TauRat.sumFromTo (TauRat.exp_term x) 2 n).toRat := by
    unfold TauRat.exp_partial
    exact TauRat.sum_sub_toRat_eq_sumFromTo (TauRat.exp_term x) 2 n hn
  have h_tri := TauRat.sumFromTo_abs_le (TauRat.exp_term x) 2 n
  have h_strong :=
    sumFromTo_exp_term_bound x R hR0 hR1 hx 2 (by omega) n hn
  have h_pow_two : (2 : Rat) ^ 2 = 4 := by norm_num
  rw [h_pow_two] at h_strong
  have h_pow_pos_n : (0 : Rat) < (2 : Rat) ^ n := by positivity
  have h_decr_nn : (0 : Rat) ≤ 4 * R / (2 : Rat) ^ n :=
    div_nonneg (by linarith) (le_of_lt h_pow_pos_n)
  have h_4R4 : (4 : Rat) * R / 4 = R := by ring
  rw [h_4R4] at h_strong
  have h_abs_diff_le_R :
      |(TauRat.exp_partial x n).toRat - (TauRat.exp_partial x 2).toRat| ≤ R := by
    rw [h_diff_eq]
    linarith
  rw [exp_partial_two_toRat] at h_abs_diff_le_R
  have h_pos := (abs_le.mp h_abs_diff_le_R).2
  linarith

-- ============================================================
-- PART 6.10: EXP STRICT MONOTONICITY (Wave R9-1a HEADLINE)
--
-- For BOUNDED inputs `a, b` with `a < b` (definite gap), `exp(a) < exp(b)`.
-- The bound condition is essential because `exp_partial`'s remainder
-- estimate depends on the radicand.
--
-- INJECTIVITY corollary: `equiv (exp a) (exp b) → equiv a b` (for
-- bounded a, b) — since `equiv` rules out both `lt` directions.
-- ============================================================

/-- **Exponential is strictly monotone on bounded inputs.**

    For `a, b : TauReal` with:
    - `a < b` (definite gap with witness `k₀, N₀`),
    - `BoundedBy a R` and `BoundedBy b R` for `R ≤ 1/(4(k₀+1))`,
    we have `exp(a) < exp(b)` (definite gap with witness
    `k = 2(k₀+1), N = max N₀ 2`).

    Proof: at any qualifying n,
      `(exp_partial (b.approx n) n) − (exp_partial (a.approx n) n)`
      ≥ ((b.approx n) − (a.approx n)) − 2R
      ≥ 1/(k₀+1) − 1/(2(k₀+1))
      = 1/(2(k₀+1)).
    Then `1/(2(k₀+1)+1) < 1/(2(k₀+1))` gives the strict gap. -/
theorem TauReal.exp_strict_mono_of_bounded
    (a b : TauReal) (R : Rat) (k₀ N₀ : Nat)
    (hR0 : 0 ≤ R)
    (hRsmall : R ≤ 1 / (4 * (((k₀ : Nat) : Rat) + 1)))
    (hR1 : R ≤ 1)
    (ha_bound : TauReal.BoundedBy a R)
    (hb_bound : TauReal.BoundedBy b R)
    (h_ab_gap : ∀ n, N₀ ≤ n →
      ((a.approx n).toRat + 1 / (((k₀ : Nat) : Rat) + 1)
        < (b.approx n).toRat)) :
    TauReal.lt (TauReal.exp a) (TauReal.exp b) := by
  refine ⟨2 * (k₀ + 1), max N₀ 2, fun n hn => ?_⟩
  have hN : N₀ ≤ n := le_of_max_le_left hn
  have h2 : 2 ≤ n := le_of_max_le_right hn
  unfold TauRat.lt
  rw [toRat_add, TauRat.ofNatRecip_toRat]
  show ((TauReal.exp a).approx n).toRat + 1 / (((2 * (k₀ + 1) : Nat) : Rat) + 1)
        < ((TauReal.exp b).approx n).toRat
  show (TauRat.exp_partial (a.approx n) n).toRat
        + 1 / (((2 * (k₀ + 1) : Nat) : Rat) + 1)
        < (TauRat.exp_partial (b.approx n) n).toRat
  -- Bound exp_partial of a from above and exp_partial of b from below.
  have hxa : |(a.approx n).toRat| ≤ R := ha_bound n
  have hxb : |(b.approx n).toRat| ≤ R := hb_bound n
  have h_a_upper := exp_partial_le_one_plus_x_add_R (a.approx n) R hR0 hR1 hxa n h2
  have h_b_lower := exp_partial_ge_one_plus_x_sub_R (b.approx n) R hR0 hR1 hxb n h2
  -- The gap inequality.
  have h_gap := h_ab_gap n hN
  -- Cast and algebra.
  have h_k1_pos : (0 : Rat) < ((k₀ : Nat) : Rat) + 1 := by
    have : (0 : Rat) ≤ ((k₀ : Nat) : Rat) := by exact_mod_cast Nat.zero_le k₀
    linarith
  have h_q_ne : ((k₀ : Nat) : Rat) + 1 ≠ 0 := ne_of_gt h_k1_pos
  have h_2k1_pos : (0 : Rat) < 2 * (((k₀ : Nat) : Rat) + 1) := by linarith
  have h_4k1_pos : (0 : Rat) < 4 * (((k₀ : Nat) : Rat) + 1) := by linarith
  have h_two_q_plus_one_pos : (0 : Rat) < 2 * (((k₀ : Nat) : Rat) + 1) + 1 := by
    linarith
  have h_strict_recip :
      1 / (2 * (((k₀ : Nat) : Rat) + 1) + 1)
        < 1 / (2 * (((k₀ : Nat) : Rat) + 1)) := by
    rw [div_lt_div_iff₀ h_two_q_plus_one_pos h_2k1_pos]
    linarith
  have h_cast_2k1 : (((2 * (k₀ + 1) : Nat) : Rat)) = 2 * (((k₀ : Nat) : Rat) + 1) := by
    push_cast; ring
  rw [h_cast_2k1]
  -- 2R ≤ 2 * 1/(4q) = 1/(2q).
  have h_2R_le_1_2q : 2 * R ≤ 1 / (2 * (((k₀ : Nat) : Rat) + 1)) := by
    have h_2_4q : (2 : Rat) * (1 / (4 * (((k₀ : Nat) : Rat) + 1)))
                    = 1 / (2 * (((k₀ : Nat) : Rat) + 1)) := by
      field_simp
      ring
    linarith [hRsmall]
  -- Algebra: 1/q - 1/(2q) = 1/(2q).
  have h_combine_alg :
      1 / (((k₀ : Nat) : Rat) + 1) - 1 / (2 * (((k₀ : Nat) : Rat) + 1))
        = 1 / (2 * (((k₀ : Nat) : Rat) + 1)) := by
    field_simp
    ring
  -- Putting it together.  Let q = (k₀ : Rat) + 1, R0 = (a.approx n).toRat, etc.
  -- exp_partial b n ≥ 1 + bn - R          [h_b_lower]
  -- exp_partial a n ≤ 1 + an + R          [h_a_upper]
  -- bn - an > 1/q                          [h_gap]
  -- ⇒ exp_partial b n - exp_partial a n ≥ (bn - an) - 2R > 1/q - 2R ≥ 1/q - 1/(2q) = 1/(2q)
  -- And 1/(2q+1) < 1/(2q), so exp_partial a n + 1/(2q+1) < exp_partial b n.
  linarith [h_combine_alg, h_strict_recip, h_a_upper, h_b_lower, h_gap, h_2R_le_1_2q]

/-- **Exp injectivity (constructive form, bounded inputs).**

    For `a, b : TauReal` bounded by `R ≤ 1/(4(k+1))` for any tolerance
    level `k`, **`a < b` implies `¬ (exp a ≡ exp b)`**.

    This is the constructive contrapositive of `exp_strict_mono`:
    a definite gap in the inputs translates to a definite gap in the
    outputs, which rules out Cauchy equivalence.

    Downstream consumers (R9-1b `log_round_trip`) use this in the form:
      assume the inequality, apply this lemma to get a definite gap
      contradicting `equiv`. -/
theorem TauReal.exp_lt_not_equiv_of_bounded
    (a b : TauReal) (R : Rat) (k₀ N₀ : Nat)
    (hR0 : 0 ≤ R)
    (hRsmall : R ≤ 1 / (4 * (((k₀ : Nat) : Rat) + 1)))
    (hR1 : R ≤ 1)
    (ha_bound : TauReal.BoundedBy a R)
    (hb_bound : TauReal.BoundedBy b R)
    (h_ab_gap : ∀ n, N₀ ≤ n →
      ((a.approx n).toRat + 1 / (((k₀ : Nat) : Rat) + 1)
        < (b.approx n).toRat)) :
    ¬ TauReal.equiv (TauReal.exp a) (TauReal.exp b) := by
  intro h_equiv
  have h_strict := TauReal.exp_strict_mono_of_bounded a b R k₀ N₀
    hR0 hRsmall hR1 ha_bound hb_bound h_ab_gap
  -- h_strict : exp a < exp b, h_equiv : exp a ≡ exp b.
  -- A < B together with A ≡ B gives B < B (via lt_of_equiv_left), contradicting irreflexivity.
  have h_self_lt : TauReal.lt (TauReal.exp b) (TauReal.exp b) :=
    TauReal.lt_of_equiv_left h_equiv h_strict
  exact TauReal.lt_irrefl _ h_self_lt

/-- **Convenience wrapper accepting `TauReal.lt` directly.**

    Same content as `exp_strict_mono_of_bounded`, but unpacks the
    `TauReal.lt` witness `(k₀, N₀, gap)` for the caller.  The radicand
    bound `R ≤ 1/(4(k₀+1))` must be supplied *after* knowing the
    extracted gap-tolerance level `k₀`.

    Usage pattern (downstream R9-1b):
      obtain ⟨k₀, N₀, h_gap⟩ := h_lt
      apply TauReal.exp_strict_mono_of_bounded _ _ R k₀ N₀ ... -/
theorem TauReal.exp_strict_mono_of_lt_bounded
    (a b : TauReal) (R : Rat) (k₀ N₀ : Nat)
    (h_lt_witness :
      ∀ n, N₀ ≤ n →
        TauRat.lt ((a.approx n).add (TauRat.ofNatRecip k₀)) (b.approx n))
    (hR0 : 0 ≤ R)
    (hRsmall : R ≤ 1 / (4 * (((k₀ : Nat) : Rat) + 1)))
    (hR1 : R ≤ 1)
    (ha_bound : TauReal.BoundedBy a R)
    (hb_bound : TauReal.BoundedBy b R) :
    TauReal.lt (TauReal.exp a) (TauReal.exp b) := by
  refine TauReal.exp_strict_mono_of_bounded a b R k₀ N₀
    hR0 hRsmall hR1 ha_bound hb_bound ?_
  intro n hN
  have h := h_lt_witness n hN
  unfold TauRat.lt at h
  rw [toRat_add, TauRat.ofNatRecip_toRat] at h
  exact h

-- ============================================================
-- PART 6.11: EXP CONGRUENCE  (Wave R11-1)
--
-- The Lipschitz/congruence lemma: `exp` carries `equiv` to `equiv`
-- on bounded inputs.  Establishes the substitution principle needed
-- by `exp_neg` (and downstream R11-2/3 — `exp_log` round-trip and
-- `log_inv`).
-- ============================================================

/-- **Power difference bound.**

    For Rats `x, y, R` with `0 ≤ R`, `|x| ≤ R`, `|y| ≤ R`:
        `|x^k − y^k| ≤ k · R^(k-1) · |x − y|` for all `k`.

    Proof: induction on `k` via the factoring
    `x^(k+1) − y^(k+1) = x · (x^k − y^k) + y^k · (x − y)`. -/
private theorem rat_pow_sub_abs_le (x y R : Rat)
    (hR0 : 0 ≤ R) (hx : |x| ≤ R) (hy : |y| ≤ R) :
    ∀ k : Nat, |x ^ k - y ^ k| ≤ (k : Rat) * R ^ (k - 1) * |x - y| := by
  intro k
  induction k with
  | zero =>
    simp
  | succ k ih =>
    have h_id : x ^ (k + 1) - y ^ (k + 1)
        = x * (x ^ k - y ^ k) + y ^ k * (x - y) := by ring
    rw [h_id]
    have h_tri : |x * (x ^ k - y ^ k) + y ^ k * (x - y)|
                  ≤ |x * (x ^ k - y ^ k)| + |y ^ k * (x - y)| := abs_add_le _ _
    rw [abs_mul, abs_mul] at h_tri
    have h_yk : |y| ^ k ≤ R ^ k :=
      Tau.Boundary.Bridge.rat_pow_le_pow_left₀ (abs_nonneg _) hy k
    have h_yk_eq : |y ^ k| = |y| ^ k := Tau.Boundary.Bridge.rat_abs_pow y k
    have h_xy_nn : 0 ≤ |x - y| := abs_nonneg _
    have h_diff_nn : 0 ≤ |x ^ k - y ^ k| := abs_nonneg _
    -- |x| · |x^k - y^k| ≤ R · (k · R^(k-1) · |x-y|)
    have h_step1 : |x| * |x ^ k - y ^ k|
        ≤ R * ((k : Rat) * R ^ (k - 1) * |x - y|) :=
      mul_le_mul hx ih h_diff_nn hR0
    -- |y^k| · |x - y| ≤ R^k · |x - y|
    have h_step2 : |y ^ k| * |x - y| ≤ R ^ k * |x - y| := by
      rw [h_yk_eq]
      exact mul_le_mul_of_nonneg_right h_yk h_xy_nn
    -- Final RHS: ((k + 1 : Nat) : Rat) * R ^ ((k + 1) - 1) * |x - y|
    --        = (k + 1) * R ^ k * |x - y|.
    have h_succ : (((k + 1 : Nat)) : Rat) * R ^ ((k + 1) - 1) * |x - y|
        = (((k : Nat)) : Rat) * R ^ k * |x - y| + R ^ k * |x - y| := by
      have h_idx : (k + 1) - 1 = k := by omega
      rw [h_idx]; push_cast; ring
    rw [h_succ]
    -- We have LHS ≤ R · (k · R^(k-1) · |x-y|) + R^k · |x-y|
    -- Need to show R · k · R^(k-1) = k · R^k.  Split on k = 0 vs k ≥ 1.
    have h_final : R * ((k : Rat) * R ^ (k - 1) * |x - y|)
        = (k : Rat) * R ^ k * |x - y| := by
      rcases Nat.eq_zero_or_pos k with hk | hk
      · -- k = 0: both sides are 0.
        subst hk; ring
      · -- k ≥ 1: R · R^(k-1) = R^k via pow_succ.
        have h_pow_eq : R * R ^ (k - 1) = R ^ k := by
          have h_k : k = (k - 1) + 1 := by omega
          conv_rhs => rw [h_k, pow_succ]
          ring
        rw [show R * ((k : Rat) * R ^ (k - 1) * |x - y|)
              = (k : Rat) * (R * R ^ (k - 1)) * |x - y| from by ring,
            h_pow_eq]
    linarith

/-- **Per-term exp difference bound.**

    For Rats `x, y, R` with `0 ≤ R`, `R ≤ 1`, `|x| ≤ R`, `|y| ≤ R`, `n ≥ 1`:
        `|(exp_term x n).toRat − (exp_term y n).toRat| ≤ |x.toRat − y.toRat| · 4 / 2^n`.

    Proof: `|exp_term x n − exp_term y n| = |x^n − y^n| / n!
                                          ≤ n · R^(n-1) · |x-y| / n!
                                          = R^(n-1)/(n-1)! · |x-y|
                                          ≤ |x-y| · 2 / 2^(n-1)`
    (since `R ≤ 1` and `(n-1)! ≥ 2^{n-2}` for `n ≥ 2`; for `n = 1` direct).
    Equivalently, `|x-y| · 4 / 2^n`. -/
private theorem exp_term_diff_abs_le (x y : TauRat) (R : Rat)
    (hR0 : 0 ≤ R) (hR1 : R ≤ 1)
    (hx : |x.toRat| ≤ R) (hy : |y.toRat| ≤ R)
    (n : Nat) (hn : 1 ≤ n) :
    |(TauRat.exp_term x n).toRat - (TauRat.exp_term y n).toRat|
      ≤ |x.toRat - y.toRat| * 4 / (2 : Rat) ^ n := by
  rw [exp_term_toRat, exp_term_toRat, TauRat.pow_toRat, TauRat.pow_toRat]
  have h_fac_pos : (0 : Rat) < (Nat.factorial n : Rat) := by
    have := Nat.factorial_pos n; exact_mod_cast this
  have h_fac_ne : (Nat.factorial n : Rat) ≠ 0 := ne_of_gt h_fac_pos
  rw [← sub_div]
  rw [abs_div, abs_of_pos h_fac_pos]
  -- Bound numerator: |x^n - y^n| ≤ n · R^(n-1) · |x - y|.
  have h_pow_diff := rat_pow_sub_abs_le x.toRat y.toRat R hR0 hx hy n
  have h_xy_nn : 0 ≤ |x.toRat - y.toRat| := abs_nonneg _
  have h_R_pow_le_one : R ^ (n - 1) ≤ 1 :=
    Tau.Boundary.Bridge.rat_pow_le_one₀ hR0 hR1 (n - 1)
  have h_R_pow_nn : 0 ≤ R ^ (n - 1) := pow_nonneg hR0 _
  have h_n_nn : (0 : Rat) ≤ (n : Rat) := by exact_mod_cast Nat.zero_le n
  -- |x^n - y^n| ≤ n · R^(n-1) · |x-y| ≤ n · 1 · |x-y| = n · |x-y|.
  -- So |x^n - y^n| / n! ≤ n · |x-y| / n! = |x-y| / (n-1)! (since n / n! = 1/(n-1)!).
  -- (n-1)! ≥ 2^(n-2) for n ≥ 2 (factorial_ge_two_pow on n-1 with hk = n-1 ≥ 1).
  -- For n = 1, (n-1)! = 1, RHS bound is |x-y| · 2 = |x-y|·4/2 = |x-y|·4/2^1.  ✓.
  -- For n ≥ 2, /(n-1)! ≤ /2^(n-2) = 4/2^n.  So bound is |x-y| · 4/2^n.
  rcases Nat.eq_or_lt_of_le hn with hn1 | hn2
  · -- n = 1: factorial 1 = 1.
    have h_n_eq : n = 1 := hn1.symm
    subst h_n_eq
    -- Goal: |x^1 - y^1| / 1! ≤ |x - y| · 4 / 2^1
    -- = |x - y| / 1 ≤ |x - y| · 2.
    have h_fac1 : (Nat.factorial 1 : Rat) = 1 := by simp [Nat.factorial]
    rw [h_fac1]
    have h_pow1 : (2 : Rat) ^ 1 = 2 := by norm_num
    rw [h_pow1]
    -- |x - y| / 1 ≤ |x - y| · 4 / 2 = 2 · |x - y|.
    have : x.toRat ^ 1 - y.toRat ^ 1 = x.toRat - y.toRat := by ring
    rw [this]
    have h_2_pos : (0 : Rat) < 2 := by norm_num
    rw [div_le_div_iff₀ (by norm_num : (0 : Rat) < 1) h_2_pos]
    -- |x - y| · 2 ≤ |x - y| · 4 · 1
    linarith
  · -- n ≥ 2.
    have hn_ge_2 : 2 ≤ n := by omega
    have h_n_minus_1_ge_1 : 1 ≤ n - 1 := by omega
    -- Use h_pow_diff: |x^n - y^n| ≤ n · R^(n-1) · |x-y| ≤ n · |x-y|.
    have h_pow_le_n : |x.toRat ^ n - y.toRat ^ n| ≤ (n : Rat) * |x.toRat - y.toRat| := by
      have h_step : (n : Rat) * R ^ (n - 1) * |x.toRat - y.toRat|
                      ≤ (n : Rat) * 1 * |x.toRat - y.toRat| := by
        apply mul_le_mul_of_nonneg_right
        apply mul_le_mul_of_nonneg_left h_R_pow_le_one h_n_nn
        exact h_xy_nn
      have h_simplify : (n : Rat) * 1 * |x.toRat - y.toRat| = (n : Rat) * |x.toRat - y.toRat| := by ring
      linarith
    -- Goal: |x^n - y^n| / n! ≤ |x - y| · 4 / 2^n.
    -- Use n! = n · (n-1)!.
    have h_fac_split : (Nat.factorial n : Rat) = (n : Rat) * (Nat.factorial (n - 1) : Rat) := by
      have h_n_eq : n = (n - 1) + 1 := by omega
      have h_fac_succ : Nat.factorial n = (n - 1 + 1) * Nat.factorial (n - 1) := by
        conv_lhs => rw [h_n_eq]
        rfl
      rw [h_fac_succ]
      have h_cast : (((n - 1 + 1) * Nat.factorial (n - 1) : Nat) : Rat)
                  = (n : Rat) * (Nat.factorial (n - 1) : Rat) := by
        have h_n_minus_1_plus_1_nat : (n - 1) + 1 = n := by omega
        rw [show ((n - 1 + 1) * Nat.factorial (n - 1) : Nat)
              = n * Nat.factorial (n - 1) by rw [h_n_minus_1_plus_1_nat]]
        push_cast; ring
      exact h_cast
    -- (n-1)! ≥ 2^(n-2)
    have h_fac_ge : (2 : Rat) ^ (n - 2) ≤ (Nat.factorial (n - 1) : Rat) := by
      have h_n_minus_2_eq : n - 2 = (n - 1) - 1 := by omega
      rw [h_n_minus_2_eq]
      have h1 : ((2 ^ ((n - 1) - 1) : Nat) : Rat) ≤ (Nat.factorial (n - 1) : Rat) := by
        exact_mod_cast Nat.factorial_ge_two_pow (n - 1) h_n_minus_1_ge_1
      have h2 : ((2 ^ ((n - 1) - 1) : Nat) : Rat) = (2 : Rat) ^ ((n - 1) - 1) := by
        push_cast; ring
      linarith
    have h_n_pos : (0 : Rat) < (n : Rat) := by exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one hn
    have h_fac_n_minus_1_pos : (0 : Rat) < (Nat.factorial (n - 1) : Rat) := by
      have := Nat.factorial_pos (n - 1); exact_mod_cast this
    have h_pow_n_minus_2_pos : (0 : Rat) < (2 : Rat) ^ (n - 2) := by positivity
    have h_pow_n_pos : (0 : Rat) < (2 : Rat) ^ n := by positivity
    -- |x^n - y^n| / n! ≤ n · |x-y| / (n · (n-1)!) = |x-y| / (n-1)! ≤ |x-y| / 2^(n-2)
    -- Now |x-y| / 2^(n-2) = |x-y| · 4 / 2^n.
    -- So target: |x^n - y^n| / n! ≤ |x-y| · 4 / 2^n.
    -- Step 1: |x^n - y^n| / n! ≤ n · |x-y| / n!.
    have h_step1 : |x.toRat ^ n - y.toRat ^ n| / (Nat.factorial n : Rat)
                    ≤ (n : Rat) * |x.toRat - y.toRat| / (Nat.factorial n : Rat) := by
      apply div_le_div_of_nonneg_right h_pow_le_n
      exact le_of_lt h_fac_pos
    -- Step 2: n · |x-y| / (n · (n-1)!) = |x-y| / (n-1)!.
    have h_step2 : (n : Rat) * |x.toRat - y.toRat| / (Nat.factorial n : Rat)
                    = |x.toRat - y.toRat| / (Nat.factorial (n - 1) : Rat) := by
      rw [h_fac_split]
      field_simp
    -- Step 3: |x-y| / (n-1)! ≤ |x-y| / 2^(n-2).
    have h_step3 : |x.toRat - y.toRat| / (Nat.factorial (n - 1) : Rat)
                    ≤ |x.toRat - y.toRat| / (2 : Rat) ^ (n - 2) := by
      rw [div_le_div_iff₀ h_fac_n_minus_1_pos h_pow_n_minus_2_pos]
      have h_xy_nn' : 0 ≤ |x.toRat - y.toRat| := h_xy_nn
      nlinarith [h_xy_nn', h_fac_ge, h_pow_n_minus_2_pos, h_fac_n_minus_1_pos]
    -- Step 4: |x-y| / 2^(n-2) = |x-y| · 4 / 2^n.
    have h_step4 : |x.toRat - y.toRat| / (2 : Rat) ^ (n - 2)
                    = |x.toRat - y.toRat| * 4 / (2 : Rat) ^ n := by
      have h_pow_eq : (2 : Rat) ^ n = (2 : Rat) ^ (n - 2) * 4 := by
        have h_n_eq : n = (n - 2) + 2 := by omega
        conv_lhs => rw [h_n_eq]
        rw [pow_add]
        norm_num
      rw [h_pow_eq]
      field_simp
    linarith

/-- **Exp partial-sum difference bound.**

    For Rats `x, y, R` with `0 ≤ R`, `R ≤ 1`, `|x| ≤ R`, `|y| ≤ R`:
        `|exp_partial x n − exp_partial y n| ≤ 8 · |x − y|` for all `n`.

    Proof by induction on `n`, with strengthened IH
    `|...| ≤ |x - y| · 8 · (1 - 1/2^n)`.  Per-step at index `n`
    contributes `≤ |x - y| · 4/2^n` (by `exp_term_diff_abs_le`), and
    `8·(1 - 1/2^n) + 4/2^n = 8 - 4/2^n ≥ 8·(1 - 1/2^(n+1))`. -/
private theorem exp_partial_diff_abs_le (x y : TauRat) (R : Rat)
    (hR0 : 0 ≤ R) (hR1 : R ≤ 1)
    (hx : |x.toRat| ≤ R) (hy : |y.toRat| ≤ R) (n : Nat) :
    |(TauRat.exp_partial x n).toRat - (TauRat.exp_partial y n).toRat|
      ≤ 8 * |x.toRat - y.toRat| := by
  have h_xy_nn : 0 ≤ |x.toRat - y.toRat| := abs_nonneg _
  -- Strengthened IH:  ≤ |x-y| · 8 · (1 - 1/2^n)
  have h_strong : ∀ n,
      |(TauRat.exp_partial x n).toRat - (TauRat.exp_partial y n).toRat|
        ≤ |x.toRat - y.toRat| * (8 - 8 / (2 : Rat) ^ n) := by
    intro n
    induction n with
    | zero =>
      show |(TauRat.exp_partial x 0).toRat - (TauRat.exp_partial y 0).toRat|
            ≤ |x.toRat - y.toRat| * (8 - 8 / (2 : Rat) ^ 0)
      rw [TauRat.exp_partial_zero, TauRat.exp_partial_zero, toRat_zero]
      simp
    | succ n ih =>
      rw [TauRat.exp_partial_succ, TauRat.exp_partial_succ, toRat_add, toRat_add]
      have h_split : (TauRat.exp_partial x n).toRat + (TauRat.exp_term x n).toRat
                      - ((TauRat.exp_partial y n).toRat + (TauRat.exp_term y n).toRat)
          = ((TauRat.exp_partial x n).toRat - (TauRat.exp_partial y n).toRat)
            + ((TauRat.exp_term x n).toRat - (TauRat.exp_term y n).toRat) := by ring
      rw [h_split]
      have h_tri := abs_add_le
        ((TauRat.exp_partial x n).toRat - (TauRat.exp_partial y n).toRat)
        ((TauRat.exp_term x n).toRat - (TauRat.exp_term y n).toRat)
      -- Per-term bound at index n.
      have h_term_diff :
          |(TauRat.exp_term x n).toRat - (TauRat.exp_term y n).toRat|
            ≤ |x.toRat - y.toRat| * 4 / (2 : Rat) ^ n := by
        rcases Nat.eq_zero_or_pos n with hn0 | hn1
        · subst hn0
          rw [exp_term_toRat, exp_term_toRat, TauRat.pow_zero, TauRat.pow_zero, toRat_one]
          have h_eq : (1 : Rat) / (Nat.factorial 0 : Rat) - 1 / (Nat.factorial 0 : Rat) = 0 := by
            simp [Nat.factorial]
          rw [h_eq, abs_zero]
          apply div_nonneg
          · exact mul_nonneg h_xy_nn (by norm_num)
          · positivity
        · exact exp_term_diff_abs_le x y R hR0 hR1 hx hy n hn1
      have h_pow_pos_n : (0 : Rat) < (2 : Rat) ^ n := by positivity
      have h_pow_pos_n1 : (0 : Rat) < (2 : Rat) ^ (n + 1) := by positivity
      have h_pow_succ : (2 : Rat) ^ (n + 1) = 2 * (2 : Rat) ^ n := by ring
      -- Algebraic combine: ih + h_term_diff ≤ target.
      -- target_{n+1} - ih = |x-y| · (8 - 8/2^(n+1)) - |x-y| · (8 - 8/2^n)
      --                  = |x-y| · (8/2^n - 8/2^(n+1))
      --                  = |x-y| · (8/2^n - 4/2^n)
      --                  = |x-y| · 4/2^n.
      -- So we need term_diff ≤ |x-y| · 4/2^n.  ✓.
      have h_target_diff :
          |x.toRat - y.toRat| * (8 - 8 / (2 : Rat) ^ (n + 1))
            - |x.toRat - y.toRat| * (8 - 8 / (2 : Rat) ^ n)
            = |x.toRat - y.toRat| * 4 / (2 : Rat) ^ n := by
        rw [h_pow_succ]
        field_simp
        ring
      linarith
  -- Conclude: 8 - 8/2^n ≤ 8.
  have h_main := h_strong n
  have h_pow_pos : (0 : Rat) < (2 : Rat) ^ n := by positivity
  have h_decr_nn : (0 : Rat) ≤ 8 / (2 : Rat) ^ n :=
    div_nonneg (by norm_num) (le_of_lt h_pow_pos)
  have h_le_8 : (8 : Rat) - 8 / (2 : Rat) ^ n ≤ 8 := by linarith
  have h_xy_mul : |x.toRat - y.toRat| * ((8 : Rat) - 8 / (2 : Rat) ^ n)
                ≤ |x.toRat - y.toRat| * 8 :=
    mul_le_mul_of_nonneg_left h_le_8 h_xy_nn
  linarith [h_main, h_xy_mul]

/-- **`exp` respects Cauchy equivalence on bounded inputs.**

    For `R ≤ 1` and `x, y : TauReal` both `BoundedBy R`, if `equiv x y`
    then `equiv (exp x hx) (exp y hy)`.

    Proof strategy: refine the input modulus `μ` at level `8·(k+1) − 1`,
    so past the refined modulus we have `|x.approx n − y.approx n| < 1/(8(k+1))`.
    Then `|exp_partial(x.approx n) n − exp_partial(y.approx n) n| ≤
        8 · |x.approx n − y.approx n| < 8 · 1/(8(k+1)) = 1/(k+1)`. -/
theorem TauReal.exp_congr (x y : TauReal) (R : Rat)
    (hR0 : 0 ≤ R) (hR1 : R ≤ 1)
    (hx : TauReal.BoundedBy x R) (hy : TauReal.BoundedBy y R)
    (h_equiv : TauReal.equiv x y) :
    TauReal.equiv (TauReal.exp x) (TauReal.exp y) := by
  obtain ⟨μ, h_mod⟩ := h_equiv
  refine ⟨fun k => μ (8 * (k + 1) - 1), fun k n hn => ?_⟩
  have h_base := h_mod (8 * (k + 1) - 1) n hn
  unfold TauRat.lt at h_base ⊢
  rw [TauRat.toRat_abs, toRat_sub] at h_base
  rw [TauRat.toRat_abs, toRat_sub]
  rw [TauRat.ofNatRecip_toRat] at h_base ⊢
  show |((TauReal.exp x).approx n).toRat - ((TauReal.exp y).approx n).toRat|
        < 1 / ((k : Rat) + 1)
  show |(TauRat.exp_partial (x.approx n) n).toRat
        - (TauRat.exp_partial (y.approx n) n).toRat|
        < 1 / ((k : Rat) + 1)
  have h_diff_bound :=
    exp_partial_diff_abs_le (x.approx n) (y.approx n) R hR0 hR1 (hx n) (hy n) n
  -- h_diff_bound : |...| ≤ 8 * |x.approx n .toRat - y.approx n .toRat|
  have h_refined_eq :
      (1 : Rat) / ((8 * (k + 1) - 1 : Nat) + 1) = 1 / (8 * ((k : Rat) + 1)) := by
    have h_nat_eq : (8 * (k + 1) - 1) + 1 = 8 * (k + 1) := by omega
    have h_cast : ((8 * (k + 1) - 1 : Nat) + 1 : Rat) = 8 * ((k : Rat) + 1) := by
      rw [show ((8 * (k + 1) - 1 : Nat) + 1 : Rat)
            = ((8 * (k + 1) - 1 + 1 : Nat) : Rat) by push_cast; ring]
      rw [h_nat_eq]
      push_cast; ring
    rw [h_cast]
  rw [h_refined_eq] at h_base
  have h_k1_pos : (0 : Rat) < (k : Rat) + 1 := by
    have : (0 : Rat) ≤ (k : Rat) := by exact_mod_cast Nat.zero_le k
    linarith
  have h_8k1_pos : (0 : Rat) < 8 * ((k : Rat) + 1) := by linarith
  have h_step1 :
      8 * |(x.approx n).toRat - (y.approx n).toRat|
        < 8 * (1 / (8 * ((k : Rat) + 1))) := by
    have : (0 : Rat) < 8 := by norm_num
    exact mul_lt_mul_of_pos_left h_base this
  have h_step2 : 8 * (1 / (8 * ((k : Rat) + 1))) = 1 / ((k : Rat) + 1) := by
    field_simp
  linarith

-- ============================================================
-- PART 6.12: EXP NEGATION (Wave R11-1)
--
-- `exp(-x) ≡ 1/exp(x)` via the chain
--   exp(-x) ≡ exp(x).inv · (exp(x) · exp(-x))
--          ≡ exp(x).inv · exp(x + -x)         [exp_add reverse]
--          ≡ exp(x).inv · exp(0)              [exp_congr on x + -x ≡ 0]
--          ≡ exp(x).inv · 1                   [exp_zero]
--          ≡ exp(x).inv.
-- For positivity (BoundedAwayFromZero) of exp(x), need R ≤ 1/4.
-- ============================================================

/-- **`exp(-x) ≡ 1/exp(x)`** for `x` BoundedBy `R ≤ 1/4`.

    The R ≤ 1/4 bound comes from `exp_pos_of_quarter`, which gives the
    `BoundedAwayFromZero` witness needed by `mul_inv_cancel`. -/
theorem TauReal.exp_neg (x : TauReal) (R : Rat)
    (hR0 : 0 ≤ R) (hR4 : R ≤ 1 / 4)
    (hx : TauReal.BoundedBy x R) :
    TauReal.equiv (TauReal.exp x.negate) ((TauReal.exp x).inv) := by
  -- Step 1: deduce -x is BoundedBy R (since |-a| = |a|).
  have hnx : TauReal.BoundedBy x.negate R := by
    intro n
    show |(x.negate.approx n).toRat| ≤ R
    show |(TauRat.negate (x.approx n)).toRat| ≤ R
    rw [toRat_negate, abs_neg]
    exact hx n
  have hR1 : R ≤ 1 := by linarith
  -- Step 2: BoundedAwayFromZero for exp(x).  Use exp_pos_of_quarter:
  --   exp(x) > 0 with witness gap 1/3 past index 1.  So |exp(x).approx n| > 1/3,
  --   i.e. > 1/(2+1).  Take k = 2, N = 1 in the BoundedAwayFromZero predicate.
  have h_exp_pos := TauReal.exp_pos_of_quarter x R hR0 hR4 hx
  have h_exp_baf : (TauReal.exp x).BoundedAwayFromZero := by
    obtain ⟨k₀, N₀, h_gap⟩ := h_exp_pos
    refine ⟨k₀, max N₀ 1, fun n hn => ?_⟩
    have hN : N₀ ≤ n := le_of_max_le_left hn
    have h := h_gap n hN
    -- h : (zero.approx n .toRat + 1/(k₀+1)) < (exp x).approx n .toRat
    -- Want: 1/(k₀+1) < |(exp x).approx n .toRat|
    unfold TauRat.lt at h ⊢
    rw [TauRat.ofNatRecip_toRat, TauRat.toRat_abs]
    rw [toRat_add, TauRat.ofNatRecip_toRat] at h
    -- (zero.approx n).toRat = 0
    have h_zero : (TauReal.zero.approx n).toRat = 0 := by
      show (TauRat.zero).toRat = 0; rw [toRat_zero]
    rw [h_zero] at h
    -- h : 0 + 1/(k₀+1) < (exp x).approx n .toRat, so the value is positive.
    have h_pos : 0 < ((TauReal.exp x).approx n).toRat := by
      have h_recip_pos : (0 : Rat) < 1 / ((k₀ : Rat) + 1) := by
        have : (0 : Rat) < (k₀ : Rat) + 1 := by
          have : (0 : Rat) ≤ (k₀ : Rat) := by exact_mod_cast Nat.zero_le k₀
          linarith
        exact div_pos (by norm_num) this
      linarith
    rw [abs_of_pos h_pos]
    linarith
  -- Step 3: use exp_add (with both BoundedBy R), then exp_congr to fold x + -x → 0.
  have h_exp_add :=
    TauReal.exp_add x x.negate R hR0 hR1 hx hnx
  -- h_exp_add : equiv (exp(x + -x)) (exp(x) · exp(-x))
  -- Step 4: x + -x ≡ 0 (kernel ring axiom).
  have h_add_neg_zero := taureal_add_negate x
  -- h_add_neg_zero : equiv (x + -x) 0
  -- Step 5: exp_congr on x + -x and 0 (need BoundedBy R for both).
  have h_xnx_bounded : TauReal.BoundedBy (x.add x.negate) R := by
    -- |(x + -x).approx n .toRat| = |x.toRat + -x.toRat| = |0| = 0 ≤ R.
    intro n
    show |((x.add x.negate).approx n).toRat| ≤ R
    show |((x.approx n).add (x.negate.approx n)).toRat| ≤ R
    rw [toRat_add]
    show |((x.approx n).toRat + (x.negate.approx n).toRat)| ≤ R
    show |((x.approx n).toRat + (TauRat.negate (x.approx n)).toRat)| ≤ R
    rw [toRat_negate]
    have h_zero : (x.approx n).toRat + -((x.approx n).toRat) = 0 := by ring
    rw [h_zero, abs_zero]
    exact hR0
  have h_zero_bounded : TauReal.BoundedBy TauReal.zero R := by
    intro n
    show |(TauReal.zero.approx n).toRat| ≤ R
    show |(TauRat.zero).toRat| ≤ R
    rw [toRat_zero, abs_zero]
    exact hR0
  have h_exp_xnx_to_exp_zero :=
    TauReal.exp_congr (x.add x.negate) TauReal.zero R hR0 hR1
      h_xnx_bounded h_zero_bounded h_add_neg_zero
  -- h_exp_xnx_to_exp_zero : equiv (exp(x + -x)) (exp 0)
  -- Step 6: exp(0) ≡ 1 (existing).
  have h_exp_zero := TauReal.exp_zero
  -- Combine: exp(x) · exp(-x) ≡ exp(x + -x) ≡ exp(0) ≡ 1.
  have h_prod_eq_one :
      TauReal.equiv ((TauReal.exp x).mul (TauReal.exp x.negate)) TauReal.one := by
    refine TauReal.equiv_trans (TauReal.equiv_symm h_exp_add) ?_
    exact TauReal.equiv_trans h_exp_xnx_to_exp_zero h_exp_zero
  -- Step 7: chain to exp(-x) ≡ exp(x).inv.
  -- exp(-x) ≡ 1 · exp(-x)  (one_mul, sym)
  --        ≡ (exp(x).inv · exp(x)) · exp(-x)  (inv_mul_cancel, sym)
  --        ≡ exp(x).inv · (exp(x) · exp(-x))  (assoc)
  --        ≡ exp(x).inv · 1   (mul_resp_equiv with h_prod_eq_one and exp(x).inv bounded)
  --        ≡ exp(x).inv  (mul_one)
  -- For "≡ exp(x).inv · 1" we use mul_respects_equiv on exp(x).inv · _.
  -- Need exp(x).inv to be bounded.  Since exp(x) ≥ 1/2 past index 1, exp(x).inv ≤ 2.
  have h_inv_bound : ∀ n,
      ((TauReal.exp x).inv.approx n).abs.toRat ≤ (2 : Nat) := by
    intro n
    -- Bound exp(x).inv at every n.
    by_cases h_nz : ((TauReal.exp x).approx n).is_nonzero
    · -- nonzero branch: exp(x).inv = TauRat.inv (exp(x).approx n).
      have h_inv_eq : (TauReal.exp x).inv.approx n = TauRat.inv ((TauReal.exp x).approx n) h_nz := by
        show (if h : ((TauReal.exp x).approx n).is_nonzero
              then TauRat.inv ((TauReal.exp x).approx n) h
              else TauRat.one) = TauRat.inv ((TauReal.exp x).approx n) h_nz
        rw [dif_pos h_nz]
      rw [h_inv_eq]
      -- |exp_partial(x.approx n) n .inv| = 1 / |exp_partial(x.approx n) n|
      -- For n ≥ 1, exp_partial ≥ 1/2, so |inv| ≤ 2.  For n = 0, exp_partial = 0, but h_nz.
      rw [TauRat.toRat_abs, toRat_inv]
      rcases Nat.eq_zero_or_pos n with hn0 | hn1
      · -- n = 0: (exp x).approx 0 = exp_partial (x.approx 0) 0 = sum 0 = 0.
        --  But h_nz says it's nonzero — that's actually a contradiction at n=0.
        --  exp_partial x 0 = TauRat.zero by exp_partial_zero, and TauRat.zero is NOT is_nonzero.
        subst hn0
        exfalso
        apply (TauRat.is_nonzero_iff_toRat_ne_zero _).mp h_nz
        show (TauRat.exp_partial (x.approx 0) 0).toRat = 0
        rw [TauRat.exp_partial_zero, toRat_zero]
      · -- n ≥ 1: use exp_partial_pos_of_quarter to get exp_partial ≥ 1/2.
        have h_lb := exp_partial_pos_of_quarter (x.approx n) R hR0 hR4 (hx n) n hn1
        -- h_lb : 1/2 ≤ (exp_partial (x.approx n) n).toRat
        have h_val_pos : 0 < ((TauReal.exp x).approx n).toRat := by
          show 0 < (TauRat.exp_partial (x.approx n) n).toRat; linarith
        have h_inv_pos : 0 < ((TauReal.exp x).approx n).toRat⁻¹ := inv_pos.mpr h_val_pos
        rw [abs_of_pos h_inv_pos]
        -- 1 / value ≤ 2 since value ≥ 1/2.
        have h_two_nat_eq : (((2 : Nat) : Rat)) = 2 := by norm_num
        rw [h_two_nat_eq]
        rw [show ((TauReal.exp x).approx n).toRat⁻¹
              = 1 / ((TauReal.exp x).approx n).toRat from by rw [one_div]]
        rw [div_le_iff₀ h_val_pos]
        -- Goal: 1 ≤ 2 · value, since value ≥ 1/2.
        show (1 : Rat) ≤ 2 * (TauRat.exp_partial (x.approx n) n).toRat
        linarith
    · -- nonzero-fail branch: exp(x).inv = TauRat.one, abs.toRat = 1 ≤ 2.
      have h_inv_eq : (TauReal.exp x).inv.approx n = TauRat.one := by
        show (if h : ((TauReal.exp x).approx n).is_nonzero
              then TauRat.inv ((TauReal.exp x).approx n) h
              else TauRat.one) = TauRat.one
        rw [dif_neg h_nz]
      rw [h_inv_eq]
      show (TauRat.one).abs.toRat ≤ (2 : Nat)
      rw [TauRat.toRat_abs, toRat_one, abs_one]; norm_num
  -- Now apply mul_respects_equiv_right_of_bound to substitute the right side.
  -- Goal: equiv (exp(x).inv · (exp(x) · exp(-x))) (exp(x).inv · 1)
  -- Equivalent via commutativity to: equiv ((exp(x) · exp(-x)) · exp(x).inv) (1 · exp(x).inv)
  have h_substituted_swap :
      TauReal.equiv (((TauReal.exp x).mul (TauReal.exp x.negate)).mul (TauReal.exp x).inv)
                     (TauReal.one.mul (TauReal.exp x).inv) :=
    TauReal.mul_respects_equiv_right_of_bound _ _ _ 2 (by norm_num) h_inv_bound h_prod_eq_one
  -- Build the chain:
  -- exp(-x) ≡ 1 · exp(-x)   [taureal_one_mul, sym]
  have step1 : TauReal.equiv (TauReal.exp x.negate) (TauReal.one.mul (TauReal.exp x.negate)) :=
    TauReal.equiv_symm (taureal_one_mul (TauReal.exp x.negate))
  -- 1 ≡ exp(x).inv · exp(x)
  have step2_inner : TauReal.equiv ((TauReal.exp x).inv.mul (TauReal.exp x)) TauReal.one :=
    TauReal.inv_mul_cancel (TauReal.exp x) h_exp_baf
  -- 1 · exp(-x) ≡ (exp(x).inv · exp(x)) · exp(-x)
  -- Apply mul_respects_equiv_right_of_bound with c = exp(-x), need exp(-x) bounded.
  have h_expnx_bound : ∀ n, ((TauReal.exp x.negate).approx n).abs.toRat ≤ (3 : Nat) := by
    intro n
    -- Convert .abs.toRat → |.toRat| via TauRat.toRat_abs.
    rw [TauRat.toRat_abs]
    have h_two_nat : ((3 : Nat) : Rat) = 3 := by norm_num
    rw [h_two_nat]
    -- Goal now: |((TauReal.exp x.negate).approx n).toRat| ≤ 3
    -- Unfold (TauReal.exp x.negate).approx n = exp_partial (x.negate.approx n) n.
    show |(TauRat.exp_partial (x.negate.approx n) n).toRat| ≤ 3
    -- And x.negate.approx n = TauRat.negate (x.approx n).
    show |(TauRat.exp_partial (TauRat.negate (x.approx n)) n).toRat| ≤ 3
    rcases Nat.eq_zero_or_pos n with hn0 | hn1
    · subst hn0; rw [TauRat.exp_partial_zero, toRat_zero, abs_zero]; norm_num
    · -- n ≥ 1: use exp_partial bounds with -x.
      have h_neg_bound : |(TauRat.negate (x.approx n)).toRat| ≤ R := by
        rw [toRat_negate, abs_neg]; exact hx n
      rcases Nat.eq_zero_or_pos (n - 1) with h_n_minus_one | _
      · -- n = 1: exp_partial _ 1 = 1.
        have h_n_eq_1 : n = 1 := by omega
        subst h_n_eq_1
        show |(TauRat.exp_partial (TauRat.negate (x.approx 1)) 1).toRat| ≤ 3
        rw [show (TauRat.exp_partial (TauRat.negate (x.approx 1)) 1).toRat = 1 from by
            show (TauRat.sum (TauRat.exp_term _) 1).toRat = 1
            rw [TauRat.sum_succ, TauRat.sum_zero, toRat_add, toRat_zero,
                exp_term_toRat, TauRat.pow_zero, toRat_one]
            simp [Nat.factorial]]
        rw [abs_one]; norm_num
      · -- n ≥ 2: use both upper and lower bounds.
        have hn2 : 2 ≤ n := by omega
        have h_lb_neg := exp_partial_ge_one_plus_x_sub_R (TauRat.negate (x.approx n)) R hR0 hR1 h_neg_bound n hn2
        have h_ub_neg := exp_partial_le_one_plus_x_add_R (TauRat.negate (x.approx n)) R hR0 hR1 h_neg_bound n hn2
        rw [toRat_negate] at h_lb_neg h_ub_neg
        have hxn_R : -R ≤ (x.approx n).toRat ∧ (x.approx n).toRat ≤ R := by
          have h_abs := hx n
          exact ⟨(abs_le.mp h_abs).1, (abs_le.mp h_abs).2⟩
        have h_pos : 0 < (TauRat.exp_partial (TauRat.negate (x.approx n)) n).toRat := by
          have : 1 - 2 * R ≤ (TauRat.exp_partial (TauRat.negate (x.approx n)) n).toRat := by
            linarith [h_lb_neg, hxn_R.2]
          linarith
        rw [abs_of_pos h_pos]
        linarith [h_ub_neg, hxn_R.1]
  have step3 :
      TauReal.equiv (TauReal.one.mul (TauReal.exp x.negate))
                    (((TauReal.exp x).inv.mul (TauReal.exp x)).mul (TauReal.exp x.negate)) := by
    -- Apply mul_resp_equiv_right with substituting 1 → exp(x).inv · exp(x), c = exp(-x).
    -- But mul_resp expects equiv a b first.  Actually we want
    --   substitute LEFT factor: 1 → exp(x).inv · exp(x).
    -- mul_respects_equiv_right_of_bound (a b c : TauReal) substitutes a → b on the left.
    refine TauReal.mul_respects_equiv_right_of_bound _ _ _ 3 (by norm_num) h_expnx_bound ?_
    exact TauReal.equiv_symm step2_inner
  -- assoc: (exp(x).inv · exp(x)) · exp(-x) ≡ exp(x).inv · (exp(x) · exp(-x))
  have step4 :
      TauReal.equiv (((TauReal.exp x).inv.mul (TauReal.exp x)).mul (TauReal.exp x.negate))
                    ((TauReal.exp x).inv.mul ((TauReal.exp x).mul (TauReal.exp x.negate))) :=
    taureal_mul_assoc _ _ _
  -- Use h_substituted_swap (already built): we have equiv on the swap form, need to rebuild.
  -- Actually the swap form is: ((exp(x) · exp(-x)) · exp(x).inv) ≡ (1 · exp(x).inv).
  -- Convert using commutativity.
  have step5 :
      TauReal.equiv ((TauReal.exp x).inv.mul ((TauReal.exp x).mul (TauReal.exp x.negate)))
                    ((TauReal.exp x).inv.mul TauReal.one) := by
    -- Need: equiv a · b a · c via commutativity to b · a c · a, apply h_substituted_swap, swap back.
    -- Or rebuild via mul_respects_equiv with the existing inv-bound.
    -- A cleaner route: chain through commutativity.
    -- exp(x).inv · (exp(x) · exp(-x)) ≡ (exp(x) · exp(-x)) · exp(x).inv (comm)
    -- (exp(x) · exp(-x)) · exp(x).inv ≡ 1 · exp(x).inv  (h_substituted_swap)
    -- 1 · exp(x).inv ≡ exp(x).inv · 1 (comm)
    refine TauReal.equiv_trans (taureal_mul_comm _ _) ?_
    refine TauReal.equiv_trans h_substituted_swap ?_
    exact taureal_mul_comm _ _
  -- exp(x).inv · 1 ≡ exp(x).inv (mul_one)
  have step6 : TauReal.equiv ((TauReal.exp x).inv.mul TauReal.one) (TauReal.exp x).inv :=
    taureal_mul_one (TauReal.exp x).inv
  -- Chain: exp(-x) → 1 · exp(-x) → (inv · exp(x)) · exp(-x) → inv · (exp(x) · exp(-x)) → inv · 1 → inv.
  exact TauReal.equiv_trans step1
        (TauReal.equiv_trans step3
          (TauReal.equiv_trans step4
            (TauReal.equiv_trans step5 step6)))

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
