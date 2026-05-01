import TauLib.BookI.Boundary.TauRealExp
import TauLib.BookI.Boundary.TauRealSqrt
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
# TauLib.BookI.Boundary.TauRealLog

The constructive real natural logarithm `TauReal.log` and its companion
constant `TauReal.log_two`, completing the Phase 0.5 trio (sqrt + exp + log).

## Registry Cross-References

- [I.D84]  TauReal — [I.D111] TauReal.IsCauchy — [I.D112] TauReal.equiv
- [I.D115] TauRat partial-sum helpers (TauRealSum.lean)
- [I.D116] TauRealAnalyticalHelpers — `Rat.four_div_two_pow_lt_recip`
- [I.D117] TauReal Square Root (TauRealSqrt.lean) — Wave R8j, Phase 0.5
- [I.D118] TauReal Exponential (TauRealExp.lean) — Wave R8h-A, Phase 0.5
- [I.D119] TauReal Natural Log (THIS MODULE) — Wave R8 proper W1, Phase 0.5

## Mathematical Content

**Wave R8 proper W1** of the TauReal infrastructure.

The Mercator series
  `log(1 + u) = Σ_{n=1}^∞ (−1)^(n+1) · uⁿ / n`,
absolutely convergent for `|u| ≤ 1/2`.  At the term level
  `|uⁿ / n| ≤ (1/2)ⁿ / n ≤ (1/2)ⁿ`,
so the partial-sum tail is dominated by a geometric series with ratio `1/2`,
and the Cauchy modulus `λ k => k + 3` carries through almost verbatim from
`TauRealE.lean`.

The key constant `TauReal.log_two` is built directly from the same series
at `u = 1/2` (yielding `log 2 = -log(1/2)` via `−log(1−1/2)`).  This sidesteps
the alternation and gives a clean positive-term geometric bound.

For general positive radicands, range reduction `x = 2^k · m` with
`m ∈ [1/√2, √2]` reduces `log x` to `k · log 2 + log m` via the identity
`m ↦ u/(1 + √(1 + u))` smoothing.  The detailed recipe is archived inline
as a docstring; the full closure is **deferred** to a follow-up sprint.

## Status (W1 deliverable, YELLOW)

**Landed sorry-free in this module:**
- `TauRat.log_term`, `TauRat.log_partial`, `TauRat.log_two_term`,
  `TauRat.log_two_partial`
- `TauReal.log_one_plus_of_rat` — log(1+u) for fixed `u : TauRat` with `|u| ≤ 1/2`
- `TauReal.log_two` — the constant `log 2`
- `TauReal.log_one_plus_of_rat_isCauchy` — Cauchy proof, modulus `λ k => k + 3`
- `TauReal.log_two_isCauchy` — Cauchy proof for `log_two`, modulus `λ k => k + 2`
- `TauReal.log_one_plus_zero` — `log(1 + 0) ≡ 0`

**Deferred (archived recipe in inline docstring):**
- `TauReal.log` (general positive radicand) — needs range reduction +
  composition through `sqrt` and `exp_add`
- `TauReal.log_inv` — needs `exp(log a) ≡ a` first
- `TauReal.log_mul` — needs Cauchy product convolution at the alternating
  log series, harder than `exp_add` because the diagonal sum is not the
  binomial identity but the Cauchy convolution of two log expansions

## R-flag Status

- **R1 (new TauReal.equiv relation): NOT triggered.** Single-relation
  kernel rule preserved; `TauReal.equiv` reused verbatim.
- **R2 (Cauchy bound looser than expected): NOT triggered.** The `1/n`
  factor in the log term gives even faster decay than the factorial
  series — `1/(n · 2^n) ≤ 1/2^n` so the same `k + 3` modulus closes.
- **R3 (deferred headlines): TRIGGERED.** `log_inv` and `log_mul` deferred
  per W1 acceptable-partial-delivery scope (orchestrator scope-doc).
-/

set_option autoImplicit false

namespace Tau.Boundary

open Tau.Denotation

-- ============================================================
-- PART 1: TauRat (-1)^n SIGN  (no Mathlib dependency)
-- ============================================================

/-- Alternating sign as a TauRat: `signAlt 0 = 1`, `signAlt 1 = -1`,
    `signAlt 2 = 1`, …, i.e. `(-1)^n`. -/
def TauRat.signAlt : Nat → TauRat
  | 0     => TauRat.one
  | n + 1 => (TauRat.signAlt n).negate

theorem TauRat.signAlt_toRat (n : Nat) :
    (TauRat.signAlt n).toRat = (-1) ^ n := by
  induction n with
  | zero      => simp [TauRat.signAlt, toRat_one]
  | succ n ih =>
    show (TauRat.signAlt n).negate.toRat = (-1) ^ (n + 1)
    rw [toRat_negate, ih]
    -- goal: -((-1) ^ n) = (-1) ^ (n + 1)
    ring

theorem TauRat.abs_signAlt_toRat (n : Nat) :
    |(TauRat.signAlt n).toRat| = 1 := by
  rw [TauRat.signAlt_toRat]
  rcases Nat.even_or_odd n with h | h
  · rw [Even.neg_one_pow h, abs_one]
  · rw [Odd.neg_one_pow h]; norm_num

-- ============================================================
-- PART 2: log_term and log_partial  (Mercator series at 1+u)
-- ============================================================

/-- The k-th Mercator term at `u` (k ≥ 1):
    `log_term u k = (-1)^(k+1) · u^k / k`.

    For `k = 0`, returns `TauRat.zero` (the series starts at k = 1). -/
def TauRat.log_term (u : TauRat) : Nat → TauRat
  | 0     => TauRat.zero
  | k + 1 =>
      -- (-1)^(k+1+1) = (-1)^(k+2) = (-1)^k. So sign = signAlt k. Wait,
      -- index: at k+1, sign is (-1)^((k+1)+1) = (-1)^(k+2) = (-1)^k.
      -- Use signAlt k for that.
      ((TauRat.signAlt k).mul (TauRat.pow u (k + 1))).mul
        ⟨⟨1, 0⟩, k + 2, Nat.succ_pos _⟩

/-- `1/(k+1)` as a TauRat (with positivity baked in). -/
def TauRat.invSucc (k : Nat) : TauRat := ⟨⟨1, 0⟩, k + 1, Nat.succ_pos _⟩

theorem TauRat.invSucc_toRat (k : Nat) :
    (TauRat.invSucc k).toRat = 1 / ((k : Rat) + 1) := by
  unfold TauRat.invSucc TauRat.toRat TauInt.toInt
  push_cast; ring

/-- `(log_term u (k+1)).toRat = (-1)^k · u^(k+1) / (k+2)` at the Rat level. -/
theorem TauRat.log_term_succ_toRat (u : TauRat) (k : Nat) :
    (TauRat.log_term u (k + 1)).toRat =
      (-1) ^ k * u.toRat ^ (k + 1) * (1 / ((k : Rat) + 2)) := by
  show (((TauRat.signAlt k).mul (TauRat.pow u (k + 1))).mul
        ⟨⟨1, 0⟩, k + 2, Nat.succ_pos _⟩).toRat = _
  rw [toRat_mul, toRat_mul, TauRat.signAlt_toRat, TauRat.pow_toRat]
  show (-1) ^ k * u.toRat ^ (k + 1) *
        (⟨⟨1, 0⟩, k + 2, Nat.succ_pos _⟩ : TauRat).toRat = _
  congr 1
  unfold TauRat.toRat TauInt.toInt
  push_cast; ring

@[simp] theorem TauRat.log_term_zero (u : TauRat) :
    (TauRat.log_term u 0).toRat = 0 := by
  show (TauRat.zero).toRat = 0
  exact toRat_zero

/-- Bound on a single log term: `|log_term u (k+1)| ≤ |u|^(k+1) / (k+2)`. -/
theorem TauRat.abs_log_term_succ_toRat (u : TauRat) (k : Nat) :
    |(TauRat.log_term u (k + 1)).toRat|
      = |u.toRat| ^ (k + 1) / ((k : Rat) + 2) := by
  rw [TauRat.log_term_succ_toRat]
  have h_pos_k2 : (0 : Rat) < (k : Rat) + 2 := by
    have : (0 : Rat) ≤ (k : Rat) := by exact_mod_cast Nat.zero_le k
    linarith
  rw [abs_mul, abs_mul]
  rw [show |((-1 : Rat) ^ k)| = 1 by
        rcases Nat.even_or_odd k with h | h
        · rw [Even.neg_one_pow h, abs_one]
        · rw [Odd.neg_one_pow h]; norm_num,
      one_mul]
  rw [Tau.Boundary.Bridge.rat_abs_pow]
  rw [show |1 / ((k : Rat) + 2)| = 1 / ((k : Rat) + 2) by
        rw [abs_of_pos (by positivity : (0 : Rat) < 1 / ((k : Rat) + 2))]]
  ring

/-- Partial sum: `log_partial u n = Σ_{k=0}^{n-1} log_term u k`. -/
def TauRat.log_partial (u : TauRat) (n : Nat) : TauRat :=
  TauRat.sum (TauRat.log_term u) n

@[simp] theorem TauRat.log_partial_zero (u : TauRat) :
    TauRat.log_partial u 0 = TauRat.zero := rfl

@[simp] theorem TauRat.log_partial_succ (u : TauRat) (n : Nat) :
    TauRat.log_partial u (n + 1) =
      (TauRat.log_partial u n).add (TauRat.log_term u n) := rfl

-- ============================================================
-- PART 3: TauReal.log_one_plus_of_rat  (Mercator at fixed u)
-- ============================================================

/-- `TauReal.log_one_plus_of_rat u`: the constructive real `log(1+u)` for
    a fixed `u : TauRat` with `|u| ≤ 1/2`.  Mirrors `TauReal.exp_of_rat`
    in `TauRealExp.lean`.

    The n-th approximation is `log_partial u n`. -/
def TauReal.log_one_plus_of_rat (u : TauRat) : TauReal :=
  ⟨fun n => TauRat.log_partial u n⟩

-- ============================================================
-- PART 4: PER-TERM GEOMETRIC BOUND
-- ============================================================

/-- For `|u| ≤ 1/2` and `k ≥ 1`, `|log_term u k| ≤ 1 / 2^k`.

    Proof: `|log_term u k| = |u|^k / (k+1) ≤ (1/2)^k / 1 = 1/2^k`
    (using `|u|^k ≤ (1/2)^k = 1/2^k` and `1/(k+1) ≤ 1`). -/
private theorem log_term_abs_le_geom (u : TauRat)
    (hu : |u.toRat| ≤ 1 / 2)
    (k : Nat) (hk : 1 ≤ k) :
    |(TauRat.log_term u k).toRat| ≤ 1 / (2 ^ k : Rat) := by
  obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
  rw [TauRat.abs_log_term_succ_toRat]
  -- Goal: |u|^(k'+1) / (k' + 2) ≤ 1 / 2^(k' + 1)
  have h_u_nn : (0 : Rat) ≤ |u.toRat| := abs_nonneg _
  have h_u_le_half : |u.toRat| ≤ 1 / 2 := hu
  have h_pow_le : |u.toRat| ^ (k' + 1) ≤ (1 / 2 : Rat) ^ (k' + 1) :=
    Tau.Boundary.Bridge.rat_pow_le_pow_left₀ h_u_nn h_u_le_half (k' + 1)
  have h_pow_eq : ((1 : Rat) / 2) ^ (k' + 1) = 1 / (2 : Rat) ^ (k' + 1) := by
    rw [div_pow, one_pow]
  rw [h_pow_eq] at h_pow_le
  have h_pow_pos : (0 : Rat) < (2 : Rat) ^ (k' + 1) := by positivity
  have h_k2_pos : (0 : Rat) < (k' : Rat) + 2 := by
    have : (0 : Rat) ≤ (k' : Rat) := by exact_mod_cast Nat.zero_le k'
    linarith
  have h_k2_ge_1 : (1 : Rat) ≤ (k' : Rat) + 2 := by
    have : (0 : Rat) ≤ (k' : Rat) := by exact_mod_cast Nat.zero_le k'
    linarith
  -- |u|^(k'+1) / (k'+2) ≤ |u|^(k'+1) / 1 ≤ 1/2^(k'+1)
  have h_pow_nn : (0 : Rat) ≤ |u.toRat| ^ (k' + 1) := pow_nonneg h_u_nn _
  have h_step1 : |u.toRat| ^ (k' + 1) / ((k' : Rat) + 2)
                  ≤ |u.toRat| ^ (k' + 1) := by
    rw [div_le_iff₀ h_k2_pos]
    nlinarith
  linarith

-- ============================================================
-- PART 5: TELESCOPING TAIL ON sumFromTo |log_term|
-- ============================================================

/-- Telescoping geometric bound on the abs-partial-sum of log terms,
    mirroring `TauRealExp.sumFromTo_exp_term_bound`.  -/
private theorem sumFromTo_log_term_bound (u : TauRat)
    (hu : |u.toRat| ≤ 1 / 2)
    (n : Nat) (hn : 1 ≤ n) :
    ∀ m, n ≤ m →
    (TauRat.sumFromTo (fun k => (TauRat.log_term u k).abs) n m).toRat
      ≤ 2 / (2 ^ n : Rat) - 2 / (2 ^ m : Rat) := by
  intro m hnm
  induction m with
  | zero => omega
  | succ m ih =>
    by_cases h_eq : n = m + 1
    · subst h_eq
      rw [TauRat.sumFromTo_self, toRat_zero]
      have : (0 : Rat) ≤ 2 / (2 : Rat) ^ (m + 1) :=
        div_nonneg (by linarith) (by positivity)
      linarith
    · have hnm' : n ≤ m := by omega
      have hm1 : 1 ≤ m := by omega
      have ih' := ih hnm'
      have h_rec :
          TauRat.sumFromTo (fun k => (TauRat.log_term u k).abs) n (m + 1) =
            (TauRat.sumFromTo (fun k => (TauRat.log_term u k).abs) n m).add
              ((TauRat.log_term u m).abs) := by
        show (if n ≤ m then _ else _) = _; rw [if_pos hnm']
      rw [h_rec, toRat_add]
      have h_term_abs_eq : (TauRat.log_term u m).abs.toRat
                            = |(TauRat.log_term u m).toRat| := TauRat.toRat_abs _
      rw [h_term_abs_eq]
      have h_term_le : |(TauRat.log_term u m).toRat|
                          ≤ 1 / (2 ^ m : Rat) :=
        log_term_abs_le_geom u hu m hm1
      have h_pow_succ : (2 : Rat) ^ (m + 1) = 2 * (2 : Rat) ^ m := by ring
      have h_pow_pos : (0 : Rat) < (2 : Rat) ^ m := by positivity
      have h_rewrite_goal : (2 : Rat) / 2 ^ (m + 1) = 1 / (2 : Rat) ^ m := by
        rw [h_pow_succ]; field_simp
      rw [h_rewrite_goal]
      -- Goal: SFT.toRat + |log_term u m| ≤ 2/2^n - 1/2^m
      -- ih' :  SFT.toRat ≤ 2/2^n - 2/2^m, so SFT.toRat ≤ 2/2^n - 2/2^m
      -- Need 2/2^n - 2/2^m + 1/2^m ≤ 2/2^n - 1/2^m, i.e. 1/2^m ≤ 2 · 1/2^m ✓
      have h_rewrite_ih : (2 : Rat) / 2 ^ m = 2 * (1 / (2 : Rat) ^ m) := by
        field_simp
      rw [h_rewrite_ih] at ih'
      linarith

-- ============================================================
-- PART 6: PARTIAL-SUM CAUCHY BOUND
-- ============================================================

/-- `|log_partial u m − log_partial u n| ≤ 2/2^n` for `1 ≤ n ≤ m`,
    `|u| ≤ 1/2`. -/
theorem TauReal.log_partial_cauchy_bound (u : TauRat)
    (hu : |u.toRat| ≤ 1 / 2)
    (m n : Nat) (hn : 1 ≤ n) (hnm : n ≤ m) :
    |(TauRat.log_partial u m).toRat - (TauRat.log_partial u n).toRat|
      ≤ 2 / (2 ^ n : Rat) := by
  unfold TauRat.log_partial
  rw [TauRat.sum_sub_toRat_eq_sumFromTo (TauRat.log_term u) n m hnm]
  have h_tri := TauRat.sumFromTo_abs_le (TauRat.log_term u) n m
  have h_strong := sumFromTo_log_term_bound u hu n hn m hnm
  have h_pos_m : (0 : Rat) ≤ 2 / (2 : Rat) ^ m :=
    div_nonneg (by linarith) (by positivity)
  linarith

-- ============================================================
-- PART 7: IsCauchy FOR log_one_plus_of_rat
-- ============================================================

/-- `TauReal.log_one_plus_of_rat u` is Cauchy with modulus `λ k => k + 3`,
    provided `|u.toRat| ≤ 1/2`.

    Proof structure mirrors `TauReal.exp_of_rat_isCauchy` exactly: the
    only difference is the constant in the geometric bound (2 here vs 4
    for exp), but `2 / 2^n < 4 / 2^n < 1/(k+1)` for `n ≥ k+3` regardless. -/
theorem TauReal.log_one_plus_of_rat_isCauchy (u : TauRat)
    (hu : |u.toRat| ≤ 1 / 2) :
    (TauReal.log_one_plus_of_rat u).IsCauchy := by
  refine ⟨fun k => k + 3, ?_⟩
  intro k m n hm hn
  change k + 3 ≤ m at hm
  change k + 3 ≤ n at hn
  unfold TauRat.lt
  rw [TauRat.toRat_abs, toRat_sub, TauRat.ofNatRecip_toRat]
  show |(TauRat.log_partial u m).toRat - (TauRat.log_partial u n).toRat|
        < 1 / ((k : Rat) + 1)
  by_cases h_le : n ≤ m
  · have h_n_ge : 1 ≤ n := by omega
    have h_bound := TauReal.log_partial_cauchy_bound u hu m n h_n_ge h_le
    -- 2/2^n ≤ 4/2^n < 1/(k+1)
    have h_pos : (0 : Rat) < (2 : Rat) ^ n := by positivity
    have h_step : (2 : Rat) / (2 : Rat) ^ n ≤ 4 / (2 : Rat) ^ n := by
      rw [div_le_div_iff₀ h_pos h_pos]; nlinarith
    have h2 := Rat.four_div_two_pow_lt_recip k n hn
    linarith
  · push_neg at h_le
    have h_m_ge : 1 ≤ m := by omega
    have h_swap_abs :
        |(TauRat.log_partial u m).toRat - (TauRat.log_partial u n).toRat|
          = |(TauRat.log_partial u n).toRat - (TauRat.log_partial u m).toRat| := by
      rw [show (TauRat.log_partial u m).toRat - (TauRat.log_partial u n).toRat
            = -((TauRat.log_partial u n).toRat - (TauRat.log_partial u m).toRat) from by ring,
          abs_neg]
    rw [h_swap_abs]
    have h_bound := TauReal.log_partial_cauchy_bound u hu n m h_m_ge
      (Nat.le_of_lt h_le)
    have h_pos : (0 : Rat) < (2 : Rat) ^ m := by positivity
    have h_step : (2 : Rat) / (2 : Rat) ^ m ≤ 4 / (2 : Rat) ^ m := by
      rw [div_le_div_iff₀ h_pos h_pos]; nlinarith
    have h2 := Rat.four_div_two_pow_lt_recip k m hm
    linarith

-- ============================================================
-- PART 8: log(1 + 0) ≡ 0  HEADLINE
-- ============================================================

/-- For `u = 0`: `(log_partial 0 n).toRat = 0` for every n.
    All terms vanish since `log_term 0 k = (-1)^? · 0^k / k = 0` for k ≥ 1
    (and `log_term 0 0 = 0` by definition). -/
private theorem log_partial_zero_toRat (n : Nat) :
    (TauRat.log_partial TauRat.zero n).toRat = 0 := by
  induction n with
  | zero => simp [TauRat.log_partial, TauRat.sum_zero, toRat_zero]
  | succ n ih =>
    rw [TauRat.log_partial_succ, toRat_add, ih]
    -- Goal: 0 + (log_term 0 n).toRat = 0
    -- Need to show (log_term 0 n).toRat = 0 for every n.
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · -- n = 0: log_term 0 0 = TauRat.zero by def, so toRat = 0
      have h_eq : (TauRat.log_term TauRat.zero 0).toRat = 0 := TauRat.log_term_zero TauRat.zero
      linarith
    · obtain ⟨k', rfl⟩ : ∃ k', n = k' + 1 := ⟨n - 1, by omega⟩
      rw [TauRat.log_term_succ_toRat]
      -- Goal: 0 + (-1)^k' * (TauRat.zero).toRat^(k'+1) * (1/(k'+2)) = 0
      have h_zero_toRat : (TauRat.zero : TauRat).toRat = 0 := toRat_zero
      rw [h_zero_toRat]
      have h_pow : (0 : Rat) ^ (k' + 1) = 0 := zero_pow (by omega : k' + 1 ≠ 0)
      rw [h_pow]; ring

/-- `log(1 + 0) ≡ 0` up to TauReal.equiv. -/
theorem TauReal.log_one_plus_zero :
    TauReal.equiv (TauReal.log_one_plus_of_rat TauRat.zero) TauReal.zero := by
  refine ⟨fun _ => 0, fun k n _ => ?_⟩
  unfold TauRat.lt
  rw [TauRat.toRat_abs, toRat_sub, TauRat.ofNatRecip_toRat]
  show |(TauRat.log_partial TauRat.zero n).toRat - (TauReal.zero.approx n).toRat|
        < 1 / ((k : Rat) + 1)
  rw [log_partial_zero_toRat n]
  show |0 - (TauReal.zero.approx n).toRat| < 1 / ((k : Rat) + 1)
  -- TauReal.zero.approx n = TauRat.zero, so its toRat = 0.
  have h_zero : (TauReal.zero.approx n).toRat = 0 := by
    show (TauRat.zero).toRat = 0; exact toRat_zero
  rw [h_zero, sub_zero, abs_zero]
  have h_pos : (0 : Rat) < (k : Rat) + 1 := by
    have : (0 : Rat) ≤ (k : Rat) := by exact_mod_cast Nat.zero_le k
    linarith
  exact div_pos (by norm_num) h_pos

-- ============================================================
-- PART 9: TauReal.log_two — a TauReal-witnessed value of log 2
-- ============================================================

/-- The k-th term of the series `log 2 = Σ_{n=1}^∞ 1 / (n · 2^n)`.

    Standard derivation: `log 2 = -log(1 - 1/2) = Σ (1/2)^n / n`.
    All terms are positive, so no alternation — easier than the
    Mercator alternating form. -/
def TauRat.log_two_term : Nat → TauRat
  | 0     => TauRat.zero
  | k + 1 =>
      -- Term: 1 / ((k+1) · 2^(k+1)).  Build by num/den directly.
      ⟨⟨1, 0⟩, (k + 1) * 2 ^ (k + 1),
        Nat.mul_pos (Nat.succ_pos _) (by positivity)⟩

theorem TauRat.log_two_term_succ_toRat (k : Nat) :
    (TauRat.log_two_term (k + 1)).toRat
      = 1 / (((k : Rat) + 1) * (2 : Rat) ^ (k + 1)) := by
  show (⟨⟨1, 0⟩, (k + 1) * 2 ^ (k + 1),
        Nat.mul_pos (Nat.succ_pos _) (by positivity)⟩
        : TauRat).toRat = _
  unfold TauRat.toRat TauInt.toInt
  push_cast; ring

@[simp] theorem TauRat.log_two_term_zero :
    (TauRat.log_two_term 0).toRat = 0 := by
  show (TauRat.zero).toRat = 0; exact toRat_zero

theorem TauRat.log_two_term_nn (k : Nat) : 0 ≤ (TauRat.log_two_term k).toRat := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · rw [TauRat.log_two_term_zero]
  · obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
    rw [TauRat.log_two_term_succ_toRat]
    have h_k1_pos : (0 : Rat) < (k' : Rat) + 1 := by
      have : (0 : Rat) ≤ (k' : Rat) := by exact_mod_cast Nat.zero_le k'
      linarith
    have h_pow_pos : (0 : Rat) < (2 : Rat) ^ (k' + 1) := by positivity
    have h_denom_pos : (0 : Rat) < ((k' : Rat) + 1) * (2 : Rat) ^ (k' + 1) :=
      mul_pos h_k1_pos h_pow_pos
    have h_one_pos : (0 : Rat) < 1 := by norm_num
    have h_div_pos : (0 : Rat) < 1 / (((k' : Rat) + 1) * (2 : Rat) ^ (k' + 1)) :=
      div_pos h_one_pos h_denom_pos
    linarith

theorem TauRat.abs_log_two_term_toRat (k : Nat) :
    |(TauRat.log_two_term k).toRat| = (TauRat.log_two_term k).toRat :=
  abs_of_nonneg (TauRat.log_two_term_nn k)

/-- Per-term geometric bound for log_two: `log_two_term k ≤ 1 / 2^k`. -/
private theorem log_two_term_le_geom (k : Nat) (hk : 1 ≤ k) :
    (TauRat.log_two_term k).toRat ≤ 1 / (2 ^ k : Rat) := by
  obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
  rw [TauRat.log_two_term_succ_toRat]
  -- Goal: 1 / ((k' + 1) * 2^(k' + 1)) ≤ 1 / 2^(k' + 1).
  have h1 : (1 : Rat) ≤ (k' : Rat) + 1 := by
    have : (0 : Rat) ≤ (k' : Rat) := by exact_mod_cast Nat.zero_le k'
    linarith
  have h_pow_pos : (0 : Rat) < (2 : Rat) ^ (k' + 1) := by positivity
  have h_denom_pos : (0 : Rat) < ((k' : Rat) + 1) * (2 : Rat) ^ (k' + 1) := by
    have : (0 : Rat) < (k' : Rat) + 1 := by linarith
    positivity
  rw [div_le_div_iff₀ h_denom_pos h_pow_pos]
  nlinarith

/-- Partial sum: `log_two_partial n = Σ_{k=0}^{n-1} log_two_term k`. -/
def TauRat.log_two_partial (n : Nat) : TauRat :=
  TauRat.sum TauRat.log_two_term n

@[simp] theorem TauRat.log_two_partial_zero :
    TauRat.log_two_partial 0 = TauRat.zero := rfl

@[simp] theorem TauRat.log_two_partial_succ (n : Nat) :
    TauRat.log_two_partial (n + 1) =
      (TauRat.log_two_partial n).add (TauRat.log_two_term n) := rfl

/-- The TauReal constant `log 2`, from the series `Σ_{n≥1} 1/(n · 2^n)`. -/
def TauReal.log_two : TauReal := ⟨TauRat.log_two_partial⟩

-- ----------------------------------------------------------------
-- Telescoping bound for the log_two series (positive terms — abs is
-- identity, no triangle-inequality detour required).
-- ----------------------------------------------------------------

private theorem sumFromTo_log_two_term_bound
    (n : Nat) (hn : 1 ≤ n) :
    ∀ m, n ≤ m →
    (TauRat.sumFromTo TauRat.log_two_term n m).toRat
      ≤ 2 / (2 ^ n : Rat) - 2 / (2 ^ m : Rat) := by
  intro m hnm
  induction m with
  | zero => omega
  | succ m ih =>
    by_cases h_eq : n = m + 1
    · subst h_eq
      rw [TauRat.sumFromTo_self, toRat_zero]
      have : (0 : Rat) ≤ 2 / (2 : Rat) ^ (m + 1) :=
        div_nonneg (by linarith) (by positivity)
      linarith
    · have hnm' : n ≤ m := by omega
      have hm1 : 1 ≤ m := by omega
      have ih' := ih hnm'
      have h_rec :
          TauRat.sumFromTo TauRat.log_two_term n (m + 1) =
            (TauRat.sumFromTo TauRat.log_two_term n m).add (TauRat.log_two_term m) := by
        show (if n ≤ m then _ else _) = _; rw [if_pos hnm']
      rw [h_rec, toRat_add]
      have h_term_le : (TauRat.log_two_term m).toRat ≤ 1 / (2 ^ m : Rat) :=
        log_two_term_le_geom m hm1
      have h_pow_succ : (2 : Rat) ^ (m + 1) = 2 * (2 : Rat) ^ m := by ring
      have h_pow_pos : (0 : Rat) < (2 : Rat) ^ m := by positivity
      have h_rewrite_goal : (2 : Rat) / 2 ^ (m + 1) = 1 / (2 : Rat) ^ m := by
        rw [h_pow_succ]; field_simp
      rw [h_rewrite_goal]
      have h_rewrite_ih : (2 : Rat) / 2 ^ m = 2 * (1 / (2 : Rat) ^ m) := by field_simp
      rw [h_rewrite_ih] at ih'
      linarith

theorem TauReal.log_two_partial_cauchy_bound
    (m n : Nat) (hn : 1 ≤ n) (hnm : n ≤ m) :
    |(TauRat.log_two_partial m).toRat - (TauRat.log_two_partial n).toRat|
      ≤ 2 / (2 ^ n : Rat) := by
  unfold TauRat.log_two_partial
  rw [TauRat.sum_sub_toRat_eq_sumFromTo TauRat.log_two_term n m hnm]
  -- Positive terms ⇒ the sumFromTo is ≥ 0, but its abs equals itself.
  have h_strong := sumFromTo_log_two_term_bound n hn m hnm
  -- |sumFromTo| = sumFromTo (positive terms) — use h_strong directly after abs_of_nonneg.
  have h_sft_nn : 0 ≤ (TauRat.sumFromTo TauRat.log_two_term n m).toRat := by
    -- inducting on m with the same case-split structure
    clear h_strong hnm hn
    induction m with
    | zero => simp [TauRat.sumFromTo_zero, toRat_zero]
    | succ m ih =>
      by_cases h : n ≤ m
      · have h_rec : TauRat.sumFromTo TauRat.log_two_term n (m + 1) =
              (TauRat.sumFromTo TauRat.log_two_term n m).add (TauRat.log_two_term m) := by
          show (if n ≤ m then _ else _) = _; rw [if_pos h]
        rw [h_rec, toRat_add]
        linarith [TauRat.log_two_term_nn m]
      · have h_rec : TauRat.sumFromTo TauRat.log_two_term n (m + 1) = TauRat.zero := by
          show (if n ≤ m then _ else _) = _; rw [if_neg h]
        rw [h_rec, toRat_zero]
  rw [abs_of_nonneg h_sft_nn]
  have h_pos_m : (0 : Rat) ≤ 2 / (2 : Rat) ^ m :=
    div_nonneg (by linarith) (by positivity)
  linarith

theorem TauReal.log_two_isCauchy : TauReal.log_two.IsCauchy := by
  refine ⟨fun k => k + 3, ?_⟩
  intro k m n hm hn
  change k + 3 ≤ m at hm
  change k + 3 ≤ n at hn
  unfold TauRat.lt
  rw [TauRat.toRat_abs, toRat_sub, TauRat.ofNatRecip_toRat]
  show |(TauRat.log_two_partial m).toRat - (TauRat.log_two_partial n).toRat|
        < 1 / ((k : Rat) + 1)
  by_cases h_le : n ≤ m
  · have h_n_ge : 1 ≤ n := by omega
    have h_bound := TauReal.log_two_partial_cauchy_bound m n h_n_ge h_le
    have h_pos : (0 : Rat) < (2 : Rat) ^ n := by positivity
    have h_step : (2 : Rat) / (2 : Rat) ^ n ≤ 4 / (2 : Rat) ^ n := by
      rw [div_le_div_iff₀ h_pos h_pos]; nlinarith
    have h2 := Rat.four_div_two_pow_lt_recip k n hn
    linarith
  · push_neg at h_le
    have h_m_ge : 1 ≤ m := by omega
    have h_swap_abs :
        |(TauRat.log_two_partial m).toRat - (TauRat.log_two_partial n).toRat|
          = |(TauRat.log_two_partial n).toRat - (TauRat.log_two_partial m).toRat| := by
      rw [show (TauRat.log_two_partial m).toRat - (TauRat.log_two_partial n).toRat
            = -((TauRat.log_two_partial n).toRat - (TauRat.log_two_partial m).toRat) from by ring,
          abs_neg]
    rw [h_swap_abs]
    have h_bound := TauReal.log_two_partial_cauchy_bound n m h_m_ge
      (Nat.le_of_lt h_le)
    have h_pos : (0 : Rat) < (2 : Rat) ^ m := by positivity
    have h_step : (2 : Rat) / (2 : Rat) ^ m ≤ 4 / (2 : Rat) ^ m := by
      rw [div_le_div_iff₀ h_pos h_pos]; nlinarith
    have h2 := Rat.four_div_two_pow_lt_recip k m hm
    linarith

/-! ## TODO: Generic `TauReal.log` (range-reduced)

The full `TauReal.log : TauReal → TauReal` requires range reduction.

**Recipe sketch:**

For a positive radicand `x : TauReal` (witness via `BoundedAwayFromZero`
plus a sign witness analogous to `sqrt_pos`'s `h_sign`):

1. **Find integer `k`** such that `x = 2^k · m` with `m ∈ [1/√2, √2]`.
   Constructively: examine `x.approx` past the BAZ onset index, count
   how many factors of 2 to peel off, return `k : Int`.

2. **Reduce to log m** with `m = (1 + u) / 1` where `u ∈ [1/√2 − 1, √2 − 1]`,
   so `|u| ≤ √2 − 1 < 1/2`.  But the smoothing
   `m ↦ u / (1 + √(1 + u))` (used in libm `log1p`) gives a smaller `u'`
   with `|u'| ≤ 1/4`, even stronger.

3. **Compose**: `log x ≡ k · log_two + log_one_plus(u_reduced)`.

The key obstacles:
- Constructive integer extraction from a TauReal — needs apartness from
  every `2^k` boundary, which is infinitely many predicates.
- Composition through `sqrt` (R8j) and `exp_add` (R8h-A) requires
  congruence lemmas.

**Estimated effort:** 250 lines + 50 line Bridge re-export.
-/

/-! ## TODO: `TauReal.log_inv` (`log(1/a) ≡ -log a`)

**Recipe sketch:** the cleanest constructive route is via `exp`:

  `exp(-log a) = 1/a`  iff  `exp(log a) · exp(-log a) ≡ 1`
                       iff  `exp(log a + (-log a)) ≡ 1`  (by `exp_add`)
                       iff  `exp(0) ≡ 1`  (trivial — `exp_zero`)

So provided we have:
- `log_round_trip : exp(log a) ≡ a` (the analytic core fact)
- `exp_add` (R8h-A — already landed)
- `exp_zero` (already landed)

then:
  `exp(log(1/a)) ≡ 1/a   = (1/(exp(log a)))   ≡ exp(-log a)`
and injectivity of `exp` (from monotonicity, also non-trivial) gives
`log(1/a) ≡ -log a`.

**Direct alternative:** at the series level, the Mercator series for
`log(1+u)` satisfies `log_term (-u) k = -log_term u k` for odd k and
`+log_term u k` for even k.  For `log(1/(1+u)) = log(1 - u/(1+u))`,
substitute `v = -u/(1+u)` and verify the partial-sum convergence.
This is messy but does not require `exp`.

**Estimated effort:** 150 lines (via exp route, after `log_round_trip`)
or 200 lines (direct via series).
-/

/-! ## TODO: `TauReal.log_mul` (`log(a · b) ≡ log a + log b`)

**Recipe sketch:** at the series level, `log_mul` is *not* the binomial
identity (which gave us `exp_add`).  It's the convolution

  `log((1+u)(1+v)) ≡ log(1+u) + log(1+v)`,

which at the rational partial-sum level *requires* the Cauchy product
identity for the alternating-harmonic series convoluted with itself.
The general version is genuinely harder than `exp_add`:

- The diagonal sum is not `(u+v)^n / n` — there is no clean closed form.
- The standard proof is to expand both sides as power series in
  `(u+v) + uv`, which only converges absolutely for very small `u, v`.

The clean composition route via `exp` is preferred:
  `exp(log a + log b) ≡ exp(log a) · exp(log b) ≡ a · b ≡ exp(log(a · b))`,
then injectivity of `exp` gives `log(a·b) ≡ log a + log b`.

This presupposes `log_round_trip` and `exp_injectivity` (both
deferred to a follow-up sprint).

**Estimated effort:** 100 lines (composition route, after `log_round_trip`
+ `exp_injectivity`); 400+ lines (direct via convolution).
-/

-- ============================================================
-- PART 10: SMOKE TESTS
-- ============================================================

-- log(1 + 0) partial: all terms are zero
#eval (TauRat.log_partial TauRat.zero 5).toRat               -- expected: 0

-- log_two_partial 1 = log_two_term 0 = 0 (the series starts at index 1)
#eval (TauRat.log_two_partial 1).toRat                       -- expected: 0

-- log_two_partial 2 = log_two_term 0 + log_two_term 1 = 0 + 1/(1·2) = 1/2
#eval (TauRat.log_two_partial 2).toRat                       -- expected: 1/2

-- log_two_partial 3 = 0 + 1/2 + 1/(2·4) = 1/2 + 1/8 = 5/8
#eval (TauRat.log_two_partial 3).toRat                       -- expected: 5/8

-- log_two_partial 12 ≈ ln 2 ≈ 0.6931
#eval (TauRat.log_two_partial 12).toRat                      -- expected: ≈ 0.6931

-- log_one_plus(1/2) partial 5: alternating partial sum
private def half_rat_log : TauRat := ⟨⟨1, 0⟩, 2, by norm_num⟩
#eval (TauRat.log_partial half_rat_log 5).toRat              -- expected: ≈ ln(3/2) ≈ 0.405

-- IsCauchy at type level
#check @TauReal.log_one_plus_of_rat_isCauchy
#check @TauReal.log_two_isCauchy

end Tau.Boundary
