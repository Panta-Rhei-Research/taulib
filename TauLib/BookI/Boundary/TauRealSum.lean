import TauLib.BookI.Boundary.TauRealInv
import TauLib.BookI.Boundary.Bridge.TauRealAbsBridge
import Mathlib.Tactic.Ring
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity

/-!
# TauLib.BookI.Boundary.TauRealSum

Partial-sum and factorial helpers on `TauRat`, used to define the
series representations of `TauReal.pi` (Leibniz) and `TauReal.e`
(factorial series) in Wave 3.

## Registry Cross-References

- [I.D35] Number Tower — `TauRat` arithmetic
- [I.D107] TauRat Semantic Bridge — `TauRat.toRat`
- [I.D109] TauRat Absolute Value — `TauRat.abs` + triangle inequality

New declarations (pending Wave 3 registry commit):
`TauRat.factorial`, `TauRat.factorial_pos`, `TauRat.sum`,
`TauRat.sum_succ`, `TauRat.sumFromTo`, `TauRat.sum_sub_eq_sumFromTo`,
`TauRat.sumFromTo_abs_le`.

## Mathematical Content

**Wave 3a** of the TauReal infrastructure (see `ROADMAP-3-HINGES.md`).

All partial-sum machinery here is implemented via pure recursive
helpers on `TauRat`, no `Mathlib.Data.Finset` dependency: we stay
strictly within the tactics-only Mathlib policy and keep the proof
obligations local to what `linarith` / `ring` / `push_cast` can close.

- `TauRat.factorial n` — the rational `n!` as a `TauRat`.
- `TauRat.sum f n = Σ_{k=0}^{n-1} f k`, defined by recursion on `n`.
- `TauRat.sumFromTo f n m = Σ_{k=n}^{m-1} f k`, defined by recursion on
  the *upper bound* `m` starting at `n`.
- Telescoping: `sum f m − sum f n = sumFromTo f n m` for `n ≤ m`.
- Triangle inequality on `sumFromTo`: bounds `|sumFromTo f n m|.toRat`
  by `sumFromTo |f| n m .toRat`, lifted from `TauRat.abs_triangle`.
-/

set_option autoImplicit false

namespace Tau.Boundary

open Tau.Denotation

-- ============================================================
-- PART 1: FACTORIAL ON TauRat
-- ============================================================

/-- Rational factorial: `TauRat.factorial n = n!` as a `TauRat`.
    Built via Lean core's `Nat.factorial`. -/
def TauRat.factorial (n : Nat) : TauRat :=
  ⟨⟨Nat.factorial n, 0⟩, 1, Nat.one_pos⟩

/-- `TauRat.factorial n` has positive `toRat` value. -/
theorem TauRat.factorial_pos (n : Nat) : 0 < (TauRat.factorial n).toRat := by
  unfold TauRat.factorial TauRat.toRat TauInt.toInt
  push_cast
  have h : 0 < Nat.factorial n := Nat.factorial_pos n
  have : (0 : Rat) < (Nat.factorial n : Rat) := by exact_mod_cast h
  linarith

/-- `TauRat.factorial n` in Rat is exactly `(n! : Rat)`. -/
theorem TauRat.factorial_toRat (n : Nat) :
    (TauRat.factorial n).toRat = (Nat.factorial n : Rat) := by
  unfold TauRat.factorial TauRat.toRat TauInt.toInt
  push_cast; ring

/-- `TauRat.factorial n` is nonzero. -/
theorem TauRat.factorial_ne_zero (n : Nat) : (TauRat.factorial n).toRat ≠ 0 :=
  ne_of_gt (TauRat.factorial_pos n)

-- ============================================================
-- PART 2: PARTIAL SUM  (Σ_{k=0}^{n-1} f k)
-- ============================================================

/-- Partial sum from 0: `sum f n = Σ_{k=0}^{n-1} f k`. -/
def TauRat.sum (f : Nat → TauRat) : Nat → TauRat
  | 0 => TauRat.zero
  | n + 1 => (TauRat.sum f n).add (f n)

@[simp] theorem TauRat.sum_zero (f : Nat → TauRat) :
    TauRat.sum f 0 = TauRat.zero := rfl

@[simp] theorem TauRat.sum_succ (f : Nat → TauRat) (n : Nat) :
    TauRat.sum f (n + 1) = (TauRat.sum f n).add (f n) := rfl

-- ============================================================
-- PART 3: RANGED SUM  (Σ_{k=n}^{m-1} f k, recursion on m)
-- ============================================================

/-- Ranged sum `sumFromTo f n m = Σ_{k=n}^{m-1} f k`, by recursion on
    the upper bound.  When `m ≤ n` the sum is zero. -/
def TauRat.sumFromTo (f : Nat → TauRat) (n : Nat) : Nat → TauRat
  | 0 => TauRat.zero
  | m + 1 =>
    if n ≤ m then (TauRat.sumFromTo f n m).add (f m)
    else TauRat.zero

@[simp] theorem TauRat.sumFromTo_zero (f : Nat → TauRat) (n : Nat) :
    TauRat.sumFromTo f n 0 = TauRat.zero := rfl

theorem TauRat.sumFromTo_self (f : Nat → TauRat) (n : Nat) :
    TauRat.sumFromTo f n n = TauRat.zero := by
  induction n with
  | zero => rfl
  | succ n _ =>
    show (if n + 1 ≤ n then _ else _) = _
    rw [if_neg (by omega)]

-- ============================================================
-- PART 4: TELESCOPING  (sum m − sum n = sumFromTo n m, for n ≤ m)
-- ============================================================

/-- Telescoping identity at the `toRat` level: the difference of two
    partial sums equals the ranged sum between them. -/
theorem TauRat.sum_sub_toRat_eq_sumFromTo (f : Nat → TauRat) (n : Nat) :
    ∀ m, n ≤ m →
    (TauRat.sum f m).toRat - (TauRat.sum f n).toRat
      = (TauRat.sumFromTo f n m).toRat := by
  intro m hnm
  induction m with
  | zero =>
    -- n ≤ 0 forces n = 0
    have hn : n = 0 := Nat.le_zero.mp hnm
    subst hn
    simp [TauRat.sum_zero, toRat_zero, TauRat.sumFromTo_zero]
  | succ m ih =>
    by_cases h_eq : n = m + 1
    · subst h_eq
      simp [TauRat.sumFromTo_self, toRat_zero]
    · have hnm' : n ≤ m := by omega
      specialize ih hnm'
      rw [TauRat.sum_succ, toRat_add]
      show (TauRat.sum f m).toRat + (f m).toRat - (TauRat.sum f n).toRat =
             (TauRat.sumFromTo f n (m + 1)).toRat
      have h_rec : TauRat.sumFromTo f n (m + 1) =
                   (TauRat.sumFromTo f n m).add (f m) := by
        show (if n ≤ m then _ else _) = _
        rw [if_pos hnm']
      rw [h_rec, toRat_add]
      linarith [ih]

-- ============================================================
-- PART 5: TRIANGLE INEQUALITY ON RANGED SUMS
-- ============================================================

/-- Triangle inequality on a ranged sum at the toRat level:
    `|sumFromTo f n m .toRat| ≤ sumFromTo |f| n m .toRat`.

    Stated with `TauRat.abs` on `f` composed at each index (wrapped into
    a function `fun k => (f k).abs`). -/
theorem TauRat.sumFromTo_abs_le (f : Nat → TauRat) (n : Nat) :
    ∀ m,
    |(TauRat.sumFromTo f n m).toRat|
      ≤ (TauRat.sumFromTo (fun k => (f k).abs) n m).toRat := by
  intro m
  induction m with
  | zero =>
    simp [TauRat.sumFromTo_zero, toRat_zero]
  | succ m ih =>
    by_cases h : n ≤ m
    · -- Both branches take the recursive case
      have h_abs_rec : TauRat.sumFromTo (fun k => (f k).abs) n (m + 1) =
            (TauRat.sumFromTo (fun k => (f k).abs) n m).add (f m).abs := by
        show (if n ≤ m then _ else _) = _; rw [if_pos h]
      have h_f_rec : TauRat.sumFromTo f n (m + 1) =
            (TauRat.sumFromTo f n m).add (f m) := by
        show (if n ≤ m then _ else _) = _; rw [if_pos h]
      rw [h_f_rec, h_abs_rec, toRat_add, toRat_add]
      -- goal: |(SFT f n m).toRat + (f m).toRat|
      --       ≤ (SFT |f| n m).toRat + (f m).abs.toRat
      have h_tri :
          |(TauRat.sumFromTo f n m).toRat + (f m).toRat|
            ≤ |(TauRat.sumFromTo f n m).toRat| + |(f m).toRat| := abs_add_le _ _
      have h_fm_abs : (f m).abs.toRat = |(f m).toRat| := TauRat.toRat_abs _
      rw [h_fm_abs]
      linarith [ih]
    · -- m < n: both sums are zero
      have h_abs_rec : TauRat.sumFromTo (fun k => (f k).abs) n (m + 1) = TauRat.zero := by
        show (if n ≤ m then _ else _) = _; rw [if_neg h]
      have h_f_rec : TauRat.sumFromTo f n (m + 1) = TauRat.zero := by
        show (if n ≤ m then _ else _) = _; rw [if_neg h]
      rw [h_f_rec, h_abs_rec, toRat_zero]
      simp

-- ============================================================
-- PART 6: CAUCHY CONVOLUTION  (Wave R8g — sorry-free closure)
--
-- Statement corrected from `4 · C² / 2^n` (FALSE for n ≥ 4;
-- counterexample C=1, n=4: 17/64 > 16/64) to `n · C² / 2^(n-1)`.
--
-- Proof chain (Engineer R8f-A archived; R8g calibration fixes applied):
-- (1) row identity: product − cauchyPStar = Σ_{i<n} aᵢ·(sumFromTo b (n−i) n)
-- (2) triangle inequality on the outer sum
-- (3) per-row bound: (C/2^i) · (2C/2^(n−i)) = 2C²/2^n
-- (4) rat_finset_sum_le_const_mul: n rows → n·2C²/2^n = nC²/2^(n−1)
-- ============================================================

/-- The n-th diagonal of the Cauchy product of sequences a and b:
    `cauchyDiag a b n = Σ_{i=0}^{n} a i · b (n − i)`. -/
def TauRat.cauchyDiag (a b : Nat → TauRat) (n : Nat) : TauRat :=
  TauRat.sum (fun i => (a i).mul (b (n - i))) (n + 1)

/-- Partial Cauchy sum:
    `cauchyPStar a b N = Σ_{k=0}^{N-1} cauchyDiag a b k`. -/
def TauRat.cauchyPStar (a b : Nat → TauRat) (N : Nat) : TauRat :=
  TauRat.sum (TauRat.cauchyDiag a b) N

@[simp] theorem TauRat.cauchyPStar_zero (a b : Nat → TauRat) :
    TauRat.cauchyPStar a b 0 = TauRat.zero := rfl

section CauchyConvolution

open BigOperators Tau.Boundary.Bridge

-- §6.1  TauRat.sum toRat ↔ Finset.range sum -----------------

private theorem sum_toRat_eq_finset (f : Nat → TauRat) (n : Nat) :
    (TauRat.sum f n).toRat = ∑ i ∈ Finset.range n, (f i).toRat := by
  induction n with
  | zero => simp [TauRat.sum_zero, toRat_zero]
  | succ n ih => rw [TauRat.sum_succ, toRat_add, ih, Finset.sum_range_succ]

-- §6.3  Key reindexing identity (R8g FIX #1, FIX #2)

private theorem cauchyPStar_toRat_eq_row_sums (a b : Nat → TauRat) (n : Nat) :
    (TauRat.cauchyPStar a b n).toRat =
    ∑ i ∈ Finset.range n, (a i).toRat * (TauRat.sum b (n - i)).toRat := by
  induction n with
  | zero =>
    simp [TauRat.cauchyPStar, TauRat.sum_zero, toRat_zero]
  | succ n ih =>
    have h_unfold : (TauRat.cauchyPStar a b (n + 1)).toRat =
        (TauRat.cauchyPStar a b n).toRat + (TauRat.cauchyDiag a b n).toRat := by
      unfold TauRat.cauchyPStar; rw [TauRat.sum_succ, toRat_add]
    rw [h_unfold, ih]
    have h_diag : (TauRat.cauchyDiag a b n).toRat =
        ∑ i ∈ Finset.range (n + 1), (a i).toRat * (b (n - i)).toRat := by
      unfold TauRat.cauchyDiag
      rw [sum_toRat_eq_finset]; congr 1; ext i; exact toRat_mul _ _
    rw [h_diag]
    rw [Finset.sum_range_succ (f := fun i => (a i).toRat * (TauRat.sum b (n + 1 - i)).toRat)]
    -- FIX #1: Replace simp set with explicit rewrites for the n+1-n step
    have h_top : n + 1 - n = 1 := by omega
    rw [h_top]
    -- Now the dangling top term is (a n).toRat * (TauRat.sum b 1).toRat
    -- Note: TauRat.sum b 1 = (TauRat.sum b 0).add (b 0) = TauRat.zero.add (b 0)
    -- so (TauRat.sum b 1).toRat = 0 + (b 0).toRat = (b 0).toRat
    have h_sum1 : (TauRat.sum b 1).toRat = (b 0).toRat := by
      rw [TauRat.sum_succ, toRat_add, TauRat.sum_zero, toRat_zero, zero_add]
    rw [h_sum1]
    have h_step : ∀ i ∈ Finset.range n,
        (a i).toRat * (TauRat.sum b (n + 1 - i)).toRat =
        (a i).toRat * (TauRat.sum b (n - i)).toRat +
        (a i).toRat * (b (n - i)).toRat := by
      intro i hi
      have hi' : i < n := Finset.mem_range.mp hi
      have h_succ_eq : n + 1 - i = (n - i) + 1 := by omega
      rw [h_succ_eq, TauRat.sum_succ, toRat_add]
      ring
    rw [Finset.sum_congr rfl h_step, Finset.sum_add_distrib]
    rw [Finset.sum_range_succ (f := fun i => (a i).toRat * (b (n - i)).toRat)]
    -- The Finset.sum_range_succ on the diag part splits off i = n term:
    -- ... + (a n).toRat * (b (n - n)).toRat
    have h_nn : n - n = 0 := Nat.sub_self n
    rw [h_nn]
    ring

-- §6.4  sumFromTo abs as Finset sum --------------------------

private theorem sumFromTo_abs_toRat_eq_finset (b : Nat → TauRat) (s m : Nat) :
    (TauRat.sumFromTo (fun k => (b k).abs) s (s + m)).toRat =
    ∑ j ∈ Finset.range m, |(b (s + j)).toRat| := by
  induction m with
  | zero =>
    simp [TauRat.sumFromTo_self, toRat_zero]
  | succ m ihm =>
    have h_le : s ≤ s + m := Nat.le_add_right s m
    have h_rec : TauRat.sumFromTo (fun k => (b k).abs) s (s + (m + 1)) =
        (TauRat.sumFromTo (fun k => (b k).abs) s (s + m)).add ((b (s + m)).abs) := by
      show (if s ≤ s + m then
              (TauRat.sumFromTo (fun k => (b k).abs) s (s + m)).add ((b (s + m)).abs)
            else TauRat.zero)
            = (TauRat.sumFromTo (fun k => (b k).abs) s (s + m)).add ((b (s + m)).abs)
      rw [if_pos h_le]
    rw [h_rec, toRat_add, ihm, Finset.sum_range_succ, TauRat.toRat_abs]

-- §6.5  Geometric tail bound (R8g FIX #3 — strengthened invariant)

/-- Strengthened tail invariant: the partial geometric sum equals
    `2*C/2^s · (1 − (1/2)^m)`, expressed via `2C/2^s − 2C/2^(s+m)`. -/
private theorem ratGeomTail_eq (C : Rat) (s : Nat) (m : Nat) :
    ∑ j ∈ Finset.range m, C / (2 : Rat) ^ (s + j)
      = 2 * C / (2 : Rat) ^ s - 2 * C / (2 : Rat) ^ (s + m) := by
  induction m with
  | zero =>
    simp only [Finset.sum_range_zero, Nat.add_zero]
    ring
  | succ m ih =>
    rw [Finset.sum_range_succ, ih]
    have h_pow : (2 : Rat) ^ (s + (m + 1)) = 2 * (2 : Rat) ^ (s + m) := by
      rw [show s + (m + 1) = (s + m) + 1 from by omega, pow_succ]
      ring
    have h_pow_ne : (2 : Rat) ^ (s + m) ≠ 0 := by positivity
    rw [h_pow]
    field_simp
    ring

private theorem ratGeomTail_le (C : Rat) (hC : 0 ≤ C) (s : Nat) (m : Nat) :
    ∑ j ∈ Finset.range m, C / (2 : Rat) ^ (s + j) ≤ 2 * C / (2 : Rat) ^ s := by
  rw [ratGeomTail_eq C s m]
  have h_nn : 0 ≤ 2 * C / (2 : Rat) ^ (s + m) := by positivity
  linarith

-- §6.6  Inline helper for `(2 : Rat)^n = 2 * (2 : Rat)^(n-1)` when 1 ≤ n.
-- (TauRealAnalyticalHelpers is not imported here; inline.)

private theorem rat_pow_pred_eq (n : Nat) (hn : 1 ≤ n) :
    (2 : Rat) ^ n = 2 * (2 : Rat) ^ (n - 1) := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  rw [Nat.add_sub_cancel, pow_succ, mul_comm]

-- §6.6  Headline theorem: cauchy_product_bound (R8g FIX #4, FIX #5)

/-- **Cauchy-product bound (Wave R8g — sorry-free closure).**

    Statement corrected from the original `4 · C² / 2^n` (FALSE for n ≥ 4;
    counterexample C=1, n=4 gives upper-triangular sum 17/64 > 16/64) to
    `n · C² / 2^(n-1)`. Downstream `exp_add` uses modulus `k ↦ 2k+3` to
    absorb the polynomial-in-n factor. -/
theorem TauRat.cauchy_product_bound
    (a b : Nat → TauRat) (C : Rat) (hC : 0 < C)
    (h_a : ∀ i, |(a i).toRat| ≤ C / (2 : Rat) ^ i)
    (h_b : ∀ j, |(b j).toRat| ≤ C / (2 : Rat) ^ j)
    (n : Nat) (hn : 1 ≤ n) :
    |(TauRat.sum a n).toRat * (TauRat.sum b n).toRat
       - (TauRat.cauchyPStar a b n).toRat|
      ≤ n * C ^ 2 / (2 : Rat) ^ (n - 1) := by
  -- (1) Row identity
  have h_row_id :
      (TauRat.sum a n).toRat * (TauRat.sum b n).toRat
        - (TauRat.cauchyPStar a b n).toRat =
      ∑ i ∈ Finset.range n,
        (a i).toRat * ((TauRat.sum b n).toRat - (TauRat.sum b (n - i)).toRat) := by
    rw [cauchyPStar_toRat_eq_row_sums, sum_toRat_eq_finset,
        rat_finset_sum_mul n (fun i => (a i).toRat) (TauRat.sum b n).toRat]
    simp_rw [mul_sub, ← Finset.sum_sub_distrib]
  rw [h_row_id]
  -- (2) Triangle inequality
  have h_tri := rat_abs_finset_sum_le
    (fun i => (a i).toRat * ((TauRat.sum b n).toRat - (TauRat.sum b (n - i)).toRat)) n
  refine h_tri.trans ?_
  simp_rw [abs_mul]
  -- (3) Per-row bound ≤ 2C²/2^n
  have h_row_bound : ∀ i ∈ Finset.range n,
      |(a i).toRat| * |(TauRat.sum b n).toRat - (TauRat.sum b (n - i)).toRat|
      ≤ 2 * C ^ 2 / (2 : Rat) ^ n := by
    intro i hi
    have hi' : i < n := Finset.mem_range.mp hi
    have h_ai := h_a i
    have h_sft_eq :
        (TauRat.sum b n).toRat - (TauRat.sum b (n - i)).toRat =
        (TauRat.sumFromTo b (n - i) n).toRat :=
      TauRat.sum_sub_toRat_eq_sumFromTo b (n - i) n (by omega)
    rw [h_sft_eq]
    have h_abs_sft : |(TauRat.sumFromTo b (n - i) n).toRat|
        ≤ (TauRat.sumFromTo (fun k => (b k).abs) (n - i) n).toRat :=
      TauRat.sumFromTo_abs_le b (n - i) n
    have h_upper : (n - i) + i = n := by omega
    have h_finset_eq :
        (TauRat.sumFromTo (fun k => (b k).abs) (n - i) n).toRat
          = ∑ j ∈ Finset.range i, |(b ((n - i) + j)).toRat| := by
      have := sumFromTo_abs_toRat_eq_finset b (n - i) i
      rw [h_upper] at this
      exact this
    rw [h_finset_eq] at h_abs_sft
    have h_bj_bound : ∀ j ∈ Finset.range i,
        |(b ((n - i) + j)).toRat| ≤ C / (2 : Rat) ^ ((n - i) + j) :=
      fun j _ => h_b ((n - i) + j)
    have h_sum_le : ∑ j ∈ Finset.range i, |(b ((n - i) + j)).toRat|
        ≤ ∑ j ∈ Finset.range i, C / (2 : Rat) ^ ((n - i) + j) :=
      Finset.sum_le_sum h_bj_bound
    have hC_nn : (0 : Rat) ≤ C := hC.le
    have h_tail : ∑ j ∈ Finset.range i, |(b ((n - i) + j)).toRat|
        ≤ 2 * C / (2 : Rat) ^ (n - i) :=
      h_sum_le.trans (ratGeomTail_le C hC_nn (n - i) i)
    have h_pow_i_nn : (0 : Rat) ≤ (2 : Rat) ^ i := by positivity
    have h_upper_bound : |(TauRat.sumFromTo b (n - i) n).toRat|
        ≤ 2 * C / (2 : Rat) ^ (n - i) :=
      h_abs_sft.trans h_tail
    have h_abs_nn : (0 : Rat) ≤ |(TauRat.sumFromTo b (n - i) n).toRat| :=
      _root_.abs_nonneg _
    calc |(a i).toRat| * |(TauRat.sumFromTo b (n - i) n).toRat|
        ≤ (C / (2 : Rat) ^ i) * (2 * C / (2 : Rat) ^ (n - i)) :=
          mul_le_mul h_ai h_upper_bound h_abs_nn
            (div_nonneg hC_nn h_pow_i_nn)
      _ = 2 * C ^ 2 / (2 : Rat) ^ n := by
          rw [div_mul_div_comm, ← pow_add]
          have h_sum_eq : i + (n - i) = n := by omega
          rw [h_sum_eq]
          ring
  -- (4) Sum n rows, each ≤ 2C²/2^n, then simplify n·(2C²/2^n) = nC²/2^(n-1)
  have h_const := rat_finset_sum_le_const_mul
    (fun i => |(a i).toRat| * |(TauRat.sum b n).toRat - (TauRat.sum b (n - i)).toRat|)
    (2 * C ^ 2 / (2 : Rat) ^ n) h_row_bound
  refine h_const.trans ?_
  have h_pow_pred_pos : (0 : Rat) < (2 : Rat) ^ (n - 1) := by positivity
  have h_pred : (2 : Rat) ^ n = 2 * (2 : Rat) ^ (n - 1) := rat_pow_pred_eq n hn
  have h_ne : (2 : Rat) ^ (n - 1) ≠ 0 := ne_of_gt h_pow_pred_pos
  have h_eq : (n : Rat) * (2 * C ^ 2 / (2 : Rat) ^ n)
      = (n : Rat) * C ^ 2 / (2 : Rat) ^ (n - 1) := by
    rw [h_pred]
    field_simp
  exact h_eq.le

-- §6.7  Alternating-Mercator Cauchy-product helpers (Wave R12-1a)

/-- Closed-form factor-out: `1/(s+j) ≤ 1/s` for `s ≥ 1, j ≥ 0`;
    factors out `1/s` from the alternating-Mercator-shape sum. -/
private theorem ratMercatorTail_eq
    (C : Rat) (hC : 0 ≤ C) (s : Nat) (hs : 1 ≤ s) (m : Nat) :
    ∑ j ∈ Finset.range m, C / (((s + j : Nat) : Rat) * (2 : Rat) ^ (s + j))
      ≤ (1 / ((s : Rat))) *
        ∑ j ∈ Finset.range m, C / (2 : Rat) ^ (s + j) := by
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum ?_
  intro j _
  have hs_pos : (0 : Rat) < (s : Rat) := by exact_mod_cast hs
  have h_sj_pos : (0 : Rat) < ((s + j : Nat) : Rat) := by
    push_cast; linarith
  have h_pow_pos : (0 : Rat) < (2 : Rat) ^ (s + j) := by positivity
  have h_le_sj : ((s : Rat)) ≤ ((s + j : Nat) : Rat) := by
    push_cast; linarith
  have h_rhs_eq : (1 / (s : Rat)) * (C / (2 : Rat) ^ (s + j))
        = C / ((s : Rat) * (2 : Rat) ^ (s + j)) := by field_simp
  rw [h_rhs_eq]
  have h_denom_lhs_pos : (0 : Rat) < ((s + j : Nat) : Rat) * (2 : Rat) ^ (s + j) := by
    positivity
  have h_denom_rhs_pos : (0 : Rat) < (s : Rat) * (2 : Rat) ^ (s + j) := by
    positivity
  have h_denom_le : (s : Rat) * (2 : Rat) ^ (s + j)
                     ≤ ((s + j : Nat) : Rat) * (2 : Rat) ^ (s + j) :=
    mul_le_mul_of_nonneg_right h_le_sj h_pow_pos.le
  exact div_le_div_of_nonneg_left hC h_denom_rhs_pos h_denom_le

/-- Combined alternating-Mercator tail bound: `Σ C/((s+j)·2^(s+j)) ≤ 2C/(s·2^s)`. -/
private theorem ratMercatorTail_le
    (C : Rat) (hC : 0 ≤ C) (s : Nat) (hs : 1 ≤ s) (m : Nat) :
    ∑ j ∈ Finset.range m, C / (((s + j : Nat) : Rat) * (2 : Rat) ^ (s + j))
      ≤ 2 * C / ((s : Rat) * (2 : Rat) ^ s) := by
  refine (ratMercatorTail_eq C hC s hs m).trans ?_
  have h_geom := ratGeomTail_le C hC s m
  have hs_pos : (0 : Rat) < (s : Rat) := by exact_mod_cast hs
  have h_eq : 2 * C / ((s : Rat) * (2 : Rat) ^ s)
      = (1 / (s : Rat)) * (2 * C / (2 : Rat) ^ s) := by
    field_simp
  rw [h_eq]
  exact mul_le_mul_of_nonneg_left h_geom (by positivity)

/-- Endpoint-product bound: `i·(n-i) ≥ n-1` for `i ∈ [1, n-1], n ≥ 2`.
    Concavity of `i ↦ i·(n-i)` on `[1, n-1]`; minimum value `n-1` at endpoints.
    Proof: lift both sides to `Int` via `zify` with the hypotheses making
    `Nat.cast_sub` rewrites unambiguous, then close with `nlinarith` on the
    factored form `(i-1)·(n-1-i) ≥ 0` (both factors nonneg in the regime). -/
private theorem nat_one_le_endpoint_product
    {i n : Nat} (hi_lo : 1 ≤ i) (hi_hi : i ≤ n - 1) (hn : 2 ≤ n) :
    n - 1 ≤ i * (n - i) := by
  have hi_le_n : i ≤ n := by omega
  have h_n_pos : 1 ≤ n := by omega
  have hni_pos : 1 ≤ n - i := by omega
  zify [hi_le_n, h_n_pos]
  -- Goal: ((n : Int) - 1) ≤ (i : Int) * ((n : Int) - (i : Int))
  -- Use (i - 1) * ((n - 1) - i) ≥ 0 to derive (since i ≥ 1 and i ≤ n-1)
  have hi_int : (1 : Int) ≤ (i : Int) := by exact_mod_cast hi_lo
  have hi_hi_int : (i : Int) ≤ ((n : Int) - 1) := by
    have h_eq : ((n - 1 : Nat) : Int) = (n : Int) - 1 := by omega
    rw [← h_eq]; exact_mod_cast hi_hi
  nlinarith [mul_nonneg (by linarith : (0 : Int) ≤ (i : Int) - 1)
                        (by linarith : (0 : Int) ≤ ((n : Int) - 1) - (i : Int))]

end CauchyConvolution

end Tau.Boundary
