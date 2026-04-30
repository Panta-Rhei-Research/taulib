import TauLib.BookI.Boundary.TauRealInv
import Mathlib.Tactic.Ring
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push
import Mathlib.Tactic.FieldSimp

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
-- PART 6: CAUCHY CONVOLUTION  (Wave R8b R4-equiv stub)
--
-- Phase 0.5 design doc §3: ~80 lines for convolution lemma to
-- enable TauRealExp.exp_add (`exp(a+b) ≡ exp(a) · exp(b)`).
--
-- R4-equiv flag: cauchy_product_bound proof requires double-induction
-- on geometric row-sums, which does not collapse to single linarith.
-- Wave R8c will close via dedicated geometric_rowsum_bound (~40 lines).
-- All other Wave R8b theorems are sorry-free; the sorry here
-- propagates to exp_add only.
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

/-- **Cauchy-product bound (Wave R8b R4-equiv stub).**

    If |a_i| ≤ C/2^i and |b_j| ≤ C/2^j for all i, j (with C > 0), then for n ≥ 1:

      |(sum a n).toRat * (sum b n).toRat − (cauchyPStar a b n).toRat| ≤ 4·C²/2^n.

    The bound comes from: the n×n product grid minus the lower-triangular
    Cauchy partial sum = the upper-triangular remainder
    `{(i,j) : i<n, j<n, i+j≥n}`. Each pair contributes ≤ C²/2^(i+j) ≤ C²/2^n.
    Summing n(n-1)/2 such pairs with the geometric row-sum gives the 4·C²/2^n
    bound via n ≤ 2^(n-1).

    **R4-equiv (Wave R8c):** the double-induction formalising the row-sum
    argument does not close with a single `linarith` call. The sorry is
    precisely located here; it is the only gap in `TauRealExp.exp_add`.

    Wave R8c task: write the dedicated `TauRat.geometric_rowsum_bound`
    intermediate lemma (~40 lines) summing `Σ_{j≥n−i} C/2^j` per row,
    then summing those row bounds. -/
theorem TauRat.cauchy_product_bound
    (a b : Nat → TauRat) (C : Rat) (hC : 0 < C)
    (h_a : ∀ i, |(a i).toRat| ≤ C / (2 : Rat) ^ i)
    (h_b : ∀ j, |(b j).toRat| ≤ C / (2 : Rat) ^ j)
    (n : Nat) (hn : 1 ≤ n) :
    |(TauRat.sum a n).toRat * (TauRat.sum b n).toRat
       - (TauRat.cauchyPStar a b n).toRat|
      ≤ 4 * C ^ 2 / (2 : Rat) ^ n := by
  sorry  -- R4-equiv: Wave R8c double-geometric-induction helper.

end Tau.Boundary
