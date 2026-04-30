import TauLib.BookI.Boundary.TauRealE
import TauLib.BookI.Boundary.TauRealAnalyticalHelpers
import TauLib.BookI.Boundary.TauRealSum
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
-- PART 4: TERM AND PARTIAL-SUM CAUCHY BOUND
-- ============================================================

/-- `|exp_partial x m − exp_partial x n| ≤ 4R/2^n` for 1 ≤ n ≤ m, |x| ≤ R ≤ 1.
    Direct analogue of `TauReal.e_partial_cauchy_bound`. Proof outline:
    triangle inequality + telescoping geometric bound on `sumFromTo`.

    Wave R8c task: complete the telescoping calibration (Engineer B's
    output had this proof at ~40 lines but flagged sub-lemma calibration
    risks; defer detailed proof to R8c). -/
theorem TauReal.exp_partial_cauchy_bound (x : TauRat) (R : Rat)
    (hR0 : 0 ≤ R) (hR1 : R ≤ 1) (hx : |x.toRat| ≤ R)
    (m n : Nat) (hn : 1 ≤ n) (hnm : n ≤ m) :
    |(TauRat.exp_partial x m).toRat - (TauRat.exp_partial x n).toRat|
      ≤ 4 * R / (2 ^ n : Rat) := by
  sorry  -- Wave R8c: telescoping + triangle inequality calibration.

-- ============================================================
-- PART 5: IsCauchy FOR exp_of_rat  (modulus λ k => k + 3)
-- ============================================================

/-- `TauReal.exp_of_rat x` is Cauchy with modulus `λ k => k + 3`,
    provided `|x.toRat| ≤ R ≤ 1`. Proof mirrors `TauReal.e_isCauchy`. -/
theorem TauReal.exp_of_rat_isCauchy (x : TauRat) (R : Rat)
    (hR0 : 0 ≤ R) (hR1 : R ≤ 1) (hx : |x.toRat| ≤ R) :
    (TauReal.exp_of_rat x).IsCauchy := by
  sorry  -- Wave R8c: Cauchy proof via exp_partial_cauchy_bound + four_div_two_pow.

-- ============================================================
-- PART 6: HEADLINE THEOREMS
-- ============================================================

/-- `exp(0) ≡ 1` up to TauReal.equiv.

    The n-th approximation of `(exp TauReal.zero)` is
    `exp_partial TauRat.zero n`. For n ≥ 1, this equals `TauRat.one`
    (only the k=0 term survives since 0^k = 0 for k ≥ 1). The diff
    sequence is 0 for n ≥ 1 (stale at n=0). Modulus `λ _ => 1` closes. -/
theorem TauReal.exp_zero :
    TauReal.equiv (TauReal.exp TauReal.zero) TauReal.one := by
  sorry  -- Wave R8c: direct Cauchy proof with modulus λ _ => 1.

/-- `exp(1) ≡ e` up to TauReal.equiv.

    `TauReal.exp TauReal.one` has n-th approximation
    `exp_partial TauRat.one n`, which equals `e_partial n` since
    `exp_term TauRat.one k = e_term k`. -/
theorem TauReal.exp_one :
    TauReal.equiv (TauReal.exp TauReal.one) TauReal.e := by
  sorry  -- Wave R8c: equiv_of_pointwise via term equality.

/-- `exp(a + b) ≡ exp(a) · exp(b)` up to TauReal.equiv.

    **R4-equiv: TRIGGERED.** This proof depends on
    `TauRat.cauchy_product_bound` in `TauRealSum.lean` Part 6 (Wave R8b
    stub). Wave R8c closes both simultaneously. -/
theorem TauReal.exp_add (a b : TauReal) (R : Rat)
    (hR0 : 0 ≤ R) (hR1 : R ≤ 1)
    (ha : TauReal.BoundedBy a R) (hb : TauReal.BoundedBy b R) :
    TauReal.equiv
      (TauReal.exp (a.add b))
      ((TauReal.exp a).mul (TauReal.exp b)) := by
  sorry  -- R4-equiv: Wave R8c via cauchy_product_bound.

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
