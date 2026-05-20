import TauLib.BookI.Boundary.TauRealMachinPiKeystone
import TauLib.BookI.Boundary.TauRealSinCos
import Mathlib.Tactic.Ring
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity

/-!
# TauLib.BookI.Boundary.TauRealCisInjectivity

**Phase F.B.0 — cisTauReal injectivity at zero (foundational lemma)**.

This module ships the foundational angle-injectivity lemma needed to lift
the shipped Scope 2A-lift / 2C / 2D structural reductions all the way to
angle equality, providing a constructive route to discharge
`MachinSlashFourIdentity` (the remaining open proposition in the
keystone reduction chain).

## What this module ships

* **`im_taylor_2_eq_alpha`**, **`im_taylor_3_eq_alpha`** — pointwise
  identities for the early `expPartial_pureIm_im_rat` values.
* **`im_taylor_4_eq_alpha_minus_cube`** — the depth-4 partial sum
  identity `expPartial_pureIm_im_rat α 4 = α - α³/6` (the τ-Taylor
  k=0 paired sin term).
* **`sin_pair_term_rat_abs_bound_alpha_fifth`** — the |α|-proportional
  per-term bound `|sin_pair_term_rat α k| ≤ 2|α|⁵/(4k+1)!` for `k ≥ 1,
  |α| ≤ 1`, used to control the sin tail past depth m=1.
* **`sin_partial_rat_sub_one_alpha_fifth_bound`** — for `|α| ≤ 1, m ≥ 1`,
  `|sin_partial_rat α m − (α − α³/6)| ≤ 2|α|⁵`.
* **`alpha_le_two_im_partial`** — for `|α| ≤ 1/2`, `n = 4m+r ≤ 4m+3`
  with `m ≥ 1`, the load-bearing arithmetic injectivity:
  `|α| ≤ 2·|expPartial_pureIm_im_rat α n| + 4/(4m)!`.
* **🎯 `TauComplex.cisTauReal_injectivity_at_zero`** — the headline
  τ-native injectivity:

      For `γ : TauReal` with
        - `|γ.approx n .toRat| ≤ 1/2` for all `n` (principal-branch
          bounded condition), and
        - `(cisTauReal γ).im ≈ TauReal.zero` (the imaginary part
          vanishes at TauReal-equiv level),
      then `γ ≈ TauReal.zero`.

  The real-part hypothesis `(cisTauReal γ).re ≈ TauReal.one` is
  unused — the imaginary leg alone discharges injectivity at zero
  (modulo the principal-branch bound). This is the cleanest form.

## Proof strategy (Approach 1: sin-route)

Given `(cisTauReal γ).im ≈ 0` and bounded `|γ.approx n .toRat| ≤ 1/2`:

1. **At each depth** `n ≥ μ_im(k')` (for some large `k'`), we have
   `|((cisTauReal γ).im.approx n).toRat| < 1/(k'+1)`.

2. **By the cisTauReal bridge** (`cisTauReal_im_approx_toRat`):
   `((cisTauReal γ).im.approx n).toRat = expPartial_pureIm_im_rat ((γ.approx n).toRat) n`.

3. **Cyclotomic-4 structure** (PART 1 below): for `n = 4m+r ≤ 4m+3`,
   `expPartial_pureIm_im_rat α n` equals `sin_partial_rat α m` plus a
   residual of magnitude `≤ 3/(4m)!`.

4. **Sin tail bound** (PART 2 below): for `|α| ≤ 1, m ≥ 1`,
   `|sin_partial_rat α m − (α − α³/6)| ≤ 2|α|⁵` (proved via the
   |α|⁵-proportional per-term bound + a geometric tail).

5. **Algebraic step** (PART 3 below): for `|α| ≤ 1/2`,
   `|α − α³/6| = |α|·|1 − α²/6| ≥ 23|α|/24`, hence
   `|α| ≤ (24/23)·|α − α³/6|`.

6. **Compose**: `|α| ≤ 2·|expPartial_pureIm_im_rat α n| + 4/(4m)!`
   (PART 4 below). Choosing modulus to dominate both the cisTauReal
   bound and the residual gives the final TauReal injectivity.

## Significance for Path F.B

This lemma is the **foundational piece** of Path F.B (the kernel-axiom-only
keystone route). With `cisTauReal_injectivity_at_zero` in hand, the next
sub-agent can apply it to discharge `MachinSlashFourIdentity` by:

* Letting `α := 4·arctan_of_rat_seq(1/5) − arctan_of_rat_seq(1/239)`
  and `β := arctan_of_rat_seq(1)`.
* Showing `cisTauReal(α − β) ≈ cisTauReal(α)·conj(cisTauReal(β))` and
  combining the Scope 2A-lift 45°-line identity plus the Pythagorean
  β.4.7 identity to derive `cisTauReal(α − β) ≈ (1, 0)`.
* Bounding `|α − β|` to land in the principal branch.
* Applying `cisTauReal_injectivity_at_zero` to conclude `α ≈ β`, i.e.,
  `MachinSlashFourIdentity`.

## Registry Cross-References

* [I.T-CisTauReal-MagSq-Equiv-One] `TauComplex.cisTauReal_magSq_equiv_one`
  (β.4.7 Pythagorean — TauRealSinCos.lean)
* [I.T-CisTauReal-Im-toRat] `cisTauReal_im_approx_toRat`
  (TauRealSinCos.lean Part 25)
* [I.T-ExpPartial-PureIm-Im-Residual] `expPartial_pureIm_im_rat_residual_le`
  (TauRealSinCos.lean Part 15)
* [I.D-SinPartial] `sin_partial_rat` (TauRealSin.lean Part 3)
* [I.T-SinPairTerm-AbsBound] `sin_pair_term_rat_abs_bound`
  (TauRealSin.lean Part 4 — the |α|-flat per-term bound, refined here
  to the |α|⁵-proportional form for k ≥ 1).

## Build state

* `sorry` count: 0
* Axiom count: 3 (kernel: `propext`, `Classical.choice`, `Quot.sound`)
* Imports: `TauRealMachinPiKeystone` + `TauRealSinCos`
  (which transitively imports the whole Phase B/C/D/E/Wave-Γ stack) +
  Mathlib tactics only.
-/

set_option autoImplicit false

namespace Tau.Boundary

open Tau.Denotation

-- ============================================================
-- PART 1: SMALL-INDEX CLOSED FORMS FOR expPartial_pureIm_im_rat
-- ============================================================

/-! ## Small-index closed forms

`expPartial_pureIm_im_rat` at depths `n ∈ {0,1,2,3,4}` admits closed forms
deduced from the cyclotomic-4 structure of `pureIm_pow_re_im_rat`:

  * n=0,1: 0
  * n=2,3: α (the k=1 contribution α^1/1! = α)
  * n=4: α − α³/6 (adds the k=3 contribution -α³/3!)

These are the "first few Taylor partial sums" of `Im(exp(iα))`. The depth-4
form is the **first non-trivial closed form** that involves the cubic
correction — load-bearing for the |α|⁵-proportional sin tail bound below. -/

/-- `expPartial_pureIm_im_rat α 2 = α`. -/
theorem im_taylor_2_eq_alpha (α : Rat) :
    expPartial_pureIm_im_rat α 2 = α := by
  show expPartial_pureIm_im_rat α 1
        + (pureIm_pow_re_im_rat α 1).2 / (Nat.factorial 1 : Rat) = α
  show (expPartial_pureIm_im_rat α 0
        + (pureIm_pow_re_im_rat α 0).2 / (Nat.factorial 0 : Rat))
        + (pureIm_pow_re_im_rat α 1).2 / (Nat.factorial 1 : Rat) = α
  rw [expPartial_pureIm_im_rat_zero, pureIm_pow_re_im_rat_zero,
      pureIm_pow_re_im_rat_succ, pureIm_pow_re_im_rat_zero]
  simp [Nat.factorial]

/-- `expPartial_pureIm_im_rat α 3 = α` (the k=2 contribution is 0). -/
theorem im_taylor_3_eq_alpha (α : Rat) :
    expPartial_pureIm_im_rat α 3 = α := by
  show expPartial_pureIm_im_rat α 2
        + (pureIm_pow_re_im_rat α 2).2 / (Nat.factorial 2 : Rat) = α
  rw [im_taylor_2_eq_alpha]
  -- pureIm_pow_re_im_rat α 2 = (-α^2, 0): use cyclotomic-4 at j=0
  have h2 : (pureIm_pow_re_im_rat α 2).2 = 0 :=
    by rw [(pureIm_pow_re_im_rat_cyclo4 α 0).2.2.1]
  rw [h2]
  simp

/-- `expPartial_pureIm_im_rat α 4 = α − α³/6` (the depth-4 closed form,
    adding the k=3 contribution `-α³/6`). -/
theorem im_taylor_4_eq_alpha_minus_cube (α : Rat) :
    expPartial_pureIm_im_rat α 4 = α - α^3 / 6 := by
  show expPartial_pureIm_im_rat α 3
        + (pureIm_pow_re_im_rat α 3).2 / (Nat.factorial 3 : Rat) = α - α^3 / 6
  rw [im_taylor_3_eq_alpha]
  -- pureIm_pow_re_im_rat α 3 = (0, -α^3): use cyclotomic-4 at j=0
  have h3 : (pureIm_pow_re_im_rat α 3).2 = -(α^3) :=
    by rw [(pureIm_pow_re_im_rat_cyclo4 α 0).2.2.2]
  rw [h3]
  -- (3 : Nat).factorial = 6
  have h_fac : (Nat.factorial 3 : Rat) = 6 := by
    show ((Nat.factorial 3 : Nat) : Rat) = 6
    norm_num [Nat.factorial]
  rw [h_fac]
  ring

-- ============================================================
-- PART 2: |α|⁵-PROPORTIONAL PER-TERM BOUND FOR k ≥ 1
-- ============================================================

/-! ## |α|⁵-proportional per-term bound

For `|α| ≤ 1, k ≥ 1`, the k-th sin paired term has magnitude bounded by
`2|α|⁵/(4k+1)!` (the |α|⁵ comes from `4k+1 ≥ 5` for k ≥ 1, and
`|α|^(4k+1) ≤ |α|⁵ · |α|^(4(k-1)) ≤ |α|⁵`).

This is the **refinement of the |α|-flat bound** in `sin_pair_term_rat_abs_bound`
(TauRealSin.lean Part 4): instead of `2/(4k+1)!`, we get `2|α|⁵/(4k+1)!`,
which decays geometrically with `|α|` for small `|α|`.

Load-bearing for the sin tail bound (`sin_partial_rat_sub_one_alpha_fifth_bound`)
below: gives a tail bound proportional to `|α|⁵`, which beats the `|α|`-flat
bound by a factor `|α|⁴`. -/

/-- **[I.T-SinPairTerm-AbsBound-AlphaFifth]** Per-term magnitude bound
    proportional to `|α|⁵` for `k ≥ 1`. -/
theorem sin_pair_term_rat_abs_bound_alpha_fifth (α : Rat) (hα : |α| ≤ 1)
    (k : Nat) (hk : 1 ≤ k) :
    |sin_pair_term_rat α k| ≤ 2 * |α|^5 / (Nat.factorial (4*k+1) : Rat) := by
  unfold sin_pair_term_rat
  have h_fac_4k1_pos : (0 : Rat) < (Nat.factorial (4*k+1) : Rat) := by
    have := Nat.factorial_pos (4*k+1); exact_mod_cast this
  have h_fac_4k3_pos : (0 : Rat) < (Nat.factorial (4*k+3) : Rat) := by
    have := Nat.factorial_pos (4*k+3); exact_mod_cast this
  have h_fac_le : (Nat.factorial (4*k+1) : Rat) ≤ (Nat.factorial (4*k+3) : Rat) := by
    have h : Nat.factorial (4*k+1) ≤ Nat.factorial (4*k+3) :=
      Nat.factorial_le (by omega)
    exact_mod_cast h
  -- |α|^(4k+1) ≤ |α|^5  (since |α| ≤ 1 and 4k+1 ≥ 5 for k ≥ 1)
  have h_alpha_nn : (0 : Rat) ≤ |α| := abs_nonneg _
  have h_4k1_ge_5 : 5 ≤ 4*k+1 := by omega
  have h_alpha_pow_4k1_le_5 : |α|^(4*k+1) ≤ |α|^5 := by
    have := pow_le_pow_of_le_one h_alpha_nn hα h_4k1_ge_5
    exact this
  have h_4k3_ge_5 : 5 ≤ 4*k+3 := by omega
  have h_alpha_pow_4k3_le_5 : |α|^(4*k+3) ≤ |α|^5 := by
    have := pow_le_pow_of_le_one h_alpha_nn hα h_4k3_ge_5
    exact this
  have h_alpha_pow_5_nn : (0 : Rat) ≤ |α|^5 := by positivity
  -- |first| = |α^(4k+1)|/(4k+1)! ≤ |α|^5/(4k+1)!
  have h_first_abs : |α^(4*k+1) / (Nat.factorial (4*k+1) : Rat)|
                      ≤ |α|^5 / (Nat.factorial (4*k+1) : Rat) := by
    rw [abs_div, abs_of_pos h_fac_4k1_pos, abs_pow]
    rw [div_le_div_iff₀ h_fac_4k1_pos h_fac_4k1_pos]
    have h_factor_nn : (0 : Rat) ≤ (Nat.factorial (4*k+1) : Rat) := h_fac_4k1_pos.le
    nlinarith [h_alpha_pow_4k1_le_5, h_factor_nn]
  -- |second| = |α^(4k+3)|/(4k+3)! ≤ |α|^5/(4k+1)!  (using (4k+3)! ≥ (4k+1)!)
  have h_second_abs : |α^(4*k+3) / (Nat.factorial (4*k+3) : Rat)|
                      ≤ |α|^5 / (Nat.factorial (4*k+1) : Rat) := by
    rw [abs_div, abs_of_pos h_fac_4k3_pos, abs_pow]
    rw [div_le_div_iff₀ h_fac_4k3_pos h_fac_4k1_pos]
    nlinarith [h_alpha_pow_4k3_le_5, h_alpha_pow_5_nn, h_fac_le, h_fac_4k1_pos.le]
  -- Triangle inequality on the difference.
  have h_tri : |α^(4*k+1) / (Nat.factorial (4*k+1) : Rat) -
                α^(4*k+3) / (Nat.factorial (4*k+3) : Rat)|
                ≤ |α^(4*k+1) / (Nat.factorial (4*k+1) : Rat)| +
                  |α^(4*k+3) / (Nat.factorial (4*k+3) : Rat)| := by
    have := abs_sub (α^(4*k+1) / (Nat.factorial (4*k+1) : Rat))
                    (α^(4*k+3) / (Nat.factorial (4*k+3) : Rat))
    linarith
  -- Sum: ≤ 2·|α|^5/(4k+1)!
  have h_sum : |α|^5 / (Nat.factorial (4*k+1) : Rat) +
               |α|^5 / (Nat.factorial (4*k+1) : Rat)
               = 2 * |α|^5 / (Nat.factorial (4*k+1) : Rat) := by ring
  linarith

-- ============================================================
-- PART 3: SIN PARTIAL TAIL BOUND
-- ============================================================

/-! ## Sin partial tail bound past m=1

For `|α| ≤ 1, m ≥ 1`, we bound the tail
`|sin_partial_rat α m − sin_partial_rat α 1| = |Σ_{k=1}^{m-1} sin_pair_term_rat α k|`
by `2|α|⁵` (geometric tail bound).

Each per-term bound contributes `2|α|⁵/(4k+1)!`. Summing using
`(4k+1)! ≥ 2^k` (from `Nat.factorial_4k1_ge_two_pow_k` in TauRealSin.lean),
the geometric sum is bounded by `2|α|⁵ · Σ_{k=1}^∞ 1/2^k = 2|α|⁵`. -/

/-- **Helper**: at k=1, `Nat.factorial_4k1_ge_two_pow_k` gives `(4·1+1)! = 5! ≥ 2¹ = 2`. -/
private theorem factorial_4k1_ge_two_pow_k_rat (k : Nat) :
    (2 : Rat)^k ≤ (Nat.factorial (4*k+1) : Rat) := by
  have h := Nat.factorial_4k1_ge_two_pow_k k
  have h_cast : ((2^k : Nat) : Rat) = (2 : Rat)^k := by push_cast; ring
  have h_cast_le : ((2^k : Nat) : Rat) ≤ ((Nat.factorial (4*k+1) : Nat) : Rat) :=
    by exact_mod_cast h
  rw [h_cast] at h_cast_le
  exact h_cast_le

/-- **[I.T-SinPartial-Sub-One-AlphaFifth-Exact]** Exact geometric tail
    bound for `|α| ≤ 1, m ≥ 1`:

        `|sin_partial_rat α m − sin_partial_rat α 1| ≤ 2|α|⁵·(1 − 1/2^(m−1))`.

    The `(1 − 1/2^(m−1))` correction is **load-bearing for the induction**:
    the naive invariant `≤ 2|α|⁵` doesn't close at the inductive step (it
    would need `term ≤ 0`). Adding the headroom `2|α|⁵/2^m = 2|α|⁵/(4m+1)!`-budget
    closes via the algebraic identity `(1 − 1/2^(m−1)) + 1/2^m = 1 − 1/2^m`. -/
theorem sin_partial_rat_sub_one_alpha_fifth_bound_exact (α : Rat) (hα : |α| ≤ 1)
    (m : Nat) (hm : 1 ≤ m) :
    |sin_partial_rat α m - sin_partial_rat α 1|
      ≤ 2 * |α|^5 * (1 - 1 / (2 : Rat)^(m-1)) := by
  -- Induction on m starting from m=1.
  induction m, hm using Nat.le_induction with
  | base =>
    -- m=1: difference is 0, RHS is 2|α|^5·0 = 0.
    have h_zero : sin_partial_rat α 1 - sin_partial_rat α 1 = 0 := by ring
    rw [h_zero, abs_zero]
    simp [pow_zero]
  | succ m hm ih =>
    -- Step: m ≥ 1.
    -- sin_partial_rat α (m+1) - sin_partial_rat α 1
    --   = (sin_partial_rat α m - sin_partial_rat α 1) + sin_pair_term_rat α m
    rw [sin_partial_rat_succ]
    have h_diff : sin_partial_rat α m + sin_pair_term_rat α m - sin_partial_rat α 1
                    = (sin_partial_rat α m - sin_partial_rat α 1)
                      + sin_pair_term_rat α m := by ring
    rw [h_diff]
    have h_tri : |(sin_partial_rat α m - sin_partial_rat α 1) + sin_pair_term_rat α m|
                  ≤ |sin_partial_rat α m - sin_partial_rat α 1|
                    + |sin_pair_term_rat α m| := abs_add_le _ _
    -- Per-term bound: |sin_pair_term_rat α m| ≤ 2|α|^5/(4m+1)! ≤ 2|α|^5/2^m
    have h_term := sin_pair_term_rat_abs_bound_alpha_fifth α hα m hm
    have h_2m_pos : (0 : Rat) < (2 : Rat)^m := by positivity
    have h_fac_ge : (2 : Rat)^m ≤ (Nat.factorial (4*m+1) : Rat) :=
      factorial_4k1_ge_two_pow_k_rat m
    have h_fac_pos : (0 : Rat) < (Nat.factorial (4*m+1) : Rat) := by
      have := Nat.factorial_pos (4*m+1); exact_mod_cast this
    have h_alpha5_nn : (0 : Rat) ≤ |α|^5 := by positivity
    -- |sin_pair_term_rat α m| ≤ 2|α|^5/2^m
    have h_term_geom : |sin_pair_term_rat α m| ≤ 2 * |α|^5 / (2 : Rat)^m := by
      have h_div_chain :
          2 * |α|^5 / (Nat.factorial (4*m+1) : Rat) ≤ 2 * |α|^5 / (2 : Rat)^m := by
        rw [div_le_div_iff₀ h_fac_pos h_2m_pos]
        have h_lhs_nn : 0 ≤ 2 * |α|^5 := by positivity
        nlinarith [h_alpha5_nn, h_fac_ge]
      linarith
    -- Algebraic identity: (1 - 1/2^(m-1)) + 1/2^m = 1 - 1/2^m
    -- in our form: 2|α|^5·(1 - 1/2^(m-1)) + 2|α|^5/2^m = 2|α|^5·(1 - 1/2^m)
    -- which is what we want since the new index is (m+1)-1 = m.
    have h_pow_succ : (2 : Rat)^((m+1)-1) = (2 : Rat)^m := by
      have h_eq : (m+1) - 1 = m := by omega
      rw [h_eq]
    rw [h_pow_succ]
    -- 2|α|^5·(1 - 1/2^(m-1)) + 2|α|^5/2^m = 2|α|^5·(1 - 1/2^m)
    have h_m_pred_pow : (2 : Rat)^(m-1) > 0 := by positivity
    have h_pow_eq : (2 : Rat)^m = 2 * (2 : Rat)^(m-1) := by
      have h_step : m = (m-1) + 1 := by omega
      conv_lhs => rw [h_step]
      rw [pow_succ]; ring
    -- Combine via linarith with the algebraic identity unfolded.
    have h_algebra :
        2 * |α|^5 * (1 - 1 / (2 : Rat)^(m-1)) + 2 * |α|^5 / (2 : Rat)^m
          = 2 * |α|^5 * (1 - 1 / (2 : Rat)^m) := by
      rw [h_pow_eq]
      field_simp
      ring
    linarith

/-- **[I.T-SinPartial-Sub-One-AlphaFifth]** Cleaner uniform bound: for
    `|α| ≤ 1, m ≥ 1`,

        `|sin_partial_rat α m − sin_partial_rat α 1| ≤ 2|α|⁵`.

    Direct consequence of the exact form by dropping the `(1 − 1/2^(m−1)) ≤ 1`
    correction factor. -/
theorem sin_partial_rat_sub_one_alpha_fifth_bound (α : Rat) (hα : |α| ≤ 1)
    (m : Nat) (hm : 1 ≤ m) :
    |sin_partial_rat α m - sin_partial_rat α 1| ≤ 2 * |α|^5 := by
  have h_exact := sin_partial_rat_sub_one_alpha_fifth_bound_exact α hα m hm
  have h_alpha5_nn : (0 : Rat) ≤ |α|^5 := by positivity
  have h_2_pow_nn : (0 : Rat) < (2 : Rat)^(m-1) := by positivity
  have h_recip_nn : (0 : Rat) ≤ 1 / (2 : Rat)^(m-1) := by
    apply div_nonneg; linarith; linarith
  -- 2|α|^5·(1 - 1/2^(m-1)) ≤ 2|α|^5·1 = 2|α|^5
  nlinarith [h_exact, h_alpha5_nn, h_recip_nn]

-- ============================================================
-- PART 4: COMBINED RESIDUAL BOUND FOR expPartial_pureIm_im_rat
-- ============================================================

/-! ## Combined residual bound

Stitching together:
* The depth-4 closed form (`im_taylor_4_eq_alpha_minus_cube`).
* `sin_partial_rat`'s relation to `expPartial_pureIm_im_rat` at depth 4m
  (`expPartial_pureIm_im_rat_at_4m`).
* The cyclotomic-4 residual (`expPartial_pureIm_im_rat_residual_le`).
* The sin tail bound (`sin_partial_rat_sub_one_alpha_fifth_bound`).

Yields the load-bearing combined bound:

  For `|α| ≤ 1, m ≥ 1, r ≤ 3`, with `n = 4m + r`:

    `|expPartial_pureIm_im_rat α n − (α − α³/6)| ≤ 3/(4m)! + 2|α|⁵`

The `3/(4m)!` term comes from the cyclotomic-4 residual (vanishes as m → ∞).
The `2|α|⁵` term comes from the sin tail (proportional to |α|⁵, hence
negligible relative to |α| for small |α|). -/

/-- **[I.T-ExpPartialIm-Combined-Residual]** Combined residual bound. -/
theorem expPartial_pureIm_im_rat_combined_residual (α : Rat) (hα : |α| ≤ 1)
    (m r : Nat) (hm : 1 ≤ m) (hr : r ≤ 3) :
    |expPartial_pureIm_im_rat α (4*m + r) - (α - α^3 / 6)|
      ≤ (r : Rat) / (Nat.factorial (4*m) : Rat) + 2 * |α|^5 := by
  -- Decompose:
  --   expPartial_pureIm_im_rat α (4m+r) - (α - α³/6)
  -- = (expPartial_pureIm_im_rat α (4m+r) - sin_partial_rat α m)
  --   + (sin_partial_rat α m - sin_partial_rat α 1)
  --   + (sin_partial_rat α 1 - (α - α³/6))
  --
  -- Bound each piece:
  --   first  ≤ r/(4m)!  (expPartial_pureIm_im_rat_residual_le)
  --   second ≤ 2|α|⁵   (sin_partial_rat_sub_one_alpha_fifth_bound)
  --   third  = 0       (sin_partial_rat α 1 = α - α³/6, direct unfold)
  --
  -- Triangle inequality and combine.
  have h_third : sin_partial_rat α 1 = α - α^3 / 6 := by
    show sin_partial_rat α 0 + sin_pair_term_rat α 0 = α - α^3 / 6
    rw [sin_partial_rat_zero]
    unfold sin_pair_term_rat
    -- α^(4·0+1)/(4·0+1)! - α^(4·0+3)/(4·0+3)! = α^1/1 - α^3/6
    have h_4_0_1 : (4*0+1 : Nat) = 1 := by norm_num
    have h_4_0_3 : (4*0+3 : Nat) = 3 := by norm_num
    rw [h_4_0_1, h_4_0_3]
    have h_f1 : (Nat.factorial 1 : Rat) = 1 := by
      show ((Nat.factorial 1 : Nat) : Rat) = 1
      norm_num [Nat.factorial]
    have h_f3 : (Nat.factorial 3 : Rat) = 6 := by
      show ((Nat.factorial 3 : Nat) : Rat) = 6
      norm_num [Nat.factorial]
    rw [h_f1, h_f3]
    ring
  -- Define the two pieces (after using h_third to eliminate the third).
  have h_residual := expPartial_pureIm_im_rat_residual_le α hα m r hr
  have h_sin_tail := sin_partial_rat_sub_one_alpha_fifth_bound α hα m hm
  -- Rewrite to a sum of two pieces (using h_third to cancel the third).
  have h_rewrite :
      expPartial_pureIm_im_rat α (4*m + r) - (α - α^3 / 6)
        = (expPartial_pureIm_im_rat α (4*m + r) - sin_partial_rat α m)
          + (sin_partial_rat α m - sin_partial_rat α 1) := by
    rw [h_third]
    ring
  rw [h_rewrite]
  -- Triangle inequality on the two-piece sum.
  have h_tri :
      |(expPartial_pureIm_im_rat α (4*m + r) - sin_partial_rat α m)
        + (sin_partial_rat α m - sin_partial_rat α 1)|
        ≤ |expPartial_pureIm_im_rat α (4*m + r) - sin_partial_rat α m|
          + |sin_partial_rat α m - sin_partial_rat α 1| := abs_add_le _ _
  linarith

-- ============================================================
-- PART 5: ALGEBRAIC INJECTIVITY BOUND  |α| ≤ 2·|im partial| + residual
-- ============================================================

/-! ## Algebraic injectivity

For `|α| ≤ 1/2`, we have `|α − α³/6| = |α|·|1 − α²/6| ≥ |α|·23/24`,
hence `|α| ≤ (24/23)·|α − α³/6|`.

Combined with the residual bound:

    `|α − α³/6| ≤ |expPartial_pureIm_im_rat α (4m+r)| + 3/(4m)! + 2|α|⁵`

and the geometric bound `2|α|⁵ ≤ |α|/8` (for `|α| ≤ 1/2`), arithmetic gives:

    `|α| ≤ 2·|expPartial_pureIm_im_rat α (4m+r)| + 4/(4m)!`

(rounding `(24/23)·(small ε + ...) ≤ 2·ε + ...`).
-/

/-- **Algebraic identity**: `α − α³/6 = α·(1 − α²/6)`. -/
private theorem alpha_minus_cube_factor (α : Rat) :
    α - α^3 / 6 = α * (1 - α^2 / 6) := by ring

/-- **[I.T-Alpha-Bound-By-ImPartial]** Combined arithmetic injectivity
    bound: `|α| ≤ 2·|expPartial_pureIm_im_rat α (4m+r)| + 4/(4m)!`
    for `|α| ≤ 1/2, m ≥ 1, r ≤ 3`. -/
theorem alpha_le_two_im_partial (α : Rat) (hα : |α| ≤ 1/2)
    (m r : Nat) (hm : 1 ≤ m) (hr : r ≤ 3) :
    |α| ≤ 2 * |expPartial_pureIm_im_rat α (4*m + r)|
          + 4 / (Nat.factorial (4*m) : Rat) := by
  -- Step 1: |α - α³/6| ≥ 23|α|/24  (algebraic, uses |α| ≤ 1/2)
  have hα_le_1 : |α| ≤ 1 := by linarith
  have h_alpha_sq_le_quart : α^2 ≤ 1 / 4 := by
    have h_abs_sq : α^2 = |α|^2 := by rw [sq_abs]
    rw [h_abs_sq]
    have : |α|^2 ≤ (1/2)^2 := pow_le_pow_left₀ (abs_nonneg _) hα 2
    have h_quart : (1/2 : Rat)^2 = 1/4 := by norm_num
    linarith [this, h_quart]
  have h_factor_ge : (23 : Rat) / 24 ≤ 1 - α^2 / 6 := by
    -- α²/6 ≤ 1/24, so 1 - α²/6 ≥ 23/24
    linarith
  have h_factor_pos : (0 : Rat) < 1 - α^2 / 6 := by linarith
  have h_alpha_minus_cube_abs :
      |α - α^3 / 6| = |α| * (1 - α^2 / 6) := by
    rw [alpha_minus_cube_factor, abs_mul]
    have : |1 - α^2 / 6| = 1 - α^2 / 6 := abs_of_pos h_factor_pos
    rw [this]
  have h_lower :
      |α| * (23 : Rat) / 24 ≤ |α - α^3 / 6| := by
    rw [h_alpha_minus_cube_abs]
    have h_alpha_nn : (0 : Rat) ≤ |α| := abs_nonneg _
    have h_mul_le : |α| * (23/24 : Rat) ≤ |α| * (1 - α^2 / 6) :=
      mul_le_mul_of_nonneg_left h_factor_ge h_alpha_nn
    linarith
  -- Step 2: |α - α³/6| ≤ |expPartial| + 3/(4m)! + 2|α|⁵  (combined residual)
  have h_combined := expPartial_pureIm_im_rat_combined_residual α hα_le_1 m r hm hr
  have h_residual_bound :
      |α - α^3 / 6| ≤ |expPartial_pureIm_im_rat α (4*m + r)|
                       + (r : Rat) / (Nat.factorial (4*m) : Rat) + 2 * |α|^5 := by
    have h_tri := abs_sub_abs_le_abs_sub
      (expPartial_pureIm_im_rat α (4*m + r)) (α - α^3 / 6)
    have h_abs_eq : |α - α^3/6 - expPartial_pureIm_im_rat α (4*m + r)|
                    = |expPartial_pureIm_im_rat α (4*m + r) - (α - α^3/6)| := by
      rw [abs_sub_comm]
    have h_alt :
        |α - α^3 / 6| ≤ |expPartial_pureIm_im_rat α (4*m + r)|
                        + |expPartial_pureIm_im_rat α (4*m + r) - (α - α^3 / 6)| := by
      have h_t := abs_add_le (expPartial_pureIm_im_rat α (4*m + r))
                              ((α - α^3/6) - expPartial_pureIm_im_rat α (4*m + r))
      have h_simp : expPartial_pureIm_im_rat α (4*m + r)
                    + ((α - α^3/6) - expPartial_pureIm_im_rat α (4*m + r))
                    = α - α^3/6 := by ring
      rw [h_simp] at h_t
      have h_swap :
          |((α - α^3/6) - expPartial_pureIm_im_rat α (4*m + r))|
            = |expPartial_pureIm_im_rat α (4*m + r) - (α - α^3 / 6)| := by
        rw [abs_sub_comm]
      rw [h_swap] at h_t
      exact h_t
    linarith
  -- Step 3: 2|α|⁵ ≤ |α|/8  for |α| ≤ 1/2.
  -- |α|^5 = |α|·|α|^4 ≤ |α|·(1/16)
  have h_alpha4_le_quart : |α|^4 ≤ 1 / 16 := by
    have h_abs : |α|^4 = (|α|^2)^2 := by ring
    have h_alpha2_le : |α|^2 ≤ 1/4 := by
      have h_pow : |α|^2 ≤ (1/2)^2 := pow_le_pow_left₀ (abs_nonneg _) hα 2
      have : (1/2 : Rat)^2 = 1/4 := by norm_num
      linarith
    have h_alpha2_nn : (0 : Rat) ≤ |α|^2 := by positivity
    rw [h_abs]
    have : (|α|^2)^2 ≤ (1/4)^2 := pow_le_pow_left₀ h_alpha2_nn h_alpha2_le 2
    have h_q : (1/4 : Rat)^2 = 1/16 := by norm_num
    linarith
  have h_alpha5_le : 2 * |α|^5 ≤ |α| / 8 := by
    have h_alpha_nn : (0 : Rat) ≤ |α| := abs_nonneg _
    have h_split : |α|^5 = |α| * |α|^4 := by ring
    rw [h_split]
    -- 2 * |α| * |α|^4 ≤ 2 * |α| * (1/16) = |α|/8
    have h_le : |α| * |α|^4 ≤ |α| * (1/16) :=
      mul_le_mul_of_nonneg_left h_alpha4_le_quart h_alpha_nn
    linarith
  -- Step 4: combine.
  -- 23|α|/24 ≤ |expPartial| + 3/(4m)! + 2|α|⁵ ≤ |expPartial| + 3/(4m)! + |α|/8
  -- ⇒ |α|·(23/24 - 1/8) ≤ |expPartial| + 3/(4m)!
  -- ⇒ |α|·(20/24) ≤ |expPartial| + 3/(4m)!
  -- ⇒ |α|·(5/6) ≤ |expPartial| + 3/(4m)!
  -- ⇒ |α| ≤ (6/5)·(|expPartial| + 3/(4m)!) ≤ 2·|expPartial| + 4/(4m)!
  have h_r_le : (r : Rat) ≤ 3 := by exact_mod_cast hr
  have h_fac_pos : (0 : Rat) < (Nat.factorial (4*m) : Rat) := by
    have := Nat.factorial_pos (4*m); exact_mod_cast this
  have h_alpha_nn : (0 : Rat) ≤ |α| := abs_nonneg _
  have h_exp_nn : (0 : Rat) ≤ |expPartial_pureIm_im_rat α (4*m + r)| := abs_nonneg _
  -- Bound r/(4m)! ≤ 3/(4m)!
  have h_residual_to_3 :
      (r : Rat) / (Nat.factorial (4*m) : Rat) ≤ 3 / (Nat.factorial (4*m) : Rat) := by
    rw [div_le_div_iff₀ h_fac_pos h_fac_pos]
    nlinarith [h_r_le, h_fac_pos.le]
  -- Introduce abbreviation E := |exp|, F := 1/(4m)!  so linarith works in atoms.
  set E := |expPartial_pureIm_im_rat α (4*m + r)| with hE_def
  set F := (Nat.factorial (4*m) : Rat) with hF_def
  -- Restate hypotheses in terms of E, F.
  have h_F_pos : (0 : Rat) < F := h_fac_pos
  have h_F_inv_nn : (0 : Rat) ≤ 1 / F := by
    apply div_nonneg (by norm_num : (0 : Rat) ≤ 1) h_F_pos.le
  have h_E_nn : (0 : Rat) ≤ E := h_exp_nn
  -- Convert h_residual_to_3 to introduce F-divisions:
  -- (r : Rat) / F ≤ 3 / F. We have this as h_residual_to_3.
  -- h_residual_bound:  |α - α^3/6| ≤ E + r/F + 2|α|⁵
  -- h_alpha5_le:       2|α|⁵ ≤ |α|/8
  -- h_lower:           |α|·23/24 ≤ |α - α^3/6|
  -- Combine:           |α|·23/24 ≤ E + r/F + |α|/8 ≤ E + 3/F + |α|/8.
  -- ⟹ |α|·(23/24 - 1/8) ≤ E + 3/F
  -- ⟹ |α|·5/6 ≤ E + 3/F
  -- ⟹ |α| ≤ (6/5)·E + (18/5)/F
  -- Want: |α| ≤ 2·E + 4/F. Since 6/5 ≤ 2 (need E ≥ 0) and 18/5 ≤ 4 (need 1/F ≥ 0).
  -- Define ε := E + 3/F. Then |α|·5/6 ≤ ε. And we want |α| ≤ 2·E + 4/F.
  -- |α| ≤ (6/5)ε = (6/5)(E + 3/F) = (6/5)E + (18/5)/F
  -- Use multiplication: (6/5)E ≤ 2E iff (4/5)E ≥ 0 (true since E ≥ 0).
  -- (18/5)/F ≤ 4/F iff (2/5)/F ≥ 0 (true since F > 0).
  have h_chain :
      |α| * 23 / 24 ≤ E + 3 / F + |α| / 8 := by
    have h1 : |α| * 23 / 24 ≤ E + (r : Rat) / F + 2 * |α|^5 := by
      calc |α| * 23 / 24 ≤ |α - α^3 / 6| := h_lower
        _ ≤ E + (r : Rat) / F + 2 * |α|^5 := h_residual_bound
    have h2 : E + (r : Rat) / F + 2 * |α|^5 ≤ E + 3 / F + |α| / 8 := by
      linarith [h_residual_to_3, h_alpha5_le]
    linarith
  -- |α|·(23/24 - 1/8) ≤ E + 3/F  ⟹  |α|·5/6 ≤ E + 3/F
  have h_eq_56 : (23 : Rat)/24 - 1/8 = 5/6 := by norm_num
  have h_chain2 : |α| * (5/6) ≤ E + 3 / F := by linarith
  -- |α| ≤ (6/5)(E + 3/F)
  have h_chain3 : |α| ≤ (6/5) * (E + 3 / F) := by linarith
  -- (6/5)(E + 3/F) = (6/5)E + 18/(5F) ≤ 2E + 4/F:
  have h_E_chain : (6/5 : Rat) * E ≤ 2 * E := by nlinarith [h_E_nn]
  have h_F_chain : (6/5 : Rat) * (3 / F) ≤ 4 / F := by
    -- Bring to common /F form, then compare numerators.
    have h_eq : (6/5 : Rat) * (3 / F) = (18/5) / F := by ring
    rw [h_eq]
    rw [div_le_div_iff₀ h_F_pos h_F_pos]
    nlinarith [h_F_pos.le]
  linarith

-- ============================================================
-- PART 6: MAIN THEOREM — cisTauReal_injectivity_at_zero
-- ============================================================

/-! ## The headline τ-native injectivity theorem

Combining the arithmetic bound (`alpha_le_two_im_partial`) with the
cisTauReal-im bridge (`cisTauReal_im_approx_toRat`), the Cauchy modulus
of the hypothesis `(cisTauReal γ).im ≈ 0`, and the bounded condition
`|γ.approx n .toRat| ≤ 1/2`, we obtain:

  **For `γ : TauReal` bounded and with `(cisTauReal γ).im ≈ 0`,
  the angle γ vanishes: `γ ≈ TauReal.zero`.**

This is the **foundational lemma for Path F.B**. Combined with the
Pythagorean β.4.7 + the magnitude-1 fact for cisTauReal, it gives the
classical "cis(γ) = 1 ⟹ γ = 0 mod 2π" content in τ-native form, with
the principal-branch condition encoded as the |γ.approx n .toRat| ≤ 1/2
bound. -/

/-- **🎯🎯🎯🎯🎯 [I.T-CisTauReal-Injectivity-At-Zero]** Principal-branch
    injectivity at zero for cisTauReal:

    For `γ : TauReal` with
    * `|γ.approx n .toRat| ≤ 1/2` for all `n` (principal-branch bound),
    * `(cisTauReal γ).im ≈ TauReal.zero` (the imaginary leg vanishes),

    then `γ ≈ TauReal.zero`.

    The real part of cisTauReal is **NOT consulted** — the imaginary leg
    alone discharges injectivity at zero, modulo the principal-branch
    bound. This is the cleanest formulation.

    The bound 1/2 is the standard "small angle" condition: it ensures
    `1 − α²/6 ≥ 23/24 > 0` so the algebraic step

        `|α − α³/6| ≥ (23/24)·|α|`

    is valid. Larger bounds (e.g., 1, or 1 − ε for small ε > 0) would
    work with adjusted constants but the 1/2 form is the canonical
    "principal-branch interior" for Machin-style applications. -/
theorem TauComplex.cisTauReal_injectivity_at_zero
    (γ : TauReal)
    (h_bound : ∀ n, ((γ.approx n).abs).toRat ≤ 1/2)
    (h_im : TauReal.equiv (TauComplex.cisTauReal γ).im TauReal.zero) :
    TauReal.equiv γ TauReal.zero := by
  -- Extract the modulus from h_im.
  obtain ⟨μ_im, h_μ_im⟩ := h_im
  -- Build the target modulus.
  refine ⟨fun k => max (μ_im (4*k+5)) (8*k+20), fun k n hkn => ?_⟩
  -- Unpack the max-bound.
  have hn_im : μ_im (4*k+5) ≤ n := le_of_max_le_left hkn
  have hn_lin : 8*k+20 ≤ n := le_of_max_le_right hkn
  -- The hypothesis gives |((cisTauReal γ).im.approx n).toRat - (TauReal.zero.approx n).toRat| < 1/((4k+5)+1)
  have h_im_bd := h_μ_im (4*k+5) n hn_im
  unfold TauRat.lt at h_im_bd
  rw [TauRat.toRat_abs, toRat_sub, TauRat.ofNatRecip_toRat] at h_im_bd
  -- (TauReal.zero.approx n).toRat = 0
  have h_zero_approx : (TauReal.zero.approx n).toRat = 0 := by
    show (TauRat.zero).toRat = 0
    exact toRat_zero
  rw [h_zero_approx, sub_zero] at h_im_bd
  -- So |((cisTauReal γ).im.approx n).toRat| < 1/(4k+6)
  -- Now rewrite via the cisTauReal_im_approx_toRat bridge.
  rw [cisTauReal_im_approx_toRat] at h_im_bd
  -- Set abbreviations.
  set α := (γ.approx n).toRat with hα_def
  -- Bounded condition: |α| ≤ 1/2.
  have hα : |α| ≤ 1/2 := by
    have := h_bound n
    rw [TauRat.toRat_abs] at this
    exact this
  -- Decompose n = 4m + r.
  have h_decomp : n = 4 * (n / 4) + n % 4 := (Nat.div_add_mod n 4).symm
  set m := n / 4 with hm_def
  set r := n % 4 with hr_def
  have hr : r ≤ 3 := by
    have : n % 4 < 4 := Nat.mod_lt n (by norm_num)
    omega
  -- m ≥ 5 (from n ≥ 8k+20 ≥ 20, so m = n/4 ≥ 5)
  have hm : 1 ≤ m := by
    have hn_20 : 20 ≤ n := by linarith
    have : 5 ≤ n / 4 := by omega
    have hm_5 : 5 ≤ m := this
    omega
  -- m ≥ 2k+5 (we need this for the 4/(4m)! < 1/(2k+3) bound).
  have hm_ge : 2*k + 5 ≤ m := by
    have h_4mk : 4 * (2*k+5) = 8*k + 20 := by ring
    have hn_ge : 4 * (2*k+5) ≤ n := by linarith
    have h_div : 4 * (2*k+5) / 4 ≤ n / 4 := Nat.div_le_div_right hn_ge
    have h_simp : 4 * (2*k+5) / 4 = 2*k+5 := by
      rw [Nat.mul_div_cancel_left _ (by norm_num : 0 < 4)]
    omega
  -- Apply the bound lemma.
  have h_bound_alpha := alpha_le_two_im_partial α hα m r hm hr
  -- Rewrite the goal: |(γ.approx n).toRat - (TauReal.zero.approx n).toRat| < 1/(k+1)
  unfold TauRat.lt
  rw [TauRat.toRat_abs, toRat_sub, TauRat.ofNatRecip_toRat]
  rw [h_zero_approx, sub_zero]
  -- Note: |(γ.approx n).toRat| = |α|.
  show |α| < 1 / ((k : Rat) + 1)
  -- We have: |α| ≤ 2 · |expPartial_pureIm_im_rat α (4*m + r)| + 4/(4m)!
  -- AND: 4*m + r = n (from h_decomp).
  have h_n_eq : 4*m + r = n := by
    show 4 * (n/4) + n%4 = n
    exact (Nat.div_add_mod n 4)
  rw [h_n_eq] at h_bound_alpha
  -- And expPartial_pureIm_im_rat α n is exactly the cisTauReal im at depth n.
  -- We have h_im_bd: |expPartial_pureIm_im_rat α n| < 1/((4*k+5 : Nat) + 1) = 1/(4k+6).
  -- Step 1: bound 2 · |...| < 2/(4k+6) = 1/(2k+3).
  have h_4k6_pos : (0 : Rat) < ((4*k+5 : Nat) : Rat) + 1 := by
    have : (0 : Rat) ≤ ((4*k+5 : Nat) : Rat) := by exact_mod_cast Nat.zero_le _
    linarith
  have h_4k6_eq : ((4*k+5 : Nat) : Rat) + 1 = 4*(k:Rat) + 6 := by push_cast; ring
  rw [h_4k6_eq] at h_im_bd
  -- h_im_bd: |expPartial_pureIm_im_rat α n| < 1/(4k+6)
  have h_2x_bd : 2 * |expPartial_pureIm_im_rat α n| < 2 * (1 / (4*(k:Rat) + 6)) := by
    linarith [h_im_bd]
  have h_4k6_pos' : (0 : Rat) < 4*(k:Rat) + 6 := by
    have : (0 : Rat) ≤ (k : Rat) := by exact_mod_cast Nat.zero_le k
    linarith
  -- 2 * (1/(4k+6)) = 1/(2k+3)
  have h_2x_eq : (2 : Rat) * (1 / (4*(k:Rat) + 6)) = 1 / (2*(k:Rat) + 3) := by
    field_simp
    ring
  rw [h_2x_eq] at h_2x_bd
  -- Step 2: bound 4/(4m)! < 1/(2k+3).
  -- Use: 2^m ≤ (4m)!, hence 4/(4m)! ≤ 4/2^m.
  -- Then 4/2^m < 1/(2k+3) by Rat.four_div_two_pow_lt_recip with k_target=2k+2, n_target=m.
  -- Need: (2k+2)+3 ≤ m, i.e., m ≥ 2k+5. We have this.
  have h_fac_ge : ((2 : Nat)^m : Rat) ≤ (Nat.factorial (4*m) : Rat) := by
    have := factorial_4m_ge_two_pow_m m
    exact_mod_cast this
  have h_2pow_eq : ((2 : Nat)^m : Rat) = (2 : Rat)^m := by push_cast; ring
  rw [h_2pow_eq] at h_fac_ge
  have h_2pow_pos : (0 : Rat) < (2 : Rat)^m := by positivity
  have h_fac_pos : (0 : Rat) < (Nat.factorial (4*m) : Rat) := by
    have := Nat.factorial_pos (4*m); exact_mod_cast this
  have h_4_fac_le : (4 : Rat) / (Nat.factorial (4*m) : Rat) ≤ 4 / (2 : Rat)^m := by
    rw [div_le_div_iff₀ h_fac_pos h_2pow_pos]
    have h_lhs_nn : (0 : Rat) ≤ 4 := by norm_num
    nlinarith [h_2pow_pos.le, h_fac_pos.le, h_fac_ge]
  have h_4_2pow_lt : (4 : Rat) / (2 : Rat)^m < 1 / (2*(k:Rat) + 3) := by
    have h_recip_eq : (2*(k:Rat) + 3) = ((2*k+2 : Nat) : Rat) + 1 := by push_cast; ring
    rw [h_recip_eq]
    apply Rat.four_div_two_pow_lt_recip
    omega
  have h_4_fac_lt : (4 : Rat) / (Nat.factorial (4*m) : Rat) < 1 / (2*(k:Rat) + 3) := by
    linarith
  -- Step 3: combine.
  -- |α| ≤ 2|exp| + 4/(4m)! < 1/(2k+3) + 1/(2k+3) = 2/(2k+3) ≤ 1/(k+1).
  have h_2k3_pos : (0 : Rat) < 2*(k:Rat) + 3 := by
    have : (0 : Rat) ≤ (k : Rat) := by exact_mod_cast Nat.zero_le k
    linarith
  have h_k1_pos : (0 : Rat) < (k : Rat) + 1 := by
    have : (0 : Rat) ≤ (k : Rat) := by exact_mod_cast Nat.zero_le k
    linarith
  have h_sum_eq : (1 : Rat) / (2*(k:Rat) + 3) + 1 / (2*(k:Rat) + 3)
                  = 2 / (2*(k:Rat) + 3) := by ring
  have h_2_over_2k3 : (2 : Rat) / (2*(k:Rat) + 3) ≤ 1 / ((k:Rat) + 1) := by
    rw [div_le_div_iff₀ h_2k3_pos h_k1_pos]
    -- 2*(k+1) ≤ 1*(2k+3) iff 2k+2 ≤ 2k+3 ✓
    linarith
  linarith

/-- **[I.T-CisTauReal-Injectivity-At-Zero-Pair]** Convenience wrapper accepting
    BOTH legs of the cisTauReal = (1, 0) hypothesis. The `h_re` hypothesis is
    discarded — only the imaginary leg is needed for injectivity at zero.

    Useful for F.B.1 callers that have proved both `cisTauReal(γ) ≈ ⟨1, 0⟩`
    via the Pythagorean + 45°-line identity. -/
theorem TauComplex.cisTauReal_injectivity_at_zero_pair
    (γ : TauReal)
    (h_bound : ∀ n, ((γ.approx n).abs).toRat ≤ 1/2)
    (_h_re : TauReal.equiv (TauComplex.cisTauReal γ).re TauReal.one)
    (h_im : TauReal.equiv (TauComplex.cisTauReal γ).im TauReal.zero) :
    TauReal.equiv γ TauReal.zero :=
  TauComplex.cisTauReal_injectivity_at_zero γ h_bound h_im

end Tau.Boundary
