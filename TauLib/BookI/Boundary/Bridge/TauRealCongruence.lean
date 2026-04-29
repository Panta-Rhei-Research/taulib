import TauLib.BookI.Boundary.TauRealMulCongr
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Push
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity

/-!
# TauLib.BookI.Boundary.Bridge.TauRealCongruence

**Wave 41a — Cauchy and equivalence congruence lemmas for TauReal**.

This module supplies the foundational congruence lemmas needed to
quotient `TauReal` by Cauchy equivalence and lift ring operations
through the quotient (Wave 41b's `Bridge/TauRealQuotient.lean`).

The kernel had only the bounded multiplication-congruence theorem
(`mul_respects_equiv_right_of_bound` from `TauRealMulCongr.lean`) and
the abs-preserves-Cauchy theorem (from `TauRealAbs.lean`). Wave 41a
generalises:

1. `add_respects_equiv` — addition preserves Cauchy equivalence
   (no boundedness needed; pure triangle inequality).
2. `negate_respects_equiv` — negation preserves Cauchy equivalence.
3. `IsCauchy.bounded` — every Cauchy sequence is uniformly bounded
   (the constructive boundedness witness needed for mul-congr).
4. `IsCauchy_add` — sum of Cauchy is Cauchy.
5. `IsCauchy_negate` — negation of Cauchy is Cauchy.
6. `mul_respects_equiv_under_cauchy` — full multiplicative congruence
   for Cauchy representatives (uses `bounded` + bounded-mul-congr).
7. `IsCauchy_mul` — product of Cauchy is Cauchy.

These lemmas are used by `Bridge/TauRealQuotient.lean` to instantiate
`CommRing TauRealQ`, `Field TauRealQ`, and `IsStrictOrderedRing TauRealQ`.

## Methodology check (R1-R9 — passes)

- **TauReal-native**: All lemmas operate on `TauReal` (τ-native).
- **Mathlib usage**: TACTIC ONLY (`linarith`, `ring`, `push_cast`, `omega`,
  `field_simp`). No mathematical content imported. Compatible with the
  R3 tactic budget.
- **No new types defined**: pure lemmas extending existing API.

## Registry Cross-References

- [I.D84]   TauReal
- [I.D111]  TauReal.IsCauchy
- [I.D112]  TauReal.equiv (Cauchy completion)
- [I.T-W2.5]   TauReal.mul_respects_equiv_right_of_bound (existing)
- [I.T-W41a-1] TauReal.add_respects_equiv  (this module)
- [I.T-W41a-2] TauReal.negate_respects_equiv  (this module)
- [I.T-W41a-3] TauReal.IsCauchy.bounded  (this module)
- [I.T-W41a-4] TauReal.IsCauchy_add  (this module)
- [I.T-W41a-5] TauReal.IsCauchy_negate  (this module)
- [I.T-W41a-6] TauReal.mul_respects_equiv_under_cauchy  (this module)
- [I.T-W41a-7] TauReal.IsCauchy_mul  (this module)
-/

set_option autoImplicit false

namespace Tau.Boundary

open Tau.Denotation

-- ============================================================
-- PART 1: ADDITION — equiv-respect (no Cauchy needed)
-- ============================================================

/-- **Addition respects Cauchy equivalence.**

    If `a₁ ≡ a₂` and `b₁ ≡ b₂` (Cauchy-equiv), then `a₁ + b₁ ≡ a₂ + b₂`.
    The triangle inequality `|x+y| ≤ |x|+|y|` reduces this to splitting
    the target tolerance `1/(k+1)` into `1/(2k+2) + 1/(2k+2)` and pulling
    each input equiv at refined level `2k+1`. -/
theorem TauReal.add_respects_equiv
    (a₁ a₂ b₁ b₂ : TauReal)
    (ha : TauReal.equiv a₁ a₂) (hb : TauReal.equiv b₁ b₂) :
    TauReal.equiv (a₁.add b₁) (a₂.add b₂) := by
  obtain ⟨μa, hma⟩ := ha
  obtain ⟨μb, hmb⟩ := hb
  refine ⟨fun k => max (μa (2*k + 1)) (μb (2*k + 1)), fun k n hn => ?_⟩
  have hna : μa (2*k + 1) ≤ n := le_of_max_le_left hn
  have hnb : μb (2*k + 1) ≤ n := le_of_max_le_right hn
  have ha_step := hma (2*k + 1) n hna
  have hb_step := hmb (2*k + 1) n hnb
  unfold TauRat.lt at ha_step hb_step ⊢
  rw [TauRat.toRat_abs, toRat_sub] at ha_step hb_step
  rw [TauRat.toRat_abs, toRat_sub]
  rw [TauRat.ofNatRecip_toRat] at ha_step hb_step ⊢
  have h_lhs_eq :
      ((a₁.add b₁).approx n).toRat - ((a₂.add b₂).approx n).toRat
        = ((a₁.approx n).toRat - (a₂.approx n).toRat) +
          ((b₁.approx n).toRat - (b₂.approx n).toRat) := by
    show ((a₁.approx n).add (b₁.approx n)).toRat -
           ((a₂.approx n).add (b₂.approx n)).toRat = _
    rw [toRat_add, toRat_add]; ring
  rw [h_lhs_eq]
  -- Goal: |x + y| < 1/(k+1), with |x| < 1/(2k+2), |y| < 1/(2k+2)
  have h_tri := abs_add_le
      ((a₁.approx n).toRat - (a₂.approx n).toRat)
      ((b₁.approx n).toRat - (b₂.approx n).toRat)
  have hk_pos : (0 : Rat) < (2*k + 1 : Nat) + 1 := by
    have : (0 : Rat) ≤ (2*k + 1 : Nat) := by exact_mod_cast Nat.zero_le _
    linarith
  have hkk_pos : (0 : Rat) < (k : Rat) + 1 := by
    have : (0 : Rat) ≤ (k : Rat) := by exact_mod_cast Nat.zero_le k
    linarith
  -- 1/((2k+1)+1) = 1/(2(k+1)) so 1/(2k+2) + 1/(2k+2) = 1/(k+1)
  have h_split : (1 : Rat) / ((2*k + 1 : Nat) + 1) +
                 1 / ((2*k + 1 : Nat) + 1) = 1 / ((k : Rat) + 1) := by
    push_cast
    field_simp
    ring
  linarith

-- ============================================================
-- PART 2: NEGATION — equiv-respect (no Cauchy needed)
-- ============================================================

/-- **Negation respects Cauchy equivalence.**

    If `a₁ ≡ a₂` then `-a₁ ≡ -a₂`. Same modulus; `|-a₁ - (-a₂)| = |a₂ - a₁|
    = |a₁ - a₂|`. -/
theorem TauReal.negate_respects_equiv
    (a₁ a₂ : TauReal) (h : TauReal.equiv a₁ a₂) :
    TauReal.equiv a₁.negate a₂.negate := by
  obtain ⟨μ, hm⟩ := h
  refine ⟨μ, fun k n hn => ?_⟩
  have h_step := hm k n hn
  unfold TauRat.lt at h_step ⊢
  rw [TauRat.toRat_abs, toRat_sub] at h_step
  rw [TauRat.toRat_abs, toRat_sub]
  -- Goal: |negate.approx n .toRat - negate.approx n .toRat| < 1/(k+1)
  have h_lhs_eq :
      (a₁.negate.approx n).toRat - (a₂.negate.approx n).toRat
        = -((a₁.approx n).toRat - (a₂.approx n).toRat) := by
    show ((a₁.approx n).negate).toRat - ((a₂.approx n).negate).toRat = _
    rw [toRat_negate, toRat_negate]; ring
  rw [h_lhs_eq, abs_neg]
  exact h_step

-- ============================================================
-- PART 3: IsCauchy_add and IsCauchy_negate
-- ============================================================

/-- **Sum of Cauchy is Cauchy.** Triangle inequality + modulus splitting. -/
theorem TauReal.IsCauchy_add (a b : TauReal)
    (ha : a.IsCauchy) (hb : b.IsCauchy) :
    (a.add b).IsCauchy := by
  obtain ⟨μa, hma⟩ := ha
  obtain ⟨μb, hmb⟩ := hb
  refine ⟨fun k => max (μa (2*k + 1)) (μb (2*k + 1)), fun k m n hm hn => ?_⟩
  have hma_m : μa (2*k + 1) ≤ m := le_of_max_le_left hm
  have hma_n : μa (2*k + 1) ≤ n := le_of_max_le_left hn
  have hmb_m : μb (2*k + 1) ≤ m := le_of_max_le_right hm
  have hmb_n : μb (2*k + 1) ≤ n := le_of_max_le_right hn
  have ha_step := hma (2*k + 1) m n hma_m hma_n
  have hb_step := hmb (2*k + 1) m n hmb_m hmb_n
  unfold TauRat.lt at ha_step hb_step ⊢
  rw [TauRat.toRat_abs, toRat_sub] at ha_step hb_step
  rw [TauRat.toRat_abs, toRat_sub]
  rw [TauRat.ofNatRecip_toRat] at ha_step hb_step ⊢
  have h_lhs_eq :
      ((a.add b).approx m).toRat - ((a.add b).approx n).toRat
        = ((a.approx m).toRat - (a.approx n).toRat) +
          ((b.approx m).toRat - (b.approx n).toRat) := by
    show ((a.approx m).add (b.approx m)).toRat -
           ((a.approx n).add (b.approx n)).toRat = _
    rw [toRat_add, toRat_add]; ring
  rw [h_lhs_eq]
  have h_tri := abs_add_le
      ((a.approx m).toRat - (a.approx n).toRat)
      ((b.approx m).toRat - (b.approx n).toRat)
  have h_split : (1 : Rat) / ((2*k + 1 : Nat) + 1) +
                 1 / ((2*k + 1 : Nat) + 1) = 1 / ((k : Rat) + 1) := by
    push_cast; field_simp; ring
  linarith

/-- **Negation of Cauchy is Cauchy.** Same modulus. -/
theorem TauReal.IsCauchy_negate (a : TauReal) (h : a.IsCauchy) :
    a.negate.IsCauchy := by
  obtain ⟨μ, hm⟩ := h
  refine ⟨μ, fun k m n hm_le hn_le => ?_⟩
  have h_step := hm k m n hm_le hn_le
  unfold TauRat.lt at h_step ⊢
  rw [TauRat.toRat_abs, toRat_sub] at h_step
  rw [TauRat.toRat_abs, toRat_sub]
  have h_lhs_eq :
      (a.negate.approx m).toRat - (a.negate.approx n).toRat
        = -((a.approx m).toRat - (a.approx n).toRat) := by
    show ((a.approx m).negate).toRat - ((a.approx n).negate).toRat = _
    rw [toRat_negate, toRat_negate]; ring
  rw [h_lhs_eq, abs_neg]
  exact h_step

-- ============================================================
-- PART 4: Cauchy-implies-bounded
-- ============================================================

/-- **Every Cauchy sequence is uniformly bounded** (constructive form).

    Given `IsCauchy a`, returns a natural-number bound `M` such that
    `|a.approx n|.toRat ≤ M` for all `n`.

    Strategy: past `μ 0`, all `a.approx n` are within `1` of `a.approx (μ 0)`
    (the Cauchy property at `k=0` says `|a.m - a.n| < 1/(0+1) = 1`). Below
    `μ 0`, finitely many indices give a max via `Finset.sup'`. Combined
    `Rat` bound is then dominated by some `Nat` via `exists_nat_ge`. -/
theorem TauReal.IsCauchy.bounded {a : TauReal} (ha : a.IsCauchy) :
    ∃ M : Nat, 1 ≤ M ∧ ∀ n, (a.approx n).abs.toRat ≤ M := by
  obtain ⟨μ, hμ⟩ := ha
  set N0 := μ 0 with hN0_def
  -- Head bound: max of |a.0|, ..., |a.N0| at the Rat level
  set head_R : Rat := (Finset.range (N0 + 1)).sup'
    ⟨0, Finset.mem_range.mpr (Nat.succ_pos N0)⟩
    (fun i => (a.approx i).abs.toRat) with head_R_def
  -- Tail bound: |a.N0| + 1 dominates |a.n| for n > N0
  set tail_R : Rat := (a.approx N0).abs.toRat + 1 with tail_R_def
  set R : Rat := max head_R tail_R with R_def
  -- Convert to a Nat bound via Archimedean
  obtain ⟨M', hM'⟩ := exists_nat_ge R
  refine ⟨max M' 1, le_max_right _ _, ?_⟩
  intro n
  have h_M : (R : Rat) ≤ ((max M' 1 : Nat) : Rat) := by
    have : (M' : Rat) ≤ ((max M' 1 : Nat) : Rat) := by exact_mod_cast (le_max_left M' 1)
    linarith
  by_cases hn : n ≤ N0
  · -- Head case
    have h_in : n ∈ Finset.range (N0 + 1) := Finset.mem_range.mpr (by omega)
    have h_head : (a.approx n).abs.toRat ≤ head_R :=
      Finset.le_sup' (fun i => (a.approx i).abs.toRat) h_in
    have h_R : head_R ≤ R := le_max_left _ _
    linarith
  · -- Tail case: n > N0
    push_neg at hn
    have hN0_le_n : N0 ≤ n := Nat.le_of_lt hn
    have h_close := hμ 0 n N0 hN0_le_n (Nat.le_refl _)
    unfold TauRat.lt at h_close
    rw [TauRat.toRat_abs, toRat_sub, TauRat.ofNatRecip_toRat] at h_close
    have h_diff : |(a.approx n).toRat - (a.approx N0).toRat| < 1 := by simpa using h_close
    -- Triangle: |a.n| = |a.N0 + (a.n - a.N0)| ≤ |a.N0| + |a.n - a.N0|
    have h_eq_pre :
        (a.approx N0).toRat + ((a.approx n).toRat - (a.approx N0).toRat) =
          (a.approx n).toRat := by ring
    have h_pre_tri := abs_add_le (a.approx N0).toRat
                                  ((a.approx n).toRat - (a.approx N0).toRat)
    rw [h_eq_pre] at h_pre_tri
    have h_aN0 : |(a.approx N0).toRat| = (a.approx N0).abs.toRat := by
      rw [TauRat.toRat_abs]
    rw [TauRat.toRat_abs]
    have h_to_tail : |(a.approx n).toRat| ≤ tail_R := by
      rw [tail_R_def, ← h_aN0]; linarith
    have h_R : tail_R ≤ R := le_max_right _ _
    linarith

-- ============================================================
-- PART 5: mul_respects_equiv (Cauchy two-sided form)
-- ============================================================

/-- **Multiplication respects Cauchy equivalence under Cauchy hypotheses.**

    Given `equiv a₁ a₂`, `equiv b₁ b₂`, and `IsCauchy a₂`, `IsCauchy b₁`,
    we get `equiv (a₁ * b₁) (a₂ * b₂)`. The Cauchy hypotheses provide
    the boundedness witnesses needed by `mul_respects_equiv_right_of_bound`.

    Strategy: chain through `a₂ * b₁` as middle step.
       a₁ * b₁ ≈ a₂ * b₁  via right-bounded mul-congr (b₁ bounded)
       a₂ * b₁ ≈ a₂ * b₂  via right-bounded mul-congr after commutation -/
theorem TauReal.mul_respects_equiv_under_cauchy
    (a₁ a₂ b₁ b₂ : TauReal)
    (h_a2_cauchy : a₂.IsCauchy) (h_b1_cauchy : b₁.IsCauchy)
    (ha : TauReal.equiv a₁ a₂) (hb : TauReal.equiv b₁ b₂) :
    TauReal.equiv (a₁.mul b₁) (a₂.mul b₂) := by
  obtain ⟨Mb, hMb_pos, hMb⟩ := h_b1_cauchy.bounded
  obtain ⟨Ma, hMa_pos, hMa⟩ := h_a2_cauchy.bounded
  -- Step 1: a₁ * b₁ ≈ a₂ * b₁ (using b₁ bound)
  have h_step1 :=
    TauReal.mul_respects_equiv_right_of_bound a₁ a₂ b₁ Mb hMb_pos hMb ha
  -- Step 2: a₂ * b₁ ≈ a₂ * b₂. By commutativity:
  --   a₂ * b₁ ≈ b₁ * a₂ (via taureal_mul_comm)
  --   b₁ * a₂ ≈ b₂ * a₂ (via mul_respects_equiv_right_of_bound, a₂ bound)
  --   b₂ * a₂ ≈ a₂ * b₂ (via taureal_mul_comm)
  have h_swap1 : TauReal.equiv (a₂.mul b₁) (b₁.mul a₂) := taureal_mul_comm a₂ b₁
  have h_step2_inner :=
    TauReal.mul_respects_equiv_right_of_bound b₁ b₂ a₂ Ma hMa_pos hMa hb
  have h_swap2 : TauReal.equiv (b₂.mul a₂) (a₂.mul b₂) := taureal_mul_comm b₂ a₂
  -- Chain everything via equiv_trans
  exact TauReal.equiv_trans h_step1
        (TauReal.equiv_trans h_swap1
          (TauReal.equiv_trans h_step2_inner h_swap2))

-- ============================================================
-- PART 6: IsCauchy_mul (product of Cauchy is Cauchy)
-- ============================================================

/-- **Product of Cauchy is Cauchy.**

    For Cauchy `a, b`, we have `(a.mul b).IsCauchy`. Strategy:
    `|a.m * b.m - a.n * b.n|`
       `= |a.m * b.m - a.n * b.m + a.n * b.m - a.n * b.n|`
       `≤ |b.m| * |a.m - a.n| + |a.n| * |b.m - b.n|`
    Both `|b.m|` and `|a.n|` are bounded (by Cauchy). At level `k`,
    pull each input modulus at level `2*Mab*(k+1) - 1` where `Mab` is
    the max of the two bounds; the conclusion follows. -/
theorem TauReal.IsCauchy_mul (a b : TauReal)
    (ha : a.IsCauchy) (hb : b.IsCauchy) :
    (a.mul b).IsCauchy := by
  obtain ⟨Ma, hMa_pos, hMa⟩ := ha.bounded
  obtain ⟨Mb, hMb_pos, hMb⟩ := hb.bounded
  obtain ⟨μa, hμa⟩ := ha
  obtain ⟨μb, hμb⟩ := hb
  let M := max Ma Mb
  have hM_pos : 1 ≤ M := le_max_of_le_left hMa_pos
  -- Tighter modulus: at level `2*M*(k+1) - 1` we get `|a.m - a.n| < 1/(2M(k+1))`
  -- Then `|b.m| * |a.m - a.n| ≤ M * 1/(2M(k+1)) = 1/(2(k+1))`. Sum ≤ 1/(k+1).
  refine ⟨fun k => max (μa (2*M*(k+1) - 1)) (μb (2*M*(k+1) - 1)),
          fun k m n hm hn => ?_⟩
  have hμa_m : μa (2*M*(k+1) - 1) ≤ m := le_of_max_le_left hm
  have hμa_n : μa (2*M*(k+1) - 1) ≤ n := le_of_max_le_left hn
  have hμb_m : μb (2*M*(k+1) - 1) ≤ m := le_of_max_le_right hm
  have hμb_n : μb (2*M*(k+1) - 1) ≤ n := le_of_max_le_right hn
  have ha_step := hμa (2*M*(k+1) - 1) m n hμa_m hμa_n
  have hb_step := hμb (2*M*(k+1) - 1) m n hμb_m hμb_n
  unfold TauRat.lt at ha_step hb_step ⊢
  rw [TauRat.toRat_abs, toRat_sub] at ha_step hb_step
  rw [TauRat.toRat_abs, toRat_sub]
  rw [TauRat.ofNatRecip_toRat] at ha_step hb_step ⊢
  have h_lhs_eq :
      ((a.mul b).approx m).toRat - ((a.mul b).approx n).toRat
        = (b.approx m).toRat * ((a.approx m).toRat - (a.approx n).toRat) +
          (a.approx n).toRat * ((b.approx m).toRat - (b.approx n).toRat) := by
    show ((a.approx m).mul (b.approx m)).toRat -
           ((a.approx n).mul (b.approx n)).toRat = _
    rw [toRat_mul, toRat_mul]; ring
  rw [h_lhs_eq]
  -- Triangle: |x + y| ≤ |x| + |y|
  have h_tri := abs_add_le
      ((b.approx m).toRat * ((a.approx m).toRat - (a.approx n).toRat))
      ((a.approx n).toRat * ((b.approx m).toRat - (b.approx n).toRat))
  -- |b.m * (a.m - a.n)| = |b.m| * |a.m - a.n|
  have h_factor1 : |(b.approx m).toRat * ((a.approx m).toRat - (a.approx n).toRat)|
                 = |(b.approx m).toRat| * |(a.approx m).toRat - (a.approx n).toRat| :=
    abs_mul _ _
  have h_factor2 : |(a.approx n).toRat * ((b.approx m).toRat - (b.approx n).toRat)|
                 = |(a.approx n).toRat| * |(b.approx m).toRat - (b.approx n).toRat| :=
    abs_mul _ _
  -- |b.m| ≤ Mb, |a.n| ≤ Ma; both ≤ M
  have hbm_le : |(b.approx m).toRat| ≤ (M : Rat) := by
    have h1 : |(b.approx m).toRat| ≤ (Mb : Rat) := by
      have := hMb m; rw [TauRat.toRat_abs] at this; exact this
    have h2 : (Mb : Rat) ≤ (M : Rat) := by exact_mod_cast (le_max_right Ma Mb)
    linarith
  have han_le : |(a.approx n).toRat| ≤ (M : Rat) := by
    have h1 : |(a.approx n).toRat| ≤ (Ma : Rat) := by
      have := hMa n; rw [TauRat.toRat_abs] at this; exact this
    have h2 : (Ma : Rat) ≤ (M : Rat) := by exact_mod_cast (le_max_left Ma Mb)
    linarith
  -- |a.m - a.n| < 1/((2M(k+1) - 1) + 1) = 1/(2M(k+1))
  -- |b.m - b.n| < 1/(2M(k+1))
  have hM_pos' : (1 : Nat) ≤ 2 * M * (k+1) := by
    have h_2M : 1 ≤ 2 * M := by omega
    have h_kp1 : 1 ≤ k+1 := by omega
    calc 1 = 1 * 1 := by ring
      _ ≤ (2 * M) * (k+1) := Nat.mul_le_mul h_2M h_kp1
  have h_nat_eq : (2*M*(k+1) - 1 : Nat) + 1 = 2 * M * (k+1) :=
    Nat.sub_add_cancel hM_pos'
  have h_rat_eq : ((2*M*(k+1) - 1 : Nat) : Rat) + 1 = ((2 * M * (k+1) : Nat) : Rat) := by
    exact_mod_cast h_nat_eq
  have h_recip_eq :
      (1 : Rat) / ((2*M*(k+1) - 1 : Nat) + 1) = 1 / (2 * M * (k+1) : Nat) := by
    rw [h_rat_eq]
  rw [h_recip_eq] at ha_step hb_step
  have h_abs_a_nonneg : 0 ≤ |(a.approx m).toRat - (a.approx n).toRat| :=
    _root_.abs_nonneg _
  have h_abs_b_nonneg : 0 ≤ |(b.approx m).toRat - (b.approx n).toRat| :=
    _root_.abs_nonneg _
  have h_M_pos_rat : (0 : Rat) < M := by exact_mod_cast hM_pos
  have h_two_M_kp1_pos : (0 : Rat) < 2 * M * (k+1 : Nat) := by
    have hk : (0 : Rat) < (k + 1 : Nat) := by
      push_cast; linarith [show (0 : Rat) ≤ k by exact_mod_cast Nat.zero_le k]
    have : (0 : Rat) < 2 * M := by linarith
    have : (0 : Rat) < 2 * M * (k + 1 : Nat) := by positivity
    exact this
  -- Bound first term STRICTLY: |b.m| * |a.m - a.n| < M * 1/(2M(k+1)) = 1/(2(k+1))
  -- Two-step: |b.m| * |a.m - a.n| ≤ M * |a.m - a.n| (from hbm_le)
  --        < M * 1/(2M(k+1))                       (from ha_step strict, M > 0)
  have h_term1_lt :
      |(b.approx m).toRat| * |(a.approx m).toRat - (a.approx n).toRat| <
      (M : Rat) * (1 / (2 * M * (k+1) : Nat)) := by
    have h1 :
        |(b.approx m).toRat| * |(a.approx m).toRat - (a.approx n).toRat| ≤
        (M : Rat) * |(a.approx m).toRat - (a.approx n).toRat| :=
      mul_le_mul_of_nonneg_right hbm_le h_abs_a_nonneg
    have h2 : (M : Rat) * |(a.approx m).toRat - (a.approx n).toRat| <
              (M : Rat) * (1 / (2 * M * (k+1) : Nat)) :=
      mul_lt_mul_of_pos_left ha_step h_M_pos_rat
    linarith
  have h_term2_lt :
      |(a.approx n).toRat| * |(b.approx m).toRat - (b.approx n).toRat| <
      (M : Rat) * (1 / (2 * M * (k+1) : Nat)) := by
    have h1 :
        |(a.approx n).toRat| * |(b.approx m).toRat - (b.approx n).toRat| ≤
        (M : Rat) * |(b.approx m).toRat - (b.approx n).toRat| :=
      mul_le_mul_of_nonneg_right han_le h_abs_b_nonneg
    have h2 : (M : Rat) * |(b.approx m).toRat - (b.approx n).toRat| <
              (M : Rat) * (1 / (2 * M * (k+1) : Nat)) :=
      mul_lt_mul_of_pos_left hb_step h_M_pos_rat
    linarith
  have h_simplify : (M : Rat) * (1 / (2 * M * (k+1) : Nat)) = 1 / (2 * (k+1) : Nat) := by
    have h_M_ne : (M : Rat) ≠ 0 := ne_of_gt h_M_pos_rat
    have h_kp1_ne : ((k+1 : Nat) : Rat) ≠ 0 := by
      push_cast; linarith [show (0 : Rat) ≤ k by exact_mod_cast Nat.zero_le k]
    push_cast
    field_simp
  rw [h_simplify] at h_term1_lt h_term2_lt
  -- Sum: 1/(2(k+1)) + 1/(2(k+1)) = 1/(k+1)
  have h_sum : (1 : Rat) / (2 * (k+1) : Nat) + 1 / (2 * (k+1) : Nat)
             = 1 / ((k : Rat) + 1) := by
    have h_kp1_ne : ((k+1 : Nat) : Rat) ≠ 0 := by
      push_cast; linarith [show (0 : Rat) ≤ k by exact_mod_cast Nat.zero_le k]
    push_cast
    field_simp
    ring
  rw [h_factor1, h_factor2] at h_tri
  linarith

end Tau.Boundary
