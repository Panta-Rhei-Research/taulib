import TauLib.BookI.Boundary.Bridge.TauRealQuotient
import TauLib.BookI.Boundary.TauRealInv
import Mathlib.Algebra.Field.Defs
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith

/-!
# TauLib.BookI.Boundary.Bridge.TauRealQuotientField

**Wave 41c — Mathlib Field bridge for TauReal (classical inverse)**.

Builds on Wave 41b's `CommRing TauRealQ` to lift the τ-native total
inverse (`TauReal.inv` from `TauRealInv.lean`) to the quotient and
instantiate Mathlib's `Field TauRealQ` as a noncomputable typeclass.

The constructive cost is **exactly one `Classical.byCases`**: bridging
`x ≠ 0` (in the quotient) to `BoundedAwayFromZero` (the apartness
witness) requires Markov's principle, supplied by `Classical.choice`.

## What this module delivers

- `TauReal.IsCauchy_inv` — Cauchy preservation under `inv` given
  `BoundedAwayFromZero` (the |1/aₘ - 1/aₙ| ≤ |aₘ-aₙ|/(δ²) bound).
- `TauReal.boundedAway_of_not_equiv_zero` — Markov-classical bridge
  from `IsCauchy a ∧ ¬ a.equiv 0` to `a.BoundedAwayFromZero`.
- `TauReal.inv_respects_equiv_under_cauchy` — congruence for inv on
  Cauchy reps (via the existing `mul_respects_equiv` machinery).
- `CauchyTauReal.inv` — noncomputable inverse on the Cauchy subtype.
- `TauRealQ.inv` — the quotient-level inverse (Quotient.lift).
- KEYSTONE: `noncomputable instance : Field TauRealQ` — every Field
  axiom proven by quotient-induction on representatives + classical
  case analysis on apartness.

## The constructive cost (made visible)

`Field TauRealQ` is **noncomputable** because the inverse uses
`Classical.byCases` to decide whether a Cauchy class equals zero.
This is inherent: deciding `(a : TauRealQ) = 0` for arbitrary `a` is
*equivalent* to Markov's principle for the τ-Real. The Field
typeclass ergonomics still work — every Mathlib theorem stated for
`Field` applies to `TauRealQ` — but the underlying inverse function
is not computable.

## What this does NOT deliver

- **No `RingEquiv` to Mathlib's `Real`** — different cardinality, see
  atlas insight `2026-04-29-constructive-real-cardinality-boundary`.
- **No `IsStrictOrderedRing`** — Wave 41d (next).
- **No `LinearOrderedField`** — structurally impossible (see atlas).

## Registry Cross-References

- [I.D146]   CauchyTauReal + TauRealQ (Wave 41b)
- [I.T225]   CommRing TauRealQ (Wave 41b)
- [I.T227]   TauReal.IsCauchy_inv (this module)
- [I.T228]   TauReal.boundedAway_of_not_equiv_zero (this module)
- [I.T229]   TauReal.inv_respects_equiv_under_cauchy (this module)
- [I.T230]   Field TauRealQ Instance (this module — KEYSTONE)
- [I.T231]   Wave 41c synthesis theorem
-/

set_option autoImplicit false

namespace Tau.Boundary

open Tau.Denotation

-- ============================================================
-- PART 1: TauReal.IsCauchy_inv
-- ============================================================

/-- **Inverse preserves Cauchy under `BoundedAwayFromZero`**.

    If `a` is Cauchy and bounded away from zero past `(k₀, N₀)`, then
    `a.inv` is Cauchy. The bound:
       |1/aₘ - 1/aₙ| = |aₙ - aₘ| / (|aₘ| · |aₙ|)
                     ≤ (k₀+1)² · |aₘ - aₙ|
    Pull Cauchy modulus at level `(k₀+1)² · (k+1) - 1`. -/
theorem TauReal.IsCauchy_inv (a : TauReal)
    (ha_cauchy : a.IsCauchy) (h_apart : a.BoundedAwayFromZero) :
    a.inv.IsCauchy := by
  obtain ⟨k₀, N₀, hN₀⟩ := h_apart
  obtain ⟨μ, hμ⟩ := ha_cauchy
  -- Each |a.n| > 1/(k₀+1) past N₀, so 1/|a.n| < k₀+1.
  -- |1/aₘ - 1/aₙ| = |aₘ - aₙ| / (|aₘ| · |aₙ|) ≤ (k₀+1)² · |aₘ - aₙ|.
  -- For target tolerance 1/(k+1), pull μ at level (k₀+1)² · (k+1) - 1.
  let M : Nat := (k₀ + 1) * (k₀ + 1)
  refine ⟨fun k => max N₀ (μ (M * (k+1) - 1)), fun k m n hm hn => ?_⟩
  have hN₀_m : N₀ ≤ m := le_of_max_le_left hm
  have hN₀_n : N₀ ≤ n := le_of_max_le_left hn
  have hμ_m : μ (M * (k+1) - 1) ≤ m := le_of_max_le_right hm
  have hμ_n : μ (M * (k+1) - 1) ≤ n := le_of_max_le_right hn
  -- Apartness witnesses
  have h_apart_m := hN₀ m hN₀_m
  have h_apart_n := hN₀ n hN₀_n
  unfold TauRat.lt at h_apart_m h_apart_n
  rw [TauRat.ofNatRecip_toRat, TauRat.toRat_abs] at h_apart_m h_apart_n
  -- 1/(k₀+1) < |aₘ.toRat|, |aₙ.toRat|
  have h_nz_m := TauReal.is_nonzero_of_bounded_away hN₀ m hN₀_m
  have h_nz_n := TauReal.is_nonzero_of_bounded_away hN₀ n hN₀_n
  -- Cauchy step
  have h_cauchy_step := hμ (M * (k+1) - 1) m n hμ_m hμ_n
  unfold TauRat.lt at h_cauchy_step
  rw [TauRat.toRat_abs, toRat_sub] at h_cauchy_step
  rw [TauRat.ofNatRecip_toRat] at h_cauchy_step
  -- Goal: |a.inv.approx m - a.inv.approx n|.toRat < 1/(k+1)
  show TauRat.lt _ _
  unfold TauRat.lt
  rw [TauRat.toRat_abs, toRat_sub]
  rw [TauRat.ofNatRecip_toRat]
  -- a.inv.approx i = TauRat.inv (a.approx i) (h_nz_i) when i ≥ N₀
  have h_inv_m : (a.inv).approx m = TauRat.inv (a.approx m) h_nz_m := by
    show (if h : (a.approx m).is_nonzero then TauRat.inv (a.approx m) h
          else TauRat.one) = TauRat.inv (a.approx m) h_nz_m
    rw [dif_pos h_nz_m]
  have h_inv_n : (a.inv).approx n = TauRat.inv (a.approx n) h_nz_n := by
    show (if h : (a.approx n).is_nonzero then TauRat.inv (a.approx n) h
          else TauRat.one) = TauRat.inv (a.approx n) h_nz_n
    rw [dif_pos h_nz_n]
  rw [h_inv_m, h_inv_n, toRat_inv, toRat_inv]
  -- Goal: |1/(aₘ.toRat) - 1/(aₙ.toRat)| < 1/(k+1)
  -- Setup: am, an nonzero in Rat
  have h_am_ne : (a.approx m).toRat ≠ 0 :=
    (TauRat.is_nonzero_iff_toRat_ne_zero (a.approx m)).mp h_nz_m
  have h_an_ne : (a.approx n).toRat ≠ 0 :=
    (TauRat.is_nonzero_iff_toRat_ne_zero (a.approx n)).mp h_nz_n
  have h_recip_eq : ((a.approx m).toRat)⁻¹ - ((a.approx n).toRat)⁻¹
                  = ((a.approx n).toRat - (a.approx m).toRat) /
                    ((a.approx m).toRat * (a.approx n).toRat) := by
    field_simp
  rw [h_recip_eq]
  rw [abs_div]
  have h_abs_prod : |(a.approx m).toRat * (a.approx n).toRat|
                  = |(a.approx m).toRat| * |(a.approx n).toRat| := abs_mul _ _
  rw [h_abs_prod]
  have h_abs_neg :
      |(a.approx n).toRat - (a.approx m).toRat| =
      |(a.approx m).toRat - (a.approx n).toRat| := by
    rw [show (a.approx n).toRat - (a.approx m).toRat
        = -((a.approx m).toRat - (a.approx n).toRat) by ring]
    exact abs_neg _
  rw [h_abs_neg]
  -- Goal: |aₘ - aₙ| / (|aₘ| · |aₙ|) < 1/(k+1)
  -- We know:
  --   |aₘ| > 1/(k₀+1), so |aₘ|·|aₙ| > 1/(k₀+1)²
  --   |aₘ - aₙ| < 1/(M(k+1))  where M = (k₀+1)²
  -- Therefore |aₘ - aₙ| / (|aₘ|·|aₙ|) < (1/M(k+1)) / (1/M) = 1/(k+1).
  have h_recip_pos : (0 : Rat) < 1 / ((k₀ : Rat) + 1) := by
    have : (0 : Rat) < (k₀ : Rat) + 1 := by
      have : (0 : Rat) ≤ (k₀ : Rat) := by exact_mod_cast Nat.zero_le k₀
      linarith
    exact div_pos (by norm_num) this
  have h_am_abs_pos : (0 : Rat) < |(a.approx m).toRat| := by linarith
  have h_an_abs_pos : (0 : Rat) < |(a.approx n).toRat| := by linarith
  have h_prod_pos : (0 : Rat) < |(a.approx m).toRat| * |(a.approx n).toRat| := by
    exact mul_pos h_am_abs_pos h_an_abs_pos
  -- Strict lower bound on |aₘ|·|aₙ|
  have h_prod_gt : (1 : Rat) / ((k₀ : Rat) + 1) * (1 / ((k₀ : Rat) + 1))
                 < |(a.approx m).toRat| * |(a.approx n).toRat| := by
    have h1 : (1 : Rat) / ((k₀ : Rat) + 1) * (1 / ((k₀ : Rat) + 1))
            < |(a.approx m).toRat| * (1 / ((k₀ : Rat) + 1)) :=
      mul_lt_mul_of_pos_right h_apart_m h_recip_pos
    have h2 : |(a.approx m).toRat| * (1 / ((k₀ : Rat) + 1))
            < |(a.approx m).toRat| * |(a.approx n).toRat| :=
      mul_lt_mul_of_pos_left h_apart_n h_am_abs_pos
    linarith
  -- Cauchy step at modulus M(k+1) - 1: |aₘ - aₙ| < 1/(M(k+1))
  have h_M_pos : 1 ≤ M := by
    show 1 ≤ (k₀ + 1) * (k₀ + 1); have : 1 ≤ k₀ + 1 := Nat.succ_le_succ (Nat.zero_le _)
    calc 1 = 1 * 1 := by ring
      _ ≤ (k₀ + 1) * (k₀ + 1) := Nat.mul_le_mul this this
  have h_Mk_pos : (1 : Nat) ≤ M * (k+1) := by
    have h_kp1 : 1 ≤ k+1 := Nat.succ_le_succ (Nat.zero_le _)
    calc 1 = 1 * 1 := by ring
      _ ≤ M * (k+1) := Nat.mul_le_mul h_M_pos h_kp1
  have h_cauchy_norm :
      ((M * (k+1) - 1 : Nat) : Rat) + 1 = ((M * (k+1) : Nat) : Rat) := by
    have : (M * (k+1) - 1 + 1 : Nat) = M * (k+1) := Nat.sub_add_cancel h_Mk_pos
    exact_mod_cast this
  rw [h_cauchy_norm] at h_cauchy_step
  -- Now: h_cauchy_step : |aₘ - aₙ| < 1 / (M(k+1))
  --       h_prod_gt : 1/M < |aₘ|·|aₙ|
  --       Goal: |aₘ - aₙ| / (|aₘ|·|aₙ|) < 1/(k+1)
  have h_M_rat_pos : (0 : Rat) < (M : Rat) := by
    exact_mod_cast h_M_pos
  have h_kp1_rat_pos : (0 : Rat) < ((k+1 : Nat) : Rat) := by
    push_cast; linarith [show (0 : Rat) ≤ k by exact_mod_cast Nat.zero_le k]
  have h_M_eq : (1 : Rat) / ((k₀ : Rat) + 1) * (1 / ((k₀ : Rat) + 1))
              = 1 / (M : Rat) := by
    have h_M_def : (M : Rat) = ((k₀ + 1 : Nat) : Rat) * ((k₀ + 1 : Nat) : Rat) := by
      show (((k₀ + 1) * (k₀ + 1) : Nat) : Rat) = _
      push_cast; ring
    rw [h_M_def]
    have h_kp1_pos : (0 : Rat) < ((k₀ : Rat) + 1) := by
      have : (0 : Rat) ≤ (k₀ : Rat) := by exact_mod_cast Nat.zero_le k₀
      linarith
    have h_kp1_ne : ((k₀ : Rat) + 1) ≠ 0 := ne_of_gt h_kp1_pos
    push_cast
    field_simp
  rw [h_M_eq] at h_prod_gt
  -- Use: a/b < c iff a < c*b (when b > 0)
  rw [div_lt_iff₀ h_prod_pos]
  -- Goal: |aₘ - aₙ| < (1/(k+1)) * (|aₘ|·|aₙ|)
  -- We have |aₘ - aₙ| < 1/(M(k+1)) and |aₘ|·|aₙ| > 1/M
  -- (1/(k+1)) * (|aₘ|·|aₙ|) > (1/(k+1)) * (1/M) = 1/(M(k+1))
  have h_chain :
      (1 : Rat) / ((k+1 : Nat) : Rat) * (1 / (M : Rat)) <
      (1 : Rat) / ((k : Rat) + 1) * (|(a.approx m).toRat| * |(a.approx n).toRat|) := by
    have h_kp1_eq : ((k+1 : Nat) : Rat) = (k : Rat) + 1 := by push_cast; ring
    rw [h_kp1_eq]
    have h_kp1_inv_pos : (0 : Rat) < 1 / ((k : Rat) + 1) := by
      apply div_pos (by norm_num); linarith
    exact mul_lt_mul_of_pos_left h_prod_gt h_kp1_inv_pos
  have h_factor : (1 : Rat) / ((k+1 : Nat) : Rat) * (1 / (M : Rat))
                = 1 / ((M * (k+1) : Nat) : Rat) := by
    have h_M_ne : (M : Rat) ≠ 0 := ne_of_gt h_M_rat_pos
    have h_kp1_ne : ((k+1 : Nat) : Rat) ≠ 0 := ne_of_gt h_kp1_rat_pos
    push_cast
    field_simp
  rw [h_factor] at h_chain
  linarith

-- ============================================================
-- PART 2: Markov-classical bridge — non-equiv-zero ⇒ BoundedAway
-- ============================================================

/-- **Classical bridge from non-equivalence-to-zero to apartness**.

    For a Cauchy `a`, if `a ≢ 0` (Cauchy-equiv), then `a` is bounded
    away from zero. Proof by classical contradiction: if not bounded
    away, then for every level there's an arbitrarily late index where
    `|aₙ|` shrinks; combined with Cauchy, the whole tail goes to zero,
    contradicting `a ≢ 0`. Uses `Classical.byContradiction`. -/
theorem TauReal.boundedAway_of_not_equiv_zero (a : TauReal)
    (ha : a.IsCauchy) (hne : ¬ TauReal.equiv a TauReal.zero) :
    a.BoundedAwayFromZero := by
  classical
  by_contra h_not_apart
  -- ¬ BoundedAwayFromZero a means ∀ k N, ∃ n ≥ N, |aₙ| ≤ 1/(k+1)
  apply hne
  -- Build equiv to zero. For each k, find N such that |aₙ| < 1/(k+1) for n ≥ N.
  obtain ⟨μ, hμ⟩ := ha
  refine ⟨fun k => μ (2*k + 1), fun k n hn => ?_⟩
  -- Want: |a.approx n - 0.approx n|.toRat = |a.approx n|.toRat < 1/(k+1)
  have h_zero_n : (TauReal.zero.approx n) = TauRat.zero := rfl
  unfold TauRat.lt
  rw [TauRat.toRat_abs, toRat_sub]
  show |(a.approx n).toRat - (TauReal.zero.approx n).toRat| < (TauRat.ofNatRecip k).toRat
  rw [h_zero_n]
  rw [show (TauRat.zero.toRat : Rat) = 0 from toRat_zero]
  rw [sub_zero]
  rw [TauRat.ofNatRecip_toRat]
  -- Construct: ¬ BoundedAway → ∀ k N, ∃ n ≥ N, ¬ (apartness witness at n)
  have h_not_apart' : ∀ k₀ N₀ : Nat, ∃ n, N₀ ≤ n ∧
      ¬ TauRat.lt (TauRat.ofNatRecip k₀) (a.approx n).abs := by
    intros k₀ N₀
    by_contra h_contra
    apply h_not_apart
    refine ⟨k₀, N₀, ?_⟩
    intros n hn
    by_contra h_ne
    exact h_contra ⟨n, hn, h_ne⟩
  obtain ⟨m, hm_ge, hm_le⟩ := h_not_apart' (2*k + 1) (μ (2*k + 1))
  unfold TauRat.lt at hm_le
  rw [TauRat.ofNatRecip_toRat, TauRat.toRat_abs] at hm_le
  -- hm_le : ¬ (1/(2k+2) < |a.approx m|.toRat), i.e., |a.approx m|.toRat ≤ 1/(2k+2)
  have hm_le' : |(a.approx m).toRat| ≤ 1 / (((2*k + 1 : Nat) : Rat) + 1) :=
    not_lt.mp hm_le
  -- Cauchy: |aₙ - aₘ| < 1/(2k+2) (using μ at 2k+1)
  have h_cauchy := hμ (2*k + 1) n m hn hm_ge
  unfold TauRat.lt at h_cauchy
  rw [TauRat.toRat_abs, toRat_sub, TauRat.ofNatRecip_toRat] at h_cauchy
  -- |aₙ - aₘ| < 1/(2k+2)
  have h_split : (a.approx n).toRat
               = (a.approx m).toRat + ((a.approx n).toRat - (a.approx m).toRat) := by ring
  have h_pre_tri := abs_add_le (a.approx m).toRat
                                ((a.approx n).toRat - (a.approx m).toRat)
  rw [← h_split] at h_pre_tri
  -- Now h_pre_tri : |aₙ| ≤ |aₘ| + |aₙ - aₘ| < 1/(2k+2) + 1/(2k+2) = 1/(k+1)
  have h_recip_split : (1 : Rat) / (((2*k + 1 : Nat) : Rat) + 1)
                     + 1 / (((2*k + 1 : Nat) : Rat) + 1)
                     = 1 / ((k : Rat) + 1) := by
    push_cast; field_simp; ring
  linarith

-- ============================================================
-- PART 3: inv_respects_equiv (under Cauchy + BoundedAway)
-- ============================================================

/-- **Inverse respects equiv on Cauchy reps, both bounded away from zero**. -/
theorem TauReal.inv_respects_equiv_under_cauchy
    (a₁ a₂ : TauReal)
    (h1_cauchy : a₁.IsCauchy) (h2_cauchy : a₂.IsCauchy)
    (h1_apart : a₁.BoundedAwayFromZero)
    (h2_apart : a₂.BoundedAwayFromZero)
    (h_equiv : TauReal.equiv a₁ a₂) :
    TauReal.equiv a₁.inv a₂.inv := by
  -- a₁ * a₁.inv ≡ 1 ≡ a₂ * a₂.inv
  -- So a₁.inv ≡ a₂.inv via:
  --   a₁.inv ≡ (a₂ * a₂.inv) * a₁.inv  (since a₂*a₂.inv ≡ 1)
  --        ≡ (a₁ * a₂.inv) * a₁.inv    (replace a₂ by a₁ via h_equiv)
  --        ≡ a₂.inv                    (a₁ * a₁.inv ≡ 1, drop)
  -- Cleaner: use the standard 1/x = 1/y when xy ≡ 1 chain.
  have h_inv_a1_cauchy : a₁.inv.IsCauchy := TauReal.IsCauchy_inv a₁ h1_cauchy h1_apart
  have h_inv_a2_cauchy : a₂.IsCauchy := h2_cauchy
  -- a₂ ≡ a₁ (symm)
  have h_equiv_sym : TauReal.equiv a₂ a₁ := TauReal.equiv_symm h_equiv
  -- a₂ * a₂.inv ≡ 1
  have h_a2_cancel : TauReal.equiv (a₂.mul a₂.inv) TauReal.one :=
    TauReal.mul_inv_cancel a₂ h2_apart
  -- a₁.inv = 1 * a₁.inv ≡ (a₂ * a₂.inv) * a₁.inv ≡ (a₁ * a₂.inv) * a₁.inv
  --       ≡ a₂.inv * (a₁ * a₁.inv) ≡ a₂.inv * 1 ≡ a₂.inv
  -- Use: a * b ≡ a' * b' when a ≡ a', b ≡ b' (under Cauchy hypotheses)
  have h_a1inv_eq : TauReal.equiv a₁.inv ((TauReal.one).mul a₁.inv) :=
    TauReal.equiv_symm (taureal_one_mul a₁.inv)
  -- Step: 1 ≡ a₂ * a₂.inv (symm of cancel)
  have h_one_eq_a2_a2inv : TauReal.equiv TauReal.one (a₂.mul a₂.inv) :=
    TauReal.equiv_symm h_a2_cancel
  -- (1 * a₁.inv) ≡ ((a₂ * a₂.inv) * a₁.inv)
  have h_step1 : TauReal.equiv ((TauReal.one).mul a₁.inv)
                                ((a₂.mul a₂.inv).mul a₁.inv) :=
    TauReal.mul_respects_equiv_under_cauchy
      TauReal.one (a₂.mul a₂.inv) a₁.inv a₁.inv
      (TauReal.IsCauchy_mul a₂ a₂.inv h2_cauchy
        (TauReal.IsCauchy_inv a₂ h2_cauchy h2_apart))
      h_inv_a1_cauchy
      h_one_eq_a2_a2inv
      (TauReal.equiv_refl a₁.inv)
  -- ((a₂ * a₂.inv) * a₁.inv) ≡ ((a₁ * a₂.inv) * a₁.inv)
  have h_step2 : TauReal.equiv ((a₂.mul a₂.inv).mul a₁.inv)
                                ((a₁.mul a₂.inv).mul a₁.inv) :=
    TauReal.mul_respects_equiv_under_cauchy
      (a₂.mul a₂.inv) (a₁.mul a₂.inv) a₁.inv a₁.inv
      (TauReal.IsCauchy_mul a₁ a₂.inv h1_cauchy
        (TauReal.IsCauchy_inv a₂ h2_cauchy h2_apart))
      h_inv_a1_cauchy
      (TauReal.mul_respects_equiv_under_cauchy
        a₂ a₁ a₂.inv a₂.inv h1_cauchy
        (TauReal.IsCauchy_inv a₂ h2_cauchy h2_apart)
        h_equiv_sym (TauReal.equiv_refl a₂.inv))
      (TauReal.equiv_refl a₁.inv)
  -- ((a₁ * a₂.inv) * a₁.inv) ≡ a₂.inv * (a₁ * a₁.inv)  (assoc + comm)
  have h_step3 : TauReal.equiv ((a₁.mul a₂.inv).mul a₁.inv)
                                (a₂.inv.mul (a₁.mul a₁.inv)) := by
    -- Rearrange via commutativity + associativity
    -- (a₁ · a₂.inv) · a₁.inv = (a₂.inv · a₁) · a₁.inv (mul_comm in first factor)
    --                       = a₂.inv · (a₁ · a₁.inv) (assoc)
    have step_a : TauReal.equiv ((a₁.mul a₂.inv).mul a₁.inv)
                                  ((a₂.inv.mul a₁).mul a₁.inv) :=
      TauReal.mul_respects_equiv_under_cauchy
        (a₁.mul a₂.inv) (a₂.inv.mul a₁) a₁.inv a₁.inv
        (TauReal.IsCauchy_mul a₂.inv a₁
          (TauReal.IsCauchy_inv a₂ h2_cauchy h2_apart) h1_cauchy)
        h_inv_a1_cauchy
        (taureal_mul_comm a₁ a₂.inv)
        (TauReal.equiv_refl a₁.inv)
    have step_b : TauReal.equiv ((a₂.inv.mul a₁).mul a₁.inv)
                                  (a₂.inv.mul (a₁.mul a₁.inv)) :=
      taureal_mul_assoc a₂.inv a₁ a₁.inv
    exact TauReal.equiv_trans step_a step_b
  -- a₂.inv * (a₁ * a₁.inv) ≡ a₂.inv * 1 ≡ a₂.inv
  have h_a1_cancel : TauReal.equiv (a₁.mul a₁.inv) TauReal.one :=
    TauReal.mul_inv_cancel a₁ h1_apart
  have h_step4 : TauReal.equiv (a₂.inv.mul (a₁.mul a₁.inv))
                                (a₂.inv.mul TauReal.one) :=
    TauReal.mul_respects_equiv_under_cauchy
      a₂.inv a₂.inv (a₁.mul a₁.inv) TauReal.one
      (TauReal.IsCauchy_inv a₂ h2_cauchy h2_apart)
      (TauReal.IsCauchy_mul a₁ a₁.inv h1_cauchy h_inv_a1_cauchy)
      (TauReal.equiv_refl a₂.inv)
      h_a1_cancel
  have h_step5 : TauReal.equiv (a₂.inv.mul TauReal.one) a₂.inv :=
    taureal_mul_one a₂.inv
  -- Chain everything
  exact TauReal.equiv_trans h_a1inv_eq
    (TauReal.equiv_trans h_step1
      (TauReal.equiv_trans h_step2
        (TauReal.equiv_trans h_step3
          (TauReal.equiv_trans h_step4 h_step5))))

-- ============================================================
-- PART 4: CauchyTauReal.inv (noncomputable, classical)
-- ============================================================

/-- **Noncomputable inverse on `CauchyTauReal`**.

    Uses `Classical.byCases` on `BoundedAwayFromZero`: for apartness
    witnesses, returns the genuine inverse (which is Cauchy by
    `IsCauchy_inv`); otherwise returns zero (Mathlib convention
    `inv 0 = 0`). -/
noncomputable def CauchyTauReal.inv (a : CauchyTauReal) : CauchyTauReal :=
  letI : Decidable a.val.BoundedAwayFromZero := Classical.propDecidable _
  if h : a.val.BoundedAwayFromZero then
    ⟨a.val.inv, TauReal.IsCauchy_inv a.val a.isCauchy h⟩
  else
    CauchyTauReal.zero

theorem CauchyTauReal.inv_respects_equiv (a₁ a₂ : CauchyTauReal)
    (h : CauchyTauReal.equiv a₁ a₂) :
    CauchyTauReal.equiv a₁.inv a₂.inv := by
  classical
  by_cases h1 : a₁.val.BoundedAwayFromZero
  · -- a₁ is bounded away. Then a₂ is also bounded away (since equiv).
    have h2 : a₂.val.BoundedAwayFromZero := by
      -- a₁.equiv a₂ ∧ ¬ a₁.equiv 0 ⇒ ¬ a₂.equiv 0 ⇒ BoundedAwayFromZero a₂
      apply TauReal.boundedAway_of_not_equiv_zero a₂.val a₂.isCauchy
      intro h_a2_eq_zero
      -- a₂ ≡ 0 and a₁ ≡ a₂ ⇒ a₁ ≡ 0, contradicting BoundedAwayFromZero a₁
      have h_a1_eq_zero : TauReal.equiv a₁.val TauReal.zero :=
        TauReal.equiv_trans h h_a2_eq_zero
      -- a₁ ≡ 0 and BoundedAway a₁ leads to contradiction:
      -- a₁ ≡ 0 means at the appropriate modulus |a₁ - 0| < 1/(k₀+1)
      -- BoundedAway means |a₁| > 1/(k₀+1). Contradiction.
      obtain ⟨k₀, N₀, hN₀⟩ := h1
      obtain ⟨μ_eq_z, hμ_eq_z⟩ := h_a1_eq_zero
      let n_test := max N₀ (μ_eq_z k₀)
      have h_n_ge_N0 : N₀ ≤ n_test := le_max_left _ _
      have h_n_ge_μ : μ_eq_z k₀ ≤ n_test := le_max_right _ _
      have h_apart_n := hN₀ n_test h_n_ge_N0
      have h_eqz_n := hμ_eq_z k₀ n_test h_n_ge_μ
      unfold TauRat.lt at h_apart_n h_eqz_n
      rw [TauRat.toRat_abs, toRat_sub] at h_eqz_n
      rw [TauRat.ofNatRecip_toRat, TauRat.toRat_abs] at h_apart_n
      rw [TauRat.ofNatRecip_toRat] at h_eqz_n
      have h_zero_n : (TauReal.zero.approx n_test) = TauRat.zero := rfl
      rw [h_zero_n, show (TauRat.zero.toRat : Rat) = 0 from toRat_zero, sub_zero] at h_eqz_n
      linarith
    -- Both bounded away. Use inv_respects_equiv_under_cauchy.
    show TauReal.equiv (CauchyTauReal.inv a₁).val (CauchyTauReal.inv a₂).val
    have h1_val : (CauchyTauReal.inv a₁).val = a₁.val.inv := by
      unfold CauchyTauReal.inv; simp only [dif_pos h1]
    have h2_val : (CauchyTauReal.inv a₂).val = a₂.val.inv := by
      unfold CauchyTauReal.inv; simp only [dif_pos h2]
    rw [h1_val, h2_val]
    exact TauReal.inv_respects_equiv_under_cauchy a₁.val a₂.val
            a₁.isCauchy a₂.isCauchy h1 h2 h
  · -- a₁ NOT bounded away. By classical, a₁.equiv 0. Then a₂.equiv 0 too.
    have h1_eq_zero : TauReal.equiv a₁.val TauReal.zero := by
      classical
      by_contra h_ne
      exact h1 (TauReal.boundedAway_of_not_equiv_zero a₁.val a₁.isCauchy h_ne)
    have h2_eq_zero : TauReal.equiv a₂.val TauReal.zero :=
      TauReal.equiv_trans (TauReal.equiv_symm h) h1_eq_zero
    have h2_not_apart : ¬ a₂.val.BoundedAwayFromZero := by
      intro h2_apart
      -- a₂.equiv 0 and BoundedAway a₂ leads to contradiction (same argument)
      obtain ⟨k₀, N₀, hN₀⟩ := h2_apart
      obtain ⟨μ_eq_z, hμ_eq_z⟩ := h2_eq_zero
      let n_test := max N₀ (μ_eq_z k₀)
      have h_n_ge_N0 : N₀ ≤ n_test := le_max_left _ _
      have h_n_ge_μ : μ_eq_z k₀ ≤ n_test := le_max_right _ _
      have h_apart_n := hN₀ n_test h_n_ge_N0
      have h_eqz_n := hμ_eq_z k₀ n_test h_n_ge_μ
      unfold TauRat.lt at h_apart_n h_eqz_n
      rw [TauRat.toRat_abs, toRat_sub] at h_eqz_n
      rw [TauRat.ofNatRecip_toRat, TauRat.toRat_abs] at h_apart_n
      rw [TauRat.ofNatRecip_toRat] at h_eqz_n
      have h_zero_n : (TauReal.zero.approx n_test) = TauRat.zero := rfl
      rw [h_zero_n, show (TauRat.zero.toRat : Rat) = 0 from toRat_zero, sub_zero] at h_eqz_n
      linarith
    show TauReal.equiv (CauchyTauReal.inv a₁).val (CauchyTauReal.inv a₂).val
    have h1_val : (CauchyTauReal.inv a₁).val = TauReal.zero := by
      unfold CauchyTauReal.inv; simp only [dif_neg h1]; rfl
    have h2_val : (CauchyTauReal.inv a₂).val = TauReal.zero := by
      unfold CauchyTauReal.inv; simp only [dif_neg h2_not_apart]; rfl
    rw [h1_val, h2_val]
    exact TauReal.equiv_refl _

-- ============================================================
-- PART 5: TauRealQ.inv (lift to quotient)
-- ============================================================

noncomputable def TauRealQ.inv : TauRealQ → TauRealQ :=
  Quotient.lift (fun a => (CauchyTauReal.inv a).toQ)
    (fun a b h => Quotient.sound (CauchyTauReal.inv_respects_equiv a b h))

@[simp] theorem TauRealQ.inv_mk (a : CauchyTauReal) :
    TauRealQ.inv a.toQ = (CauchyTauReal.inv a).toQ := rfl

noncomputable instance : Inv TauRealQ := ⟨TauRealQ.inv⟩

-- ============================================================
-- PART 6: Field TauRealQ instance (KEYSTONE — noncomputable)
-- ============================================================

private theorem TauRealQ.from_equiv {a b : CauchyTauReal}
    (h : CauchyTauReal.equiv a b) : a.toQ = b.toQ :=
  Quotient.sound h

/-- **Wave 41c KEYSTONE: Field TauRealQ instance** (noncomputable).

    The constructive cost is exactly one `Classical.byCases` on
    `a.val.BoundedAwayFromZero`, deferred via `CauchyTauReal.inv`.
    Every Field axiom proven by Quotient.inductionOn + classical
    case analysis. Inherits CommRing axioms from Wave 41b. -/
noncomputable instance : Field TauRealQ where
  __ := (inferInstance : CommRing TauRealQ)
  inv := TauRealQ.inv
  exists_pair_ne :=
    ⟨(0 : TauRealQ), (1 : TauRealQ), by
      intro h
      have h_eq : CauchyTauReal.zero.toQ = CauchyTauReal.one.toQ := h
      rw [CauchyTauReal.toQ_eq_iff] at h_eq
      obtain ⟨μ, hμ⟩ := h_eq
      have h_step := hμ 0 (μ 0) (le_refl _)
      unfold TauRat.lt at h_step
      rw [TauRat.toRat_abs, toRat_sub, TauRat.ofNatRecip_toRat] at h_step
      have h_zero_n : CauchyTauReal.zero.val.approx (μ 0) = TauRat.zero := rfl
      have h_one_n : CauchyTauReal.one.val.approx (μ 0) = TauRat.one := rfl
      rw [h_zero_n, h_one_n] at h_step
      rw [show (TauRat.zero.toRat : Rat) = 0 from toRat_zero] at h_step
      rw [show (TauRat.one.toRat : Rat) = 1 from toRat_one] at h_step
      simp at h_step⟩
  mul_inv_cancel x hx := by
    induction x using Quotient.ind with
    | _ a =>
    -- a.toQ ≠ 0, so a.val ≢ 0 (Cauchy-equiv), so a.val.BoundedAwayFromZero
    have h_not_zero : ¬ TauReal.equiv a.val TauReal.zero := by
      intro h_eq
      apply hx
      show a.toQ = CauchyTauReal.zero.toQ
      rw [CauchyTauReal.toQ_eq_iff]
      exact h_eq
    have h_apart : a.val.BoundedAwayFromZero :=
      TauReal.boundedAway_of_not_equiv_zero a.val a.isCauchy h_not_zero
    -- Goal: a.toQ * (TauRealQ.inv a.toQ) = 1
    show TauRealQ.mul a.toQ (TauRealQ.inv a.toQ) = TauRealQ.one
    -- TauRealQ.inv a.toQ = (CauchyTauReal.inv a).toQ
    -- CauchyTauReal.inv a = ⟨a.val.inv, ..⟩  (since BoundedAway)
    show (a.mul (CauchyTauReal.inv a)).toQ = CauchyTauReal.one.toQ
    apply TauRealQ.from_equiv
    show TauReal.equiv (a.val.mul (CauchyTauReal.inv a).val) TauReal.one
    have h_inv_val : (CauchyTauReal.inv a).val = a.val.inv := by
      classical
      unfold CauchyTauReal.inv
      simp only [dif_pos h_apart]
    rw [h_inv_val]
    exact TauReal.mul_inv_cancel a.val h_apart
  inv_zero := by
    classical
    show TauRealQ.inv (0 : TauRealQ) = 0
    show TauRealQ.inv CauchyTauReal.zero.toQ = CauchyTauReal.zero.toQ
    rw [TauRealQ.inv_mk]
    apply TauRealQ.from_equiv
    show TauReal.equiv (CauchyTauReal.inv CauchyTauReal.zero).val TauReal.zero
    -- zero is not BoundedAwayFromZero, so inv branches to zero
    have h_zero_not_apart : ¬ CauchyTauReal.zero.val.BoundedAwayFromZero := by
      intro ⟨k, N, hN⟩
      have := hN N (le_refl _)
      unfold TauRat.lt at this
      rw [TauRat.ofNatRecip_toRat, TauRat.toRat_abs] at this
      have h_zero_eq : CauchyTauReal.zero.val.approx N = TauRat.zero := rfl
      rw [h_zero_eq, show (TauRat.zero.toRat : Rat) = 0 from toRat_zero, abs_zero] at this
      have h_recip_pos : (0 : Rat) < 1 / ((k : Rat) + 1) := by
        have : (0 : Rat) < (k : Rat) + 1 := by
          have : (0 : Rat) ≤ (k : Rat) := by exact_mod_cast Nat.zero_le k
          linarith
        exact div_pos (by norm_num) this
      linarith
    have h_branch : (CauchyTauReal.inv CauchyTauReal.zero).val = TauReal.zero := by
      unfold CauchyTauReal.inv
      simp only [dif_neg h_zero_not_apart]
      rfl
    rw [h_branch]
    exact TauReal.equiv_refl _
  nnqsmul := _
  qsmul := _

-- ============================================================
-- PART 7: Wave 41c synthesis theorem
-- ============================================================

/-- **Wave 41c H8 Mathlib-Field-Bridge Synthesis (KEYSTONE)**.

    Five-clause structural significance:
    1. Field TauRealQ instance exists (noncomputable, classical).
    2. The constructive cost is exactly Classical.byCases on
       BoundedAwayFromZero (Markov for τ-Real).
    3. Cauchy subtype closed under inv (under apartness).
    4. mul_inv_cancel for nonzero (apartness ⇒ inverse witness).
    5. inv_zero = 0 (Mathlib convention; degenerate case). -/
theorem h8_taureal_mathlib_field_bridge_synthesis :
    Nonempty (Field TauRealQ) ∧
    -- Markov-classical bridge witnessed
    (∀ a : TauReal, a.IsCauchy → ¬ TauReal.equiv a TauReal.zero →
      a.BoundedAwayFromZero) ∧
    -- IsCauchy preserved under inv (apartness hypothesis)
    (∀ a : TauReal, a.IsCauchy → a.BoundedAwayFromZero → a.inv.IsCauchy) ∧
    -- inv respects equiv on Cauchy reps
    (∀ a₁ a₂ : TauReal, a₁.IsCauchy → a₂.IsCauchy →
      a₁.BoundedAwayFromZero → a₂.BoundedAwayFromZero →
      TauReal.equiv a₁ a₂ → TauReal.equiv a₁.inv a₂.inv) ∧
    -- mul_inv_cancel at TauReal level (Wave 41c upstream)
    (∀ a : TauReal, a.BoundedAwayFromZero →
      TauReal.equiv (a.mul a.inv) TauReal.one) :=
  ⟨⟨inferInstance⟩,
   TauReal.boundedAway_of_not_equiv_zero,
   TauReal.IsCauchy_inv,
   TauReal.inv_respects_equiv_under_cauchy,
   TauReal.mul_inv_cancel⟩

end Tau.Boundary
