import TauLib.BookV.Cosmology.HeavySeedBirth
import TauLib.BookI.Boundary.TauRealSqrt
import TauLib.BookI.Boundary.Bridge.TauRealQuotientField
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push
import Mathlib.Tactic.FieldSimp

/-!
# TauLib.BookV.Cosmology.IotaTauTauRealHelpers

**Shared `iota_tau_TauReal`-related helpers extracted from `T2KerrUniqueness.lean`
(Wave R10-5 refactor).**

This module collects the small but load-bearing collection of toRat-level
identities, eventual-positivity / eventual-bound / `BoundedAwayFromZero`
witnesses, and `IsCauchy` witnesses for `iota_tau_TauReal` and the radicand
`1 − ι_τ` (alias `1 − iota_tau_T2_bound_TauReal`).

Originally these lived as `private theorem`s inside `T2KerrUniqueness.lean`
(around lines 350–505), feeding the headline `f_iota_t2_TauReal_squared_eq`
and `f_iota_t2_TauReal_isCauchy` results. Wave R10-5 promotes them so that
downstream consumers (HSB tightening in Wave R10-2 onward, Wave R11+
V.T-LRD-1B/C/D Cauchy-rate work, etc.) can reuse them without re-proving
inline.

**Provenance notes:**
- All proofs are verbatim ports from the original private definitions in
  `T2KerrUniqueness.lean` — the only delta is dropping the `private`
  keyword and relocating to this module.
- The `iota_tau_T2_bound_TauReal := iota_tau_TauReal` alias from
  `HeavySeedBirth.lean:477` makes the `_T2_bound_TauReal`-named lemmas
  defeq-applicable to plain `iota_tau_TauReal` consumers.

**Trust budget:** zero `sorry`, zero new `axiom`. All proofs delegate to
existing named lemmas in `BookI/Boundary/*` and structural Cauchy /
toRat identities.
-/

namespace Tau.BookV.Cosmology

open Tau.Boundary

-- ============================================================
-- HELPER 1: pi_plus_e_approx_in_interval
-- ============================================================

/-- For every `n ≥ 1`, the toRat value of `(π + e).approx n` lies in the
    closed interval `[11/3, 7]`. Combines `pi_plus_e_partial_lower_bound`
    and `pi_plus_e_approx_le_seven` with a unified unfolding. -/
theorem pi_plus_e_approx_in_interval (n : Nat) (hn : 1 ≤ n) :
    (11 : Rat) / 3 ≤ ((TauReal.pi.add TauReal.e).approx n).toRat ∧
    ((TauReal.pi.add TauReal.e).approx n).toRat ≤ 7 := by
  have h_unfold :
      ((TauReal.pi.add TauReal.e).approx n).toRat
        = (TauRat.pi_partial n).toRat + (TauRat.e_partial n).toRat := by
    show ((TauReal.pi.approx n).add (TauReal.e.approx n)).toRat = _
    rw [toRat_add]; rfl
  refine ⟨?_, ?_⟩
  · rw [h_unfold]; exact TauReal.pi_plus_e_partial_lower_bound n hn
  · exact TauReal.pi_plus_e_approx_le_seven n

-- ============================================================
-- HELPER 2: iota_tau_TauReal_approx_toRat_eq
-- ============================================================

/-- `iota_tau_TauReal.approx n .toRat = 2 / (π+e).approx n .toRat` for every
    `n ≥ 1`.

    Mirrors the unfolding inside `iota_tau_mul_pi_plus_e_eq_two` (lines
    132–154 of `TauRealIotaTau.lean`): past the BAZ modulus,
    `(π+e).approx n` is nonzero, so `inv` takes the `TauRat.inv` branch and
    `toRat` reduces to scalar division. -/
theorem iota_tau_TauReal_approx_toRat_eq (n : Nat) (hn : 1 ≤ n) :
    (iota_tau_TauReal.approx n).toRat
      = 2 / ((TauReal.pi.add TauReal.e).approx n).toRat := by
  have h_pe_pos : 0 < ((TauReal.pi.add TauReal.e).approx n).toRat := by
    have h_lb := (pi_plus_e_approx_in_interval n hn).1
    linarith
  have h_pe_nz : ((TauReal.pi.add TauReal.e).approx n).is_nonzero := by
    rw [TauRat.is_nonzero_iff_toRat_ne_zero]
    linarith
  -- iota_tau_TauReal.approx n
  --   = TauReal.iota_tau.approx n
  --   = (TauReal.two.approx n).mul ((π+e).inv.approx n)
  show (((TauReal.two.approx n).mul ((TauReal.pi.add TauReal.e).inv.approx n))).toRat
        = 2 / ((TauReal.pi.add TauReal.e).approx n).toRat
  have h_inv_approx :
      (TauReal.pi.add TauReal.e).inv.approx n
        = TauRat.inv ((TauReal.pi.add TauReal.e).approx n) h_pe_nz := by
    show (if h : ((TauReal.pi.add TauReal.e).approx n).is_nonzero
          then TauRat.inv ((TauReal.pi.add TauReal.e).approx n) h
          else TauRat.one) = _
    rw [dif_pos h_pe_nz]
  rw [h_inv_approx, toRat_mul, TauReal.two_approx_toRat, toRat_inv]
  -- 2 * ((π+e).toRat)⁻¹ = 2 / (π+e).toRat
  rw [div_eq_mul_inv]

-- ============================================================
-- HELPER 3: iota_tau_TauReal_lt_one_eventually
-- ============================================================

/-- For every `n ≥ 1`, `(iota_tau_TauReal.approx n).toRat < 1`.

    `iota_tau ≈ 2/(π+e) ≤ 2/(11/3) = 6/11 < 1`. The constant `11/3` is
    the lower bound established by `pi_plus_e_partial_lower_bound`. -/
theorem iota_tau_TauReal_lt_one_eventually :
    ∃ Ns : Nat, ∀ n : Nat, Ns ≤ n →
      (iota_tau_TauReal.approx n).toRat < 1 := by
  refine ⟨1, fun n hn => ?_⟩
  rw [iota_tau_TauReal_approx_toRat_eq n hn]
  have ⟨h_lb, _⟩ := pi_plus_e_approx_in_interval n hn
  have h_pe_pos : 0 < ((TauReal.pi.add TauReal.e).approx n).toRat := by linarith
  rw [div_lt_one h_pe_pos]
  linarith

-- ============================================================
-- HELPER 4: one_sub_iota_tau_T2_bound_pos_eventually
-- ============================================================

/-- The radicand `1 − ι_τ` is eventually positive. Direct corollary of
    `iota_tau_TauReal_lt_one_eventually`: at toRat level,
    `((1 − ι_τ).approx n).toRat = 1 − (ι_τ.approx n).toRat`. -/
theorem one_sub_iota_tau_T2_bound_pos_eventually :
    ∃ Ns : Nat, ∀ n : Nat, Ns ≤ n →
      0 < (((TauReal.one).sub iota_tau_T2_bound_TauReal).approx n).toRat := by
  obtain ⟨Ns, h_iota_lt_one⟩ := iota_tau_TauReal_lt_one_eventually
  refine ⟨Ns, fun n hn => ?_⟩
  have h_unfold :
      (((TauReal.one).sub iota_tau_T2_bound_TauReal).approx n).toRat
        = 1 - (iota_tau_T2_bound_TauReal.approx n).toRat := by
    show (((TauReal.one).approx n).add ((iota_tau_T2_bound_TauReal).negate.approx n)).toRat = _
    rw [toRat_add]
    show ((TauReal.one).approx n).toRat
            + ((iota_tau_T2_bound_TauReal.approx n).negate).toRat = _
    rw [toRat_negate]
    show (TauRat.one).toRat + (- (iota_tau_T2_bound_TauReal.approx n).toRat) = _
    rw [toRat_one]; ring
  rw [h_unfold]
  show 0 < 1 - (iota_tau_TauReal.approx n).toRat
  have h_lt := h_iota_lt_one n hn
  linarith

-- ============================================================
-- HELPER 5: one_sub_iota_tau_T2_bound_BAZ
-- ============================================================

/-- The radicand `1 − ι_τ` is bounded away from zero. From
    `(iota.approx n).toRat ≤ 6/11`, we get
    `(1 − ι_τ).approx n .toRat ≥ 5/11 > 1/3`, giving BAZ with witness
    `k = 2` (so `1/(k+1) = 1/3`). -/
theorem one_sub_iota_tau_T2_bound_BAZ :
    ((TauReal.one).sub iota_tau_T2_bound_TauReal).BoundedAwayFromZero := by
  refine ⟨2, 1, fun n hn => ?_⟩
  unfold TauRat.lt
  rw [TauRat.ofNatRecip_toRat, TauRat.toRat_abs]
  have h_iota_eq := iota_tau_TauReal_approx_toRat_eq n hn
  have ⟨h_lb, h_ub⟩ := pi_plus_e_approx_in_interval n hn
  have h_pe_pos : 0 < ((TauReal.pi.add TauReal.e).approx n).toRat := by linarith
  -- iota.approx n .toRat = 2 / (π+e).approx n .toRat ≤ 2/(11/3) = 6/11
  have h_iota_le : (iota_tau_TauReal.approx n).toRat ≤ 6 / 11 := by
    rw [h_iota_eq, div_le_iff₀ h_pe_pos]
    linarith
  have h_one_sub_unfold :
      (((TauReal.one).sub iota_tau_T2_bound_TauReal).approx n).toRat
        = 1 - (iota_tau_T2_bound_TauReal.approx n).toRat := by
    -- Same unfolding chain as `pos_eventually` (which works):
    show (((TauReal.one).approx n).add ((iota_tau_T2_bound_TauReal).negate.approx n)).toRat = _
    rw [toRat_add]
    show ((TauReal.one).approx n).toRat
            + ((iota_tau_T2_bound_TauReal.approx n).negate).toRat = _
    rw [toRat_negate]
    show (TauRat.one).toRat + (- (iota_tau_T2_bound_TauReal.approx n).toRat) = _
    rw [toRat_one]; ring
  rw [h_one_sub_unfold]
  -- iota_tau_T2_bound_TauReal = iota_tau_TauReal definitionally (via HSB:476 alias)
  -- so the upper bound on iota carries through.
  have h_iota_T2_le : (iota_tau_T2_bound_TauReal.approx n).toRat ≤ 6 / 11 := h_iota_le
  have h_pos : 0 < 1 - (iota_tau_T2_bound_TauReal.approx n).toRat := by linarith
  rw [abs_of_pos h_pos]
  show (1 : Rat) / ((2 : Nat) + 1) < 1 - (iota_tau_T2_bound_TauReal.approx n).toRat
  push_cast
  linarith

-- ============================================================
-- HELPER 6: iota_tau_TauReal_isCauchy
-- ============================================================

/-- `iota_tau_TauReal.IsCauchy`. By definition,
    `iota_tau_TauReal = TauReal.div TauReal.two (π + e) = 2.mul (π+e).inv`,
    a product of two Cauchy sequences (the constant `2` and `inv` of the
    Cauchy `π + e`). -/
theorem iota_tau_TauReal_isCauchy : iota_tau_TauReal.IsCauchy := by
  show (TauReal.two.mul (TauReal.pi.add TauReal.e).inv).IsCauchy
  apply TauReal.IsCauchy_mul
  · -- TauReal.two = TauReal.fromTauRat ⟨⟨2,0⟩, 1, _⟩ — constant sequence is Cauchy
    refine ⟨fun _ => 0, fun k _ _ _ _ => ?_⟩
    show TauRat.lt _ _
    unfold TauRat.lt
    rw [TauRat.toRat_abs, toRat_sub]
    show |(TauReal.two.approx _).toRat - (TauReal.two.approx _).toRat|
            < (TauRat.ofNatRecip k).toRat
    rw [TauReal.two_approx_toRat, TauReal.two_approx_toRat]
    simp
    exact TauRat.ofNatRecip_pos k
  · apply TauReal.IsCauchy_inv
    · exact TauReal.IsCauchy_add _ _ TauReal.pi_isCauchy TauReal.e_isCauchy
    · exact TauReal.pi_plus_e_boundedAwayFromZero

-- ============================================================
-- HELPER 7: one_sub_iota_tau_T2_bound_isCauchy
-- ============================================================

/-- The radicand `1 − ι_τ` is Cauchy. -/
theorem one_sub_iota_tau_T2_bound_isCauchy :
    ((TauReal.one).sub iota_tau_T2_bound_TauReal).IsCauchy := by
  show ((TauReal.one).add iota_tau_T2_bound_TauReal.negate).IsCauchy
  apply TauReal.IsCauchy_add
  · exact TauReal.one_isCauchy
  · exact TauReal.IsCauchy_negate _ iota_tau_TauReal_isCauchy

-- ============================================================
-- HELPER 8: one_sub_iota_tau_T2_bound_sign
-- ============================================================

/-- The `h_sign` witness for `sqrt_sq` / `sqrt_isCauchy` instantiated at
    `a := 1 − ι_τ`. Identical to `one_sub_iota_tau_T2_bound_pos_eventually`;
    exposed under this name for use at sqrt API call sites. -/
theorem one_sub_iota_tau_T2_bound_sign :
    ∃ Ns : Nat, ∀ n : Nat, Ns ≤ n →
      0 < (((TauReal.one).sub iota_tau_T2_bound_TauReal).approx n).toRat :=
  one_sub_iota_tau_T2_bound_pos_eventually

end Tau.BookV.Cosmology
