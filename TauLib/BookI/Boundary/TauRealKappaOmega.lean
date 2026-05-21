import TauLib.BookI.Boundary.TauRealIotaTau
import TauLib.BookI.Boundary.TauRealIotaTauBBP
import TauLib.BookI.Boundary.Bridge.TauRealQuotientField
import Mathlib.Tactic.Ring
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity

/-!
# TauLib.BookI.Boundary.TauRealKappaOmega

The Möbius companion `κ_ω := ι_τ / (1 + ι_τ)` at TauReal level, closing
the algebraic triad `{ι_τ, κ_D, κ_ω}` of the paper's
**Corollary 8.11 (Möbius companion scalar)**.

## Paper reference

`papers/research-papers/iota-tau/main.tex`, Corollary 8.11 (around line
3143) defines `κ_ω := ι_τ / (1+ι_τ) ≈ 0.25445` as the canonical Möbius
transform `x ↦ x/(1+x)` of `ι_τ`, satisfying the structural identity

  `κ_ω · (1 + ι_τ) ≡ ι_τ`      (paper eq:triad-mobius)

This module ships the τ-native form: `TauReal.kappa_omega`, its
`IsCauchy` certificate, the defining identity above (as
`TauReal.equiv`), and a BBP-flavoured 50-digit numerical certificate
(via `native_decide`) mirroring the `TauReal.iota_tau_bbp_certified_50d`
pattern of `TauRealIotaTauBBP.lean`.

## V3 substantive gap close

This module addresses the audit note from the 2nd audit pass:

> §8 Möbius companion `κ_ω` — only fiat product `κ_ω·ι_τ` exists in
> TauLib (`BookV/Cosmology/H0TensionLCDM.lean`); no structural
> definition of `κ_ω`.

The fiat `kappa_omega_iota_x10000 = 868` from `H0TensionLCDM.lean:402`
is the `Nat`-scaled prediction product `κ_ω · ι_τ ≈ 0.0868` used by the
σ₈ suppression callsite. This module provides the *structural*
Cauchy-completion form of `κ_ω` itself, decoupled from the fiat-Nat
product downstream.

## Public API

* `TauReal.kappa_omega` — the Cauchy `κ_ω = ι_τ / (1 + ι_τ)`.
* `TauReal.one_plus_iota_tau_boundedAwayFromZero` —
  apartness witness needed to invert `1 + ι_τ`.
* `TauReal.kappa_omega_isCauchy` — Cauchy stability certificate.
* `TauReal.kappa_omega_mul_one_plus_iota_tau_eq_iota_tau` —
  the defining identity `κ_ω · (1 + ι_τ) ≡ ι_τ` (paper eq:triad-mobius).
* `TauReal.kappa_omega_bbp` — BBP-flavoured variant for high-precision
  certification (uses `TauReal.pi_bbp` instead of `TauReal.pi`).
* `TauRat.kappa_omega_fiat_50d` — the 50-decimal mpmath truncation.
* `TauReal.kappa_omega_bbp_certified_50d` — the 50-digit
  `native_decide` certificate.

## Trust budget

* `sorry`: 0.
* Axioms: kernel-only (no new axioms introduced).
-/

set_option autoImplicit false

namespace Tau.Boundary

open Tau.Denotation

-- ============================================================
-- PART 1: STRUCTURAL κ_ω = ι_τ / (1 + ι_τ)
-- ============================================================

/-- The Möbius companion of `ι_τ`, structurally defined as
    `ι_τ / (1 + ι_τ)` in the Cauchy completion of TauRat.

    Closes the triad `{ι_τ, κ_D, κ_ω}` algebraically: from
    `κ_D = 1 − ι_τ` and `κ_ω · (1+ι_τ) = ι_τ`, we derive
    `κ_ω = ι_τ · κ_D / (1 − ι_τ²)` (paper eq:triad-product).

    Numerical value: `κ_ω ≈ 0.254456989684478870914650414407…`. -/
def TauReal.kappa_omega : TauReal :=
  TauReal.div TauReal.iota_tau (TauReal.one.add TauReal.iota_tau)

-- ============================================================
-- PART 2: APPROX-LEVEL HELPERS — positivity of ι_τ and 1 + ι_τ
-- ============================================================

/-- `(ι_τ.approx n).toRat ≥ 0` for `n ≥ 1`.

    Reduces to `2 / (π + e).approx n .toRat ≥ 0` via the inverse
    branch (past index 1, `(π + e).approx n` is nonzero), and
    `(π+e).approx n .toRat ≥ 11/3 > 0`. -/
theorem TauReal.iota_tau_approx_nonneg (n : Nat) (hn : 1 ≤ n) :
    0 ≤ (TauReal.iota_tau.approx n).toRat := by
  have h_pe_pos : 0 < ((TauReal.pi.add TauReal.e).approx n).toRat := by
    have h := TauReal.pi_plus_e_partial_pos n hn
    show 0 < ((TauReal.pi.approx n).add (TauReal.e.approx n)).toRat
    rw [toRat_add]
    exact h
  have h_pe_nz : ((TauReal.pi.add TauReal.e).approx n).is_nonzero := by
    rw [TauRat.is_nonzero_iff_toRat_ne_zero]
    linarith
  -- iota_tau.approx n = (two.approx n).mul ((π+e).inv.approx n)
  have h_unfold :
      (TauReal.iota_tau.approx n).toRat
        = 2 / ((TauReal.pi.add TauReal.e).approx n).toRat := by
    show (((TauReal.two.approx n).mul
          ((TauReal.pi.add TauReal.e).inv.approx n))).toRat = _
    have h_inv_approx :
        (TauReal.pi.add TauReal.e).inv.approx n
          = TauRat.inv ((TauReal.pi.add TauReal.e).approx n) h_pe_nz := by
      show (if h : ((TauReal.pi.add TauReal.e).approx n).is_nonzero
            then TauRat.inv ((TauReal.pi.add TauReal.e).approx n) h
            else TauRat.one) = _
      rw [dif_pos h_pe_nz]
    rw [h_inv_approx, toRat_mul, TauReal.two_approx_toRat, toRat_inv,
        div_eq_mul_inv]
  rw [h_unfold]
  have h2 : (0 : Rat) ≤ 2 := by norm_num
  have h_pe_nn : (0 : Rat) ≤ ((TauReal.pi.add TauReal.e).approx n).toRat := by
    linarith
  exact div_nonneg h2 h_pe_nn

/-- `(1 + ι_τ).approx n .toRat = 1 + (ι_τ.approx n).toRat`. -/
theorem TauReal.one_plus_iota_tau_approx_toRat (n : Nat) :
    ((TauReal.one.add TauReal.iota_tau).approx n).toRat
      = 1 + (TauReal.iota_tau.approx n).toRat := by
  show ((TauReal.one.approx n).add (TauReal.iota_tau.approx n)).toRat = _
  rw [toRat_add]
  show (TauRat.one.toRat) + _ = _
  rw [toRat_one]

-- ============================================================
-- PART 3: (1 + ι_τ) IS BOUNDED AWAY FROM ZERO
-- ============================================================

/-- `(1 + ι_τ).BoundedAwayFromZero` — the apartness witness needed to
    invert `1 + ι_τ` and thus form the Möbius companion `κ_ω`.

    Witnesses: `k = 1, N = 1`, giving threshold `1/(k+1) = 1/2`. Past
    `n ≥ 1` we have `ι_τ.approx n ≥ 0`, hence `(1 + ι_τ).approx n ≥ 1
    > 1/2`. -/
theorem TauReal.one_plus_iota_tau_boundedAwayFromZero :
    (TauReal.one.add TauReal.iota_tau).BoundedAwayFromZero := by
  refine ⟨1, 1, fun n hn => ?_⟩
  unfold TauRat.lt
  rw [TauRat.ofNatRecip_toRat, TauRat.toRat_abs]
  -- Goal: 1 / ((1 : Nat) + 1) < |(1 + ι_τ).approx n .toRat|
  rw [TauReal.one_plus_iota_tau_approx_toRat]
  have h_nonneg := TauReal.iota_tau_approx_nonneg n hn
  -- 1 + (iota_tau.approx n).toRat ≥ 1 > 0
  have h_pos : (0 : Rat) < 1 + (TauReal.iota_tau.approx n).toRat := by linarith
  rw [abs_of_pos h_pos]
  show (1 : Rat) / ((1 : Nat) + 1) < 1 + (TauReal.iota_tau.approx n).toRat
  push_cast
  linarith

-- ============================================================
-- PART 4: CAUCHY STABILITY OF κ_ω
-- ============================================================

/-- `(1 + ι_τ).IsCauchy` — sum of two Cauchy reals (constant `1` and
    the Cauchy `ι_τ`). -/
theorem TauReal.one_plus_iota_tau_isCauchy :
    (TauReal.one.add TauReal.iota_tau).IsCauchy :=
  TauReal.IsCauchy_add TauReal.one TauReal.iota_tau
    TauReal.one_isCauchy TauReal.iota_tau_isCauchy

/-- **`TauReal.kappa_omega.IsCauchy`** — the Cauchy stability
    certificate.

    Composition: `kappa_omega = iota_tau · (1 + iota_tau)⁻¹`.
    Each step preserves Cauchy:
    * `iota_tau` is Cauchy (`TauReal.iota_tau_isCauchy`).
    * `1 + iota_tau` is Cauchy (constant `1` + Cauchy `iota_tau`).
    * `(1 + iota_tau)⁻¹` is Cauchy (BAZ-witnessed inverse).
    * Product of two Cauchy is Cauchy (`IsCauchy_mul`). -/
theorem TauReal.kappa_omega_isCauchy : TauReal.kappa_omega.IsCauchy := by
  show (TauReal.iota_tau.mul (TauReal.one.add TauReal.iota_tau).inv).IsCauchy
  apply TauReal.IsCauchy_mul
  · exact TauReal.iota_tau_isCauchy
  · apply TauReal.IsCauchy_inv
    · exact TauReal.one_plus_iota_tau_isCauchy
    · exact TauReal.one_plus_iota_tau_boundedAwayFromZero

-- ============================================================
-- PART 5: DEFINING IDENTITY  κ_ω · (1 + ι_τ) ≡ ι_τ
-- ============================================================

/-- **Paper eq:triad-mobius** (Corollary 8.11):
    `κ_ω · (1 + ι_τ) ≡ ι_τ` at the Cauchy completion.

    Proof: past the BAZ modulus `N = 1` (where `(1+ι_τ).approx n ≥ 1`
    is nonzero), every `(1+ι_τ).approx n` is invertible and the
    pointwise product `(κ_ω · (1+ι_τ)).approx n = ι_τ.approx n · (1+ι_τ).approx n / (1+ι_τ).approx n = ι_τ.approx n`
    holds exactly at `toRat` level via `field_simp`. The Cauchy
    equivalence then has zero pointwise difference past `N = 1`. -/
theorem TauReal.kappa_omega_mul_one_plus_iota_tau_eq_iota_tau :
    TauReal.equiv
      (TauReal.kappa_omega.mul (TauReal.one.add TauReal.iota_tau))
      TauReal.iota_tau := by
  obtain ⟨k₀, N₀, hN₀⟩ := TauReal.one_plus_iota_tau_boundedAwayFromZero
  refine ⟨fun _ => N₀, fun k n hn => ?_⟩
  -- hn : N₀ ≤ n, so (1 + iota_tau).approx n is nonzero
  have h_nz : ((TauReal.one.add TauReal.iota_tau).approx n).is_nonzero :=
    TauReal.is_nonzero_of_bounded_away hN₀ n hn
  -- Compute LHS at toRat level
  have h_lhs_toRat :
      ((TauReal.kappa_omega.mul (TauReal.one.add TauReal.iota_tau)).approx n).toRat
        = (TauReal.iota_tau.approx n).toRat := by
    show (((TauReal.kappa_omega.approx n).mul
          ((TauReal.one.add TauReal.iota_tau).approx n))).toRat = _
    -- kappa_omega.approx n = (iota_tau.approx n).mul ((1 + iota_tau).inv.approx n)
    have h_kw_approx :
        TauReal.kappa_omega.approx n
          = (TauReal.iota_tau.approx n).mul
              ((TauReal.one.add TauReal.iota_tau).inv.approx n) := rfl
    rw [h_kw_approx]
    -- (1+iota_tau).inv.approx n takes the TauRat.inv branch under h_nz
    have h_inv_approx :
        (TauReal.one.add TauReal.iota_tau).inv.approx n
          = TauRat.inv ((TauReal.one.add TauReal.iota_tau).approx n) h_nz := by
      show (if h : ((TauReal.one.add TauReal.iota_tau).approx n).is_nonzero
            then TauRat.inv ((TauReal.one.add TauReal.iota_tau).approx n) h
            else TauRat.one) = _
      rw [dif_pos h_nz]
    rw [h_inv_approx, toRat_mul, toRat_mul, toRat_inv]
    have h_opi_ne :
        ((TauReal.one.add TauReal.iota_tau).approx n).toRat ≠ 0 :=
      (TauRat.is_nonzero_iff_toRat_ne_zero _).mp h_nz
    field_simp
  -- Cauchy bound on the difference
  unfold TauRat.lt
  rw [TauRat.toRat_abs, toRat_sub, TauRat.ofNatRecip_toRat]
  rw [h_lhs_toRat]
  have h_zero : |(TauReal.iota_tau.approx n).toRat
                  - (TauReal.iota_tau.approx n).toRat| = 0 := by
    have : (TauReal.iota_tau.approx n).toRat
              - (TauReal.iota_tau.approx n).toRat = 0 := by ring
    rw [this, abs_zero]
  rw [h_zero]
  have h_pos_k1 : (0 : Rat) < 1 / ((k : Rat) + 1) := by
    have : (0 : Rat) ≤ (k : Rat) := by exact_mod_cast Nat.zero_le k
    have : (0 : Rat) < (k : Rat) + 1 := by linarith
    exact div_pos (by norm_num) this
  linarith

-- ============================================================
-- PART 6: BBP VARIANT FOR HIGH-PRECISION CERTIFICATION
-- ============================================================

/-- The BBP-flavoured `κ_ω`, structurally identical in shape to
    `TauReal.kappa_omega` but built atop `TauReal.iota_tau_bbp`
    (`TauRealIotaTauBBP.lean`) — which uses the BBP π series with
    `6/16^n` geometric decay — so that 50-digit precision is reachable
    in feasible `native_decide` runtime.

    Definitional shape: `κ_ω^bbp := ι_τ^bbp / (1 + ι_τ^bbp)`. -/
def TauReal.kappa_omega_bbp : TauReal :=
  TauReal.div TauReal.iota_tau_bbp (TauReal.one.add TauReal.iota_tau_bbp)

-- ============================================================
-- PART 7: 50-DIGIT FIAT TRUNCATION OF κ_ω
-- ============================================================

/-- The 50-decimal-place truncation of `κ_ω`, computed via mpmath at
    dps=70 from the high-precision `κ_ω = ι_τ/(1+ι_τ)` with
    `ι_τ = 2/(π+e)`.

    Value:
    `0.25445698968447887091465041440792668278769226179167`. -/
def TauRat.kappa_omega_fiat_50d : TauRat :=
  ⟨⟨25445698968447887091465041440792668278769226179167, 0⟩,
   100000000000000000000000000000000000000000000000000,
   by positivity⟩

-- ============================================================
-- PART 8: 50-DIGIT NUMERICAL CERTIFICATE
-- ============================================================

/-- **🎯 50-digit κ_ω certificate**.

    `|TauReal.kappa_omega_bbp.approx 200 − TauRat.kappa_omega_fiat_50d| < 10⁻⁴⁹`.

    Backs the paper's `κ_ω ≈ 0.25445` numerical claim
    (Corollary 8.11) at 50-digit precision, complementing the existing
    `TauReal.iota_tau_bbp_certified_50d` for `ι_τ`.

    **Witness-depth choice (200)**: identical to the `ι_τ` setup
    (`iota_tau_bbp_certified_50d`, `TauRealIotaTauBBP.lean:116`):
    * `pi_bbp.approx 200` error `≤ 6/16^200 ≈ 4×10⁻²⁴²` — vastly past 50 digits.
    * `e.approx 200` error `≤ 4/2^200 ≈ 2×10⁻⁶⁰` — 60 digits, past 50.
    * Propagated through inverse + multiplication for ι_τ, then through
      another inverse + multiplication for `ι_τ/(1+ι_τ)`: the cumulative
      error is `≈ 10⁻⁵⁹`, far inside the `10⁻⁴⁹` tolerance.

    **Discharge**: `native_decide`. The kernel evaluates
    `kappa_omega_bbp.approx 200` to a concrete `TauRat`, subtracts the
    fiat, takes absolute value, and compares against `1/(10^49 - 1)` via
    compiled byte-code. -/
theorem TauReal.kappa_omega_bbp_certified_50d :
    TauRat.lt
      (((TauReal.kappa_omega_bbp.approx 200).sub
         TauRat.kappa_omega_fiat_50d).abs)
      (TauRat.ofNatRecip (10^49 - 1)) := by
  unfold TauRat.lt
  native_decide

end Tau.Boundary
