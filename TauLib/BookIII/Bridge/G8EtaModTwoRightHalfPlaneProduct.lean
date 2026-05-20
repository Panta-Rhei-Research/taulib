import TauLib.BookIII.Bridge.G8EtaModTwoConditionalSeriesProductBridge

/-!
# TauLib.BookIII.Bridge.G8EtaModTwoRightHalfPlaneProduct

Safe-half-plane eta product algebra for the Lane-A zero-height corridor.

The conditional-series/product bridge already names the analytic targets that
remain on the real open unit interval.  This module closes the theorem-backed
ordinary `LSeries` product identity on the safe half-plane `1 < Re(s)` and
then forwards it to Mathlib's mod-two `ZMod.LFunction`.

No result here uses RH, accepted coverage, the final live hinge, O3, full
divisor transfer, or analytic-completion uniqueness.
-/

set_option autoImplicit false

noncomputable section

namespace Tau.BookIII.Bridge

open Complex Filter

open scoped BigOperators Topology

-- ============================================================
-- EVEN COEFFICIENT DECOMPOSITION
-- ============================================================

/-- Indicator for the positive-index even terms in the mod-two coefficient
    decomposition. -/
def g8EtaModTwoEvenIndicator (n : ℕ) : ℂ :=
  if Even n then 1 else 0

/-- Mod-two coefficient that selects the even residue class. -/
def g8EtaModTwoEvenCoeff : ZMod 2 → ℂ :=
  fun j => if j = 0 then 1 else 0

/-- The mod-two even coefficient agrees with the natural-number even
    indicator. -/
theorem g8EtaModTwoEvenCoeff_nat_eq_indicator (n : ℕ) :
    g8EtaModTwoEvenCoeff (n : ZMod 2) =
      g8EtaModTwoEvenIndicator n := by
  unfold g8EtaModTwoEvenCoeff g8EtaModTwoEvenIndicator
  by_cases hEven : Even n
  · rw [(ZMod.natCast_eq_zero_iff_even).mpr hEven]
    simp [hEven]
  · have hOdd : Odd n := Nat.not_even_iff_odd.mp hEven
    rw [(ZMod.natCast_eq_one_iff_odd).mpr hOdd]
    simp [hEven]

/-- The eta mod-two coefficient is `1 - 2 * evenIndicator` on positive
    indices, matching odd `+1` and even `-1`. -/
theorem g8EtaModTwoNatCoeff_eq_one_sub_two_evenIndicator (n : ℕ) :
    g8EtaModTwoNatCoeff n =
      (fun m : ℕ =>
        (1 : ℂ) - (2 : ℂ) * g8EtaModTwoEvenIndicator m) n := by
  by_cases hEven : Even n
  · rw [g8EtaModTwoNatCoeff_of_even hEven]
    norm_num [g8EtaModTwoEvenIndicator, hEven]
  · have hOdd : Odd n := Nat.not_even_iff_odd.mp hEven
    rw [g8EtaModTwoNatCoeff_of_odd hOdd]
    norm_num [g8EtaModTwoEvenIndicator, hEven]

-- ============================================================
-- EVEN SUBSERIES ON THE SAFE HALF-PLANE
-- ============================================================

/-- The mod-two even `LFunction` is the scaled zeta function.  This is a
    finite residue-class calculation inside Mathlib's `ZMod.LFunction`. -/
theorem g8EtaModTwoEvenCoeff_LFunction_eq_scaledZeta (s : ℂ) :
    ZMod.LFunction g8EtaModTwoEvenCoeff s =
      (2 : ℂ) ^ (-s) * riemannZeta s := by
  unfold ZMod.LFunction g8EtaModTwoEvenCoeff
  rw [← (ZMod.finEquiv 2).toEquiv.sum_comp
    (fun j : ZMod 2 =>
      (if j = 0 then (1 : ℂ) else 0) *
        HurwitzZeta.hurwitzZeta (ZMod.toAddCircle j) s)]
  rw [Fin.sum_univ_two]
  norm_num [ZMod.finEquiv, HurwitzZeta.hurwitzZeta_zero]

/-- The ordinary even-indicator `LSeries` is the scaled zeta function on
    `1 < Re(s)`. -/
theorem g8EtaModTwoEvenIndicator_LSeries_eq_scaledZeta
    {s : ℂ} (hs : 1 < s.re) :
    LSeries g8EtaModTwoEvenIndicator s =
      (2 : ℂ) ^ (-s) * riemannZeta s := by
  calc
    LSeries g8EtaModTwoEvenIndicator s =
        LSeries (fun n : ℕ => g8EtaModTwoEvenCoeff (n : ZMod 2)) s := by
      exact (LSeries_congr
        (fun {n} _ => g8EtaModTwoEvenCoeff_nat_eq_indicator n) s).symm
    _ = ZMod.LFunction g8EtaModTwoEvenCoeff s :=
      (ZMod.LFunction_eq_LSeries g8EtaModTwoEvenCoeff (s := s) hs).symm
    _ = (2 : ℂ) ^ (-s) * riemannZeta s :=
      g8EtaModTwoEvenCoeff_LFunction_eq_scaledZeta s

/-- The even-indicator `LSeries` is summable on the safe half-plane. -/
theorem g8EtaModTwoEvenIndicator_LSeriesSummable_of_one_lt_re
    {s : ℂ} (hs : 1 < s.re) :
    LSeriesSummable g8EtaModTwoEvenIndicator s := by
  have hZMod :
      LSeriesSummable
        (fun n : ℕ => g8EtaModTwoEvenCoeff (n : ZMod 2)) s :=
    ZMod.LSeriesSummable_of_one_lt_re g8EtaModTwoEvenCoeff (s := s) hs
  exact (LSeriesSummable_congr s
    (fun {n} _ => g8EtaModTwoEvenCoeff_nat_eq_indicator n)).mp hZMod

-- ============================================================
-- PRODUCT IDENTITIES
-- ============================================================

/-- The theorem-backed ordinary `LSeries` product identity on the safe
    half-plane. -/
theorem g8EtaModTwoLSeriesProductIdentityOnRightHalfPlane_theorem :
    G8EtaModTwoLSeriesProductIdentityOnRightHalfPlane := by
  intro s hs
  have hOne : LSeriesSummable (1 : ℕ → ℂ) s :=
    LSeriesSummable_one_iff.mpr hs
  have hEven : LSeriesSummable g8EtaModTwoEvenIndicator s :=
    g8EtaModTwoEvenIndicator_LSeriesSummable_of_one_lt_re hs
  exact {
    productIdentity := by
      calc
        LSeries g8EtaModTwoNatCoeff s =
            LSeries
              (fun n : ℕ =>
                (1 : ℂ) - (2 : ℂ) * g8EtaModTwoEvenIndicator n) s := by
          exact LSeries_congr
            (fun {n} _ =>
              g8EtaModTwoNatCoeff_eq_one_sub_two_evenIndicator n) s
        _ = LSeries ((1 : ℕ → ℂ) -
              (2 : ℂ) • g8EtaModTwoEvenIndicator) s := by
          rfl
        _ = LSeries (1 : ℕ → ℂ) s -
              LSeries ((2 : ℂ) • g8EtaModTwoEvenIndicator) s := by
          rw [LSeries_sub hOne (hEven.smul 2)]
        _ = riemannZeta s -
              2 * ((2 : ℂ) ^ (-s) * riemannZeta s) := by
          rw [LSeries_one_eq_riemannZeta hs, LSeries_smul,
            g8EtaModTwoEvenIndicator_LSeries_eq_scaledZeta hs]
        _ = (1 - (2 : ℂ) ^ (1 - s)) * riemannZeta s := by
          have hpow :
              (2 : ℂ) ^ (1 - s) =
                (2 : ℂ) * (2 : ℂ) ^ (-s) := by
            calc
              (2 : ℂ) ^ (1 - s) =
                  (2 : ℂ) ^ ((1 : ℂ) + -s) := by
                ring_nf
              _ = (2 : ℂ) ^ (1 : ℂ) * (2 : ℂ) ^ (-s) := by
                rw [Complex.cpow_add _ _ (by norm_num : (2 : ℂ) ≠ 0)]
              _ = (2 : ℂ) * (2 : ℂ) ^ (-s) := by
                rw [Complex.cpow_one]
          rw [hpow]
          ring
  }

/-- The theorem-backed mod-two `LFunction` product identity on the safe
    half-plane. -/
theorem g8EtaModTwoLFunctionProductIdentityOnRightHalfPlane_theorem :
    G8EtaModTwoLFunctionProductIdentityOnRightHalfPlane :=
  g8EtaModTwoLFunctionProductIdentityOnRightHalfPlane_of_LSeriesProduct
    g8EtaModTwoLSeriesProductIdentityOnRightHalfPlane_theorem

-- ============================================================
-- RED-TEAM FALSIFIERS
-- ============================================================

/-- Any safe-half-plane ordinary product mismatch refutes the theorem-backed
    product identity. -/
theorem G8EtaModTwoLSeriesProductRightHalfPlaneMismatch.refutesTheorem
    (w : G8EtaModTwoLSeriesProductRightHalfPlaneMismatch) :
    False :=
  w.refutes g8EtaModTwoLSeriesProductIdentityOnRightHalfPlane_theorem

/-- Any safe-half-plane `LFunction` product mismatch refutes the theorem-backed
    `LFunction` product identity. -/
structure G8EtaModTwoLFunctionProductRightHalfPlaneMismatch where
  s : ℂ
  halfPlane : 1 < s.re
  mismatch :
    g8EtaModTwoLFunction s ≠
      (1 - (2 : ℂ) ^ (1 - s)) * riemannZeta s

/-- The `LFunction` product mismatch falsifier refutes the theorem-backed
    right-half-plane identity. -/
theorem G8EtaModTwoLFunctionProductRightHalfPlaneMismatch.refutesTheorem
    (w : G8EtaModTwoLFunctionProductRightHalfPlaneMismatch) :
    False :=
  w.mismatch
    (g8EtaModTwoLFunctionProductIdentityOnRightHalfPlane_theorem
      w.s w.halfPlane).productIdentity

end Tau.BookIII.Bridge
